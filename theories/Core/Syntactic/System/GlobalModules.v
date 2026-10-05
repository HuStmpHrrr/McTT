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

Lemma qname_strip_snoc_inv : forall mp p y r,
    qname_strip mp (qname_app p (y :: nil)) = Some r ->
    (exists r', qname_strip mp p = Some r' /\ r = r' ++ y :: nil) \/ r = nil.
Proof.
  intros * H; unfold qname_strip, qname_app in *; cbn in *.
  destruct (path_beq (q_unit mp) (q_unit p)); [ exact (strip_prefix_snoc_inv _ _ _ _ H) | discriminate ].
Qed.

Lemma qname_strip_snoc : forall mp p y r,
    qname_strip mp p = Some r -> qname_strip mp (qname_app p (y :: nil)) = Some (r ++ y :: nil).
Proof.
  intros * H; unfold qname_strip, qname_app in *; cbn in *.
  destruct (path_beq (q_unit mp) (q_unit p)); [ exact (strip_prefix_snoc _ _ _ _ H) | discriminate ].
Qed.

Lemma gs_find_tele_snoc : forall Ξ p y U ip' T,
    gs_find_tele Ξ (qname_app p (y :: nil)) = Some (U, ip', T) -> ip' <> nil ->
    exists ip, gs_find_tele Ξ p = Some (U, ip, T) /\ ip' = ip ++ y :: nil.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H Hne; cbn in H |- *; [ discriminate |].
  destruct (qname_strip mp (qname_app p (y :: nil))) as [r |] eqn:Hs.
  - injection H as <- <- <-.
    destruct (qname_strip_snoc_inv _ _ _ _ Hs) as [(r' & Hr' & ->) | ->]; [| contradiction ].
    rewrite Hr'; eauto.
  - destruct (qname_strip mp p) as [r |] eqn:Hp.
    + rewrite (qname_strip_snoc _ _ y _ Hp) in Hs; discriminate.
    + exact (IH _ _ _ _ _ H Hne).
Qed.

Lemma gs_find_tele_snoc_none : forall Ξ p y,
    gs_find_tele Ξ (qname_app p (y :: nil)) = None -> gs_find_tele Ξ p = None.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H |- *; [ reflexivity |].
  destruct (qname_strip mp (qname_app p (y :: nil))) as [r |] eqn:Hs; [ discriminate |].
  destruct (qname_strip mp p) as [r |] eqn:Hp; [ rewrite (qname_strip_snoc _ _ y _ Hp) in Hs; discriminate |].
  exact (IH _ _ H).
Qed.

Lemma gs_find_tele_snoc_fwd : forall Ξ p y U ip T,
    gs_find_tele Ξ p = Some (U, ip, T) -> gs_find_tele Ξ (qname_app p (y :: nil)) = Some (U, ip ++ y :: nil, T) \/
    exists U' T', gs_find_tele Ξ (qname_app p (y :: nil)) = Some (U', nil, T').
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H |- *; [ discriminate |].
  destruct (qname_strip mp (qname_app p (y :: nil))) as [r |] eqn:Hs.
  - destruct (qname_strip_snoc_inv _ _ _ _ Hs) as [(r' & Hr' & ->) | ->].
    + rewrite Hr' in H; injection H as <- <- <-; left; reflexivity.
    + right; eauto.
  - destruct (qname_strip mp p) as [r |] eqn:Hp; [ rewrite (qname_strip_snoc _ _ y _ Hp) in Hs; discriminate |].
    exact (IH _ _ _ _ _ H).
Qed.

Lemma gs_find_snoc_tele : forall Ξ p,
    gs_find Ξ p = option_map (fun r => let '(U, ip, _) := r in (U, ip)) (gs_find_tele Ξ p).
Proof. exact gs_find_tele_find. Qed.

(** ** Bodies of Modules *)

Lemma gm_subbody_module : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') -> gm_submodule T Φ x ip = Some (mr_body T').
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| z ip]; [ injection H as <- <-; reflexivity | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gm_module_subbody : forall Φ T x ip T',
    gm_submodule T Φ x ip = Some (mr_body T') -> exists Φ', gm_subbody T Φ x ip = Some (T', Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| z ip]; [ injection H as <-; eauto | exact (IH _ _ _ _ _ H) ].
Qed.

Lemma gm_subbody_snoc : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y, gm_submodule T Φ x (ip ++ y :: nil) = gm_submodule T' Φ' y nil /\
      gm_subbody T Φ x (ip ++ y :: nil) = gm_subbody T' Φ' y nil.
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
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
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
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
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
  - destruct ip as [| w ip]; cbn; [ discriminate | exact (IH _ _ _ _ _ _ H y) ].
  - injection H as <- <-; reflexivity.
Qed.

(** ** Coherence of a Body with its Telescope *)

Fixpoint gm_coh (T : ctx) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_open Φ0 _ _ => gm_coh T Φ0
  | gm_ext Φ0 _ (ge_def _ _ A _) => gm_coh T Φ0 /\ exists A0, A = ctx_pi T A0
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body Φ'))) => gm_coh T Φ0 /\ tele_ass Δ /\ gm_coh (Δ ++ T) Φ'
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_alias _))) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  end.

Lemma gm_coh_subbody : forall Φ T x ip T' Φ',
    gm_coh T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * Hc H; cbn in Hc, H; [ discriminate | | exact (IH _ _ _ _ _ _ Hc H) ].
  destruct E as [b pv A B | ? [Δ [Φ0 | E0]]];
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
  - destruct E as [b' pv' A' B' | pm' U]; [ injection H as <- <- <- <-; destruct Hc as [_ ?]; assumption | discriminate ].
  - destruct E as [b' pv' A' B' | ? [Δ [Φ0 | E0]]]; eapply IH; try eassumption; apply Hc.
Qed.

Lemma gm_coh_child : forall Φ T y r,
    gm_coh T Φ -> gm_submodule T Φ y nil = Some r ->
    (exists Δ, r = mr_body (Δ ++ T) /\ tele_ass Δ) \/
    (exists U Δ, r = mr_alias U nil /\ gu_params U = Δ ++ T /\ tele_ass Δ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc H; cbn in Hc, H; [ discriminate | | eauto ].
  destruct (String.eqb y z).
  - destruct E as [b pv A B | ? [Δ [Φ0 | E0]]]; [ discriminate | |].
    + injection H as <-; destruct Hc as (_ & HΔ & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
  - destruct E as [b pv A B | ? [Δ [Φ0 | E0]]]; eapply IH; try eassumption; apply Hc.
Qed.

(** ** Coherence of Well-Formed Bodies *)

Lemma wf_gmod_coh :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> forall Ξ' mp' Δ Φ, Ξ = (mp', gu_body Δ Φ) :: Ξ' ->
     match E with
     | ge_def _ _ A _ => exists A0, A = ctx_pi (Δ ++ gs_tele Ξ') A0
     | ge_mod _ (gu_mk Δ1 (md_body Φ1)) => tele_ass Δ1 /\ gm_coh (Δ1 ++ Δ ++ gs_tele Ξ') Φ1
     | ge_mod _ (gu_mk Δ1 (md_alias _)) => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
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
    destruct E as [b pv A B | ? [Δ1 [Φ1 | E1]]]; cbn; split; auto.
Qed.

(** ** Bodies in a Global Context *)


Lemma gc_module_body : forall Θ Ξ p T,
    gc_module Θ Ξ p = Some (mr_body T) -> exists Φ, gc_body Θ Ξ p = Some (T, Φ).
Proof.
  intros * H; unfold gc_module, gc_body in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_module_subbody _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in H |- *; [ injection H as <-; eauto | exact (gm_module_subbody _ _ _ _ _ H) ].
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
    (forall y r, gc_module Θ Ξ (qname_app p (y :: nil)) = Some r -> gm_submodule T Φ y nil = Some r) /\
    (forall y, gc_module Θ Ξ (qname_app p (y :: nil)) <> None ->
       gc_body Θ Ξ (qname_app p (y :: nil)) = gm_subbody T Φ y nil) /\
    (forall z E, gc_resolve Θ Ξ (qname_app p (z :: nil)) = Some E -> gm_resolve Φ (z :: nil) = Some E).
Proof.
  intros * H; unfold gc_body in H.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - assert (Fy : forall y, gs_find_tele Ξ (qname_app p (y :: nil)) = Some (U, (x :: ip) ++ y :: nil, T0) \/
                   exists U' T', gs_find_tele Ξ (qname_app p (y :: nil)) = Some (U', nil, T'))
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
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:El; [| discriminate ].
    pose proof (gm_body_snoc _ _ _ _ _ H) as Hs.
    assert (Fy : forall y, gs_find_tele Ξ (qname_app p (y :: nil)) = None \/
                   exists U' T', gs_find_tele Ξ (qname_app p (y :: nil)) = Some (U', nil, T')).
    { intros y; destruct (gs_find_tele Ξ (qname_app p (y :: nil))) as [[[U' ip'] T'] |] eqn:E1; [| left; reflexivity ].
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
  induction 1 as [| Θ d fp Δ Φ Hd IH HΦ Hfr Hfr']; intros fq V Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [| eauto ].
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
  induction 1 as [| Θ Ξ mp Δ Φ HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; [ discriminate |].
  destruct (qname_strip mp p); [| eauto ].
  injection Hf as <- <- <-.
  exact (proj2 (proj2 wf_gmod_coh _ _ _ _ _ HΦ)).
Qed.

Lemma wf_gstack_deps : forall Θ Ξ, wf_gstack Θ Ξ -> wf_gdeps Θ.
Proof. induction 1; assumption. Qed.

Lemma gc_body_coh : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> gm_coh T Φ.
Proof.
  intros * Hg * H.
  pose proof Hg as Hs.
  unfold gc_body in H.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - exact (proj1 (gm_coh_subbody _ _ _ _ _ _ (wf_gstack_coh _ _ Hs _ _ _ _ Ef) H)).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; [| discriminate ].
    pose proof (wf_gdeps_coh _ (wf_gstack_deps _ _ Hs) _ _ El) as Hc.
    destruct (q_chain p) as [| x ip]; cbn in H; [ injection H as <- <-; exact Hc |].
    exact (proj1 (gm_coh_subbody _ _ _ _ _ _ Hc H)).
Qed.

(** ** A Closed Module Is Read in its Body *)

Lemma qname_app_app : forall p l m, qname_app (qname_app p l) m = qname_app p (l ++ m).
Proof. intros; unfold qname_app; cbn; rewrite app_assoc; reflexivity. Qed.


Lemma gm_subbody_app : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y ch, gm_submodule T Φ x (ip ++ y :: ch) = gm_submodule T' Φ' y ch /\
      gm_subbody T Φ x (ip ++ y :: ch) = gm_subbody T' Φ' y ch /\
      gm_resolve Φ (x :: ip ++ y :: ch) = gm_resolve Φ' (y :: ch).
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y ch; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y ch) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y ch) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
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
    forall ch, gs_find_tele Ξ (qname_app p ch) = Some (U, x :: ip ++ ch, T).
Proof.
  induction 1 as [| Θ Ξ mp Vp VΦ HΞ IH HV Hff]; intros * Hf Hin ch; cbn in Hf |- *; [ discriminate |].
  destruct (qname_strip mp p) as [r |] eqn:Hs.
  - injection Hf; intros; subst.
    apply qname_strip_app_inv in Hs; subst p.
    rewrite qname_app_app, qname_strip_app; reflexivity.
  - pose proof (IH _ _ _ _ _ Hf Hin ch) as Hf'.
    destruct (qname_strip mp (qname_app p ch)) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [mq W] Ξ'']; [ discriminate |].
    destruct Hff as (x1 & -> & Hfr).
    apply qname_strip_app_inv in Hs'.
    cbn in Hf'.
    rewrite Hs', qname_app_in, qname_strip_app in Hf'.
    injection Hf' as <- <- _ _.
    exact (Hfr Hin).
Qed.


Lemma gs_find_tele_filed : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U, gds_lookup Θ (q_unit p) = Some U -> forall ch, gs_find_tele Ξ (qname_app p ch) = None.
Proof.
  intros * HΞ p U Hl ch.
  pose proof (wf_gstack_frames _ _ HΞ) as Hfr.
  induction Ξ as [| [mp V] Ξ' IH]; cbn; [ reflexivity |].
  assert (Hne : path_beq (q_unit mp) (q_unit (qname_app p ch)) = false).
  { destruct (path_beq (q_unit mp) (q_unit (qname_app p ch))) eqn:Hb; [| reflexivity ].
    apply path_beq_true in Hb; cbn in Hb.
    pose proof (Hfr mp V (or_introl eq_refl)) as Hn; rewrite Hb in Hn; congruence. }
  unfold qname_strip; rewrite Hne.
  inversion HΞ; subst.
  apply IH; [ assumption | intros; eapply Hfr; right; eassumption ].
Qed.

Lemma gc_body_module : forall Θ Ξ p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> gc_module Θ Ξ p = Some (mr_body T).
Proof.
  intros * H; unfold gc_body, gc_module in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_subbody_module _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in H |- *; [ injection H as <- <-; reflexivity | exact (gm_subbody_module _ _ _ _ _ _ H) ].
Qed.

(** What resolves below a closed module is what its body says. *)
Theorem closed_read : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    forall ch, gc_module Θ Ξ (qname_app p ch) = gm_module T Φ ch /\ gc_body Θ Ξ (qname_app p ch) = gm_body T Φ ch /\
      (ch <> nil -> gc_resolve Θ Ξ (qname_app p ch) = gm_resolve Φ ch).
Proof.
  intros * Hg * H ch.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_body in H0.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_subbody_head _ _ _ _ _ H0) ch) as Ef'.
    unfold gc_module, gc_body, gc_resolve; rewrite gs_find_tele_find, Ef'; cbn.
    destruct ch as [| y ch]; [ rewrite !app_nil_r; split; [ exact (gm_subbody_module _ _ _ _ _ _ H0) | split; [ exact H0 | congruence ] ] |].
    destruct (gm_subbody_app _ _ _ _ _ _ H0 y ch) as (H1 & H2 & H3).
    split; [ exact H1 | split; [ exact H2 | intros _; exact H3 ] ].
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    unfold gc_module, gc_body, gc_resolve; rewrite gs_find_tele_find, Ef'; cbn [option_map].
    cbn [qname_app q_unit q_chain]; rewrite El.
    exact (gm_body_app _ _ _ _ _ H0 ch).
Qed.

(** ** The Facts the Semantics Uses *)

Lemma wf_gc_child : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T y T',
    gc_module Θ Ξ p = Some (mr_body T) -> gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_body T') ->
    exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ HΦ (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & [= ->] & HΔ) | (U & Δ & [=] & _)]; eauto.
Qed.

Lemma wf_gc_alias_params : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T y U ch,
    gc_module Θ Ξ p = Some (mr_body T) -> gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U ch) ->
    ch = nil /\ exists Δ, gu_params U = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ HΦ (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & [=] & _) | (U' & Δ & [= <- <-] & HU & HΔ)]; eauto.
Qed.

Lemma wf_gc_def_type : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T z b pv A B,
    gc_module Θ Ξ p = Some (mr_body T) -> gc_resolve Θ Ξ (qname_app p (z :: nil)) = Some (ge_def b pv A B) ->
    exists A0, A = ctx_pi T A0.
Proof.
  intros * Hg * Hp Hz.
  destruct (gc_module_body _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ HΦ (z :: nil)) as (_ & _ & H3); rewrite (H3 ltac:(discriminate)) in Hz.
  exact (gm_coh_def _ _ _ _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hz).
Qed.

(** ** Decomposing Paths into Bodies *)

Lemma gm_resolve_subbody : forall Φ T x ip z E,
    gm_resolve Φ (x :: ip ++ z :: nil) = Some E ->
    exists T' Φ', gm_subbody T Φ x ip = Some (T', Φ') /\ gm_resolve Φ' (z :: nil) = Some E.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct ip as [| w ip]; cbn in H.
  - destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate; eauto.
  - destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate.
    exact (IH _ _ _ _ _ _ H).
Qed.

Lemma gm_resolve_decomp : forall ip Φ T z E,
    gm_resolve Φ (ip ++ z :: nil) = Some E ->
    exists T' Φ', gm_body T Φ ip = Some (T', Φ') /\ gm_resolve Φ' (z :: nil) = Some E.
Proof.
  intros [| x ip] Φ T z E H; [ exists T, Φ; split; [ reflexivity | exact H ] |].
  exact (gm_resolve_subbody _ _ _ _ _ _ H).
Qed.

Lemma gm_body_snoc_inv : forall ip Φ T y T2 Φ2,
    gm_body T Φ (ip ++ y :: nil) = Some (T2, Φ2) ->
    exists T1 Φ1, gm_body T Φ ip = Some (T1, Φ1) /\ gm_subbody T1 Φ1 y nil = Some (T2, Φ2).
Proof.
  intros [| x ip] Φ T y T2 Φ2 H; cbn [app gm_body] in *; [ exists T, Φ; auto |].
  revert Φ T x H; induction ip as [| w ip IHip]; intros Φ T x H; cbn [app] in H.
  - revert H; induction Φ as [| Φ IH z E0 | Φ IH c]; intros H; cbn in H |- *; [ discriminate | | exact (IH H) ].
    destruct (String.eqb x z); [| exact (IH H) ].
    destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate; eauto.
  - revert H; induction Φ as [| Φ IH z E0 | Φ IH c]; intros H; cbn in H |- *; [ discriminate | | exact (IH H) ].
    destruct (String.eqb x z); [| exact (IH H) ].
    destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate.
    exact (IHip _ _ _ H).
Qed.

Lemma gm_module_body_some : forall T Φ ch T'',
    gm_module T Φ ch = Some (mr_body T'') -> exists Φ'', gm_body T Φ ch = Some (T'', Φ'').
Proof.
  intros * H; destruct ch as [| x ip]; cbn in H |- *; [ injection H as <-; eauto | exact (gm_module_subbody _ _ _ _ _ H) ].
Qed.

Lemma gm_submodule_alias_decomp : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) ->
    exists pre y T' Φ', x :: ip = pre ++ y :: r /\ gm_body T Φ pre = Some (T', Φ') /\
      gm_submodule T' Φ' y nil = Some (mr_alias U nil).
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c its] * H; cbn in H; [ discriminate | |].
  - destruct (String.eqb x z) eqn:Exz.
    + destruct E0 as [? ? ? ? | pm [Δ [Φ0 | E1]]]; try discriminate.
      * destruct ip as [| w ip]; [ discriminate |].
        destruct (IH _ _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz.
        destruct pre as [| v pre]; cbn in Hb |- *; [ injection Hb as <- <-; reflexivity | exact Hb ].
      * injection H as <- <-.
        exists nil, x, T, (gm_ext Φ z (ge_mod pm (gu_mk Δ (md_alias E1)))); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; reflexivity.
    + destruct (IH _ _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
      destruct pre as [| v pre]; cbn in Heq, Hb.
      * injection Heq as <- <-; injection Hb as <- <-.
        exists nil, x, T, (gm_ext Φ z E0); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; exact Hs.
      * injection Heq as <- Heq.
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz; exact Hb.
  - destruct (IH _ _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
    destruct pre as [| v pre]; cbn in Heq, Hb.
    + injection Heq as <- <-; injection Hb as <- <-.
      exists nil, x, T, (gm_open Φ c its); split; [ reflexivity |]; split; [ reflexivity | exact Hs ].
    + exists (v :: pre), y, T', Φ'; split; [ exact Heq |]; split; [ exact Hb | exact Hs ].
Qed.

Lemma gm_submodule_alias_app : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) ->
    forall ch, gm_submodule T Φ x (ip ++ ch) = Some (mr_alias U (r ++ ch)) /\
      (ch <> nil -> gm_resolve Φ (x :: ip ++ ch) = None).
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c] * H ch; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H ch) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H ch) ].
  destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ _ H ch).
  - injection H as <- <-; split; [ reflexivity |].
    intros Hne; destruct (ip ++ ch) eqn:E; [ destruct ch; [ contradiction | destruct ip; discriminate ] | reflexivity ].
Qed.

Lemma gm_coh_body_tele : forall T Φ ip T' Φ',
    gm_coh T Φ -> gm_body T Φ ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hc H; destruct ip as [| x ip]; cbn in H.
  - injection H as <- <-; split; [ exact Hc | exists nil; split; [ reflexivity | constructor ] ].
  - exact (gm_coh_subbody _ _ _ _ _ _ Hc H).
Qed.

(** ** Frames Do Not Hide the Members of a Closed Module *)

Lemma gs_find_tele_head : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U x ip T, gs_find_tele Ξ p = Some (U, x :: ip, T) -> List.In x (gm_names (gu_mod U)) ->
    exists Fp, p = qname_app Fp (x :: ip) /\
      forall ip', gs_find_tele Ξ (qname_app Fp (x :: ip')) = Some (U, x :: ip', T).
Proof.
  induction 1 as [| Θ Ξ mp Vp VΦ HΞ IH HV Hff]; intros * Hf Hin; cbn in Hf; [ discriminate |].
  destruct (qname_strip mp p) as [r |] eqn:Hs.
  - injection Hf; intros; subst.
    exists mp; split; [ apply qname_strip_app_inv; exact Hs |].
    intros ip'; cbn; rewrite qname_strip_app; reflexivity.
  - destruct (IH _ _ _ _ _ Hf Hin) as (Fp & -> & HF).
    exists Fp; split; [ reflexivity |]; intros ip'.
    pose proof (HF ip') as Hf'.
    cbn; destruct (qname_strip mp (qname_app Fp (x :: ip'))) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [mq W] Ξ'']; [ discriminate |].
    destruct Hff as (x1 & -> & Hfr).
    apply qname_strip_app_inv in Hs'.
    cbn in Hf'.
    rewrite Hs', qname_app_in, qname_strip_app in Hf'.
    injection Hf' as <- <- _ _.
    exact (Hfr Hin).
Qed.

Lemma gc_module_alias_app : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p U r0,
    gc_module Θ Ξ p = Some (mr_alias U r0) ->
    forall ch, gc_module Θ Ξ (qname_app p ch) = Some (mr_alias U (r0 ++ ch)) /\
      (ch <> nil -> gc_resolve Θ Ξ (qname_app p ch) = None).
Proof.
  intros * Hg * H ch.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_module in H0.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_submodule_head _ _ _ _ _ H0) ch) as Ef'.
    destruct (gm_submodule_alias_app _ _ _ _ _ _ H0 ch) as [H1 H2].
    unfold gc_module, gc_resolve; rewrite gs_find_tele_find, Ef'; cbn.
    split; [ exact H1 | exact H2 ].
  - destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    unfold gc_module, gc_resolve; rewrite gs_find_tele_find, Ef'; cbn [option_map qname_app q_unit q_chain]; rewrite El.
    destruct (q_chain p) as [| x ip]; cbn in H0 |- *; [ discriminate |].
    destruct (gm_submodule_alias_app _ _ _ _ _ _ H0 ch) as [H1 H2].
    split; [ exact H1 | exact H2 ].
Qed.

Lemma gc_module_alias_decomp : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p U r0,
    gc_module Θ Ξ p = Some (mr_alias U r0) ->
    exists qp y, p = qname_app qp (y :: r0) /\ gc_module Θ Ξ (qname_app qp (y :: nil)) = Some (mr_alias U nil).
Proof.
  intros * Hg * H.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_module in H0.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; [ discriminate | |].
  - destruct (gs_find_tele_head _ _ Hs _ _ _ _ _ Ef (gm_submodule_head _ _ _ _ _ H0)) as (Fp & -> & HF).
    destruct (gm_submodule_alias_decomp _ _ _ _ _ _ H0) as (pre & y & T' & Φ' & Heq & Hb & Hy).
    exists (qname_app Fp pre), y; split; [ rewrite qname_app_app, <- Heq; reflexivity |].
    rewrite qname_app_app.
    destruct pre as [| v pre]; cbn in Heq, Hb |- *.
    + injection Heq as <- _; injection Hb as <- <-.
      unfold gc_module; rewrite (HF nil); exact Hy.
    + injection Heq as <- _.
      unfold gc_module; rewrite (HF (pre ++ y :: nil)).
      rewrite (proj1 (gm_subbody_snoc _ _ _ _ _ _ Hb y)); exact Hy.
  - destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:El; [| discriminate ].
    destruct (q_chain p) as [| x ip] eqn:Em; cbn in H0; [ discriminate |].
    destruct (gm_submodule_alias_decomp _ _ _ _ _ _ H0) as (pre & y & T' & Φ' & Heq & Hb & Hy).
    set (Fp := {| q_unit := q_unit p; q_chain := nil |}).
    assert (Hp : p = qname_app Fp (x :: ip)) by (destruct p; cbn in *; subst; reflexivity).
    assert (ElF : gds_lookup Θ (q_unit Fp) = Some V) by exact El.
    exists (qname_app Fp pre), y; split; [ rewrite Hp, qname_app_app, <- Heq; reflexivity |].
    rewrite qname_app_app.
    unfold gc_module; rewrite (gs_find_tele_filed _ _ Hs _ _ ElF); cbn [qname_app q_unit q_chain Fp]; rewrite El; cbn [app].
    destruct pre as [| v pre]; cbn in Heq, Hb |- *.
    + injection Heq as <- _; injection Hb as <- <-; exact Hy.
    + injection Heq as <- _.
      rewrite (proj1 (gm_subbody_snoc _ _ _ _ _ _ Hb y)); exact Hy.
Qed.

(** ** A Name Is a Definition or a Module, Not Both *)

Lemma gm_resolve_def_not_module : forall Φ T z b pv A B ip,
    gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> gm_submodule T Φ z ip = None.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H; cbn in H |- *; [ reflexivity | | eauto ].
  destruct (String.eqb z y); [| eauto ].
  destruct E as [? ? ? ? | U]; [ reflexivity | discriminate ].
Qed.

Lemma gm_submodule_alias_resolve : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) -> gm_resolve Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate.
  - destruct ip as [| w ip]; [ discriminate | exact (IH _ _ _ _ _ _ H) ].
  - destruct ip; reflexivity.
Qed.

Lemma gm_body_prefix : forall ch2 ch1 T Φ T2 Φ2,
    gm_body T Φ (ch1 ++ ch2) = Some (T2, Φ2) -> exists T1 Φ1, gm_body T Φ ch1 = Some (T1, Φ1).
Proof.
  induction ch2 as [| y ch2 IH] using rev_ind; intros * H; [ rewrite app_nil_r in H; eauto |].
  rewrite app_assoc in H.
  destruct (gm_body_snoc_inv _ _ _ _ _ _ H) as (T1 & Φ1 & H1 & _).
  exact (IH _ _ _ _ _ H1).
Qed.

(** A path through an alias names no definition and no body module, so a
    prefix of a path naming one is no alias. *)
Lemma gc_prefix_not_alias : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p ch,
    ch <> nil ->
    (exists T, gc_module Θ Ξ (qname_app p ch) = Some (mr_body T)) \/
    (exists U, gc_module Θ Ξ (qname_app p ch) = Some (mr_alias U nil)) \/
    (exists E, gc_resolve Θ Ξ (qname_app p ch) = Some E) ->
    forall U r, gc_module Θ Ξ p <> Some (mr_alias U r).
Proof.
  intros * Hg * Hne Hx U r Ha.
  destruct (gc_module_alias_app _ _ Hg _ _ _ Ha ch) as [H1 H2].
  destruct Hx as [(T & HT) | [(U' & HU) | (E & HE)]]; [ congruence | | rewrite (H2 Hne) in HE; discriminate ].
  rewrite H1 in HU; injection HU as _ Hr; destruct ch; [ contradiction | destruct r; discriminate ].
Qed.

(** A body module, or a module with a definition, has no alias among the
    prefixes of its path. *)
Lemma gc_chain_no_alias : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p,
    (exists T, gc_module Θ Ξ p = Some (mr_body T)) \/
    (exists x U, gc_module Θ Ξ (qname_app p (x :: nil)) = Some (mr_alias U nil)) \/
    (exists x E, gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some E) ->
    forall m1 m2, q_chain p = m1 ++ m2 -> m1 <> nil ->
    forall U r, gc_module Θ Ξ (q_abs (q_unit p) m1) <> Some (mr_alias U r).
Proof.
  intros * Hg [fp ms] Hx m1 m2 Hm Hne1 U r; cbn [q_unit q_chain] in *; subst ms.
  destruct m2 as [| y m2].
  - rewrite List.app_nil_r in Hx.
    destruct Hx as [(T & HT) | [(x & U' & HU) | (x & E & HE)]]; [ congruence | |].
    + eapply gc_prefix_not_alias with (ch := x :: nil); [ exact Hg | discriminate | right; left; exists U'; exact HU ].
    + eapply gc_prefix_not_alias with (ch := x :: nil); [ exact Hg | discriminate | right; right; exists E; exact HE ].
  - destruct Hx as [(T & HT) | [(x & U' & HU) | (x & E & HE)]].
    + eapply gc_prefix_not_alias with (ch := y :: m2); [ exact Hg | discriminate | left; exists T; exact HT ].
    + eapply gc_prefix_not_alias with (ch := (y :: m2) ++ x :: nil); [ exact Hg | discriminate | right; left; exists U' ].
      unfold qname_app in *; cbn in *; rewrite <- app_assoc in HU; exact HU.
    + eapply gc_prefix_not_alias with (ch := (y :: m2) ++ x :: nil); [ exact Hg | discriminate | right; right; exists E ].
      unfold qname_app in *; cbn in *; rewrite <- app_assoc in HE; exact HE.
Qed.

Lemma gc_module_alias_resolve : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p U r0,
    gc_module Θ Ξ p = Some (mr_alias U r0) -> gc_resolve Θ Ξ p = None.
Proof.
  intros * Hg * H.
  pose proof Hg as Hs.
  unfold gc_module, gc_resolve in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; cbn; [ discriminate | exact (gm_submodule_alias_resolve _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [V |]; [| reflexivity ].
  destruct (q_chain p) as [| x ip]; cbn in H; [ discriminate | exact (gm_submodule_alias_resolve _ _ _ _ _ _ H) ].
Qed.

(** ** Validity of Bodies, by Induction over Insertion

    The induction of [GlobalPresup] for entries, extended to what a module
    contributes besides its definitions: its telescope ([F]) and its aliases.
    [V Θ2 Ξ2 T E] is the validity at [Θ2 ⍮ Ξ2] of an entry [E] other than a body
    module, checked over the telescope [T]. *)

Section ModInduction.
  Variable V : gdeps -> gstack -> ctx -> gentry -> Prop.
  Variable F : gdeps -> gstack -> ctx -> Prop.

  Fixpoint gm_valid (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (Φ : gmod) : Prop :=
    match Φ with
    | gm_nil => True
    | gm_open Φ0 _ _ => gm_valid Θ2 Ξ2 T Φ0
    | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body Φ'))) =>
        gm_valid Θ2 Ξ2 T Φ0 /\ F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θ2 Ξ2 (Δ ++ T) Φ'
    | gm_ext Φ0 _ E => gm_valid Θ2 Ξ2 T Φ0 /\ V Θ2 Ξ2 T E
    end.

  Definition ge_valid (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
    match E with
    | ge_mod _ (gu_mk Δ (md_body Φ')) => F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θ2 Ξ2 (Δ ++ T) Φ'
    | _ => V Θ2 Ξ2 T E
    end.

  Lemma gm_valid_ext : forall Θ2 Ξ2 T Φ x E,
      gm_valid Θ2 Ξ2 T (Φ ⊳ x ↦ E) <-> gm_valid Θ2 Ξ2 T Φ /\ ge_valid Θ2 Ξ2 T E.
  Proof. intros; destruct E as [? ? ? ? | ? [Δ [Φ' | E']]]; cbn; tauto. Qed.

  Fixpoint gs_valid (Θ2 : gdeps) (Ξ2 : gstack) (Ξ : gstack) : Prop :=
    match Ξ with
    | nil => True
    | (_, U) :: Ξ' =>
        F Θ2 Ξ2 (gu_params U ++ gs_tele Ξ') /\ gm_valid Θ2 Ξ2 (gu_params U ++ gs_tele Ξ') (gu_mod U) /\
        gs_valid Θ2 Ξ2 Ξ'
    end.

  Definition gds_valid (Θ2 : gdeps) (Ξ2 : gstack) (Θ : gdeps) : Prop :=
    forall fp U, gds_lookup Θ fp = Some U -> F Θ2 Ξ2 (gu_params U) /\ gm_valid Θ2 Ξ2 (gu_params U) (gu_mod U).

  (** Everything filed or open at [Θ ⍮ Ξ] is valid wherever [Θ ⍮ Ξ] embeds. *)
  Definition GoodV (Θ : gdeps) (Ξ : gstack) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 -> gds_valid Θ2 Ξ2 Θ /\ gs_valid Θ2 Ξ2 Ξ.

  Hypothesis Hdef : forall Θ Ξ A M b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M))).
  Hypothesis Hax : forall Θ Ξ A i b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i -> GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
  Hypothesis Halias : forall Θ Ξ pv Δ E Θ2 Ξ2,
      tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
      GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
  Hypothesis Hnil : forall Θ Ξ Δ Θ2 Ξ2,
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ).

  Definition GoodEV (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 ->
      (forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> gc_resolve Θ2 Ξ2 (qname_app mp ip) = Some E0) ->
      (forall x (ip : list String.string) r, ge_submodule (gs_tele Ξ) E x ip = Some r ->
         gc_module Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) ->
      (forall x (ip : list String.string) r, ge_subbody (gs_tele Ξ) E x ip = Some r ->
         gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) ->
      ge_valid Θ2 Ξ2 (gs_tele Ξ) E.

  Definition GoodMV (Θ : gdeps) (Ξ : gstack) (mp : qname) (Δ : ctx) (Φ : gmod) : Prop :=
    forall Θ2 Ξ2, Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 -> Emb Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ) /\ gm_valid Θ2 Ξ2 (Δ ++ gs_tele Ξ) Φ.

  Definition GoodUV (Θ : gdeps) (Ξ : gstack) (mp : qname) (U : gunit) : Prop :=
    forall Θ2 Ξ2, Emb Θ ((mp, U) :: Ξ) Θ2 Ξ2 -> Emb Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (gu_params U ++ gs_tele Ξ) /\ gm_valid Θ2 Ξ2 (gu_params U ++ gs_tele Ξ) (gu_mod U).

  Definition GoodDV (Θ : gdeps) (d : gdep) : Prop :=
    forall fp U, List.In (fp, U) d -> GoodUV Θ nil (q_abs fp nil) U.

  Theorem global_valid_all :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> GoodV Θ Ξ) /\
    (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> GoodEV Θ Ξ mp E) /\
    (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> GoodMV Θ Ξ mp Δ Φ) /\
    (forall Θ d, wf_gdep Θ d -> GoodDV Θ d) /\
    (forall Θ, wf_gdeps Θ -> GoodV Θ nil) /\
    (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> GoodV Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - intros Θ2 Ξ2 He _ _ _; cbn; eapply Hax; eassumption.
    - intros Θ2 Ξ2 He _ _ _; cbn; eapply Hdef; eassumption.
    - intros Θ2 Ξ2 He Hin Hmod Hbod; cbn.
      apply H0; [ eapply Emb_nested; [ exact He | exact Hin | exact Hmod | exact Hbod ] | exact He ].
    - intros Θ2 Ξ2 He _ _ _; cbn; eapply Halias; eassumption.
    - intros Θ2 Ξ2 _ He; split; [ eapply Hnil; eassumption | exact I ].
    - rename H0 into IHΦ, H2 into IHE.
      intros Θ2 Ξ2 He Hout.
      assert (He' : Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Emb_pre; [ apply gc_sub_grow; eassumption | exact He ]).
      destruct (IHΦ _ _ He' Hout) as [HF HΦ].
      split; [ exact HF |]; apply gm_valid_ext; split; [ exact HΦ |].
      eapply IHE; [ exact He' | | | ].
      + intros ip0 E1 HE1; rewrite qname_app_in; apply (gc_sub_resolve _ _ _ _ _ _ (em_res _ _ _ _ He)).
        rewrite gc_resolve_frame_here; cbn [gu_mod]; rewrite gm_resolve_ext_here; exact HE1.
      + intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_sub_module _ _ _ _ _ _ (em_res _ _ _ _ He)).
        rewrite gc_module_frame_here; cbn [gu_mod gu_params]; apply gm_submodule_ext_here; exact Hr0.
      + intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_sub_body _ _ _ _ _ _ (em_res _ _ _ _ He)).
        rewrite gc_body_frame_here; cbn [gu_mod gu_params]; apply gm_subbody_ext_here; exact Hr0.
    - intros ? ? [].
    - intros fq V' [[= <- <-] | Hin]; eauto.
    - intros Θ2 Ξ2 _; split; [ intros fp U Hl; unfold gds_lookup, gd_lookup in Hl; cbn in Hl; discriminate | exact I ].
    - rename H0 into IHΘ, H2 into IHd.
      pose proof (wf_gdep_fresh _ _ H1) as Hfr.
      intros Θ2 Ξ2 He; split; [| exact I ].
      intros fp U Hl; unfold gds_lookup in Hl; cbn [List.concat] in Hl.
      apply gd_lookup_app_inv in Hl as [Hl | Hl].
      + destruct (IHd _ _ (gd_lookup_in _ _ _ Hl) Θ2 Ξ2) as [HF HV].
        * eapply Emb_pre; [ apply gc_sub_file; eassumption | exact He ].
        * eapply Emb_pre; [ apply gc_sub_level; eassumption | exact He ].
        * cbn [gs_tele] in HF, HV; rewrite app_nil_r in HF, HV; split; assumption.
      + exact (proj1 (IHΘ Θ2 Ξ2 ltac:(eapply Emb_pre; [ apply gc_sub_level; eassumption | exact He ])) fp U Hl).
    - rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He.
      assert (He0 : Emb Θ Ξ Θ2 Ξ2) by (eapply Emb_pre; [ apply gc_sub_push; eassumption | exact He ]).
      destruct (IHΞ _ _ He0) as [HΘ HΞ]; split; [ exact HΘ |].
      destruct (IHU _ _ He He0); cbn [gs_valid]; repeat split; assumption.
  Qed.

  Corollary global_valid : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> GoodV Θ Ξ.
  Proof. intros; apply global_valid_all; assumption. Qed.

  (** *** Reading validity back *)

  Lemma gm_valid_subbody : forall Φ Θ2 Ξ2 T x ip T' Φ',
      gm_valid Θ2 Ξ2 T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> F Θ2 Ξ2 T' /\ gm_valid Θ2 Ξ2 T' Φ'.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; try discriminate.
    destruct Hv as (_ & HF & Hv); destruct ip as [| w ip].
    - injection H as <- <-; split; assumption.
    - exact (IH _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_body : forall Θ2 Ξ2 T Φ ip T' Φ',
      F Θ2 Ξ2 T -> gm_valid Θ2 Ξ2 T Φ -> gm_body T Φ ip = Some (T', Φ') -> F Θ2 Ξ2 T' /\ gm_valid Θ2 Ξ2 T' Φ'.
  Proof.
    intros * HF Hv H; destruct ip as [| x ip]; cbn in H;
      [ injection H as <- <-; split; assumption | exact (gm_valid_subbody _ _ _ _ _ _ _ _ Hv H) ].
  Qed.

  Lemma gm_valid_resolve : forall Φ Θ2 Ξ2 T ip E,
      gm_valid Θ2 Ξ2 T Φ -> gm_resolve Φ ip = Some E -> exists T', V Θ2 Ξ2 T' E.
  Proof.
    fix IH 1; intros [| Φ y E0 | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ Hv H) ].
    destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y);
      [| destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate.
    - injection H as <-; exists T; exact (proj2 Hv).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_def : forall Φ Θ2 Ξ2 T z b pv A B,
      gm_valid Θ2 Ξ2 T Φ -> gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> V Θ2 Ξ2 T (ge_def b pv A B).
  Proof.
    induction Φ as [| Φ IH y E0 | Φ IH c]; intros * Hv H; cbn in Hv, H; [ discriminate | | eauto ].
    destruct (String.eqb z y);
      [| destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]]]; try discriminate.
    injection H; intros; subst; exact (proj2 Hv).
  Qed.

  Lemma gm_valid_alias : forall Φ Θ2 Ξ2 T x ip U r,
      gm_valid Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_alias U r) -> exists T' pv, V Θ2 Ξ2 T' (ge_mod pv U).
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]]]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [Φ0 | E0]]]; try discriminate.
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - injection H as <- _; exists T, pm; exact (proj2 Hv).
  Qed.

  Lemma gs_valid_find : forall Θ2 Ξ2 Ξ p U ip T,
      gs_valid Θ2 Ξ2 Ξ -> gs_find_tele Ξ p = Some (U, ip, T) ->
      F Θ2 Ξ2 (gu_params U ++ T) /\ gm_valid Θ2 Ξ2 (gu_params U ++ T) (gu_mod U).
  Proof.
    induction Ξ as [| [mp U0] Ξ IH]; intros * Hv H; cbn in Hv, H; [ discriminate |].
    destruct (qname_strip mp p); [ injection H as <- <- <-; split; apply Hv | exact (IH _ _ _ _ (proj2 (proj2 Hv)) H) ].
  Qed.

  Lemma good_body : forall Θ Ξ Θ2 Ξ2 p T Φ, GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      gc_body Θ Ξ p = Some (T, Φ) -> F Θ2 Ξ2 T /\ gm_valid Θ2 Ξ2 T Φ.
  Proof.
    intros * HG He H; destruct (HG _ _ He) as [HΘ HΞ]; unfold gc_body in H.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [HF Hv]; exact (gm_valid_subbody _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [HF Hv]; exact (gm_valid_body _ _ _ _ _ _ _ HF Hv H).
  Qed.

  Lemma good_resolve : forall Θ Ξ Θ2 Ξ2 p E, GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      gc_resolve Θ Ξ p = Some E -> exists T, V Θ2 Ξ2 T E.
  Proof.
    intros * HG He H; destruct (HG _ _ He) as [HΘ HΞ]; unfold gc_resolve in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ p) as [[[U ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_resolve _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_resolve _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_alias : forall Θ Ξ Θ2 Ξ2 p U r, GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      gc_module Θ Ξ p = Some (mr_alias U r) -> exists T pv, V Θ2 Ξ2 T (ge_mod pv U).
  Proof.
    intros * HG He H; destruct (HG _ _ He) as [HΘ HΞ]; unfold gc_module in H.
    destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_alias _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv].
      destruct (q_chain p) as [| x ip]; [ discriminate |]; exact (gm_valid_alias _ _ _ _ _ _ _ _ Hv H).
  Qed.
End ModInduction.

(** ** Member Types Are Functional *)

Lemma gc_resolve_module_alias_excl : forall Θ Ξ p E U r,
    gc_resolve Θ Ξ p = Some E -> gc_module Θ Ξ p = Some (mr_alias U r) -> False.
Proof.
  intros * Hr Hm; unfold gc_resolve, gc_module in *.
  rewrite gs_find_tele_find in Hr.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |]; cbn in Hr; [ discriminate | |].
  - rewrite (gm_submodule_alias_resolve _ _ _ _ _ _ Hm) in Hr; discriminate.
  - destruct (gds_lookup Θ (q_unit p)) as [V |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; [ discriminate |].
    rewrite (gm_submodule_alias_resolve _ _ _ _ _ _ Hm) in Hr; discriminate.
Qed.

Lemma member_type_functional : forall Θ Ξ,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R -> forall R', member_type Θ Ξ Γ H ch R' -> R = R') /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R -> forall R', unit_member_type Θ Ξ Γ U ch R' -> R = R').
Proof.
  intros Θ Ξ; apply member_type_both_ind.
  all: intros *; intros; match goal with H' : _ _ _ _ _ _ ?A' |- _ = ?A' => inversion H'; subst end;
    try congruence;
    try solve [ exfalso; eapply gc_resolve_module_alias_excl; eassumption ];
    try solve [ match goal with H1 : gc_module _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
                  rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate end ];
    try solve [ match goal with Hl : _ ∋ # _ ⇒ₘ _, Hl' : _ ∋ # _ ⇒ₘ _ |- _ =>
                  pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hl'); subst; eauto end ];
    eauto.
  - match goal with E1 : gc_module _ _ ?p = _, E2 : gc_module _ _ ?p = _ |- _ =>
      rewrite E1 in E2; injection E2; intros; subst end; eauto.
  - match goal with IH : forall R', member_type _ _ _ ?H _ R' -> _ = R', Hm : member_type _ _ _ ?H _ _ |- _ =>
      apply IH in Hm; subst end; congruence.
  - match goal with E1 : gm_prefix_upto _ _ = _, E2 : gm_prefix_upto _ _ = _ |- _ =>
      rewrite E1 in E2; injection E2; intros; subst end.
    f_equal; eauto.
  - f_equal; eauto.
Qed.
