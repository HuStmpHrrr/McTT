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

Lemma strip_prefix_snoc : forall l m y r,
    strip_prefix l m = Some r -> strip_prefix l (m ++ y :: nil) = Some (r ++ y :: nil).
Proof. intros * H; apply strip_prefix_spec in H; subst; rewrite <- app_assoc; apply strip_prefix_app. Qed.

(** ** Bodies of Modules *)

Lemma gm_subbody_module : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') -> exists oD, gm_submodule T Φ x ip = Some (mr_body T' oD).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
    destruct ip as [| z ip]; [ injection H as <- <-; eexists; reflexivity | exact (IH _ _ _ _ _ _ H) | injection H as <- <-; eexists; reflexivity | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gm_module_subbody : forall Φ T x ip T' oD,
    gm_submodule T Φ x ip = Some (mr_body T' oD) -> exists Φ', gm_subbody T Φ x ip = Some (T', Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
    destruct ip as [| z ip]; [ injection H as <- _; eauto | exact (IH _ _ _ _ _ _ H) | injection H as <- _; eauto | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gm_subbody_snoc : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y, gm_submodule T Φ x (ip ++ y :: nil) = gm_submodule T' Φ' y nil /\
      gm_subbody T Φ x (ip ++ y :: nil) = gm_subbody T' Φ' y nil.
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; split; reflexivity | exact (IH _ _ _ _ _ _ H y) ]).
Qed.

Lemma gm_subbody_resolve : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall z, gm_resolve Φ (x :: ip ++ z :: nil) = gm_resolve Φ' (z :: nil).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H z; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H z) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H z) ].
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; reflexivity | specialize (IH _ _ _ _ _ _ H z); cbn in IH; exact IH ]).
Qed.

(** ** Coherence of a Body with its Telescope *)

Fixpoint gm_coh (T : ctx) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_open Φ0 _ _ => gm_coh T Φ0
  | gm_ext Φ0 _ (ge_def _ _ A _) => gm_coh T Φ0 /\ exists A0, A = ctx_pi T A0
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body Φ'))) => gm_coh T Φ0 /\ tele_ass Δ /\ gm_coh (Δ ++ T) Φ'
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_alias _))) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  | gm_ext Φ0 _ (ge_ind _ D Φ') =>
      gm_coh T Φ0 /\ (exists Δ0, ind_uparams D = Δ0 ++ T /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ'
  | gm_ext Φ0 _ (ge_ind_alias _ Δ _ _) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  end.

Lemma gm_coh_subbody : forall Φ T x ip T' Φ',
    gm_coh T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * Hc H; cbn in Hc, H; [ discriminate | | exact (IH _ _ _ _ _ _ Hc H) ].
  destruct E as [b pv A B | ? [Δ [Φ0 | E0]] | ? D Φ0 | ? Δa pa Nsa];
    destruct (String.eqb x y); try discriminate; try (eapply IH; [ apply Hc | exact H ]).
  - destruct Hc as (Hc1 & HΔ & Hc2).
    destruct ip as [| w ip].
    + injection H as <- <-; split; [ exact Hc2 | eauto ].
    + destruct (IH _ _ _ _ _ _ Hc2 H) as (Hc' & Δ' & -> & HΔ').
      split; [ exact Hc' | exists (Δ' ++ Δ); rewrite app_assoc; split; [ reflexivity | apply Forall_app; auto ] ].
  - destruct Hc as (Hc1 & (Δ & HΔe & HΔ) & Hc2).
    destruct ip as [| w ip].
    + injection H as <- <-; split; [ exact Hc2 | eauto ].
    + destruct (IH _ _ _ _ _ _ Hc2 H) as (Hc' & Δ' & -> & HΔ').
      split; [ exact Hc' | exists (Δ' ++ Δ); rewrite HΔe, app_assoc; split; [ reflexivity | apply Forall_app; auto ] ].
Qed.

Lemma gm_coh_child : forall Φ T y r,
    gm_coh T Φ -> gm_submodule T Φ y nil = Some r ->
    (exists Δ oD, r = mr_body (Δ ++ T) oD /\ tele_ass Δ) \/
    (exists U Δ, r = mr_alias U nil /\ gu_params U = Δ ++ T /\ tele_ass Δ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc H; cbn in Hc, H; [ discriminate | | eauto ].
  destruct (String.eqb y z).
  - destruct E as [b pv A B | ? [Δ [Φ0 | E0]] | ? D Φ0 | ? Δa pa Nsa]; [ discriminate | | | | ].
    + injection H as <-; destruct Hc as (_ & HΔ & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
    + injection H as <-; destruct Hc as (_ & (Δ0 & -> & HΔ) & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
  - destruct E as [b pv A B | ? [Δ [Φ0 | E0]] | ? ? ? | ? Δa pa Nsa]; eapply IH; try eassumption; apply Hc.
Qed.

(** ** Coherence of Well-Formed Bodies *)

(** The uniform parameters of a declaration over the frames' parameters
    [T] extend [T] by assumptions. *)
Lemma uparams_split : forall D Δ T, ind_params D = Δ ++ T -> List.length T <= ind_nu D ->
    ind_nu D <= ind_np D -> tele_ass (ind_params D) ->
    exists Δ0, ind_uparams D = Δ0 ++ T /\ tele_ass Δ0.
Proof.
  intros * Hp Hl Hle Ha; exists (List.skipn (ind_nn D) Δ); unfold ind_uparams; rewrite Hp.
  assert (Hn : ind_nn D <= List.length Δ)
    by (unfold ind_nn, ind_np in *; rewrite Hp, List.length_app in *; lia).
  rewrite List.skipn_app, (proj2 (Nat.sub_0_le _ _) Hn); cbn [List.skipn]; split; [ reflexivity |].
  rewrite Hp in Ha; apply Forall_app in Ha as [Ha _]; apply Forall_skipn'; exact Ha.
Qed.

Lemma wf_gmod_coh :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> forall Ξ' mp' Δ Φ, Ξ = (mp', gu_body Δ Φ) :: Ξ' ->
     match E with
     | ge_def _ _ A _ => exists A0, A = ctx_pi (Δ ++ gs_tele Ξ') A0
     | ge_mod _ (gu_mk Δ1 (md_body Φ1)) => tele_ass Δ1 /\ gm_coh (Δ1 ++ Δ ++ gs_tele Ξ') Φ1
     | ge_mod _ (gu_mk Δ1 (md_alias _)) => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
     | ge_ind _ D Φ1 =>
         (exists Δ0, ind_uparams D = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ1
     | ge_ind_alias _ Δ1 _ _ => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
     end) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> tele_ass Δ /\ gm_coh (Δ ++ gs_tele Ξ) Φ).
Proof.
  apply global_wf_mut_ind; intros; subst; cbn.
  - eauto.
  - eauto.
  - match goal with IH : tele_ass ?Δ' /\ _ |- _ => destruct IH as [HΔ Hc] end.
    cbn in Hc; split; [ exact HΔ | exact Hc ].
  - exists Δ; cbn; auto.
  - (* the module of an inductive type, before its members *)
    split; [| exact I ].
    match goal with Hp : ind_params ?D = ?Δd ++ _ |- _ => exact (uparams_split _ _ _ Hp ltac:(assumption) ltac:(assumption) ltac:(assumption)) end.
  - (* one more member *)
    match goal with Heq : (_, _) :: _ = (_, _) :: _ |- _ => injection Heq as -> -> -> end; subst.
    match goal with IHE : forall _ _ _ _, _ = _ -> _ |- _ => specialize (IHE _ _ _ _ eq_refl); cbn in IHE; destruct IHE as [HU Hc] end.
    split; [ exact HU | cbn; split; [ exact Hc | eauto ] ].
  - (* an inductive alias *)
    eexists; split; [ reflexivity | assumption ].
  - split; [ assumption | exact I ].
  - match goal with IH : tele_ass Δ /\ _ |- _ => destruct IH as [HΔ Hc] end.
    split; [ exact HΔ |].
    match goal with IHE : forall _ _ _ _, _ = _ -> _ |- _ => specialize (IHE _ _ _ _ eq_refl); cbn in IHE end.
    destruct E as [b pv A B | ? [Δ1 [Φ1 | E1]] | ? D1 Φ1 | ? Δa pa Nsa]; cbn; try split; auto; apply IHE.
Qed.

(** ** Bodies in a Global Context *)


Lemma gc_module_body : forall Θ Ξ p T oD,
    gc_module Θ Ξ p = Some (mr_body T oD) -> exists Φ, gc_body Θ Ξ p = Some (T, Φ).
Proof.
  intros * H; unfold gc_module, gc_module_u, gc_body in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_module_subbody _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in H |- *; [ injection H as <- _; eauto | exact (gm_module_subbody _ _ _ _ _ _ H) ].
Qed.

Lemma gm_body_snoc : forall T0 Φu ms T Φ,
    gm_body T0 Φu ms = Some (T, Φ) ->
    forall y oD0, gm_module T0 oD0 Φu (ms ++ y :: nil) = gm_submodule T Φ y nil /\
      gm_body T0 Φu (ms ++ y :: nil) = gm_subbody T Φ y nil /\
      forall z, gm_resolve Φu (ms ++ z :: nil) = gm_resolve Φ (z :: nil).
Proof.
  intros * H y oD0; destruct ms as [| x ip]; cbn in H |- *.
  - injection H as <- <-; split; [ reflexivity | split; reflexivity ].
  - destruct (gm_subbody_snoc _ _ _ _ _ _ H y) as [H1 H2].
    split; [ exact H1 | split; [ exact H2 | intros z; exact (gm_subbody_resolve _ _ _ _ _ _ H z) ] ].
Qed.



(** ** Coherence of What a Well-Formed Context Reads *)

Lemma wf_gstack_coh : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U ip T, gs_find_tele Ξ p = Some (U, ip, T) -> gm_coh (gu_params U ++ T) (gu_mod U).
Proof.
  induction 1 as [| | Θ Ξ mp Δ Φ HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; try discriminate.
  destruct (qname_strip mp p); [| eauto ].
  injection Hf as <- <- <-.
  exact (proj2 (proj2 wf_gmod_coh _ _ _ _ _ HΦ)).
Qed.

Lemma wf_gdeps_coh : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall fp U, gds_lookup Θ fp = Some U -> gm_coh (gu_params U) (gu_mod U).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Δ Φ HΞ IH HΦ Hff]; intros fp U Hl; cbn in Hl; [ discriminate | | eauto ].
  destruct (path_beq fp fq); [ injection Hl as -> | eauto ].
  pose proof (wf_gstack_coh _ _ Hg (q_abs fq nil) U nil nil) as Hc; rewrite app_nil_r in Hc; apply Hc.
  cbn; unfold qname_strip; cbn; rewrite path_beq_refl; reflexivity.
Qed.

Lemma gc_body_coh : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> gm_coh T Φ.
Proof.
  intros * Hg * H.
  pose proof Hg as Hs.
  unfold gc_body in H.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - exact (proj1 (gm_coh_subbody _ _ _ _ _ _ (wf_gstack_coh _ _ Hs _ _ _ _ Ef) H)).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; [| discriminate ].
    pose proof (wf_gdeps_coh _ _ Hs _ _ El) as Hc.
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
  destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
    (destruct ip as [| w ip]; cbn;
     [ injection H as <- <-; split; [ reflexivity | split; reflexivity ]
     | specialize (IH _ _ _ _ _ _ H y ch); cbn in IH; exact IH ]).
Qed.

Lemma gm_body_app : forall T0 oD0 Φu ms T oD Φ,
    gm_body T0 Φu ms = Some (T, Φ) -> gm_module T0 oD0 Φu ms = Some (mr_body T oD) ->
    forall ch, gm_module T0 oD0 Φu (ms ++ ch) = gm_module T oD Φ ch /\ gm_body T0 Φu (ms ++ ch) = gm_body T Φ ch /\
      (ch <> nil -> gm_resolve Φu (ms ++ ch) = gm_resolve Φ ch).
Proof.
  intros * H Hm [| y ch].
  - rewrite app_nil_r; cbn; split; [| split; [ exact H | congruence ] ].
    exact Hm.
  - destruct ms as [| x ip]; cbn in H |- *; [ injection H as <- <-; split; [ reflexivity | split; reflexivity ] |].
    destruct (gm_subbody_app _ _ _ _ _ _ H y ch) as (H1 & H2 & H3).
    split; [ exact H1 | split; [ exact H2 | intros _; exact H3 ] ].
Qed.

Lemma gs_find_tele_app : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U x ip T, gs_find_tele Ξ p = Some (U, x :: ip, T) -> List.In x (gm_names (gu_mod U)) ->
    forall ch, gs_find_tele Ξ (qname_app p ch) = Some (U, x :: ip ++ ch, T).
Proof.
  induction 1 as [| | Θ Ξ mp Vp VΦ HΞ IH HV Hff]; intros * Hf Hin ch; cbn in Hf |- *; [ discriminate | discriminate |].
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

Lemma gc_body_module : forall Θ Ξ p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> exists oD, gc_module Θ Ξ p = Some (mr_body T oD).
Proof.
  intros * H; unfold gc_body, gc_module, gc_module_u in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_subbody_module _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in H |- *; [ injection H as <- <-; eexists; reflexivity | exact (gm_subbody_module _ _ _ _ _ _ H) ].
Qed.

(** What resolves below a closed module is what its body says. *)
Theorem closed_read : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T oD Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    gc_module Θ Ξ p = Some (mr_body T oD) ->
    forall ch, gc_module Θ Ξ (qname_app p ch) = gm_module T oD Φ ch /\ gc_body Θ Ξ (qname_app p ch) = gm_body T Φ ch /\
      (ch <> nil -> gc_resolve Θ Ξ (qname_app p ch) = gm_resolve Φ ch).
Proof.
  intros * Hg * H Hm ch.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_body in H0.
  pose proof Hm as Hm0; unfold gc_module, gc_module_u in Hm0.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_subbody_head _ _ _ _ _ H0) ch) as Ef'.
    unfold gc_module, gc_module_u, gc_body, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn.
    destruct ch as [| y ch]; [ rewrite !app_nil_r; split; [ exact Hm0 | split; [ exact H0 | congruence ] ] |].
    destruct (gm_subbody_app _ _ _ _ _ _ H0 y ch) as (H1 & H2 & H3).
    split; [ exact H1 | split; [ exact H2 | intros _; exact H3 ] ].
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    unfold gc_module, gc_module_u, gc_body, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn [option_map].
    cbn [qname_app q_unit q_chain]; rewrite El.
    exact (gm_body_app _ _ _ _ _ _ _ H0 Hm0 ch).
Qed.

(** The same, the declaration the body is filed with read off [ind_lookup]. *)
Corollary closed_read_body : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    forall ch, gc_module Θ Ξ (qname_app p ch) = gm_module T (ind_lookup Θ Ξ p) Φ ch /\
      gc_body Θ Ξ (qname_app p ch) = gm_body T Φ ch /\
      (ch <> nil -> gc_resolve Θ Ξ (qname_app p ch) = gm_resolve Φ ch).
Proof.
  intros * Hg * H; destruct (gc_body_module _ _ _ _ _ H) as [oD Hm].
  rewrite (ind_lookup_body _ _ _ _ _ Hm); exact (closed_read _ _ Hg _ _ _ _ H Hm).
Qed.

(** ** The Facts the Semantics Uses *)

Lemma wf_gc_child : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T oD y T' oD',
    gc_module Θ Ξ p = Some (mr_body T oD) -> gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_body T' oD') ->
    exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ _ HΦ Hp (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & oD0 & [= -> _] & HΔ) | (U & Δ & [=] & _)]; eauto.
Qed.

Lemma wf_gc_alias_params : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T oD y U ch,
    gc_module Θ Ξ p = Some (mr_body T oD) -> gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U ch) ->
    ch = nil /\ exists Δ, gu_params U = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ _ HΦ Hp (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & oD0 & [=] & _) | (U' & Δ & [= <- <-] & HU & HΔ)]; eauto.
Qed.

(** ** Decomposing Paths into Bodies *)

Lemma gm_resolve_subbody : forall Φ T x ip z E,
    gm_resolve Φ (x :: ip ++ z :: nil) = Some E ->
    exists T' Φ', gm_subbody T Φ x ip = Some (T', Φ') /\ gm_resolve Φ' (z :: nil) = Some E.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct ip as [| w ip]; cbn in H.
  - destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate; eauto.
  - destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
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
    destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate; eauto.
  - revert H; induction Φ as [| Φ IH z E0 | Φ IH c]; intros H; cbn in H |- *; [ discriminate | | exact (IH H) ].
    destruct (String.eqb x z); [| exact (IH H) ].
    destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
      exact (IHip _ _ _ H).
Qed.

Lemma gm_module_body_some : forall T oD Φ ch T'' oD',
    gm_module T oD Φ ch = Some (mr_body T'' oD') -> exists Φ'', gm_body T Φ ch = Some (T'', Φ'').
Proof.
  intros * H; destruct ch as [| x ip]; cbn in H |- *; [ injection H as <- _; eauto | exact (gm_module_subbody _ _ _ _ _ _ H) ].
Qed.

Lemma gm_submodule_alias_decomp : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) ->
    exists pre y T' Φ', x :: ip = pre ++ y :: r /\ gm_body T Φ pre = Some (T', Φ') /\
      gm_submodule T' Φ' y nil = Some (mr_alias U nil).
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c its] * H; cbn in H; [ discriminate | |].
  - destruct (String.eqb x z) eqn:Exz.
    + destruct E0 as [? ? ? ? | pm [Δ [Φ0 | E1]] | ? D0 Φ0 | pm Δa pa Nsa]; try discriminate.
      * destruct ip as [| w ip]; [ discriminate |].
        destruct (IH _ _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz.
        destruct pre as [| v pre]; cbn in Hb |- *; [ injection Hb as <- <-; reflexivity | exact Hb ].
      * injection H as <- <-.
        exists nil, x, T, (gm_ext Φ z (ge_mod pm (gu_mk Δ (md_alias E1)))); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; reflexivity.
      * destruct ip as [| w ip]; [ discriminate |].
        destruct (IH _ _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz.
        destruct pre as [| v pre]; cbn in Hb |- *; [ injection Hb as <- <-; reflexivity | exact Hb ].
      * injection H as <- <-.
        exists nil, x, T, (gm_ext Φ z (ge_ind_alias pm Δa pa Nsa)); split; [ reflexivity |]; split; [ reflexivity |].
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
  destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ _ H ch).
  - injection H as <- <-; split; [ reflexivity |].
    intros Hne; destruct (ip ++ ch) eqn:E; [ destruct ch; [ contradiction | destruct ip; discriminate ] | reflexivity ].
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
  induction 1 as [| | Θ Ξ mp Vp VΦ HΞ IH HV Hff]; intros * Hf Hin; cbn in Hf; [ discriminate | discriminate |].
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

(** A global alias is an alias unit. *)
Lemma gm_submodule_alias_unit : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) -> exists Δ E, U = gu_mk Δ (md_alias E).
Proof.
  fix IH 1; intros [| Φ y E | Φ c its] * Hs; cbn in Hs; [ discriminate | | exact (IH _ _ _ _ _ _ Hs) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ Hs) ].
  destruct E as [? ? ? ? | ? [Δ [Φ' | E']] | ? D Φ' | ? Δ p Ns]; try discriminate.
  - destruct ip; [ discriminate | exact (IH _ _ _ _ _ _ Hs) ].
  - injection Hs as <- _; eauto.
  - destruct ip; [ discriminate | exact (IH _ _ _ _ _ _ Hs) ].
  - injection Hs as <- _; eauto.
Qed.

Lemma gc_module_alias_unit : forall Θ Ξ p U r,
    gc_module Θ Ξ p = Some (mr_alias U r) -> exists Δ E, U = gu_mk Δ (md_alias E).
Proof.
  intros * H; unfold gc_module, gc_module_u in H.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |]; [ discriminate | eapply gm_submodule_alias_unit; exact H |].
  destruct (gds_lookup Θ (q_unit p)) as [V |]; [| discriminate ].
  unfold gm_module in H; destruct (q_chain p) as [| x ip]; [ discriminate | eapply gm_submodule_alias_unit; exact H ].
Qed.

Lemma gc_module_alias_app : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p U r0,
    gc_module Θ Ξ p = Some (mr_alias U r0) ->
    forall ch, gc_module Θ Ξ (qname_app p ch) = Some (mr_alias U (r0 ++ ch)) /\
      (ch <> nil -> gc_resolve Θ Ξ (qname_app p ch) = None).
Proof.
  intros * Hg * H ch.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_module, gc_module_u in H0.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_submodule_head _ _ _ _ _ H0) ch) as Ef'.
    destruct (gm_submodule_alias_app _ _ _ _ _ _ H0 ch) as [H1 H2].
    unfold gc_module, gc_module_u, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn.
    split; [ exact H1 | exact H2 ].
  - destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    unfold gc_module, gc_module_u, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn [option_map qname_app q_unit q_chain]; rewrite El.
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
  pose proof H as H0; unfold gc_module, gc_module_u in H0.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; [ discriminate | |].
  - destruct (gs_find_tele_head _ _ Hs _ _ _ _ _ Ef (gm_submodule_head _ _ _ _ _ H0)) as (Fp & -> & HF).
    destruct (gm_submodule_alias_decomp _ _ _ _ _ _ H0) as (pre & y & T' & Φ' & Heq & Hb & Hy).
    exists (qname_app Fp pre), y; split; [ rewrite qname_app_app, <- Heq; reflexivity |].
    rewrite qname_app_app.
    destruct pre as [| v pre]; cbn in Heq, Hb |- *.
    + injection Heq as <- _; injection Hb as <- <-.
      unfold gc_module, gc_module_u; rewrite (HF nil); exact Hy.
    + injection Heq as <- _.
      unfold gc_module, gc_module_u; rewrite (HF (pre ++ y :: nil)).
      rewrite (proj1 (gm_subbody_snoc _ _ _ _ _ _ Hb y)); exact Hy.
  - destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:El; [| discriminate ].
    destruct (q_chain p) as [| x ip] eqn:Em; cbn in H0; [ discriminate |].
    destruct (gm_submodule_alias_decomp _ _ _ _ _ _ H0) as (pre & y & T' & Φ' & Heq & Hb & Hy).
    set (Fp := {| q_unit := q_unit p; q_chain := nil |}).
    assert (Hp : p = qname_app Fp (x :: ip)) by (destruct p; cbn in *; subst; reflexivity).
    assert (ElF : gds_lookup Θ (q_unit Fp) = Some V) by exact El.
    exists (qname_app Fp pre), y; split; [ rewrite Hp, qname_app_app, <- Heq; reflexivity |].
    rewrite qname_app_app.
    unfold gc_module, gc_module_u; rewrite (gs_find_tele_filed _ _ Hs _ _ ElF); cbn [qname_app q_unit q_chain Fp]; rewrite El; cbn [app].
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
  destruct E as [? ? ? ? | U | ? ? ? | ? Δa pa Nsa]; [ reflexivity | discriminate | discriminate | discriminate ].
Qed.

Lemma gm_submodule_alias_resolve : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) -> gm_resolve Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D0 Φ0 | ? Δa pa Nsa]; try discriminate.
  - destruct ip as [| w ip]; [ discriminate | exact (IH _ _ _ _ _ _ H) ].
  - destruct ip; reflexivity.
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

(** A path through an alias names no definition, no body module and no
    inductive type, so a prefix of a path naming one is no alias. *)
Lemma gc_prefix_not_alias : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p ch,
    ch <> nil ->
    (exists T oD, gc_module Θ Ξ (qname_app p ch) = Some (mr_body T oD)) \/
    (exists U, gc_module Θ Ξ (qname_app p ch) = Some (mr_alias U nil)) \/
    (exists E, gc_resolve Θ Ξ (qname_app p ch) = Some E) \/
    (exists D, ind_lookup Θ Ξ (qname_app p ch) = Some D) ->
    forall U r, gc_module Θ Ξ p <> Some (mr_alias U r).
Proof.
  intros * Hg * Hne Hx U r Ha.
  destruct (gc_module_alias_app _ _ Hg _ _ _ Ha ch) as [H1 H2].
  destruct Hx as [(T & oD & HT) | [(U' & HU) | [(E & HE) | (D & HD)]]];
    [ congruence | | rewrite (H2 Hne) in HE; discriminate | exact (ind_lookup_not_alias _ _ _ _ _ _ HD H1) ].
  rewrite H1 in HU; injection HU as _ Hr; destruct ch; [ contradiction | destruct r; discriminate ].
Qed.

(** A body module, or a module with a definition or an inductive type, has
    no alias among the prefixes of its path. *)
Lemma gc_chain_no_alias : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p,
    (exists T oD, gc_module Θ Ξ p = Some (mr_body T oD)) \/
    (exists x U, gc_module Θ Ξ (qname_app p (x :: nil)) = Some (mr_alias U nil)) \/
    (exists x E, gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some E) \/
    (exists x D, ind_lookup Θ Ξ (qname_app p (x :: nil)) = Some D) ->
    forall m1 m2, q_chain p = m1 ++ m2 -> m1 <> nil ->
    forall U r, gc_module Θ Ξ (q_abs (q_unit p) m1) <> Some (mr_alias U r).
Proof.
  intros * Hg [fp ms] Hx m1 m2 Hm Hne1 U r; cbn [q_unit q_chain] in *; subst ms.
  destruct m2 as [| y m2].
  - rewrite List.app_nil_r in Hx.
    destruct Hx as [(T & oD & HT) | [(x & U' & HU) | [(x & E & HE) | (x & D & HD)]]]; [ congruence | | |].
    + eapply gc_prefix_not_alias with (ch := x :: nil); [ exact Hg | discriminate | right; left; exists U'; exact HU ].
    + eapply gc_prefix_not_alias with (ch := x :: nil); [ exact Hg | discriminate | right; right; left; exists E; exact HE ].
    + eapply gc_prefix_not_alias with (ch := x :: nil); [ exact Hg | discriminate | right; right; right; exists D; exact HD ].
  - destruct Hx as [(T & oD & HT) | [(x & U' & HU) | [(x & E & HE) | (x & D & HD)]]].
    + eapply gc_prefix_not_alias with (ch := y :: m2); [ exact Hg | discriminate | left; exists T, oD; exact HT ].
    + eapply gc_prefix_not_alias with (ch := (y :: m2) ++ x :: nil); [ exact Hg | discriminate | right; left; exists U' ].
      unfold qname_app in *; cbn in *; rewrite <- app_assoc in HU; exact HU.
    + eapply gc_prefix_not_alias with (ch := (y :: m2) ++ x :: nil); [ exact Hg | discriminate | right; right; left; exists E ].
      unfold qname_app in *; cbn in *; rewrite <- app_assoc in HE; exact HE.
    + eapply gc_prefix_not_alias with (ch := (y :: m2) ++ x :: nil); [ exact Hg | discriminate | right; right; right; exists D ].
      unfold qname_app in *; cbn in *; rewrite <- app_assoc in HD; exact HD.
Qed.

Lemma gc_module_alias_resolve : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p U r0,
    gc_module Θ Ξ p = Some (mr_alias U r0) -> gc_resolve Θ Ξ p = None.
Proof.
  intros * Hg * H.
  pose proof Hg as Hs.
  unfold gc_module, gc_module_u, gc_resolve, gc_resolve_u in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; cbn; [ discriminate | exact (gm_submodule_alias_resolve _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [V |]; [| reflexivity ].
  destruct (q_chain p) as [| x ip]; cbn in H; [ discriminate | exact (gm_submodule_alias_resolve _ _ _ _ _ _ H) ].
Qed.

(** ** Validity of Bodies, by Induction over Insertion

    The induction of [GlobalPresup] for entries, extended to what a module
    contributes besides its definitions: its telescope ([F]) and its aliases.
    [V Θ2 Ξ2 T E] is the validity at [Θ2 ⍮ Ξ2] of an entry [E] other than a body
    module, checked over the telescope [T]. *)

(** *** Embeddings keeping bodies

    The validity of modules is stated at every target that keeps their
    bodies ([gc_subx]): a body valid at the source is the one read at the
    target.  The module of an inductive type grows while its members are
    checked, so each member is valid wherever the context it is checked in
    is ([Hdef] below). *)

Record Embx (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { emx_wf : ⊢g Θ2 ⍮ Ξ2
  ; emx_res : gc_subx Θ1 Ξ1 Θ2 Ξ2 }.

Lemma Embx_emb : forall Θ1 Ξ1 Θ2 Ξ2, Embx Θ1 Ξ1 Θ2 Ξ2 -> Emb Θ1 Ξ1 Θ2 Ξ2.
Proof. intros * [Hg Hs]; constructor; [ exact Hg | exact (gc_subx_sub _ _ _ _ Hs) ]. Qed.

Lemma Embx_refl : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Embx Θ Ξ Θ Ξ.
Proof. intros; constructor; [ assumption | apply gc_subx_refl ]. Qed.

Lemma Embx_pre : forall Θ1 Ξ1 Θ Ξ Θ2 Ξ2,
    gc_subx Θ1 Ξ1 Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> Embx Θ1 Ξ1 Θ2 Ξ2.
Proof. intros * H [Hg He]; constructor; [ assumption | eapply gc_subx_trans; eassumption ]. Qed.

(** What an entry contributes, its sub-bodies as they are. *)
Definition Ctbx (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (mp : qname) (E : gentry) : Prop :=
  Ctb Θ2 Ξ2 T mp E /\
  (forall x (ip : list String.string) r, ge_subbody T E x ip = Some r ->
     gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r).

Lemma Ctbx_frame : forall Θ mp Δ Φ x E Ξ Θ2 Ξ2,
    gc_subx Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ) Θ2 Ξ2 ->
    Ctbx Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mp x) E.
Proof.
  intros * Hs; split; [ exact (Ctb_frame _ _ _ _ _ _ _ _ _ (gc_subx_sub _ _ _ _ Hs)) |].
  intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_subx_body _ _ _ _ _ _ Hs).
  rewrite gc_body_frame_here; cbn [gu_mod gu_params]; apply gm_subbody_ext_here; exact Hr0.
Qed.

Lemma Embx_nested : forall Θ Ξ mp Δ' Φ' Θ2 Ξ2,
    Embx Θ Ξ Θ2 Ξ2 ->
    Ctbx Θ2 Ξ2 (gs_tele Ξ) mp (ge_body false Δ' Φ') ->
    Embx Θ ((mp, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * He [Hc Hbod]; constructor; [ exact (emx_wf _ _ _ _ He) | split ].
  - exact (em_res _ _ _ _ (Emb_nested _ _ _ _ _ _ _ (Embx_emb _ _ _ _ He) Hc)).
  - intros p r Hr; destruct (gc_body_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'].
    + apply Hbod; exact Hm.
    + exact (gc_subx_body _ _ _ _ _ _ (emx_res _ _ _ _ He) Hr').
Qed.

Lemma Ctbx_ind_ext : forall Θ2 Ξ2 T mp pv D Φ x b pv' A B,
    gm_fresh x Φ -> Ctbx Θ2 Ξ2 T mp (ge_ind pv D (Φ ⊳ x ↦ ge_def b pv' A B)) -> Ctbx Θ2 Ξ2 T mp (ge_ind pv D Φ).
Proof.
  intros * Hf [Hc Hbod]; split; [ exact (Ctb_ind_ext _ _ _ _ _ _ _ _ _ _ _ _ Hf Hc) |].
  intros z ip r Hr; apply Hbod; cbn [ge_subbody] in Hr |- *; apply gm_subbody_ext_fresh; assumption.
Qed.

Section ModInduction.
  Variable V : gdeps -> gstack -> ctx -> gentry -> Prop.
  Variable F : gdeps -> gstack -> ctx -> Prop.
  (** The validity of the declaration of an inductive type. *)
  Variable VD : gdeps -> gstack -> ind_decl -> Prop.

  (** A body is valid when its definitions and aliases are, and its body
      modules and the modules of its inductive types are, over their
      telescopes; the declaration of an inductive type is valid too. *)
  Fixpoint gm_valid (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (Φ : gmod) : Prop :=
    match Φ with
    | gm_nil => True
    | gm_open Φ0 _ _ => gm_valid Θ2 Ξ2 T Φ0
    | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body Φ'))) =>
        gm_valid Θ2 Ξ2 T Φ0 /\ F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θ2 Ξ2 (Δ ++ T) Φ'
    | gm_ext Φ0 _ (ge_ind _ D Φ') =>
        gm_valid Θ2 Ξ2 T Φ0 /\ VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D) /\ gm_valid Θ2 Ξ2 (ind_uparams D) Φ'
    | gm_ext Φ0 _ (ge_ind_alias pv Δ p Ns) =>
        gm_valid Θ2 Ξ2 T Φ0 /\ V Θ2 Ξ2 T (ge_mod pv (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns)))) /\
        V Θ2 Ξ2 T (ge_ind_alias pv Δ p Ns)
    | gm_ext Φ0 _ E => gm_valid Θ2 Ξ2 T Φ0 /\ V Θ2 Ξ2 T E
    end.

  Definition ge_valid (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
    match E with
    | ge_mod _ (gu_mk Δ (md_body Φ')) => F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θ2 Ξ2 (Δ ++ T) Φ'
    | ge_ind _ D Φ' => VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D) /\ gm_valid Θ2 Ξ2 (ind_uparams D) Φ'
    (** An inductive alias is valid as the module alias it is a view as, and
        as itself, the term it δ-unfolds to. *)
    | ge_ind_alias pv Δ p Ns =>
        V Θ2 Ξ2 T (ge_mod pv (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns)))) /\ V Θ2 Ξ2 T E
    | _ => V Θ2 Ξ2 T E
    end.

  Lemma gm_valid_ext : forall Θ2 Ξ2 T Φ x E,
      gm_valid Θ2 Ξ2 T (Φ ⊳ x ↦ E) <-> gm_valid Θ2 Ξ2 T Φ /\ ge_valid Θ2 Ξ2 T E.
  Proof. intros; destruct E as [? ? ? ? | ? [Δ [Φ' | E']] | ? ? ? | ? Δa pa Nsa]; cbn; tauto. Qed.

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
    forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> gds_valid Θ2 Ξ2 Θ /\ gs_valid Θ2 Ξ2 Ξ.

  (** A definition is checked in a closed telescope [T]: the frames'
      parameters, or the uniform parameters of the inductive type whose
      module it is a member of.  It is valid wherever what the context it is
      checked in files and has open is valid, along any growth. *)
  Hypothesis Hdef : forall Θ Ξ T A M b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ T ⊢ M : A -> Emb Θ Ξ Θ2 Ξ2 -> gds_valid Θ2 Ξ2 Θ -> gs_valid Θ2 Ξ2 Ξ ->
      V Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
  Hypothesis Hax : forall Θ Ξ A i b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
  Hypothesis Halias : forall Θ Ξ pv Δ E Θ2 Ξ2,
      tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
      GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
  Hypothesis Hindalias : forall Θ Ξ pv Δ p Ns D Θ2 Ξ2,
      tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> List.length Ns <= ind_nu D ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
      GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns).
  Hypothesis Hnil : forall Θ Ξ Δ Θ2 Ξ2,
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
  (** A declaration, and the telescope of its uniform parameters, which its
      module's members are checked in. *)
  Hypothesis Hind : forall Θ Ξ D Θ2 Ξ2,
      decl_typed Θ Ξ D -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D).

  (** An entry, and the context it is checked in. *)
  Definition GoodEV (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    GoodV Θ Ξ /\
    forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> Ctbx Θ2 Ξ2 (gs_tele Ξ) mp E -> ge_valid Θ2 Ξ2 (gs_tele Ξ) E.

  Definition GoodMV (Θ : gdeps) (Ξ : gstack) (mp : qname) (Δ : ctx) (Φ : gmod) : Prop :=
    GoodV Θ Ξ /\
    forall Θ2 Ξ2, Embx Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 -> Embx Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ) /\ gm_valid Θ2 Ξ2 (Δ ++ gs_tele Ξ) Φ.

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
    (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> GoodV Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - split; [ assumption | intros Θ2 Ξ2 He _; cbn; eapply Hax; eassumption ].
    - split; [ assumption |]; intros Θ2 Ξ2 He _; cbn.
      destruct (H0 _ _ He) as [HΘ HΞ]; eapply Hdef; [ eassumption | exact (Embx_emb _ _ _ _ He) | exact HΘ | exact HΞ ].
    - destruct H0 as [HG HM]; split; [ exact HG |]; intros Θ2 Ξ2 He Hc; cbn.
      apply HM; [ exact (Embx_nested _ _ _ _ _ _ _ He Hc) | exact He ].
    - split; [ assumption | intros Θ2 Ξ2 He _; cbn; eapply Halias; eassumption ].
    - (* an inductive type, before the members of its module *)
      split; [ assumption |]; intros Θ2 Ξ2 He _; cbn.
      edestruct Hind as [HD HF]; [| eassumption | exact He |].
      { repeat match goal with H : decl_mvc _ |- _ => destruct H as (? & ? & ?) end.
        repeat split; eauto. }
      repeat split; assumption.
    - (* one more member of the module of an inductive type: valid wherever
         the context it is checked in, with the entry so far, is *)
      rename H0 into IHE.
      destruct IHE as [HG IHE]; split; [ exact HG |].
      intros Θ2 Ξ2 He Hc.
      pose proof (Ctbx_ind_ext _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) Hc) as Hc0.
      destruct (IHE _ _ He Hc0) as (HD & HF & HΦ).
      destruct (HG _ _ He) as [HΘ HΞ].
      cbn; split; [ exact HD | split; [ exact HF | split; [ exact HΦ |] ] ].
      eapply Hdef; [ eassumption | apply Emb_entry; [ exact (Embx_emb _ _ _ _ He) | exact (proj1 Hc0) ] | exact HΘ |].
      cbn [gs_valid gu_params gu_mod] in HΞ |- *; destruct HΞ as (HF0 & HΦ0 & HΞ0).
      split; [ exact HF0 | split; [| exact HΞ0 ] ].
      apply gm_valid_ext; split; [ exact HΦ0 |]; cbn; repeat split; assumption.
    - (* an inductive alias: valid as the module alias it is a view as, and
         as itself *)
      split; [ assumption | intros Θ2 Ξ2 He _; cbn; split; [ eapply Halias | eapply Hindalias ]; eassumption ].
    - split; [ assumption |]; intros Θ2 Ξ2 _ He; split; [ eapply Hnil; eassumption | exact I ].
    - rename H0 into IHΦ, H2 into IHE.
      destruct IHΦ as [HG IHΦ]; split; [ exact HG |].
      intros Θ2 Ξ2 He Hout.
      assert (He' : Embx Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Embx_pre; [ apply gc_subx_grow; eassumption | exact He ]).
      destruct (IHΦ _ _ He' Hout) as [HF HΦ].
      split; [ exact HF |]; apply gm_valid_ext; split; [ exact HΦ |].
      exact (proj2 IHE _ _ He' (Ctbx_frame _ _ _ _ _ _ _ _ _ (emx_res _ _ _ _ He))).
    - intros Θ2 Ξ2 _; split; [ intros fp U Hl; discriminate | exact I ].
    - (* a filed unit: valid as its closed frame was *)
      rename H into Hg, H0 into IHU.
      match goal with |- GoodV ((?f, _) :: _) nil => rename f into fp0 end.
      intros Θ2 Ξ2 He; split; [| exact I ].
      destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (_ & _ & [Hn _]).
      destruct (IHU Θ2 Ξ2 ltac:(eapply Embx_pre; [ apply gc_subx_file; exact Hn | exact He ])) as [HΘ HΞ].
      intros fq W Hl; cbn in Hl; destruct (path_beq fq fp0);
        [ injection Hl as <-; cbn [gs_valid gs_tele] in HΞ; rewrite app_nil_r in HΞ; tauto | exact (HΘ _ _ Hl) ].
    - rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He.
      assert (He0 : Embx Θ Ξ Θ2 Ξ2) by (eapply Embx_pre; [ apply gc_subx_push; eassumption | exact He ]).
      destruct (IHΞ _ _ He0) as [HΘ HΞ]; split; [ exact HΘ |].
      destruct (proj2 IHU _ _ He He0); cbn [gs_valid]; repeat split; assumption.
  Qed.

  Corollary global_valid : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> GoodV Θ Ξ.
  Proof. intros; apply global_valid_all; assumption. Qed.

  (** *** Reading validity back *)

  Lemma gm_valid_subbody : forall Φ Θ2 Ξ2 T x ip T' Φ',
      gm_valid Θ2 Ξ2 T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> F Θ2 Ξ2 T' /\ gm_valid Θ2 Ξ2 T' Φ'.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? D Φ0 | ? Δa pa Nsa]; try discriminate.
    - destruct Hv as (_ & HF & Hv); destruct ip as [| w ip].
      + injection H as <- <-; split; assumption.
      + exact (IH _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & HF & Hv); destruct ip as [| w ip].
      + injection H as <- <-; split; assumption.
      + exact (IH _ _ _ _ _ _ _ _ Hv H).
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
      [| destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? D Φ0 | ? Δa pa Nsa]; try discriminate.
    - injection H as <-; exists T; exact (proj2 Hv).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_def : forall Φ Θ2 Ξ2 T z b pv A B,
      gm_valid Θ2 Ξ2 T Φ -> gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> V Θ2 Ξ2 T (ge_def b pv A B).
  Proof.
    induction Φ as [| Φ IH y E0 | Φ IH c]; intros * Hv H; cbn in Hv, H; [ discriminate | | eauto ].
    destruct (String.eqb z y);
      [| destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E0 as [? ? ? ? | ? [Δ [Φ0 | E1]] | ? ? ? | ? Δa pa Nsa]; try discriminate.
    injection H; intros; subst; exact (proj2 Hv).
  Qed.

  Lemma gm_valid_alias : forall Φ Θ2 Ξ2 T x ip U r,
      gm_valid Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_alias U r) -> exists T' pv, V Θ2 Ξ2 T' (ge_mod pv U).
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [Φ0 | E0]] | ? D Φ0 | pm Δa pa Nsa]; try discriminate.
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - injection H as <- _; exists T, pm; exact (proj2 Hv).
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - injection H as <- _; exists T, pm; exact (proj1 (proj2 Hv)).
  Qed.

  Lemma gm_valid_ind_target : forall Φ Θ2 Ξ2 T ip Δ p Ns,
      gm_valid Θ2 Ξ2 T Φ -> gm_ind_target Φ ip = Some (Δ, p, Ns) -> exists T' pv, V Θ2 Ξ2 T' (ge_ind_alias pv Δ p Ns).
  Proof.
    unfold gm_ind_target; fix IH 1; intros [| Φ y E0 | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y);
      [| destruct E0 as [? ? ? ? | ? [Δ0 [Φ0 | E1]] | ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ0 [Φ0 | E1]] | ? D Φ0 | pm Δa pa Nsa]; cbn in H; try discriminate.
    - injection H as -> -> ->; exists T, pm; exact (proj2 (proj2 Hv)).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_ind : forall Φ Θ2 Ξ2 T x ip T' D,
      gm_valid Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_body T' (Some D)) -> VD Θ2 Ξ2 D.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [Φ0 | E0]] | ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [Φ0 | E0]] | ? D0 Φ0 | pm Δa pa Nsa]; try discriminate.
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - destruct ip as [| w ip]; [ injection H as _ <-; exact (proj1 (proj2 Hv)) |].
      destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gs_valid_find : forall Θ2 Ξ2 Ξ p U ip T,
      gs_valid Θ2 Ξ2 Ξ -> gs_find_tele Ξ p = Some (U, ip, T) ->
      F Θ2 Ξ2 (gu_params U ++ T) /\ gm_valid Θ2 Ξ2 (gu_params U ++ T) (gu_mod U).
  Proof.
    induction Ξ as [| [mp U0] Ξ IH]; intros * Hv H; cbn in Hv, H; [ discriminate |].
    destruct (qname_strip mp p); [ injection H as <- <- <-; split; apply Hv | exact (IH _ _ _ _ (proj2 (proj2 Hv)) H) ].
  Qed.

  Lemma good_body : forall Θ Ξ Θ2 Ξ2 p T Φ, gds_valid Θ2 Ξ2 Θ -> gs_valid Θ2 Ξ2 Ξ ->
      gc_body Θ Ξ p = Some (T, Φ) -> F Θ2 Ξ2 T /\ gm_valid Θ2 Ξ2 T Φ.
  Proof.
    intros * HΘ HΞ H; unfold gc_body in H.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [HF Hv]; exact (gm_valid_subbody _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [HF Hv]; exact (gm_valid_body _ _ _ _ _ _ _ HF Hv H).
  Qed.

  Lemma good_resolve : forall Θ Ξ Θ2 Ξ2 p E, gds_valid Θ2 Ξ2 Θ -> gs_valid Θ2 Ξ2 Ξ ->
      gc_resolve Θ Ξ p = Some E -> exists T, V Θ2 Ξ2 T E.
  Proof.
    intros * HΘ HΞ H; unfold gc_resolve, gc_resolve_u in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ p) as [[[U ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_resolve _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_resolve _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_alias : forall Θ Ξ Θ2 Ξ2 p U r, gds_valid Θ2 Ξ2 Θ -> gs_valid Θ2 Ξ2 Ξ ->
      gc_module Θ Ξ p = Some (mr_alias U r) -> exists T pv, V Θ2 Ξ2 T (ge_mod pv U).
  Proof.
    intros * HΘ HΞ H; unfold gc_module, gc_module_u in H.
    destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_alias _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv].
      destruct (q_chain p) as [| x ip]; [ discriminate |]; exact (gm_valid_alias _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_ind_alias : forall Θ Ξ Θ2 Ξ2 pq Δ p Ns, gds_valid Θ2 Ξ2 Θ -> gs_valid Θ2 Ξ2 Ξ ->
      ind_alias_lookup Θ Ξ pq = Some (Δ, p, Ns) -> exists T pv, V Θ2 Ξ2 T (ge_ind_alias pv Δ p Ns).
  Proof.
    intros * HΘ HΞ H; unfold ind_alias_lookup, ind_alias_lookup_u in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ pq) as [[[U ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_ind_target _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit pq)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_ind_target _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_ind : forall Θ Ξ Θ2 Ξ2 p D, gds_valid Θ2 Ξ2 Θ -> gs_valid Θ2 Ξ2 Ξ ->
      ind_lookup Θ Ξ p = Some D -> VD Θ2 Ξ2 D.
  Proof.
    intros * HΘ HΞ H.
    destruct (ind_lookup_module _ _ _ _ H) as [T H']; unfold gc_module, gc_module_u in H'.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_ind _ _ _ _ _ _ _ _ Hv H').
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv].
      destruct (q_chain p) as [| x ip]; [ discriminate |]; exact (gm_valid_ind _ _ _ _ _ _ _ _ Hv H').
  Qed.
End ModInduction.

(** ** Member Types Are Functional *)

Lemma gc_resolve_module_alias_excl : forall Θ Ξ p E U r,
    gc_resolve Θ Ξ p = Some E -> gc_module Θ Ξ p = Some (mr_alias U r) -> False.
Proof.
  intros * Hr Hm; unfold gc_resolve, gc_resolve_u, gc_module, gc_module_u in *.
  rewrite gs_find_tele_find in Hr.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |]; cbn in Hr; [ discriminate | |].
  - rewrite (gm_submodule_alias_resolve _ _ _ _ _ _ Hm) in Hr; discriminate.
  - destruct (gds_lookup Θ (q_unit p)) as [V |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; [ discriminate |].
    rewrite (gm_submodule_alias_resolve _ _ _ _ _ _ Hm) in Hr; discriminate.
Qed.

Lemma member_type_functional_all : forall Θ Ξ,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R -> forall R', member_type Θ Ξ Γ H ch R' -> R = R') /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R -> forall R', unit_member_type Θ Ξ Γ U ch R' -> R = R') /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall Φx', body_xp Θ Ξ Γ Φ Φx' -> Φx = Φx') /\
    (forall io Γ H its gs, items_gen Θ Ξ io Γ H its gs -> forall gs', items_gen Θ Ξ io Γ H its gs' -> gs = gs').
Proof.
  intros Θ Ξ; apply member_type_both_ind.
  1-12: intros *; intros; match goal with H' : _ _ _ _ _ _ ?A' |- _ = ?A' => inversion H'; subst end;
    repeat match goal with
      | IH : forall Φx', body_xp _ _ ?G ?Φ Φx' -> ?X = Φx', Hb : body_xp _ _ ?G ?Φ ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (IH _ Hb); subst Y
      end;
    try congruence;
    try solve [ exfalso; eapply gc_resolve_module_alias_excl; eassumption ];
    try solve [ match goal with H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
                  rewrite H1 in H2; discriminate end ];
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
  - intros * H'; inversion H'; reflexivity.
  - intros * Hx IH * H'; inversion H'; subst; f_equal; eauto.
  - intros * Hx IH Hm _ Htl Hg IHg Hok * H'; inversion H'; subst.
    match goal with Hb : body_xp _ _ _ _ ?Y |- _ => pose proof (IH _ Hb); subst Y end.
    match goal with Hg' : items_gen _ _ _ _ _ _ ?Y |- _ => pose proof (IHg _ Hg'); subst Y end.
    reflexivity.
  - intros * H'; inversion H'; reflexivity.
  - intros * Hg IH * H'; inversion H'; subst; f_equal; eauto.
  - intros * Hm IHm Hg IH * H'; inversion H'; subst;
      match goal with Hm' : member_type _ _ _ _ _ _ |- _ => pose proof (IHm _ Hm') as E end; try discriminate E.
    injection E as <-; f_equal; eauto.
  - intros * Hm IHm Hg IH * H'; inversion H'; subst;
      match goal with Hm' : member_type _ _ _ _ _ _ |- _ => pose proof (IHm _ Hm') as E end; try discriminate E.
    injection E as <-; f_equal; eauto.
  - intros * Hm IHm Hq Hi Hg IH * H'; inversion H'; subst;
      match goal with Hm' : member_type _ _ _ _ _ _ |- _ => pose proof (IHm _ Hm') as E end; try discriminate E.
    + match goal with Hq' : mod_qname _ = Some _, Hi' : _ = Some _ |- _ => rewrite Hq in Hq'; injection Hq' as <-; rewrite Hi in Hi'; injection Hi' as <- <- <- end.
      f_equal; eauto.
    + match goal with Hn : forall mp, _ -> _ = None |- _ => rewrite (Hn _ Hq) in Hi; discriminate end.
  - intros * Hm IHm Hn Hg IH * H'; inversion H'; subst;
      match goal with Hm' : member_type _ _ _ _ _ _ |- _ => pose proof (IHm _ Hm') as E end; try discriminate E.
    + match goal with Hq' : mod_qname _ = Some _, Hi' : _ = Some _ |- _ => rewrite (Hn _ Hq') in Hi'; discriminate end.
    + f_equal; eauto.
Qed.

Corollary member_type_functional : forall Θ Ξ,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R -> forall R', member_type Θ Ξ Γ H ch R' -> R = R') /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R -> forall R', unit_member_type Θ Ξ Γ U ch R' -> R = R').
Proof. intros; destruct (member_type_functional_all Θ Ξ) as (H1 & H2 & _); split; assumption. Qed.

Corollary body_xp_functional : forall Θ Ξ Γ Φ Φx Φx', body_xp Θ Ξ Γ Φ Φx -> body_xp Θ Ξ Γ Φ Φx' -> Φx = Φx'.
Proof. intros * H1 H2; exact (proj1 (proj2 (proj2 (member_type_functional_all Θ Ξ))) _ _ _ H1 _ H2). Qed.

Corollary items_gen_functional : forall Θ Ξ io Γ H its gs gs',
    items_gen Θ Ξ io Γ H its gs -> items_gen Θ Ξ io Γ H its gs' -> gs = gs'.
Proof. intros * H1 H2; exact (proj2 (proj2 (proj2 (member_type_functional_all Θ Ξ))) _ _ _ _ _ H1 _ H2). Qed.

Lemma unit_xp_functional : forall Θ Ξ Γ U Ux Ux', unit_xp Θ Ξ Γ U Ux -> unit_xp Θ Ξ Γ U Ux' -> Ux = Ux'.
Proof.
  intros * H1 H2; destruct H1; inversion H2; subst; [ f_equal; f_equal; eapply body_xp_functional; eassumption | reflexivity ].
Qed.


