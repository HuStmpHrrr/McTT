(** * Paths and Descriptions in a Well-Formed Global Context

    What a path names in a global context, read off its frames and filed
    units, and how a description a module expression denotes is read off
    the same storage: in a well-formed context a closed description is the
    body stored at some path, its entries are what resolves below that path,
    the description a module expression denotes is unique, and it grows
    with the context ([mdenote_grow]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Structural.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Reading Paths *)
Lemma qname_strip_app : forall mp ip, qname_strip mp (qname_app mp ip) = Some ip.
Proof.
  intros; unfold qname_strip, qname_app; cbn; rewrite path_beq_refl; apply strip_prefix_app.
Qed.

Lemma qname_strip_app_inv : forall mp p ip, qname_strip mp p = Some ip -> p = qname_app mp ip.
Proof.
  intros [fp ms] [fq ns] ip H; unfold qname_strip, qname_app in *; cbn in *.
  destruct (path_beq fp fq) eqn:Hb; [| discriminate ].
  apply path_beq_true in Hb; subst.
  apply strip_prefix_spec in H; subst; reflexivity.
Qed.

Lemma qname_app_in : forall mp x ip, qname_app (qname_in mp x) ip = qname_app mp (x :: ip).
Proof. intros; unfold qname_app, qname_in; cbn; rewrite <- List.app_assoc; reflexivity. Qed.

(** Reading a frame: what is in it, or what is outside it. *)
Lemma gc_resolve_frame : forall Θ mp U Ξ p E,
    gc_resolve Θ ((mp, U) :: Ξ) p = Some E ->
    (exists ip, p = qname_app mp ip /\ gm_resolve (gu_mod U) ip = Some E) \/
    gc_resolve Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_resolve, gc_resolve_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_resolve_frame_here : forall Θ mp U Ξ ip,
    gc_resolve Θ ((mp, U) :: Ξ) (qname_app mp ip) = gm_resolve (gu_mod U) ip.
Proof. intros; unfold gc_resolve, gc_resolve_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_module_frame : forall Θ mp U Ξ p r,
    gc_module Θ ((mp, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_module Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_module, gc_module_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_module_frame_here : forall Θ mp U Ξ x ip,
    gc_module Θ ((mp, U) :: Ξ) (qname_app mp (x :: ip)) = gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_module, gc_module_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_body_frame : forall Θ mp U Ξ p r,
    gc_body Θ ((mp, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_subbody (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_body Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_body in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_body_frame_here : forall Θ mp U Ξ x ip,
    gc_body Θ ((mp, U) :: Ξ) (qname_app mp (x :: ip)) = gm_subbody (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_body; cbn; rewrite qname_strip_app; reflexivity. Qed.

(** Every frame of a well-formed stack belongs to a unit not filed. *)
Lemma wf_gstack_frames : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp U, List.In (mp, U) Ξ -> gds_lookup Θ (q_unit mp) = None.
Proof.
  induction 1 as [| | Θ Ξ mq Δ Φ HΞ IH HV Hff]; intros mp V0 Hin; try (cbn in Hin; contradiction).
  destruct Hin as [[= <- <-] | Hin]; [| eauto ].
  destruct Ξ as [| [mr W] Ξ']; cbn in Hff.
  - exact (proj1 Hff).
  - destruct Hff as (x & -> & _); cbn; apply (IH mr W); left; reflexivity.
Qed.

(** ** Prefixes of Extended Paths *)

Lemma strip_prefix_snoc : forall l m y r,
    strip_prefix l m = Some r -> strip_prefix l (m ++ y :: nil) = Some (r ++ y :: nil).
Proof. intros * H; apply strip_prefix_spec in H; subst; rewrite <- app_assoc; apply strip_prefix_app. Qed.

(** ** Bodies of Modules *)


Lemma gm_module_subbody : forall Φ T x ip T' oD,
    gm_submodule T Φ x ip = Some (mr_body T' oD) -> exists Φ', gm_subbody T Φ x ip = Some (T', Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
    destruct ip as [| z ip]; try discriminate; first [ injection H as <- _; eauto | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gm_subbody_snoc : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y, gm_submodule T Φ x (ip ++ y :: nil) = gm_submodule T' Φ' y nil /\
      gm_subbody T Φ x (ip ++ y :: nil) = gm_subbody T' Φ' y nil.
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; split; reflexivity | exact (IH _ _ _ _ _ _ H y) ]).
Qed.

Lemma gm_subbody_resolve : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall z, gm_resolve Φ (x :: ip ++ z :: nil) = gm_resolve Φ' (z :: nil).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H z; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H z) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H z) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; reflexivity | specialize (IH _ _ _ _ _ _ H z); cbn in IH; exact IH ]).
Qed.

(** ** Coherence of a Body with its Telescope *)

(** A body of definitions only: the module of an inductive type. *)
Fixpoint gm_defs (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ0 _ (ge_def _ _ _ _) => gm_defs Φ0
  | _ => False
  end.

Lemma gm_defs_submodule : forall Φ T y ip, gm_defs Φ -> gm_submodule T Φ y ip = None.
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hd; cbn in Hd |- *; [ reflexivity | | contradiction ].
  destruct E; try contradiction; destruct (String.eqb y z); auto.
Qed.

(** [gm_coh T Φ]: the body [Φ], filed over the telescope [T], is coherent
    with it: every definition's type is closed over [T], every module's and
    alias's parameters extend [T], and every inductive member's uniform
    parameters extend [T], its own body made of definitions only. *)
Fixpoint gm_coh (T : ctx) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_open Φ0 _ _ => gm_coh T Φ0
  | gm_ext Φ0 _ (ge_def _ _ A _) => gm_coh T Φ0 /\ exists A0, A = ctx_pi T A0
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body sm Φ'))) => gm_coh T Φ0 /\ tele_ass Δ /\ gm_coh (Δ ++ T) Φ'
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_alias _))) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  | gm_ext Φ0 _ (ge_ind _ _ _ D Φ') =>
      gm_coh T Φ0 /\ (exists Δ0, ind_uparams D = Δ0 ++ T /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ' /\ gm_defs Φ'
  | gm_ext Φ0 _ (ge_ind_alias _ Δ _ _ _ _) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  end.

Lemma gm_coh_subbody : forall Φ T x ip T' Φ',
    gm_coh T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * Hc H; cbn in Hc, H; [ discriminate | | exact (IH _ _ _ _ _ _ Hc H) ].
  destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | ? Δa pma pa ka Nsa];
    destruct (String.eqb x y); try discriminate; try (eapply IH; [ apply Hc | exact H ]).
  - destruct Hc as (Hc1 & HΔ & Hc2).
    destruct ip as [| w ip].
    + injection H as <- <-; split; [ exact Hc2 | eauto ].
    + destruct (IH _ _ _ _ _ _ Hc2 H) as (Hc' & Δ' & -> & HΔ').
      split; [ exact Hc' | exists (Δ' ++ Δ); rewrite app_assoc; split; [ reflexivity | apply Forall_app; auto ] ].
  - destruct Hc as (Hc1 & (Δ & HΔe & HΔ) & Hc2 & _).
    destruct ip as [| w ip].
    + injection H as <- <-; split; [ exact Hc2 | eauto ].
    + destruct (IH _ _ _ _ _ _ Hc2 H) as (Hc' & Δ' & -> & HΔ').
      split; [ exact Hc' | exists (Δ' ++ Δ); rewrite HΔe, app_assoc; split; [ reflexivity | apply Forall_app; auto ] ].
Qed.

Lemma gm_coh_child : forall Φ T y r,
    gm_coh T Φ -> gm_submodule T Φ y nil = Some r ->
    (exists Δ oD, r = mr_body (Δ ++ T) oD /\ tele_ass Δ) \/
    (exists U Δ, r = mr_alias U /\ gu_params U = Δ ++ T /\ tele_ass Δ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc H; cbn in Hc, H; [ discriminate | | eauto ].
  destruct (String.eqb y z).
  - destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | ? Δa pma pa ka Nsa]; [ discriminate | | | | ].
    + injection H as <-; destruct Hc as (_ & HΔ & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
    + injection H as <-; destruct Hc as (_ & (Δ0 & -> & HΔ) & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
  - destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? ? ? | ? Δa pma pa ka Nsa]; eapply IH; try eassumption; apply Hc.
Qed.

(** ** Coherence of Well-Formed Bodies *)

(** The uniform parameters of a group over the frames' parameters [T]
    extend [T] by assumptions. *)
Lemma uparams_split : forall (D : ind_decl) Δ T, ind_uparams D = Δ ++ T -> tele_ass (ind_uparams D) ->
    exists Δ0, ind_uparams D = Δ0 ++ T /\ tele_ass Δ0.
Proof.
  intros * Hp Ha; exists Δ; split; [ exact Hp |].
  rewrite Hp in Ha; apply Forall_app in Ha as [Ha _]; exact Ha.
Qed.

Lemma wf_gmod_coh :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> forall Ξ' mp' Δ Φ, Ξ = (mp', gu_body Δ Φ) :: Ξ' ->
     match E with
     | ge_def _ _ A _ => exists A0, A = ctx_pi (Δ ++ gs_tele Ξ') A0
     | ge_mod _ (gu_mk Δ1 (md_body sm Φ1)) => tele_ass Δ1 /\ gm_coh (Δ1 ++ Δ ++ gs_tele Ξ') Φ1
     | ge_mod _ (gu_mk Δ1 (md_alias _)) => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
     | ge_ind _ _ _ D Φ1 =>
         (exists Δ0, ind_uparams D = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ1 /\ gm_defs Φ1
     | ge_ind_alias _ Δ1 _ _ _ _ => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
     end) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> tele_ass Δ /\ gm_coh (Δ ++ gs_tele Ξ) Φ).
Proof.
  apply global_wf_mut_ind; intros; subst; cbn.
  - eauto.
  - match goal with IH : tele_ass ?Δ' /\ _ |- _ => destruct IH as [HΔ Hc] end.
    cbn in Hc; split; [ exact HΔ | exact Hc ].
  - exists Δ; cbn; auto.
  - (* the module of the first member of a group, before its members *)
    split; [| split; exact I ].
    match goal with Hp : ind_uparams ?D = ?Δd ++ _ |- _ => exact (uparams_split _ _ _ Hp ltac:(assumption)) end.
  - (* the module of a later member, before its members *)
    match goal with Heq : (_, _) :: _ = (_, _) :: _ |- _ => injection Heq; intros; subst end.
    split; [| split; exact I ].
    match goal with Hp : ind_uparams ?D = ?Δd ++ _ |- _ => exact (uparams_split _ _ _ Hp ltac:(assumption)) end.
  - (* one more member *)
    match goal with Heq : (_, _) :: _ = (_, _) :: _ |- _ => injection Heq as -> -> -> end; subst.
    match goal with IHE : forall _ _ _ _, _ = _ -> _ |- _ => specialize (IHE _ _ _ _ eq_refl); cbn in IHE; destruct IHE as (HU & Hc & Hd) end.
    split; [ exact HU | cbn; split; [ split; [ exact Hc | eauto ] | exact Hd ] ].
  - (* an inductive alias *)
    eexists; split; [ reflexivity | assumption ].
  - split; [ assumption | exact I ].
  - match goal with IH : tele_ass Δ /\ _ |- _ => destruct IH as [HΔ Hc] end.
    split; [ exact HΔ |].
    match goal with IHE : forall _ _ _ _, _ = _ -> _ |- _ => specialize (IHE _ _ _ _ eq_refl); cbn in IHE end.
    destruct E as [b pv A B | ? [Δ1 [? Φ1 | E1]] | ? ? ? D1 Φ1 | ? Δa pma pa ka Nsa]; cbn; try split; auto; apply IHE.
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

Lemma wf_gstack_coh : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall p U ip T, gs_find_tele Ξ p = Some (U, ip, T) -> gm_coh (gu_params U ++ T) (gu_mod U).
Proof.
  induction 1 as [| | Θ Ξ mp Δ Φ HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; try discriminate.
  destruct (qname_strip mp p); [| eauto ].
  injection Hf as <- <- <-.
  exact (proj2 (proj2 wf_gmod_coh _ _ _ _ _ HΦ)).
Qed.

Lemma wf_gdeps_coh : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall fp U, gds_lookup Θ fp = Some U -> gm_coh (gu_params U) (gu_mod U).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Δ Φ HΞ IH HΦ Hff]; intros fp U Hl; cbn in Hl; [ discriminate | | eauto ].
  destruct (path_beq fp fq); [ injection Hl as -> | eauto ].
  pose proof (wf_gstack_coh _ _ Hg (q_abs fq nil) U nil nil) as Hc; rewrite app_nil_r in Hc; apply Hc.
  cbn; unfold qname_strip; cbn; rewrite path_beq_refl; reflexivity.
Qed.

Lemma gc_body_coh : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> gm_coh T Φ.
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
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
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

Lemma gs_find_tele_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
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


Lemma gs_find_tele_filed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
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


(** What resolves below a closed module is what its body says. *)
Theorem closed_read : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T oD Φ, gc_body Θ Ξ p = Some (T, Φ) ->
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

(** The same, the member the body is filed with read off [ind_mlookup]. *)
Corollary closed_read_body : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    forall ch, gc_module Θ Ξ (qname_app p ch) = gm_module T (ind_mlookup Θ Ξ p) Φ ch /\
      gc_body Θ Ξ (qname_app p ch) = gm_body T Φ ch /\
      (ch <> nil -> gc_resolve Θ Ξ (qname_app p ch) = gm_resolve Φ ch).
Proof.
  intros * Hg * H; destruct (gc_body_module _ _ _ _ _ H) as [oD Hm].
  rewrite (ind_mlookup_body _ _ _ _ _ Hm); exact (closed_read _ _ Hg _ _ _ _ H Hm).
Qed.

(** ** The Facts the Semantics Uses *)

Lemma wf_gc_child : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T oD y T' oD',
    gc_module Θ Ξ p = Some (mr_body T oD) -> gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_body T' oD') ->
    exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ _ HΦ Hp (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & oD0 & [= -> _] & HΔ) | (U & Δ & [=] & _)]; eauto.
Qed.

Lemma wf_gc_alias_params : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T oD y U,
    gc_module Θ Ξ p = Some (mr_body T oD) -> gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U) ->
    exists Δ, gu_params U = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ _ HΦ Hp (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & oD0 & [=] & _) | (U' & Δ & [= <-] & HU & HΔ)]; eauto.
Qed.

(** ** Decomposing Paths into Bodies *)

Lemma gm_resolve_subbody : forall Φ T x ip z E,
    gm_resolve Φ (x :: ip ++ z :: nil) = Some E ->
    exists T' Φ', gm_subbody T Φ x ip = Some (T', Φ') /\ gm_resolve Φ' (z :: nil) = Some E.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct ip as [| w ip]; cbn in H.
  - destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate; eauto.
  - destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
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
    destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate; eauto.
  - revert H; induction Φ as [| Φ IH z E0 | Φ IH c]; intros H; cbn in H |- *; [ discriminate | | exact (IH H) ].
    destruct (String.eqb x z); [| exact (IH H) ].
    destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
      exact (IHip _ _ _ H).
Qed.

Lemma gm_module_body_some : forall T oD Φ ch T'' oD',
    gm_module T oD Φ ch = Some (mr_body T'' oD') -> exists Φ'', gm_body T Φ ch = Some (T'', Φ'').
Proof.
  intros * H; destruct ch as [| x ip]; cbn in H |- *; [ injection H as <- _; eauto | exact (gm_module_subbody _ _ _ _ _ _ H) ].
Qed.

Lemma gm_submodule_alias_decomp : forall Φ T x ip U,
    gm_submodule T Φ x ip = Some (mr_alias U) ->
    exists pre y T' Φ', x :: ip = pre ++ y :: nil /\ gm_body T Φ pre = Some (T', Φ') /\
      gm_submodule T' Φ' y nil = Some (mr_alias U).
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c its] * H; cbn in H; [ discriminate | |].
  - destruct (String.eqb x z) eqn:Exz.
    + destruct E0 as [? ? ? ? | pm [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | pm Δa pma pa ka Nsa]; try discriminate.
      * destruct ip as [| w ip]; [ discriminate |].
        destruct (IH _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz.
        destruct pre as [| v pre]; cbn in Hb |- *; [ injection Hb as <- <-; reflexivity | exact Hb ].
      * destruct ip as [| w ip]; [| discriminate ]; injection H as <-.
        exists nil, x, T, (gm_ext Φ z (ge_mod pm (gu_mk Δ (md_alias E1)))); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; reflexivity.
      * destruct ip as [| w ip]; [ discriminate |].
        destruct (IH _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz.
        destruct pre as [| v pre]; cbn in Hb |- *; [ injection Hb as <- <-; reflexivity | exact Hb ].
      * destruct ip as [| w ip]; [| discriminate ]; injection H as <-.
        exists nil, x, T, (gm_ext Φ z (ge_ind_alias pm Δa pma pa ka Nsa)); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; reflexivity.
    + destruct (IH _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
      destruct pre as [| v pre]; cbn in Heq, Hb.
      * injection Heq as <- ->; injection Hb as <- <-.
        exists nil, x, T, (gm_ext Φ z E0); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; exact Hs.
      * injection Heq as <- Heq.
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz; exact Hb.
  - destruct (IH _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
    destruct pre as [| v pre]; cbn in Heq, Hb.
    + injection Heq as <- ->; injection Hb as <- <-.
      exists nil, x, T, (gm_open Φ c its); split; [ reflexivity |]; split; [ reflexivity | exact Hs ].
    + exists (v :: pre), y, T', Φ'; split; [ exact Heq |]; split; [ exact Hb | exact Hs ].
Qed.

(** Nothing is read past an alias. *)
Lemma gm_submodule_alias_app : forall Φ T x ip U,
    gm_submodule T Φ x ip = Some (mr_alias U) ->
    forall ch, ch <> nil ->
      gm_submodule T Φ x (ip ++ ch) = None /\ gm_subbody T Φ x (ip ++ ch) = None /\
      gm_resolve Φ (x :: ip ++ ch) = None.
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c] * H ch Hch; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ H ch Hch) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ H ch Hch) ].
  destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ H ch Hch).
  - destruct ip as [| w ip]; [| discriminate ]; destruct ch as [| v ch]; [ contradiction |]; cbn; repeat split; reflexivity.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ H ch Hch).
  - destruct ip as [| w ip]; [| discriminate ]; destruct ch as [| v ch]; [ contradiction |]; cbn; repeat split; reflexivity.
Qed.

Lemma gm_coh_body_tele : forall T Φ ip T' Φ',
    gm_coh T Φ -> gm_body T Φ ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hc H; destruct ip as [| x ip]; cbn in H.
  - injection H as <- <-; split; [ exact Hc | exists nil; split; [ reflexivity | constructor ] ].
  - exact (gm_coh_subbody _ _ _ _ _ _ Hc H).
Qed.

(** ** Frames Do Not Hide the Members of a Closed Module *)

Lemma gs_find_tele_head : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
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
Lemma gm_submodule_alias_unit : forall Φ T x ip U,
    gm_submodule T Φ x ip = Some (mr_alias U) -> exists Δ E, U = gu_mk Δ (md_alias E).
Proof.
  fix IH 1; intros [| Φ y E | Φ c its] * Hs; cbn in Hs; [ discriminate | | exact (IH _ _ _ _ _ Hs) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ Hs) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Δ pm p k Ns]; try discriminate;
    destruct ip; try discriminate; first [ exact (IH _ _ _ _ _ Hs) | injection Hs as <-; eauto ].
Qed.

Lemma gc_module_alias_unit : forall Θ Ξ p U,
    gc_module Θ Ξ p = Some (mr_alias U) -> exists Δ E, U = gu_mk Δ (md_alias E).
Proof.
  intros * H; unfold gc_module, gc_module_u in H.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |]; [ discriminate | eapply gm_submodule_alias_unit; exact H |].
  destruct (gds_lookup Θ (q_unit p)) as [V |]; [| discriminate ].
  unfold gm_module in H; destruct (q_chain p) as [| x ip]; [ discriminate | eapply gm_submodule_alias_unit; exact H ].
Qed.

Lemma gc_module_alias_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p U,
    gc_module Θ Ξ p = Some (mr_alias U) ->
    forall ch, ch <> nil ->
      gc_module Θ Ξ (qname_app p ch) = None /\ gc_body Θ Ξ (qname_app p ch) = None /\
      gc_resolve Θ Ξ (qname_app p ch) = None.
Proof.
  intros * Hg * H ch Hch.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_module, gc_module_u in H0.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_submodule_head _ _ _ _ _ H0) ch) as Ef'.
    destruct (gm_submodule_alias_app _ _ _ _ _ H0 ch Hch) as (H1 & H2 & H3).
    unfold gc_module, gc_module_u, gc_body, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn.
    repeat split; assumption.
  - destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    unfold gc_module, gc_module_u, gc_body, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn [option_map qname_app q_unit q_chain]; rewrite El.
    destruct (q_chain p) as [| x ip]; cbn in H0 |- *; [ discriminate |].
    destruct (gm_submodule_alias_app _ _ _ _ _ H0 ch Hch) as (H1 & H2 & H3).
    repeat split; assumption.
Qed.

(** ** A Name Is a Definition or a Module, Not Both *)

Lemma gm_resolve_def_not_module : forall Φ T z b pv A B ip,
    gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> gm_submodule T Φ z ip = None.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H; cbn in H |- *; [ reflexivity | | eauto ].
  destruct (String.eqb z y); [| eauto ].
  destruct E as [? ? ? ? | U | ? ? ? ? ? | ? Δa pma pa ka Nsa]; [ reflexivity | discriminate | discriminate | discriminate ].
Qed.

Lemma gm_submodule_alias_resolve : forall Φ T x ip U,
    gm_submodule T Φ x ip = Some (mr_alias U) -> gm_resolve Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ H) ].
  destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
    destruct ip as [| w ip]; try discriminate; first [ reflexivity | exact (IH _ _ _ _ _ H) ].
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
Lemma gc_prefix_not_alias : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p ch,
    ch <> nil ->
    (exists T oD, gc_module Θ Ξ (qname_app p ch) = Some (mr_body T oD)) \/
    (exists U, gc_module Θ Ξ (qname_app p ch) = Some (mr_alias U)) \/
    (exists E, gc_resolve Θ Ξ (qname_app p ch) = Some E) \/
    (exists D, ind_lookup Θ Ξ (qname_app p ch) = Some D) ->
    forall U, gc_module Θ Ξ p <> Some (mr_alias U).
Proof.
  intros * Hg * Hne Hx U Ha.
  destruct (gc_module_alias_app _ _ Hg _ _ Ha ch Hne) as (H1 & _ & H3).
  destruct Hx as [(T & oD & HT) | [(U' & HU) | [(E & HE) | (D & HD)]]]; try congruence.
  rewrite ind_lookup_unfold, ind_mlookup_unfold, H1 in HD; discriminate.
Qed.

(** A body module, or a module with a definition or an inductive type, has
    no alias among the prefixes of its path. *)
Lemma gc_chain_no_alias : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p,
    (exists T oD, gc_module Θ Ξ p = Some (mr_body T oD)) \/
    (exists x U, gc_module Θ Ξ (qname_app p (x :: nil)) = Some (mr_alias U)) \/
    (exists x E, gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some E) \/
    (exists x D, ind_lookup Θ Ξ (qname_app p (x :: nil)) = Some D) ->
    forall m1 m2, q_chain p = m1 ++ m2 -> m1 <> nil ->
    forall U, gc_module Θ Ξ (q_abs (q_unit p) m1) <> Some (mr_alias U).
Proof.
  intros * Hg [fp ms] Hx m1 m2 Hm Hne1 U; cbn [q_unit q_chain] in *; subst ms.
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

Lemma gc_module_alias_resolve : forall Θ Ξ p U,
    gc_module Θ Ξ p = Some (mr_alias U) -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H.
  unfold gc_module, gc_module_u, gc_resolve, gc_resolve_u in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; cbn; [ discriminate | exact (gm_submodule_alias_resolve _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [V |]; [| reflexivity ].
  destruct (q_chain p) as [| x ip]; cbn in H; [ discriminate | exact (gm_submodule_alias_resolve _ _ _ _ _ H) ].
Qed.

(** ** Open Frames *)

Lemma qname_strip_refl : forall m, qname_strip m m = Some nil.
Proof. intros; rewrite <- (qname_app_nil m) at 2; apply qname_strip_app. Qed.

Lemma qname_strip_length : forall m p ip, qname_strip m p = Some ip ->
    List.length (q_chain p) = List.length (q_chain m) + List.length ip.
Proof.
  intros * H; unfold qname_strip in H.
  destruct (path_beq (q_unit m) (q_unit p)); [| discriminate ].
  apply strip_prefix_spec in H; rewrite H, List.length_app; reflexivity.
Qed.

(** An open frame is found at its own path, over the telescope of the frames
    outside it; the frame outside it is found at its parent path, and the
    frame's own name is fresh there.  The outermost frame is a unit not filed. *)
Lemma gs_find_tele_frame : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp U T0, gs_find_tele Ξ mp = Some (U, nil, T0) ->
    (q_chain mp = nil /\ gds_lookup Θ (q_unit mp) = None /\ T0 = nil) \/
    (exists c y V T1, q_chain mp = c ++ y :: nil /\
       gs_find_tele Ξ (q_abs (q_unit mp) c) = Some (V, nil, T1) /\
       gm_fresh y (gu_mod V) /\ T0 = gu_params V ++ T1).
Proof.
  induction 1 as [| | Θ Ξ mf Δf Φf HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; [ discriminate | discriminate |].
  destruct (qname_strip mf mp) as [ip |] eqn:Hs.
  - injection Hf as HU Hip HT; subst ip U T0.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst mf.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hff |- *.
    + left; destruct Hff as [Hn Hc]; repeat split; assumption.
    + destruct Hff as (x & -> & Hx); right.
      exists (q_chain mq), x, V, (gs_tele Ξ'); split; [ reflexivity |].
      split; [| split; [ exact Hx | reflexivity ] ].
      cbn [gs_find_tele].
      change (q_unit (qname_in mq x)) with (q_unit mq).
      replace (q_abs (q_unit mq) (q_chain mq)) with mq by (destruct mq; reflexivity).
      change (q_abs (q_unit mq) (q_chain mq ++ x :: nil)) with (qname_in mq x).
      destruct (qname_strip (qname_in mq x) mq) as [r |] eqn:Hr'.
      * exfalso; apply qname_strip_length in Hr'; unfold qname_in in Hr'; cbn in Hr'; rewrite List.length_app in Hr'; cbn in Hr'; lia.
      * rewrite qname_strip_refl; reflexivity.
  - destruct (IH _ _ _ Hf) as [Hr | (c & y & V & T1 & Hc & HV & Hy & ->)]; [ left; exact Hr | right ].
    exists c, y, V, T1; split; [ exact Hc |]; split; [| split; [ exact Hy | reflexivity ] ].
    cbn [gs_find_tele]; destruct (qname_strip mf (q_abs (q_unit mp) c)) as [r |] eqn:Hr; [| exact HV ].
    exfalso.
    unfold qname_strip in Hr, Hs; cbn in Hr.
    destruct (path_beq (q_unit mf) (q_unit mp)); [| discriminate ].
    apply strip_prefix_spec in Hr.
    rewrite Hc, Hr, <- List.app_assoc, strip_prefix_app in Hs; discriminate.
Qed.

(** A closed module has no open frame inside it. *)
Lemma gc_module_child_not_frame : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall p r y, gc_module Θ Ξ p = Some r -> gc_frame Ξ (qname_in p y) = None.
Proof.
  intros * HΞ * Hm; unfold gc_frame.
  destruct (gs_find_tele Ξ (qname_in p y)) as [[[U [| x ip]] T0] |] eqn:Ef; try reflexivity;
    try (destruct U as [? [[|] ? | ?]]; reflexivity).
  exfalso.
  destruct (gs_find_tele_frame _ _ HΞ _ _ _ Ef) as [(Hc & _) | (c & y' & V & T1 & Hc & HV & _)];
    cbn in Hc; [ destruct (q_chain p); discriminate |].
  apply List.app_inj_tail in Hc as [<- <-].
  unfold gc_module, gc_module_u in Hm.
  change (q_unit (qname_in p y)) with (q_unit p) in HV.
  replace (q_abs (q_unit p) (q_chain p)) with p in HV by (destruct p; reflexivity).
  rewrite HV in Hm; discriminate.
Qed.

(** Below an open frame, a name it declares is read in it: no frame inside
    it is named so, a frame being named fresh where it is pushed. *)
Lemma gs_find_tele_frame_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp U T0, gs_find_tele Ξ mp = Some (U, nil, T0) ->
    forall y, List.In y (gm_names (gu_mod U)) ->
    forall ch, gs_find_tele Ξ (qname_app mp (y :: ch)) = Some (U, y :: ch, T0).
Proof.
  induction 1 as [| | Θ Ξ mf Δf Φf HΞ IH HΦ Hff]; intros * Hf y Hin ch; cbn in Hf |- *; [ discriminate | discriminate |].
  destruct (qname_strip mf mp) as [r |] eqn:Hs.
  - injection Hf as HU Hr HT; subst r U T0.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst mf.
    rewrite qname_strip_app; reflexivity.
  - pose proof (IH _ _ _ Hf _ Hin ch) as Hf'.
    destruct (qname_strip mf (qname_app mp (y :: ch))) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [mq W] Ξ'']; [ discriminate |].
    destruct Hff as (x1 & -> & Hfr).
    apply qname_strip_app_inv in Hs'.
    cbn in Hf'.
    rewrite Hs', qname_app_in, qname_strip_app in Hf'.
    injection Hf' as HW Hx1 _ _; subst W x1.
    exact (Hfr Hin).
Qed.

(** A name just below an open frame is a frame itself, or read in it. *)
Lemma gs_find_tele_child : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp U T0, gs_find_tele Ξ mp = Some (U, nil, T0) ->
    forall y, (exists V T1, gs_find_tele Ξ (qname_in mp y) = Some (V, nil, T1)) \/
              gs_find_tele Ξ (qname_in mp y) = Some (U, y :: nil, T0).
Proof.
  induction 1 as [| | Θ Ξ mf Δf Φf HΞ IH HΦ Hff]; intros * Hf y; cbn in Hf |- *; [ discriminate | discriminate |].
  destruct (qname_strip mf mp) as [ip |] eqn:Hs.
  - injection Hf as HU Hip HT; subst ip U T0.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst mf.
    right; replace (qname_in mp y) with (qname_app mp (y :: nil)) by (destruct mp; reflexivity).
    rewrite qname_strip_app; reflexivity.
  - destruct (qname_strip mf (qname_in mp y)) as [s |] eqn:Hs'.
    + left; destruct s as [| z s0 _] using rev_ind; [ eauto |].
      exfalso; apply qname_strip_app_inv in Hs'.
      assert (Hm : mp = qname_app mf s0).
      { destruct mp as [u c], mf as [u' c']; unfold qname_in, qname_app in Hs' |- *; cbn in Hs' |- *.
        injection Hs' as -> Hc; rewrite app_assoc in Hc; apply app_inj_tail in Hc as [-> _]; reflexivity. }
      rewrite Hm, qname_strip_app in Hs; discriminate.
    + exact (IH _ _ _ Hf y).
Qed.

(** The open frame at [p], and the closed module at [p]: where the body of a
    closed description is stored. *)
Definition loc (Θ : gdeps) (Ξ : gstack) (p : qname) (T : ctx) (Φ : gmod) : Prop :=
  gc_frame Ξ p = Some (T, Φ) \/ gc_body Θ Ξ p = Some (T, Φ).

(** Reading below an open frame. *)
Lemma gc_frame_below : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp T Φ, gc_frame Ξ mp = Some (T, Φ) ->
    forall y, List.In y (gm_names Φ) ->
    forall ch, gc_entry Θ Ξ (qname_app mp (y :: ch)) = gm_entry Φ (y :: ch) /\
      gc_resolve Θ Ξ (qname_app mp (y :: ch)) = gm_resolve Φ (y :: ch) /\
      gc_module Θ Ξ (qname_app mp (y :: ch)) = gm_submodule T Φ y ch /\
      gc_body Θ Ξ (qname_app mp (y :: ch)) = gm_subbody T Φ y ch /\
      ind_alias_lookup Θ Ξ (qname_app mp (y :: ch)) = gm_ind_target Φ (y :: ch).
Proof.
  intros * Hg * Hfr y Hin ch; unfold gc_frame in Hfr.
  destruct (gs_find_tele Ξ mp) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
  injection Hfr as <- <-.
  pose proof (gs_find_tele_frame_app _ _ Hg _ _ _ Ef y Hin ch) as Ef'.
  unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u, gc_module, gc_module_u, gc_body,
    ind_alias_lookup, ind_alias_lookup_u; rewrite !gs_find_tele_find, Ef'; cbn.
  repeat split; reflexivity.
Qed.

Lemma gm_subbody_entry_app : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y ch, gm_entry Φ (x :: ip ++ y :: ch) = gm_entry Φ' (y :: ch).
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y ch; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y ch) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y ch) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; reflexivity | specialize (IH _ _ _ _ _ _ H y ch); cbn in IH; exact IH ]).
Qed.

Lemma ind_alias_lookup_entry : forall Θ Ξ p,
    ind_alias_lookup Θ Ξ p = match gc_entry Θ Ξ p with Some E => ge_ind_target E | None => None end.
Proof.
  intros; unfold ind_alias_lookup, ind_alias_lookup_u, gc_entry, gc_entry_u, gm_ind_target.
  destruct (gs_find Ξ p) as [[U ip] |]; [ reflexivity |].
  destruct (gds_lookup Θ (q_unit p)); reflexivity.
Qed.

(** What is stored below a closed module is what its body says. *)
Theorem closed_read_entry : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    forall y ch, gc_entry Θ Ξ (qname_app p (y :: ch)) = gm_entry Φ (y :: ch) /\
      ind_alias_lookup Θ Ξ (qname_app p (y :: ch)) = gm_ind_target Φ (y :: ch).
Proof.
  intros * Hg * H y ch.
  pose proof H as H0; unfold gc_body in H0.
  enough (Hen : gc_entry Θ Ξ (qname_app p (y :: ch)) = gm_entry Φ (y :: ch)).
  { split; [ exact Hen |]; rewrite ind_alias_lookup_entry, Hen; reflexivity. }
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hg _ _ _ _ _ Ef (gm_subbody_head _ _ _ _ _ H0) (y :: ch)) as Ef'.
    unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find, Ef'; cbn.
    exact (gm_subbody_entry_app _ _ _ _ _ _ H0 y ch).
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hg _ _ El (y :: ch)) as Ef'.
    unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find, Ef'; cbn [option_map qname_app q_unit q_chain]; rewrite El.
    destruct (q_chain p) as [| x ip]; cbn in H0 |- *; [ injection H0 as <- <-; reflexivity |].
    exact (gm_subbody_entry_app _ _ _ _ _ _ H0 y ch).
Qed.

Corollary wf_gstack_closed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> gctx_closed Θ Ξ.
Proof. intros * Hg; destruct wf_scoped as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H); exact (H _ _ Hg). Qed.

(** What is stored below where a body is stored is what the body says. *)
Lemma loc_read : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ ->
    forall y, List.In y (gm_names Φ) ->
    forall ch, gc_entry Θ Ξ (qname_app p (y :: ch)) = gm_entry Φ (y :: ch) /\
      gc_resolve Θ Ξ (qname_app p (y :: ch)) = gm_resolve Φ (y :: ch) /\
      gc_module Θ Ξ (qname_app p (y :: ch)) = gm_submodule T Φ y ch /\
      gc_body Θ Ξ (qname_app p (y :: ch)) = gm_subbody T Φ y ch /\
      ind_alias_lookup Θ Ξ (qname_app p (y :: ch)) = gm_ind_target Φ (y :: ch).
Proof.
  intros * Hg * [Hl | Hl] y Hin ch; [ exact (gc_frame_below _ _ Hg _ _ _ Hl _ Hin ch) |].
  destruct (gc_body_module _ _ _ _ _ Hl) as [oD Hm].
  destruct (closed_read _ _ Hg _ _ _ _ Hl Hm (y :: ch)) as (H1 & H2 & H3).
  destruct (closed_read_entry _ _ Hg _ _ _ Hl y ch) as [H4 H5].
  repeat split; [ exact H4 | exact (H3 ltac:(discriminate)) | exact H1 | exact H2 | exact H5 ].
Qed.

(** An open frame names nothing it does not declare. *)
Lemma gc_entry_frame_name : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp T Φ, gc_frame Ξ mp = Some (T, Φ) ->
    forall y E, gc_entry Θ Ξ (qname_in mp y) = Some E -> List.In y (gm_names Φ).
Proof.
  induction 1 as [| | Θ Ξ mf Δf Φf HΞ IH HΦ Hff]; intros * Hfr y E He; unfold gc_frame in Hfr; cbn in Hfr; try discriminate.
  unfold gc_entry, gc_entry_u in He; cbn in He.
  destruct (qname_strip mf mp) as [r |] eqn:Hs.
  - destruct r as [| z r]; [| discriminate ]; injection Hfr as <- <-.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst mf.
    rewrite <- (qname_app_nil (qname_in mp y)), qname_app_in, qname_strip_app in He.
    destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin); exact Hin.
  - destruct (qname_strip mf (qname_in mp y)) as [r |] eqn:Hs'.
    + exfalso.
      destruct r as [| w r] using rev_ind; [ rewrite gm_entry_nil in He; discriminate |].
      unfold qname_strip in Hs, Hs'; cbn in Hs'.
      destruct (path_beq (q_unit mf) (q_unit mp)) eqn:Hb; [| discriminate ].
      apply strip_prefix_spec in Hs'.
      rewrite List.app_assoc in Hs'; apply List.app_inj_tail in Hs' as [Hs' _].
      rewrite Hs', strip_prefix_app in Hs; discriminate.
    + exact (IH _ _ _ Hfr _ _ He).
Qed.

Lemma qname_in_app : forall p y, qname_in p y = qname_app p (y :: nil).
Proof. intros; rewrite <- (qname_app_nil (qname_in p y)), qname_app_in; reflexivity. Qed.

(** ** Entries of Stored Bodies *)

(** A body with no local open: every stored body is one. *)
Fixpoint gm_noopen (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' _ _ => gm_noopen Φ'
  | gm_open _ _ _ => False
  end.

Lemma body_closed_noopen : forall Φ k, body_closed k Φ -> gm_noopen Φ.
Proof. induction Φ as [| Φ IH x E | Φ IH H its]; intros k HΦ; cbn in *; [ exact I | exact (IH _ (proj1 HΦ)) | exact HΦ ]. Qed.

Lemma gm_prefix_entry : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 ->
    exists Φ0 E, Φ1 = gm_ext Φ0 y E /\ gm_entry Φ (y :: nil) = Some E.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * Hp; cbn in Hp |- *; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as <-; eauto |]; eauto.
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

Lemma gm_entry_prefix : forall Φ y E, gm_noopen Φ -> gm_entry Φ (y :: nil) = Some E ->
    exists Φ0, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E).
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hn He; cbn in Hn, He |- *; [ discriminate | | contradiction ].
  destruct (String.eqb_spec y x) as [-> |]; [ injection He as <-; eauto | eauto ].
Qed.

Lemma gm_prefix_upto_fresh : forall Φ y, gm_fresh y Φ -> gm_prefix_upto Φ y = None.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * Hf; unfold gm_fresh in Hf; cbn in Hf |- *; [ reflexivity | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ exfalso; apply Hf; left; reflexivity |].
    apply IH; intros Hin; apply Hf; right; exact Hin.
  - destruct (existsb _ _); [ reflexivity |].
    apply IH; intros Hin; apply Hf; apply List.in_or_app; right; exact Hin.
Qed.

(** Frames hold body units. *)
Lemma gs_find_tele_body : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p U ip T,
    gs_find_tele Ξ p = Some (U, ip, T) -> exists Δ Φ, U = gu_body Δ Φ.
Proof.
  induction 1 as [| | Θ Ξ mf Δf Φf HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; try discriminate.
  destruct (qname_strip mf p); [ injection Hf as <- _ _; eauto | eauto ].
Qed.

(** A stored body is closed. *)
Lemma loc_closed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ -> unit_closed T Φ.
Proof.
  intros * Hg * [Hl | Hl]; pose proof (wf_gstack_closed _ _ Hg) as Hc.
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hl as <- <-.
    exact (stack_closed_find _ _ _ _ _ (proj2 Hc) Ef).
  - exact (gctx_closed_body _ _ _ _ _ Hc Hl).
Qed.

(** The entries of a stored body are what is stored below where it is. *)
Lemma loc_entry : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ ->
    forall y E, gc_entry Θ Ξ (qname_in p y) = Some E <-> gm_entry Φ (y :: nil) = Some E.
Proof.
  intros * Hg * Hl y E; rewrite qname_in_app; split; intros He.
  - assert (Hin : List.In y (gm_names Φ)).
    { destruct Hl as [Hl | Hl].
      - rewrite <- qname_in_app in He; exact (gc_entry_frame_name _ _ Hg _ _ _ Hl _ _ He).
      - rewrite (proj1 (closed_read_entry _ _ Hg _ _ _ Hl y nil)) in He.
        destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin); exact Hin. }
    rewrite (proj1 (loc_read _ _ Hg _ _ _ Hl _ Hin nil)) in He; exact He.
  - destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin).
    rewrite (proj1 (loc_read _ _ Hg _ _ _ Hl _ Hin nil)); exact He.
Qed.

Lemma gm_entry_subbody_mod : forall Φ T y pv Δ sm Φ',
    gm_entry Φ (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) ->
    gm_subbody T Φ y nil = Some (Δ ++ T, Φ') /\ gm_submodule T Φ y nil = Some (mr_body (Δ ++ T) None).
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * He; cbn in He |- *; [ discriminate | | eauto ].
  destruct (String.eqb y x); [ injection He as ->; split; reflexivity | eauto ].
Qed.

Lemma gm_entry_subbody_ind : forall Φ T y pv pq k D Φ',
    gm_entry Φ (y :: nil) = Some (ge_ind pv pq k D Φ') ->
    gm_subbody T Φ y nil = Some (ind_uparams D, Φ') /\
    gm_submodule T Φ y nil = Some (mr_body (ind_uparams D) (Some (pq, k, D))).
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * He; cbn in He |- *; [ discriminate | | eauto ].
  destruct (String.eqb y x); [ injection He as ->; split; reflexivity | eauto ].
Qed.

(** A body module stored in a stored body is stored below it, over the
    longer telescope. *)
Lemma loc_child_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ ->
    forall y pv Δ sm Φ', gm_entry Φ (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) ->
    gc_body Θ Ξ (qname_in p y) = Some (Δ ++ T, Φ') /\ gc_module Θ Ξ (qname_in p y) = Some (mr_body (Δ ++ T) None).
Proof.
  intros * Hg * Hl * He.
  destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin).
  destruct (loc_read _ _ Hg _ _ _ Hl _ Hin nil) as (_ & _ & Hm & Hb & _).
  destruct (gm_entry_subbody_mod _ T _ _ _ _ _ He) as [Hb' Hm'].
  rewrite qname_in_app, Hb, Hm; split; assumption.
Qed.

(** The unit a module expression names directly. *)
Lemma gc_unit_cases : forall Θ Ξ H T Φ, gc_unit Θ Ξ H = Some (T, Φ) ->
    exists mp, mod_qname H = Some mp /\
      (gc_frame Ξ mp = Some (T, Φ) \/
       (gs_find_tele Ξ mp = None /\ q_chain mp = nil /\ gc_body Θ Ξ mp = Some (T, Φ) /\
        gc_module Θ Ξ mp = Some (mr_body T None))).
Proof.
  intros * Hu; unfold gc_unit in Hu.
  destruct (mod_qname H) as [mp |] eqn:Hq; [| discriminate ]; exists mp; split; [ reflexivity |].
  destruct (gs_find_tele Ξ mp) as [[[U [| ? ?]] T0] |] eqn:Hf.
  - left; unfold gc_frame; rewrite Hf; exact Hu.
  - discriminate.
  - right; destruct (q_chain mp) as [| ? ?] eqn:Hc; [| discriminate ].
    destruct (gds_lookup Θ (q_unit mp)) as [U |] eqn:Hl; [| discriminate ].
    destruct U as [Δ [[|] Φ0 | E]]; try discriminate; injection Hu as <- <-.
    unfold gc_body, gc_module, gc_module_u; rewrite Hf, Hl, Hc; cbn; repeat split; reflexivity.
Qed.

Corollary gc_unit_loc : forall Θ Ξ H T Φ, gc_unit Θ Ξ H = Some (T, Φ) -> exists mp, mod_qname H = Some mp /\ loc Θ Ξ mp T Φ.
Proof.
  intros * Hu; destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hl | (_ & _ & Hl & _)]); exists mp; split; auto;
    [ left | right ]; exact Hl.
Qed.

(** ** What a Module Expression Denotes Is Unique *)

(** An open frame inside another is named fresh in it. *)
Lemma gc_unit_mem_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H0 y T Φ,
    gc_unit Θ Ξ (me_mem H0 y) = Some (T, Φ) ->
    exists T' Φ', gc_unit Θ Ξ H0 = Some (T', Φ') /\ gm_fresh y Φ'.
Proof.
  intros * Hg * Hu.
  destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hl | (_ & Hc & _)]); cbn in Hq;
    destruct (mod_qname H0) as [mq |] eqn:Hq0; try discriminate; injection Hq as <-; cbn in *.
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |}) as [[[U [| ? ?]] T0] |] eqn:Ef;
      try (destruct U as [? [[|] ? | ?]]); try discriminate.
    destruct (gs_find_tele_frame _ _ Hg _ _ _ Ef) as [(Hc & _) | (c & y' & V & T1 & Hc & HV & Hy & _)];
      cbn in Hc; [ destruct (q_chain mq); discriminate |].
    apply List.app_inj_tail in Hc as [<- <-].
    destruct (gs_find_tele_body _ _ Hg _ _ _ _ HV) as (Δv & Φv & ->).
    exists (Δv ++ T1), Φv; split; [| exact Hy ].
    unfold gc_unit; rewrite Hq0; cbn [q_unit] in HV; replace (q_abs (q_unit mq) (q_chain mq)) with mq in HV by (destruct mq; reflexivity).
    rewrite HV; reflexivity.
  - destruct (q_chain mq); discriminate.
Qed.

Lemma unit_denote_unique : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H Γ R p T Φ,
    mod_qname H = Some p -> gc_unit Θ Ξ H = Some (T, Φ) -> mdenote Θ Ξ Γ H R -> R = ds_closed nil p T Φ nil.
Proof.
  intros Θ Ξ Hg; induction H as [fp | x | H0 IH y | H0 IH N | U]; intros * Hq Hu Hm; inversion Hm; subst;
    try (match goal with Hu' : gc_unit _ _ _ = Some _, Hq' : mod_qname _ = Some _ |- _ =>
           rewrite Hu in Hu'; rewrite Hq in Hq'; injection Hu' as <- <-; injection Hq' as <-; reflexivity end);
    try (unfold gc_unit in Hu; cbn in Hu; discriminate).
  destruct (gc_unit_mem_parent _ _ Hg _ _ _ _ Hu) as (T' & Φ' & Hu0 & Hf).
  cbn in Hq; destruct (mod_qname H0) as [p0 |] eqn:Hq0; [| discriminate ].
  match goal with H1 : mdenote _ _ _ H0 _ |- _ => rewrite (IH _ _ _ _ _ eq_refl Hu0 H1) in * end.
  match goal with Hmd : ds_mod _ _ _ = Some _, He : ds_entry _ _ = Some _ |- _ =>
    cbn in Hmd; injection Hmd as <-; cbn in He; rewrite (gm_prefix_upto_fresh _ _ Hf) in He; discriminate end.
Qed.

Theorem mdenote_functional_all : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> forall R', mdenote Θ Ξ Γ H R' -> R = R') /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> forall R', udenote Θ Ξ Γ o U R' -> R = R') /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> forall R', edenote Θ Ξ Γ o E R' -> R = R') /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall Φx', body_xp Θ Ξ Γ Φ Φx' -> Φx = Φx') /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> forall gs', items_gen Θ Ξ g Γ H its gs' -> gs = gs').
Proof.
  intros Θ Ξ Hg; apply mdenote_all_ind.
  - intros * Hq Hu R' Hm'; symmetry; exact (unit_denote_unique _ _ Hg _ _ _ _ _ _ Hq Hu Hm').
  - intros * Hl Hu IH R' Hm'; inversion Hm'; subst.
    + match goal with Hu' : gc_unit _ _ _ = Some _ |- _ => unfold gc_unit in Hu'; discriminate end.
    + match goal with Hl' : _ ∋ # _ ≔ₘ _ |- _ => rewrite (ctx_lookup_mod_functional _ _ _ _ Hl Hl') in IH end; eauto.
  - intros * Hu IH R' Hm'; inversion Hm'; subst; [ match goal with Hu' : gc_unit _ _ _ = Some _ |- _ => unfold gc_unit in Hu'; discriminate end | eauto ].
  - intros * Hm IH Ha R' Hm'; inversion Hm'; subst;
      [ match goal with Hu' : gc_unit _ _ _ = Some _ |- _ => unfold gc_unit in Hu'; discriminate end |].
    match goal with H1 : mdenote _ _ _ H _ |- _ => rewrite <- (IH _ H1) in * end; congruence.
  - intros * Hm IH Hmd He Hed IHe Hr R' Hm'; inversion Hm'; subst.
    + match goal with Hu' : gc_unit _ _ _ = Some _, Hq' : mod_qname _ = Some _ |- _ =>
        exact (unit_denote_unique _ _ Hg _ _ _ _ _ _ Hq' Hu' ltac:(eapply dn_mem; eassumption)) end.
    + match goal with H1 : mdenote _ _ _ H _ |- _ => rewrite <- (IH _ H1) in * end.
      match goal with H1 : ds_mod _ _ R0 = _ |- _ => rewrite Hmd in H1; injection H1 as <- end.
      match goal with H1 : ds_entry R0m y = _ |- _ => rewrite He in H1; injection H1 as <- <- <- end.
      match goal with H1 : edenote _ _ _ _ _ _ |- _ => rewrite <- (IHe _ H1) in * end.
      congruence.
  - intros * Hx IH Hb R' Hu'; inversion Hu'; subst.
    match goal with H1 : body_xp _ _ _ _ _ |- _ => rewrite <- (IH _ H1) in * end; congruence.
  - intros * Hm IH Hmd R' Hu'; inversion Hu'; subst.
    match goal with H1 : mdenote _ _ _ _ _ |- _ => rewrite <- (IH _ H1) in * end; congruence.
  - intros * He; inversion He; reflexivity.
  - intros * Hu IH R' He; inversion He; subst; eauto.
  - intros * He; inversion He; reflexivity.
  - intros * He; inversion He; reflexivity.
  - intros * Hx; inversion Hx; reflexivity.
  - intros * Hx IH Φx' Hx'; inversion Hx'; subst; f_equal; eauto.
  - intros * Hx IH Hm IHm Hmd Hgn IHg Hok Φx' Hx'; inversion Hx'; subst.
    match goal with H1 : body_xp _ _ _ Φ _ |- _ => pose proof (IH _ H1) as E; subst end.
    match goal with H1 : items_gen _ _ _ _ _ _ _ |- _ => rewrite (IHg _ H1) end; reflexivity.
  - intros * Hg'; inversion Hg'; reflexivity.
  - intros * Hgn IH gs' Hg'; inversion Hg'; subst; f_equal; eauto.
  - intros * Hm IHm Hgn IH gs' Hg'; inversion Hg'; subst;
      match goal with H1 : mdenote _ _ _ (me_mem _ _) _ |- _ => pose proof (IHm _ H1) as E end;
      try discriminate E; try (subst; contradiction).
    injection E as <- <-; f_equal; eauto.
  - intros * Hm IHm Hk Hgn IH gs' Hg'; inversion Hg'; subst;
      match goal with H1 : mdenote _ _ _ (me_mem _ _) _ |- _ => pose proof (IHm _ H1) as E end; subst;
      try (cbn in Hk; contradiction).
    f_equal; eauto.
  - intros * Hm IHm Hl Hmp Hml Hgn IH gs' Hg'; inversion Hg'; subst;
      match goal with H1 : mdenote _ _ _ (me_mem _ _) _ |- _ => pose proof (IHm _ H1) as E end;
      try discriminate E; try (subst; cbn in *; contradiction).
    injection E as <- <- <- <-.
    match goal with H1 : ind_lookup _ _ _ = Some _ |- _ => rewrite Hl in H1; injection H1 as <- end.
    match goal with H1 : ind_mpath _ _ = Some _ |- _ => rewrite Hmp in H1; injection H1 as <- end.
    f_equal; eauto.
Qed.

(** ** Bodies Stored at Paths Are What Paths Denote *)

(** Where a body module is stored: an open frame, or a closed module that is
    not the module of an inductive type. *)
Definition loc_mod (Θ : gdeps) (Ξ : gstack) (p : qname) (T : ctx) (Φ : gmod) : Prop :=
  gc_frame Ξ p = Some (T, Φ) \/ (gc_body Θ Ξ p = Some (T, Φ) /\ gc_module Θ Ξ p = Some (mr_body T None)).

Lemma loc_mod_loc : forall Θ Ξ p T Φ, loc_mod Θ Ξ p T Φ -> loc Θ Ξ p T Φ.
Proof. intros * [H | [H _]]; [ left | right ]; exact H. Qed.

(** The frame a lookup reads in is found at its own path. *)
Lemma gs_find_tele_found : forall Ξ p U ip T, gs_find_tele Ξ p = Some (U, ip, T) ->
    exists F, qname_strip F p = Some ip /\ gs_find_tele Ξ F = Some (U, nil, T).
Proof.
  induction Ξ as [| [mf V] Ξ IH]; intros * Hf; cbn in Hf |- *; [ discriminate |].
  destruct (qname_strip mf p) as [r |] eqn:Hs.
  - injection Hf as <- <- <-; exists mf; split; [ exact Hs | rewrite qname_strip_refl; reflexivity ].
  - destruct (IH _ _ _ _ Hf) as (F & HF & HFf); exists F; split; [ exact HF |].
    destruct (qname_strip mf F) as [r |] eqn:Hr; [| exact HFf ].
    exfalso; apply qname_strip_app_inv in Hr, HF; subst; rewrite qname_app_app, qname_strip_app in Hs; discriminate.
Qed.

Lemma gm_subbody_entry_inv : forall Φ T x T' Φ',
    gm_subbody T Φ x nil = Some (T', Φ') -> gm_submodule T Φ x nil = Some (mr_body T' None) ->
    exists pv Δ sm, gm_entry Φ (x :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) /\ T' = Δ ++ T.
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hb Hm; cbn in Hb, Hm |- *; [ discriminate | | eauto ].
  destruct (String.eqb x z); [| eauto ].
  destruct E as [? ? ? ? | pv [Δ [sm Φ0 | E0]] | ? ? D Φ0 | ? Δa pa Nsa]; try discriminate.
  injection Hb as <- <-; eauto.
Qed.

Lemma gm_coh_ind_defs : forall Φ T x ip T' D Φ',
    gm_coh T Φ -> gm_submodule T Φ x ip = Some (mr_body T' (Some D)) -> gm_subbody T Φ x ip = Some (T', Φ') ->
    gm_defs Φ'.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * Hc Hm Hb; cbn in Hc, Hm, Hb; [ discriminate | | exact (IH _ _ _ _ _ _ _ Hc Hm Hb) ].
  destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Δa pma pa ka Nsa];
    destruct (String.eqb x y); try discriminate;
    try (eapply IH; [ first [ exact (proj1 Hc) | exact Hc ] | exact Hm | exact Hb ]).
  - destruct ip as [| w ip]; [ discriminate |]; destruct Hc as (_ & _ & Hc); exact (IH _ _ _ _ _ _ _ Hc Hm Hb).
  - destruct Hc as (_ & _ & Hc & Hd); destruct ip as [| w ip]; [ injection Hb as <- <-; exact Hd |].
    exact (IH _ _ _ _ _ _ _ Hc Hm Hb).
Qed.

Lemma body_closed_entry_mod : forall Φ k y pv Δ sm Φ',
    body_closed k Φ -> gm_entry Φ (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) -> sm = sm_closed.
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc He; cbn in Hc, He; [ discriminate | | contradiction ].
  destruct Hc as [Hc HE]; destruct (String.eqb y z); [ injection He as ->; exact (proj1 HE) | eauto ].
Qed.

(** The parent of a body module that is no module of an inductive type is a
    stored module body, which has it as a body entry. *)
(** A module below a path is read in the body at the path. *)
Lemma parent_loc_any : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y T Φ oDy,
    gc_body Θ Ξ (qname_in mq y) = Some (T, Φ) -> gc_module Θ Ξ (qname_in mq y) = Some (mr_body T oDy) ->
    exists Tq Φq, loc_mod Θ Ξ mq Tq Φq /\ gm_subbody Tq Φq y nil = Some (T, Φ) /\ gm_submodule Tq Φq y nil = Some (mr_body T oDy).
Proof.
  intros * Hg * Hb Hm.
  assert (Hent : forall Tq Φq, loc_mod Θ Ξ mq Tq Φq -> gm_subbody Tq Φq y nil = Some (T, Φ) ->
                   gm_submodule Tq Φq y nil = Some (mr_body T oDy) ->
                   exists (_ _ : unit), loc_mod Θ Ξ mq Tq Φq /\ gm_subbody Tq Φq y nil = Some (T, Φ) /\
                     gm_submodule Tq Φq y nil = Some (mr_body T oDy))
    by (intros; exists tt, tt; auto).
  unfold gc_body in Hb; unfold gc_module, gc_module_u in Hm.
  destruct (gs_find_tele Ξ (qname_in mq y)) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - destruct (gs_find_tele_body _ _ Hg _ _ _ _ Ef) as (ΔU & ΦU & ->); cbn [gu_params gu_mod] in *.
    destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & HFf).
    apply qname_strip_app_inv in HF.
    destruct ip as [| w ip] using rev_ind.
    + (* the parent is the frame *)
      assert (mq = F) as ->.
      { rewrite qname_in_app in HF; destruct mq as [fq cq], F as [ff cf]; unfold qname_app in HF; cbn in HF.
        injection HF as -> Hc; apply List.app_inj_tail in Hc as [-> _]; reflexivity. }
      rewrite qname_in_app in HF; unfold qname_app in HF; destruct F as [ff cf]; cbn in HF.
      injection HF as Hc; apply List.app_inj_tail in Hc as [_ <-].
      destruct (Hent (ΔU ++ T0) ΦU) as (pv & Δ & Hl & He & HT);
        [ left; unfold gc_frame; rewrite HFf; reflexivity | exact Hb | exact Hm |].
      exists (ΔU ++ T0), ΦU; auto.
    + (* the parent is a body module of the frame *)
      assert (Hy : w = y /\ mq = qname_app F (x :: ip)).
      { rewrite qname_in_app in HF; destruct mq as [fq cq], F as [ff cf]; unfold qname_app in HF |- *; cbn in HF |- *.
        injection HF as -> Hc; rewrite List.app_comm_cons, List.app_assoc in Hc.
        apply List.app_inj_tail in Hc as [-> ->]; split; reflexivity. }
      destruct Hy as [-> ->].
      destruct (gm_body_snoc_inv (x :: ip) _ _ _ _ _ Hb) as (Tq & Φq & Hbq & Hby); cbn [gm_body] in Hbq.
      destruct (gm_subbody_snoc _ _ _ _ _ _ Hbq y) as [Hmy _]; rewrite Hmy in Hm.
      destruct (gs_find_tele_head _ _ Hg _ _ _ _ _ Ef (gm_subbody_head _ _ _ _ _ Hb)) as (Fp & HFp & HFall).
      assert (HEq : qname_app F (x :: ip ++ y :: nil) = qname_app Fp (x :: ip ++ y :: nil)).
      { rewrite <- HFp, qname_in_app, qname_app_app; reflexivity. }
      assert (Fp = F) as ->.
      { destruct F as [ff cf], Fp as [fp' cp']; unfold qname_app in HEq; cbn in HEq; injection HEq as -> Hc.
        apply List.app_inv_tail in Hc as ->; reflexivity. }
      pose proof (HFall ip) as Efq.
      destruct (gm_subbody_module _ _ _ _ _ _ Hbq) as [oD HmD].
      destruct oD as [D |].
      * exfalso.
        pose proof (gm_coh_ind_defs _ _ _ _ _ _ _ (wf_gstack_coh _ _ Hg _ _ _ _ HFf) HmD Hbq) as Hd.
        rewrite (gm_defs_submodule _ _ _ _ Hd) in Hm; discriminate.
      * destruct (Hent Tq Φq) as (pv & Δ & Hl & He & HT); [| exact Hby | exact Hm |].
        { right; unfold gc_body, gc_module, gc_module_u; rewrite Efq; cbn; split; assumption. }
        exists Tq, Φq; auto.
  - (* a filed unit *)
    destruct (gds_lookup Θ (q_unit (qname_in mq y))) as [Uf |] eqn:El; [| discriminate ].
    cbn [q_unit qname_in q_chain] in El, Hb, Hm.
    destruct (gm_body_snoc_inv (q_chain mq) _ _ _ _ _ Hb) as (Tq & Φq & Hbq & Hby).
    destruct (gm_body_snoc _ _ _ _ _ Hbq y None) as (Hmy & _); unfold gm_module in Hmy, Hm.
    destruct (q_chain mq) as [| x ip] eqn:Hc; cbn [app] in *.
    + injection Hbq as <- <-.
      destruct (Hent (gu_params Uf) (gu_mod Uf)) as (pv & Δ & Hl & He & HT); [| exact Hby | exact Hm |].
      { right; pose proof (gs_find_tele_filed _ _ Hg {| q_unit := q_unit mq; q_chain := nil |} _ El nil) as Ef0.
        rewrite qname_app_nil in Ef0.
        replace mq with {| q_unit := q_unit mq; q_chain := nil |} by (destruct mq; cbn in *; subst; reflexivity).
        unfold gc_body, gc_module, gc_module_u; rewrite Ef0; cbn; rewrite El; split; reflexivity. }
      exists (gu_params Uf), (gu_mod Uf); auto.
    + rewrite Hmy in Hm.
      pose proof (gs_find_tele_filed _ _ Hg {| q_unit := q_unit mq; q_chain := nil |} _ El (x :: ip)) as Ef0.
      assert (Hmq : mq = qname_app {| q_unit := q_unit mq; q_chain := nil |} (x :: ip)) by (destruct mq; cbn in *; subst; reflexivity).
      rewrite <- Hmq in Ef0.
      destruct (gm_subbody_module _ _ _ _ _ _ Hbq) as [oD HmD].
      destruct oD as [D |].
      * exfalso.
        pose proof (gm_coh_ind_defs _ _ _ _ _ _ _ (wf_gdeps_coh _ _ Hg _ _ El) HmD Hbq) as Hd.
        rewrite (gm_defs_submodule _ _ _ _ Hd) in Hm; discriminate.
      * destruct (Hent Tq Φq) as (pv & Δ & Hl & He & HT); [| exact Hby | exact Hm |].
        { right; unfold gc_body, gc_module, gc_module_u; rewrite Ef0; cbn; rewrite El, Hc; cbn; split; assumption. }
        exists Tq, Φq; auto.
Qed.

Lemma parent_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y T Φ,
    gc_body Θ Ξ (qname_in mq y) = Some (T, Φ) -> gc_module Θ Ξ (qname_in mq y) = Some (mr_body T None) ->
    exists Tq Φq pv Δ, loc_mod Θ Ξ mq Tq Φq /\
      gm_entry Φq (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm_closed Φ))) /\ T = Δ ++ Tq.
Proof.
  intros * Hg * Hb Hm.
  destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hm) as (Tq & Φq & Hl & Hb' & Hm').
  destruct (gm_subbody_entry_inv _ _ _ _ _ Hb' Hm') as (pv & Δ & sm & He & ->).
  pose proof (proj2 (loc_closed _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hl))) as Hc.
  rewrite (body_closed_entry_mod _ _ _ _ _ _ _ Hc He) in He; eauto 7.
Qed.

(** Filed units are body units. *)
Lemma wf_gds_body : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall fp U, gds_lookup Θ fp = Some U -> exists Δ Φ, U = gu_body Δ Φ.
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Δ Φ HΞ IH HΦ Hff]; intros fp U Hl; cbn in Hl; [ discriminate | | eauto ].
  destruct (path_beq fp fq); [ injection Hl as <- | eauto ].
  exact (gs_find_tele_body _ _ Hg (q_abs fq nil) V nil nil ltac:(cbn; rewrite qname_strip_refl; reflexivity)).
Qed.

Lemma body_xp_noopen : forall Θ Ξ Γ Φ, gm_noopen Φ -> body_xp Θ Ξ Γ Φ Φ.
Proof. induction Φ as [| Φ IH x E | Φ IH H its]; intros Hn; cbn in Hn; [ constructor | constructor; auto | contradiction ]. Qed.

Lemma body_closed_entry_noopen : forall Φ k y pv Δ sm Φ',
    body_closed k Φ -> gm_entry Φ (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) -> gm_noopen Φ'.
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc He; cbn in Hc, He; [ discriminate | | contradiction ].
  destruct Hc as [Hc HE]; destruct (String.eqb y z); [ injection He as ->; exact (body_closed_noopen _ _ (proj2 (proj2 HE))) | eauto ].
Qed.

(** A chain of selections from a unit naming where a body module is stored
    denotes that body, with no argument. *)
Theorem mdenote_of_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H mp T Φ Γ,
    mod_qname H = Some mp -> loc_mod Θ Ξ mp T Φ -> mdenote Θ Ξ Γ H (ds_closed nil mp T Φ nil).
Proof.
  intros Θ Ξ Hg; induction H as [fp | x | H0 IH y | H0 IH N | U]; intros * Hq Hl; cbn in Hq; try discriminate.
  - injection Hq as <-; apply dn_unit; [ reflexivity |]; unfold gc_unit; cbn [mod_qname].
    destruct Hl as [Hl | [Hb Hm]]; [ unfold gc_frame in Hl; destruct (gs_find_tele Ξ (q_abs fp nil)) as [[[U [| ? ?]] T0] |];
      try (destruct U as [? [[|] ? | ?]]); try discriminate; exact Hl |].
    unfold gc_body in Hb; destruct (gs_find_tele Ξ (q_abs fp nil)) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
    + exfalso; destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & _).
      apply qname_strip_length in HF; cbn in HF; lia.
    + cbn in Hb |- *; destruct (gds_lookup Θ fp) as [Uf |] eqn:El; [| discriminate ].
      destruct (wf_gds_body _ _ Hg _ _ El) as (Δ & Φ0 & ->); cbn in Hb; injection Hb as <- <-; reflexivity.
  - destruct (mod_qname H0) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
    change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y) in Hl.
    destruct Hl as [Hl | [Hb Hm]].
    + apply dn_unit; [ cbn; rewrite Hq0; reflexivity |]; unfold gc_unit; cbn [mod_qname]; rewrite Hq0.
      unfold gc_frame in Hl; change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y).
      destruct (gs_find_tele Ξ (qname_in mq y)) as [[[U [| ? ?]] T0] |];
        try (destruct U as [? [[|] ? | ?]]); try discriminate; exact Hl.
    + destruct (parent_loc _ _ Hg _ _ _ _ Hb Hm) as (Tq & Φq & pv & Δ & Hlq & He & ->).
      pose proof (IH _ _ _ Γ eq_refl Hlq) as Hm0.
      pose proof (proj2 (loc_closed _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq))) as Hcq.
      destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hcq) He) as (Φ0 & Hp).
      eapply dn_mem with (R0 := ds_closed nil mq Tq Φq nil) (Γy := nil) (rd := rd_closed nil nil (apps (a_mem (qname_mod mq) y) nil))
        (E := ge_read Tq (ge_mod pv (gu_mk Δ (md_body sm_closed Φ)))) (R := ds_closed nil (qname_in mq y) (Δ ++ Tq) Φ nil).
      * exact Hm0.
      * reflexivity.
      * cbn; rewrite Hp; reflexivity.
      * cbn [ge_read ds_epath]; apply en_mod.
        eapply un_body; [ apply body_xp_noopen, (body_closed_entry_noopen _ _ _ _ _ _ _ Hcq He) | reflexivity ].
      * reflexivity.
Qed.

Lemma gc_unit_of_frame : forall Θ Ξ H mp T Φ,
    mod_qname H = Some mp -> gc_frame Ξ mp = Some (T, Φ) -> gc_unit Θ Ξ H = Some (T, Φ).
Proof.
  intros * Hq Hl; unfold gc_unit; rewrite Hq; unfold gc_frame in Hl.
  destruct (gs_find_tele Ξ mp) as [[[U [| ? ?]] T0] |]; try (destruct U as [? [[|] ? | ?]]); try discriminate; exact Hl.
Qed.

(** A unit that is open or an alias, and an entry that is not a closed
    body module: what they denote does not depend on where they are
    stored. *)
Definition unit_oa (U : gunit) : Prop :=
  match U with
  | gu_mk _ (md_body sm_open _) | gu_mk _ (md_alias _) => True
  | _ => False
  end.

Definition entry_oa (E : gentry) : Prop :=
  match E with
  | ge_mod _ U => unit_oa U
  | _ => True
  end.

(** ** Descriptions Grow with the Global Context

    A description read in a bigger context is the same, but for the body of
    a closed description, which is stored at the same path in both: a
    closed description is always related through its storage. *)

Definition ds_closedb (R : mdesc) : bool :=
  match R with
  | ds_closed _ _ _ _ _ => true
  | _ => false
  end.

Definition dsg (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (R1 R2 : mdesc) : Prop :=
  (R1 = R2 /\ ds_closedb R1 = false) \/
  exists Θ' T Φ1 Φ2 Ns p, R1 = ds_closed Θ' p T Φ1 Ns /\ R2 = ds_closed Θ' p T Φ2 Ns /\
    loc Θ1 Ξ1 p T Φ1 /\ loc Θ2 Ξ2 p T Φ2.

(** A path is stored as one module at most. *)
Lemma loc_functional : forall Θ Ξ p T Φ T' Φ', loc Θ Ξ p T Φ -> loc Θ Ξ p T' Φ' -> T = T' /\ Φ = Φ'.
Proof.
  intros * [H1 | H1] [H2 | H2]; unfold gc_frame, gc_body in *;
    destruct (gs_find_tele Ξ p) as [[[U [| ? ?]] T0] |]; try (destruct U as [? [[|] ? | ?]]);
    try discriminate; try congruence.
  all: rewrite H1 in H2; injection H2 as <- <-; split; reflexivity.
Qed.

Lemma ds_closedb_at : forall R N R', ds_at R N = Some R' -> ds_closedb R' = ds_closedb R.
Proof.
  intros [A om | Δ Φ | Θ0 p0 T Φ Ns | Θ0 p0 Ns] N R' Ha; cbn in Ha.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; reflexivity.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; [ injection Ha as <-; reflexivity | discriminate ].
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; reflexivity.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; reflexivity.
Qed.

Lemma ds_closedb_ats : forall Ns R R', ds_ats R Ns = Some R' -> ds_closedb R' = ds_closedb R.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; reflexivity |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  rewrite (IH _ _ Ha); exact (ds_closedb_at _ _ _ E).
Qed.

Lemma ds_closedb_up : forall Θ' R, ds_closedb (ds_up Θ' R) = ds_closedb R.
Proof. intros ? []; reflexivity. Qed.

Lemma ds_closedb_read : forall rd R R', ds_read rd R = Some R' -> ds_closedb R' = ds_closedb R.
Proof.
  intros [Θ' Φ' | Θ' Ns M] * Hr; cbn in Hr.
  { destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite ds_closedb_up; destruct R; reflexivity. }
  destruct (ds_ats R Ns) as [R1 |] eqn:E; cbn in Hr; [| discriminate ]; injection Hr as <-.
  rewrite ds_closedb_up, <- (ds_closedb_ats _ _ _ E); destruct Θ', Ns; destruct R1 as [? [] | | |]; reflexivity.
Qed.

Lemma entry_term_open : forall E R, entry_term E = Some R -> ds_closedb R = false.
Proof. intros [] R He; cbn in He; try discriminate; injection He as <-; reflexivity. Qed.

(** The body a path is stored as is the one [gc_loc] finds. *)
Lemma gc_loc_of_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ -> gc_loc Θ Ξ p = Some (T, Φ).
Proof.
  intros * Hg * Hl; unfold gc_loc.
  destruct (gc_frame Ξ p) as [[T' Φ'] |] eqn:E; [| destruct Hl as [Hl | Hl]; [ congruence | exact Hl ] ].
  destruct (loc_functional _ _ _ _ _ _ _ (or_introl E) Hl) as [-> ->]; reflexivity.
Qed.

Section Grow.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis Hg2 : ⊢ᵍ Θ2 ⍮ Ξ2.
  Hypothesis Hs : gc_sub Θ1 Ξ1 Θ2 Ξ2.

  Lemma dsg_refl : forall R, ds_closedb R = false -> (dsg Θ1 Ξ1 Θ2 Ξ2) R R.
  Proof. intros; left; split; [ reflexivity | assumption ]. Qed.

  (** A description grows into one description at most. *)
  Lemma dsg_functional : forall R R2 R2', (dsg Θ1 Ξ1 Θ2 Ξ2) R R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) R R2' -> R2 = R2'.
  Proof.
    intros * [[<- Hc] | (Θ' & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)]
      [[<- Hc'] | (Θ'' & T' & Φ1' & Φ2' & Ns' & p' & E & -> & H1' & H2')]; try reflexivity; try (subst; discriminate).
    injection E as <- <- <- <- <-.
    destruct (loc_functional _ _ _ _ _ _ _ H2 H2') as [_ <-]; reflexivity.
  Qed.

  Lemma dsg_ty : forall R1 R2 A, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_ty Θ1 Ξ1 R1 = Some A -> ds_ty Θ2 Ξ2 R2 = Some A.
  Proof.
    intros * [[<- _] | (? & ? & ? & ? & ? & ? & -> & -> & _)] Ht; cbn in *; try discriminate.
    destruct R1 as [| | | Θ' p k Ns]; cbn in *; try assumption.
    destruct (ind_lookup Θ1 Ξ1 p) as [D |] eqn:Hl; [| discriminate ].
    rewrite (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl); exact Ht.
  Qed.

  Lemma dsg_red : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_red R1 = ds_red R2.
  Proof. intros * [[<- _] | (? & ? & ? & ? & ? & ? & -> & -> & _)]; reflexivity. Qed.

  Lemma dsg_tele : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_tele R1 = ds_tele R2.
  Proof. intros * [[<- _] | (? & ? & ? & ? & ? & ? & -> & -> & _)]; reflexivity. Qed.

  Lemma dsg_is_mod : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_is_mod R1 -> ds_is_mod R2.
  Proof. intros * [[<- _] | (? & ? & ? & ? & ? & ? & -> & -> & _)] H; [ exact H | exact I ]. Qed.

  Lemma dsg_mod : forall R1 R2 R1m, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_mod Θ1 Ξ1 R1 = Some R1m ->
      exists R2m, ds_mod Θ2 Ξ2 R2 = Some R2m /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1m R2m.
  Proof.
    intros * [[<- Hc] | (Θ' & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)] Hm; cbn in *.
    - destruct R1 as [| | | Θ' p k Ns]; cbn in *; try discriminate;
        try (injection Hm as <-; eexists; split; [ reflexivity | apply dsg_refl; exact Hc ]).
      destruct (ind_lookup Θ1 Ξ1 p) as [D |] eqn:Hl; [| discriminate ].
      rewrite (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl).
      destruct (ind_mpath D k) as [pm |]; [| discriminate ].
      destruct (gc_body Θ1 Ξ1 pm) as [[T Φ] |] eqn:Hb; [| discriminate ]; injection Hm as <-.
      destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hb) as (Φ' & Hb' & _); rewrite Hb'.
      eexists; split; [ reflexivity |]; right; do 6 eexists; split; [ reflexivity | split; [ reflexivity |] ].
      split; right; eassumption.
    - injection Hm as <-; eexists; split; [ reflexivity |]; right; do 6 eexists; eauto.
  Qed.

  Lemma dsg_mtele : forall R1 R2 T, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_mtele Θ1 Ξ1 R1 = Some T -> ds_mtele Θ2 Ξ2 R2 = Some T.
  Proof.
    intros * Hd Ht; unfold ds_mtele in *.
    destruct (ds_mod Θ1 Ξ1 R1) as [R1m |] eqn:Hm; [| discriminate ].
    destruct (dsg_mod _ _ _ Hd Hm) as (R2m & -> & Hdm); rewrite <- (dsg_tele _ _ Hdm); exact Ht.
  Qed.

  Lemma dsg_at : forall R1 R2 N R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_at R1 N = Some R1' -> exists R2', ds_at R2 N = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    intros * [[<- Hc] | (Θ' & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)] Ha.
    - eexists; split; [ exact Ha | apply dsg_refl; rewrite (ds_closedb_at _ _ _ Ha); exact Hc ].
    - cbn in *; destruct (tele_split (rev Θ')) as [((?, ?), ?) | ?]; injection Ha as <-;
        (eexists; split; [ reflexivity | right; do 6 eexists; eauto ]).
  Qed.

  Lemma dsg_ats : forall Ns R1 R2 R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_ats R1 Ns = Some R1' -> exists R2', ds_ats R2 Ns = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    induction Ns as [| N Ns IH]; intros * Hd Ha; cbn in *; [ injection Ha as <-; eauto |].
    destruct (ds_at R1 N) as [R1a |] eqn:Ea; [| discriminate ].
    destruct (dsg_at _ _ _ _ Hd Ea) as (R2a & -> & Hda); eauto.
  Qed.

  Lemma dsg_up : forall Θ' R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_up Θ' R1) (ds_up Θ' R2).
  Proof.
    intros * [[<- Hc] | (Θ0 & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)]; [ apply dsg_refl; rewrite ds_closedb_up; exact Hc |].
    right; cbn; do 6 eexists; eauto.
  Qed.

  Lemma dsg_sub : forall σ R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_sub R1 σ) (ds_sub R2 σ).
  Proof.
    intros * [[<- Hc] | (Θ0 & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)];
      [ apply dsg_refl; destruct R1; exact Hc | right; cbn; do 6 eexists; eauto ].
  Qed.

  Lemma dsg_self : forall M R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_self M R1) (ds_self M R2).
  Proof.
    intros * [[<- Hc] | (Θ0 & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)];
      [ apply dsg_refl; destruct R1 as [? [] | | |]; exact Hc | right; cbn; do 6 eexists; eauto ].
  Qed.

  Lemma dsg_named : forall Θ Ns M R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_named Θ Ns M R1) (ds_named Θ Ns M R2).
  Proof. intros [|] [|] * Hd; cbn [ds_named]; first [ exact Hd | apply dsg_self; exact Hd ]. Qed.

  Lemma dsg_read : forall rd R1 R2 R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_read rd R1 = Some R1' -> exists R2', ds_read rd R2 = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    intros [Θ' Φ' | Θ' Ns M] * Hd Hr; cbn in *.
    - destruct (gm_fill Φ') as [σ |]; cbn in *; [ injection Hr as <- | discriminate ].
      eexists; split; [ reflexivity | apply dsg_up, dsg_sub; exact Hd ].
    - destruct (ds_ats R1 Ns) as [R1a |] eqn:Ea; [| discriminate ]; injection Hr as <-.
      destruct (dsg_ats _ _ _ _ Hd Ea) as (R2a & -> & Hda); eexists; split; [ reflexivity | apply dsg_up, dsg_named; exact Hda ].
  Qed.

  (** The entries of a stored body, read at both contexts. *)
  Lemma loc_entry_grow : forall p T Φ1 Φ2 y Φ0 E1, loc Θ1 Ξ1 p T Φ1 -> loc Θ2 Ξ2 p T Φ2 ->
      gm_prefix_upto Φ1 y = Some (gm_ext Φ0 y E1) ->
      exists Φ0' E2, gm_prefix_upto Φ2 y = Some (gm_ext Φ0' y E2) /\ entry_grows E1 E2.
  Proof.
    intros * H1 H2 Hp.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0' & E1' & [= <- <-] & He1).
    apply (loc_entry _ _ Hg1 _ _ _ H1) in He1.
    destruct (gc_sub_entry _ _ _ _ _ _ Hs He1) as (E2 & He2 & Hgr).
    apply (loc_entry _ _ Hg2 _ _ _ H2) in He2.
    destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg2 _ _ _ H2))) He2) as (Φ0'' & Hp2).
    eauto.
  Qed.

  Theorem mdenote_grow_all :
    (forall Γ H R1, mdenote Θ1 Ξ1 Γ H R1 -> exists R2, mdenote Θ2 Ξ2 Γ H R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2) /\
    (forall Γ o U R1, udenote Θ1 Ξ1 Γ o U R1 -> o = None \/ unit_oa U ->
       exists R2, udenote Θ2 Ξ2 Γ o U R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2) /\
    (forall Γ o E R1, edenote Θ1 Ξ1 Γ o E R1 -> o = None \/ entry_oa E ->
       exists R2, edenote Θ2 Ξ2 Γ o E R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2) /\
    (forall Γ Φ Φx, body_xp Θ1 Ξ1 Γ Φ Φx -> body_xp Θ2 Ξ2 Γ Φ Φx) /\
    (forall g Γ H its gs, items_gen Θ1 Ξ1 g Γ H its gs -> items_gen Θ2 Ξ2 g Γ H its gs).
  Proof.
    apply mdenote_all_ind.
    - (* a unit or an open frame *)
      intros Γ H p0 T Φ Hq0 Hu.
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hl | (_ & _ & Hb & Hm)]); rewrite Hq0 in Hq; injection Hq as <-.
      + destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hl) as (Φ' & [Hl' | [Hb' Hm']]).
        * exists (ds_closed nil p0 T Φ' nil); split; [ apply dn_unit; [ exact Hq0 | exact (gc_unit_of_frame _ _ _ _ _ _ Hq0 Hl') ] |].
          right; do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; left; eassumption ] ].
        * exists (ds_closed nil p0 T Φ' nil); split; [ apply (mdenote_of_loc _ _ Hg2 _ p0); [ exact Hq0 | right; split; assumption ] |].
          right; do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; [ left | right ]; eassumption ] ].
      + destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hb) as (Φ' & Hb' & _).
        pose proof (gc_sub_module _ _ _ _ _ _ Hs Hm) as Hm'.
        exists (ds_closed nil p0 T Φ' nil); split; [ apply (mdenote_of_loc _ _ Hg2 _ p0); [ exact Hq0 | right; split; assumption ] |].
        right; do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; right; eassumption ] ].
    - intros * Hl Hu IH; destruct (IH (or_introl eq_refl)) as (R2 & Hu2 & Hd); exists R2; split; [ econstructor; eassumption | exact Hd ].
    - intros * Hu IH; destruct (IH (or_introl eq_refl)) as (R2 & Hu2 & Hd); exists R2; split; [ econstructor; eassumption | exact Hd ].
    - intros * Hm IH Ha; destruct IH as (R2 & Hm2 & Hd).
      destruct (dsg_at _ _ _ _ Hd Ha) as (R2' & Ha2 & Hd'); exists R2'; split; [ econstructor; eassumption | exact Hd' ].
    - (* a selection *)
      intros Γ H y R0 R0m Γy E rd R R' Hm IH Hmd He Hed IHe Hr.
      destruct IH as (R0' & Hm2 & Hd0).
      destruct (dsg_mod _ _ _ Hd0 Hmd) as (R0m' & Hmd2 & Hdm).
      destruct Hdm as [[<- Hc] | (Θ' & T & Φ1 & Φ2 & Ns & p & -> & -> & H1 & H2)].
      + destruct IHe as (R2 & Hed2 & Hd2); [ left; destruct R0m; try discriminate; reflexivity |].
        destruct (dsg_read _ _ _ _ Hd2 Hr) as (R2' & Hr2 & Hd2').
        exists R2'; split; [ econstructor; eassumption | exact Hd2' ].
      + cbn in He; destruct (gm_prefix_upto Φ1 y) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
        injection He as <- <- <-.
        pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= -> <-] & _).
        destruct (loc_entry_grow _ _ _ _ _ _ _ H1 H2 Hp) as (Φ0' & E2 & Hp2 & Hgr).
        assert (HE : exists R2, edenote Θ2 Ξ2 (nil ++ Γ) (Some (qname_in p x)) (ge_read T E2) R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R R2).
        { destruct E1 as [b pv A B | pv [Δ [sm Φy1 | E']] | pv pq k D ΦD | pv Δa pma pa ka Nsa]; cbn in Hgr.
          - subst E2; apply IHe; right; exact I.
          - destruct E2 as [| pv' [Δ' [sm' Φy2 | ?]] | ? ? ? ? ? | ? ? ? ? ? ?]; cbn in Hgr; try discriminate; try contradiction.
            destruct Hgr as (<- & <- & <-).
            pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & He1).
            pose proof (gm_prefix_entry _ _ _ Hp2) as (? & ? & [= <- <-] & He2).
            pose proof (proj2 (loc_closed _ _ Hg1 _ _ _ H1)) as Hc1.
            pose proof (proj2 (loc_closed _ _ Hg2 _ _ _ H2)) as Hc2.
            pose proof (body_closed_entry_mod _ _ _ _ _ _ _ Hc1 He1) as ->.
            cbn [ge_read] in Hed |- *.
            inversion Hed; subst.
            match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
            match goal with Hx : body_xp _ _ _ Φy1 _ |- _ =>
              pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg1)))) _ _ _ Hx _
                            (body_xp_noopen Θ1 Ξ1 _ _ (body_closed_entry_noopen _ _ _ _ _ _ _ Hc1 He1))) as <- end.
            match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
            exists (ds_closed nil (qname_in p x) (Δ ++ T) Φy2 nil); split.
            + apply en_mod; eapply un_body; [ apply body_xp_noopen | reflexivity ].
              exact (body_closed_entry_noopen _ _ _ _ _ _ _ Hc2 He2).
            + right; cbn; do 6 eexists; split; [ reflexivity | split; [ reflexivity |] ].
              split; right;
                [ exact (proj1 (loc_child_mod _ _ Hg1 _ _ _ H1 _ _ _ _ _ He1))
                | exact (proj1 (loc_child_mod _ _ Hg2 _ _ _ H2 _ _ _ _ _ He2)) ].
          - subst E2; apply IHe; right; exact I.
          - destruct E2 as [| ? [? [? ?| ?]] | pv' pq' k' D' ΦD' | ? ? ? ? ? ?]; cbn in Hgr; try discriminate; try contradiction.
            destruct Hgr as (<- & <- & <- & <-).
            inversion Hed; subst; exists (ds_ind nil pq k nil); split; [ constructor | apply dsg_refl; reflexivity ].
          - subst E2; apply IHe; right; exact I. }
        destruct HE as (R2 & Hed2 & Hd2).
        destruct (dsg_read _ _ _ _ Hd2 Hr) as (R2' & Hr2 & Hd2').
        exists R2'; split; [| exact Hd2' ].
        eapply dn_mem; [ exact Hm2 | exact Hmd2 | cbn; rewrite Hp2; reflexivity | exact Hed2 | exact Hr2 ].
    - intros * Hx IH Hb Ho; exists R; split; [ econstructor; [ exact IH | exact Hb ] |].
      apply dsg_refl; destruct sm; cbn in Hb; [ injection Hb as <-; reflexivity |].
      destruct Ho as [-> | []]; discriminate.
    - intros * Hm IH Hmd _; destruct IH as (R2 & Hm2 & Hd).
      destruct (dsg_mod _ _ _ Hd Hmd) as (R2m & Hmd2 & Hdm).
      exists (ds_up Δ R2m); split; [ econstructor; eassumption | apply dsg_up; exact Hdm ].
    - intros; eexists; split; [ constructor | apply dsg_refl; reflexivity ].
    - intros * Hu IH Ho; destruct IH as (R2 & Hu2 & Hd); [ exact Ho | exists R2; split; [ constructor; exact Hu2 | exact Hd ] ].
    - intros; eexists; split; [ constructor | apply dsg_refl; reflexivity ].
    - intros; eexists; split; [ constructor | apply dsg_refl; reflexivity ].
    - intros; constructor.
    - intros; constructor; assumption.
    - intros * Hx IH Hm IHm Hmd Hgn IHg Hok.
      destruct IHm as (R2 & Hm2 & Hd).
      destruct (dsg_mod _ _ _ Hd Hmd) as (R2m & Hmd2 & _).
      econstructor; eassumption.
    - intros; constructor.
    - intros; constructor; assumption.
    - intros * Hm IHm Hgn IH; destruct IHm as (R2 & Hm2 & [[<- _] | (? & ? & ? & ? & ? & ? & [=] & _)]).
      econstructor; eassumption.
    - intros * Hm IHm Hk Hgn IH; destruct IHm as (R2 & Hm2 & Hd).
      econstructor; [ exact Hm2 | exact (dsg_is_mod _ _ Hd Hk) | exact IH ].
    - intros * Hm IHm Hl Hmp Hml Hgn IH; destruct IHm as (R2 & Hm2 & [[<- _] | (? & ? & ? & ? & ? & ? & [=] & _)]).
      econstructor; [ eassumption | exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) | eassumption
                    | exact (ind_mlookup_gc_sub _ _ _ _ _ _ Hs Hml) | eassumption ].
  Qed.
  (** A stored body is stored in the bigger context, perhaps grown. *)
  Lemma loc_grow : forall p T Φ1, loc Θ1 Ξ1 p T Φ1 -> exists Φ2, loc Θ2 Ξ2 p T Φ2.
  Proof.
    intros * [Hl | Hl].
    - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hl) as (Φ2 & [Hl2 | [Hb2 _]]); exists Φ2; [ left | right ]; assumption.
    - destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hl) as (Φ2 & Hb2 & _); exists Φ2; right; exact Hb2.
  Qed.

  Lemma gc_loc_grow : forall p T Φ1, gc_loc Θ1 Ξ1 p = Some (T, Φ1) ->
      exists Φ2, gc_loc Θ2 Ξ2 p = Some (T, Φ2) /\ loc Θ1 Ξ1 p T Φ1 /\ loc Θ2 Ξ2 p T Φ2.
  Proof.
    intros * Hl.
    assert (H1 : loc Θ1 Ξ1 p T Φ1) by (unfold gc_loc in Hl; destruct (gc_frame Ξ1 p) eqn:E;
      [ injection Hl as ->; left; exact E | right; exact Hl ]).
    destruct (loc_grow _ _ _ H1) as (Φ2 & H2); exists Φ2; split; [| split; assumption ].
    apply (gc_loc_of_loc _ _ Hg2 _ _ _ H2).
  Qed.

  (** A description grown stands for the same unit. *)
  Lemma dsg_unit : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_unit R1 = ds_unit R2.
  Proof. intros * [[<- _] | (Θ0 & T & Φ1 & Φ2 & Ns & p & -> & -> & _)]; [ reflexivity | destruct Θ0; reflexivity ]. Qed.

End Grow.

(** ** An Inductive Type Is Stored at its Own Path *)

(** A member of a group is stored at the path its declaration gives it,
    and the group at its first member. *)
Record ind_selfpath (pq : qname) (k : nat) (D : ind_decl) (p : qname) : Prop := mk_ind_selfpath
  { (** The member's path is [p] *)
    isp_path : ind_mpath D k = Some p
    (** The group is named by its first member's path *)
  ; isp_group : k = 0 -> pq = p
    (** The member is a declared one *)
  ; isp_decl : k < ind_ndecl D }.

(** [gm_selfpath p Φ]: every inductive member filed in the body [Φ],
    stored at [p], is stored at its own path. *)
Definition gm_selfpath (p : qname) (Φ : gmod) : Prop :=
  forall ip pv pq k D Φ', gm_entry Φ ip = Some (ge_ind pv pq k D Φ') -> ind_selfpath pq k D (qname_app p ip).

Lemma gm_selfpath_nil : forall p, gm_selfpath p gm_nil.
Proof. intros p ip * H; destruct ip; discriminate. Qed.

Lemma gm_selfpath_ext : forall p Φ x E, gm_selfpath p Φ ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> ind_selfpath pq k D (qname_in p x)) ->
    (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_selfpath (qname_in p x) Φ') ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> gm_selfpath (qname_in p x) Φ') ->
    gm_selfpath p (Φ ⊳ x ↦ E).
Proof.
  intros * HΦ HE HM HI ip * He; cbn in He.
  destruct ip as [| y ip]; [ discriminate |].
  destruct (String.eqb_spec y x) as [-> |]; [| exact (HΦ _ _ _ _ _ _ He) ].
  rewrite <- qname_app_in.
  destruct ip as [| z ip']; [ injection He as ->; rewrite qname_app_nil; eapply HE; reflexivity |].
  destruct E as [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? ? ?]; try discriminate.
  - eapply (HM _ _ _ _ eq_refl); exact He.
  - eapply (HI _ _ _ _ _ eq_refl); exact He.
Qed.

Lemma ind_selfpath_decl : forall pq k D M p, ind_member D k = Some M -> im_head M = mh_decl p -> (k = 0 -> pq = p) ->
    k < ind_ndecl D -> ind_selfpath pq k D p.
Proof. intros * HM Hh Hk Hlt; constructor; [ unfold ind_mpath, im_path; rewrite HM, Hh; reflexivity | exact Hk | exact Hlt ]. Qed.

Lemma wf_gmod_selfpath :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E ->
     (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> ind_selfpath pq k D mp /\ gm_selfpath mp Φ') /\
     (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_selfpath mp Φ')) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> gm_selfpath mp Φ).
Proof.
  apply global_wf_mut_ind; intros.
  all: try solve [ split; intros * Heq; discriminate ].
  all: try solve [ apply gm_selfpath_nil ].
  - (* a nested module *)
    split; intros * Heq; [ discriminate | injection Heq as <- <- <- <-; assumption ].
  - (* the first member of a group, before the members of its module *)
    split; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate ].
    split; [ eapply ind_selfpath_decl; [ eassumption | eassumption | reflexivity |] | apply gm_selfpath_nil ].
    match goal with Ho : ind_order_ok ?D, HM : ind_member ?D 0 = Some ?M, Hh : im_head ?M = mh_decl _ |- _ =>
      apply (proj1 (Ho _ _ HM)); unfold im_is_decl; rewrite Hh; reflexivity end.
  - (* a later member, before the members of its module *)
    split; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate ].
    split; [ eapply ind_selfpath_decl; [ eassumption | eassumption | intros; lia | eassumption ] | apply gm_selfpath_nil ].
  - (* one more member of the module *)
    split; intros * Heq; [| discriminate ]; injection Heq as <- <- <- <- <-.
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => destruct (proj1 IH _ _ _ _ _ eq_refl) as [Hsp HΦ] end.
    split; [ exact Hsp |].
    apply gm_selfpath_ext; [ exact HΦ | intros * [=] | intros * [=] | intros * [=] ].
  - (* an entry *)
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => rename IH into H2 end.
    apply gm_selfpath_ext; [ assumption | | |].
    + intros * ->; exact (proj1 (proj1 H2 _ _ _ _ _ eq_refl)).
    + intros * ->; exact (proj2 H2 _ _ _ _ eq_refl).
    + intros * ->; exact (proj2 (proj1 H2 _ _ _ _ _ eq_refl)).
Qed.

Lemma wf_gstack_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall fp U, gds_lookup Θ fp = Some U -> gm_selfpath (q_abs fp nil) (gu_mod U)) /\
    (forall mp U, List.In (mp, U) Ξ -> gm_selfpath mp (gu_mod U)).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Δ Φ HΞ IH HΦ Hff].
  - split; intros * H; [ discriminate | contradiction ].
  - destruct IH as [IHΘ IHΞ]; split; [| intros * [] ].
    intros fp U Hl; cbn in Hl; destruct (path_beq fp fq) eqn:Hb; [| exact (IHΘ _ _ Hl) ].
    injection Hl as <-; apply path_beq_true in Hb; subst; exact (IHΞ _ _ (or_introl eq_refl)).
  - destruct IH as [IHΘ IHΞ]; split; [ exact IHΘ |].
    intros mp' U [[= <- <-] | Hin]; [ exact ((proj2 wf_gmod_selfpath) _ _ _ _ _ HΦ) | exact (IHΞ _ _ Hin) ].
Qed.

(** A member of a group is stored at the path its declaration gives it,
    and the first member at the group's path. *)
Lemma gc_entry_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pv pq k D Φ,
    gc_entry Θ Ξ p = Some (ge_ind pv pq k D Φ) -> ind_selfpath pq k D p.
Proof.
  intros * Hg * He; destruct (wf_gstack_selfpath _ _ Hg) as [HΘ HΞ].
  unfold gc_entry, gc_entry_u in He; rewrite gs_find_tele_find in He.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |] eqn:Ef; cbn in He.
  - destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & HFf).
    apply qname_strip_app_inv in HF as ->.
    assert (Hin : List.In (F, U) Ξ).
    { clear - HFf; induction Ξ as [| [mf V] Ξ IH]; cbn in HFf; [ discriminate |].
      destruct (qname_strip mf F) as [r |] eqn:Hs.
      - injection HFf as HU Hr HT; subst; left.
        apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst; reflexivity.
      - right; exact (IH HFf). }
    exact (HΞ _ _ Hin _ _ _ _ _ _ He).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    pose proof (HΘ _ _ Hl _ _ _ _ _ _ He) as Hsp; destruct p; exact Hsp.
Qed.


(** A group of inductive types is an entry of the body of its parent,
    stored at its own path, at its first member. *)
Lemma ind_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p D, ind_lookup Θ Ξ p = Some D ->
    exists mq y Tq Φq pv Φ', p = qname_in mq y /\ loc_mod Θ Ξ mq Tq Φq /\
      gm_entry Φq (y :: nil) = Some (ge_ind pv p 0 D Φ').
Proof.
  intros * Hg * Hl.
  destruct (ind_lookup_module _ _ _ _ Hl) as (T & pq0 & Hm).
  destruct p as [u ch]; destruct ch as [| y ch _] using rev_ind.
  - exfalso; unfold gc_module, gc_module_u in Hm.
    destruct (gs_find_tele Ξ {| q_unit := u; q_chain := nil |}) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
    + destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & _).
      apply qname_strip_length in HF; cbn in HF; lia.
    + cbn in Hm; destruct (gds_lookup Θ u); [ cbn in Hm; discriminate | discriminate ].
  - set (mq := {| q_unit := u; q_chain := ch |}).
    assert (Hp : {| q_unit := u; q_chain := ch ++ y :: nil |} = qname_in mq y) by reflexivity.
    rewrite Hp in Hm |- *.
    destruct (gc_module_body _ _ _ _ _ Hm) as [Φ Hb].
    destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hm) as (Tq & Φq & Hlq & _ & Hmq).
    destruct (gm_submodule_entry _ _ _ _ _ _ _ _ Hmq) as (pv & Φ' & He).
    assert (pq0 = qname_in mq y) as ->.
    { assert (He' : gc_entry Θ Ξ (qname_in mq y) = Some (ge_ind pv pq0 0 D Φ'))
        by (apply (proj2 (loc_entry _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq) _ _)); exact He).
      exact (isp_group _ _ _ _ (gc_entry_selfpath _ _ Hg _ _ _ _ _ _ He') eq_refl). }
    exists mq, y, Tq, Φq, pv, Φ'; auto.
Qed.

Lemma qname_mod_in : forall mq y, qname_mod (qname_in mq y) = me_mem (qname_mod mq) y.
Proof.
  intros [u ch] y; unfold qname_mod, qname_in; cbn [q_unit q_chain].
  generalize (me_unit u); induction ch as [| z ch IH]; intros H; cbn; [ reflexivity | apply IH ].
Qed.

Lemma mod_qname_qname_mod : forall p, mod_qname (qname_mod p) = Some p.
Proof.
  intros [u ch]; unfold qname_mod; cbn [q_unit q_chain].
  rewrite (mod_qname_mems ch (me_unit u) (q_abs u nil) eq_refl); reflexivity.
Qed.

(** The module expression of an inductive type denotes its type former. *)
Lemma mdenote_ind_path : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p D Γ R, ind_lookup Θ Ξ p = Some D ->
    mdenote Θ Ξ Γ (qname_mod p) R -> R = ds_ind nil p 0 nil.
Proof.
  intros * Hg * Hl Hm.
  destruct (ind_parent _ _ Hg _ _ Hl) as (mq & y & Tq & Φq & pv & Φ' & -> & Hlq & He).
  rewrite qname_mod_in in Hm.
  apply (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm).
  pose proof (proj2 (loc_closed _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq))) as Hc.
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hc) He) as (Φ0 & Hp).
  eapply dn_mem; [ exact (mdenote_of_loc _ _ Hg _ _ _ _ Γ (mod_qname_qname_mod mq) Hlq) | reflexivity
                 | cbn; rewrite Hp; reflexivity | constructor | reflexivity ].
Qed.

(** A module applied to arguments denotes what it denotes, at them. *)
Lemma mdenote_apps_inv : forall Θ Ξ Γ Ns H R, mdenote Θ Ξ Γ (me_apps H Ns) R ->
    exists R0, mdenote Θ Ξ Γ H R0 /\ ds_ats R0 Ns = Some R.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm; cbn in Hm |- *; [ eauto |].
  destruct (IH _ _ Hm) as (R1 & Hm1 & Ha).
  inversion Hm1; subst; [ unfold gc_unit in *; cbn in *; discriminate |].
  match goal with Hat : ds_at ?R0 N = Some R1 |- _ => exists R0; rewrite Hat end.
  split; assumption.
Qed.

(** ** A Member Is Filed beside its Group

    Every member of a group of inductive types is filed in the module its
    group's first member is filed in ([wf_gentry_ind_mem_nil]), so the group
    a member names is found wherever the member is. *)

(** [gm_grouped p Φ]: every inductive member filed in [Φ], stored at [p],
    has its group's first member filed in the same module. *)
Definition gm_grouped (p : qname) (Φ : gmod) : Prop :=
  forall pre y pv pq k D Φ', gm_entry Φ (pre ++ y :: nil) = Some (ge_ind pv pq k D Φ') ->
    exists y0 pv0 Φ0, pq = qname_app p (pre ++ y0 :: nil) /\ gm_entry Φ (pre ++ y0 :: nil) = Some (ge_ind pv0 pq 0 D Φ0).

Lemma gm_grouped_nil : forall p, gm_grouped p gm_nil.
Proof. intros p pre * H; discriminate. Qed.

Lemma gm_entry_inner : forall Φ x E pre y,
    gm_entry (Φ ⊳ x ↦ E) (x :: pre ++ y :: nil) =
      match E with
      | ge_mod _ (gu_mk _ (md_body _ Φ')) => gm_entry Φ' (pre ++ y :: nil)
      | ge_ind _ _ _ _ Φ' => gm_entry Φ' (pre ++ y :: nil)
      | _ => None
      end.
Proof. intros; cbn; rewrite String.eqb_refl; destruct pre; reflexivity. Qed.

Lemma gm_grouped_ext : forall p Φ x E, gm_fresh x Φ -> gm_grouped p Φ ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' ->
       exists y0 pv0 Φ0, pq = qname_in p y0 /\ gm_entry (Φ ⊳ x ↦ E) (y0 :: nil) = Some (ge_ind pv0 pq 0 D Φ0)) ->
    (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_grouped (qname_in p x) Φ') ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> gm_grouped (qname_in p x) Φ') ->
    gm_grouped p (Φ ⊳ x ↦ E).
Proof.
  intros * Hf HΦ HE HM HI pre y * He.
  destruct pre as [| z pre].
  - cbn [List.app] in He |- *.
    destruct (String.eqb_spec y x) as [-> | Hne].
    + cbn in He; rewrite String.eqb_refl in He; injection He as HE'.
      destruct (HE _ _ _ _ _ HE') as (y0 & pv0 & Φ0 & -> & H0).
      exists y0, pv0, Φ0; split; [ rewrite <- qname_app_in, qname_app_nil; reflexivity | exact H0 ].
    + cbn in He; destruct (String.eqb_spec y x) as [| _ ]; [ contradiction |].
      destruct (HΦ nil y _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
      exists y0, pv0, Φ0; split; [ reflexivity | apply gm_entry_ext_fresh; assumption ].
  - destruct (String.eqb_spec z x) as [-> | Hne].
    + cbn [List.app] in He |- *; rewrite gm_entry_inner in He.
      destruct E as [? ? ? ? | pv1 [Δ1 [sm1 Φ1 | E1]] | pv1 pq1 k1 D1 Φ1 | ? ? ? ? ? ?]; try discriminate.
      * destruct (HM _ _ _ _ eq_refl _ _ _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
        exists y0, pv0, Φ0; split; [ rewrite qname_app_in; reflexivity | rewrite gm_entry_inner; exact H0 ].
      * destruct (HI _ _ _ _ _ eq_refl _ _ _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
        exists y0, pv0, Φ0; split; [ rewrite qname_app_in; reflexivity | rewrite gm_entry_inner; exact H0 ].
    + assert (He0 : gm_entry Φ ((z :: pre) ++ y :: nil) = Some (ge_ind pv pq k D Φ')).
      { cbn [List.app] in He |- *; cbn in He; destruct (String.eqb_spec z x) as [| _ ]; [ contradiction | exact He ]. }
      destruct (HΦ _ _ _ _ _ _ _ He0) as (y0 & pv0 & Φ0 & -> & H0).
      exists y0, pv0, Φ0; split; [ reflexivity | apply gm_entry_ext_fresh; assumption ].
Qed.

Lemma wf_gmod_grouped :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E ->
     (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> gm_grouped mp Φ' /\
        ((k = 0 /\ pq = mp) \/
         exists mq y y0 Δ Φ0 Ξ0 pv0 Φm, Ξ = (mq, gu_body Δ Φ0) :: Ξ0 /\ mp = qname_in mq y /\ pq = qname_in mq y0 /\
           gm_entry Φ0 (y0 :: nil) = Some (ge_ind pv0 pq 0 D Φm))) /\
     (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_grouped mp Φ')) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> gm_grouped mp Φ).
Proof.
  apply global_wf_mut_ind; intros.
  all: try solve [ split; intros * Heq; discriminate ].
  all: try solve [ apply gm_grouped_nil ].
  - (* a nested module *)
    split; intros * Heq; [ discriminate | injection Heq as <- <- <- <-; assumption ].
  - (* the first member of a group, before the members of its module *)
    split; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate ].
    split; [ apply gm_grouped_nil | left; split; reflexivity ].
  - (* a later member, before the members of its module *)
    split; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate ].
    split; [ apply gm_grouped_nil | right; do 8 eexists; split; [ reflexivity | split; [ reflexivity | split; [ reflexivity | eassumption ] ] ] ].
  - (* one more member of the module *)
    split; intros * Heq; [| discriminate ]; injection Heq as <- <- <- <- <-.
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => destruct (proj1 IH _ _ _ _ _ eq_refl) as [HΦ Hk] end.
    split; [| exact Hk ].
    apply gm_grouped_ext; [ assumption | exact HΦ | intros * [=] | intros * [=] | intros * [=] ].
  - (* an entry *)
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => rename IH into H2 end.
    apply gm_grouped_ext; [ assumption | assumption | | |].
    + intros * ->; destruct (proj1 H2 _ _ _ _ _ eq_refl) as [_ [[-> ->] | (mq & y & y0 & Δ0 & Φ0 & Ξ0 & pv0 & Φm & HΞ & _ & -> & Hen)]].
      * do 3 eexists; split; [ reflexivity | cbn; rewrite String.eqb_refl; reflexivity ].
      * injection HΞ as <- _ <- _.
        do 3 eexists; split; [ reflexivity | apply gm_entry_ext_fresh; [ assumption | exact Hen ] ].
    + intros * ->; exact (proj2 H2 _ _ _ _ eq_refl).
    + intros * ->; exact (proj1 (proj1 H2 _ _ _ _ _ eq_refl)).
Qed.

Lemma wf_gstack_grouped : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall fp U, gds_lookup Θ fp = Some U -> gm_grouped (q_abs fp nil) (gu_mod U)) /\
    (forall mp U, List.In (mp, U) Ξ -> gm_grouped mp (gu_mod U)).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Δ Φ HΞ IH HΦ Hff].
  - split; intros * H; [ discriminate | contradiction ].
  - destruct IH as [IHΘ IHΞ]; split; [| intros * [] ].
    intros fp U Hl; cbn in Hl; destruct (path_beq fp fq) eqn:Hb; [| exact (IHΘ _ _ Hl) ].
    injection Hl as <-; apply path_beq_true in Hb; subst; exact (IHΞ _ _ (or_introl eq_refl)).
  - destruct IH as [IHΘ IHΞ]; split; [ exact IHΘ |].
    intros mp' U [[= <- <-] | Hin]; [ exact ((proj2 wf_gmod_grouped) _ _ _ _ _ HΦ) | exact (IHΞ _ _ Hin) ].
Qed.

Lemma gm_grouped_subbody : forall p Φ T x ip T' Φ',
    gm_grouped p Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> gm_grouped (qname_app p (x :: ip)) Φ'.
Proof.
  intros * HG Hb pre y * He.
  assert (Hre : forall l z, gm_entry Φ (x :: ip ++ l ++ z :: nil) = gm_entry Φ' (l ++ z :: nil)).
  { intros l z; destruct l as [| a l]; cbn [List.app]; [ apply (gm_subbody_entry_app _ _ _ _ _ _ Hb) |].
    exact (gm_subbody_entry_app _ _ _ _ _ _ Hb a (l ++ z :: nil)). }
  rewrite <- Hre in He.
  replace (x :: ip ++ pre ++ y :: nil) with ((x :: ip ++ pre) ++ y :: nil) in He by (cbn; rewrite <- List.app_assoc; reflexivity).
  destruct (HG _ _ _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
  exists y0, pv0, Φ0; split.
  - rewrite qname_app_app; f_equal; cbn; rewrite <- List.app_assoc; reflexivity.
  - rewrite <- Hre; replace (x :: ip ++ pre ++ y0 :: nil) with ((x :: ip ++ pre) ++ y0 :: nil) by (cbn; rewrite <- List.app_assoc; reflexivity).
    exact H0.
Qed.

(** Every body stored at a path has its members beside their groups. *)
Lemma loc_grouped : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ -> gm_grouped p Φ.
Proof.
  intros * Hg * Hl; destruct (wf_gstack_grouped _ _ Hg) as [HΘ HΞ].
  assert (Hframe : forall qq U ip T0, gs_find_tele Ξ qq = Some (U, ip, T0) -> exists F, qq = qname_app F ip /\ gm_grouped F (gu_mod U)).
  { intros * Ef; destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & HFf).
    apply qname_strip_app_inv in HF; exists F; split; [ exact HF |].
    apply HΞ; clear - HFf; induction Ξ as [| [mf V] Ξ IH]; cbn in HFf; [ discriminate |].
    destruct (qname_strip mf F) as [r |] eqn:Hs.
    - injection HFf as HU Hr HT; subst; left.
      apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst; reflexivity.
    - right; exact (IH HFf). }
  destruct Hl as [Hl | Hl].
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[U ip] T0] |] eqn:Ef; [| discriminate ].
    destruct U as [Δ [[|] Φ0 | E]], ip as [| ? ?]; try discriminate; injection Hl as <- <-.
    destruct (Hframe _ _ _ _ Ef) as (F & -> & HF); rewrite qname_app_nil; exact HF.
  - unfold gc_body in Hl.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
    + destruct (Hframe _ _ _ _ Ef) as (F & -> & HF); exact (gm_grouped_subbody _ _ _ _ _ _ _ HF Hl).
    + destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; [| discriminate ].
      pose proof (HΘ _ _ El) as HU.
      destruct p as [u ch]; cbn [q_chain q_unit] in Hl, HU.
      destruct ch as [| x ip]; cbn in Hl; [ injection Hl as <- <-; exact HU |].
      exact (gm_grouped_subbody _ _ _ _ _ _ _ HU Hl).
Qed.

(** A member of a group is an entry of the body of its parent. *)
Lemma ind_mparent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D, ind_mlookup Θ Ξ p = Some (pq, k, D) ->
    exists mq y Tq Φq pv Φ', p = qname_in mq y /\ loc_mod Θ Ξ mq Tq Φq /\
      gm_entry Φq (y :: nil) = Some (ge_ind pv pq k D Φ').
Proof.
  intros * Hg * Hl.
  destruct (ind_mlookup_module _ _ _ _ Hl) as [T Hm].
  destruct p as [u ch]; destruct ch as [| y ch _] using rev_ind.
  - exfalso; unfold gc_module, gc_module_u in Hm.
    destruct (gs_find_tele Ξ {| q_unit := u; q_chain := nil |}) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
    + destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & _).
      apply qname_strip_length in HF; cbn in HF; lia.
    + cbn in Hm; destruct (gds_lookup Θ u); [ cbn in Hm; discriminate | discriminate ].
  - set (mq := {| q_unit := u; q_chain := ch |}).
    assert (Hp : {| q_unit := u; q_chain := ch ++ y :: nil |} = qname_in mq y) by reflexivity.
    rewrite Hp in Hm |- *.
    destruct (gc_module_body _ _ _ _ _ Hm) as [Φ Hb].
    destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hm) as (Tq & Φq & Hlq & _ & Hmq).
    destruct (gm_submodule_entry _ _ _ _ _ _ _ _ Hmq) as (pv & Φ' & He).
    exists mq, y, Tq, Φq, pv, Φ'; auto.
Qed.

(** A member is stored at the path its declaration gives it. *)
Lemma ind_mlookup_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D,
    ind_mlookup Θ Ξ p = Some (pq, k, D) -> ind_selfpath pq k D p.
Proof.
  intros * Hg * Hl; destruct (ind_mlookup_entry _ _ _ _ _ _ Hl) as (pv & Φ & He).
  exact (gc_entry_selfpath _ _ Hg _ _ _ _ _ _ He).
Qed.

(** The group a member names is found. *)
Lemma ind_mlookup_group : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D,
    ind_mlookup Θ Ξ p = Some (pq, k, D) -> ind_lookup Θ Ξ pq = Some D.
Proof.
  intros * Hg * Hl.
  destruct (ind_mlookup_module _ _ _ _ Hl) as [T Hm].
  destruct p as [u ch]; destruct ch as [| y ch _] using rev_ind.
  - exfalso; unfold gc_module, gc_module_u in Hm.
    destruct (gs_find_tele Ξ {| q_unit := u; q_chain := nil |}) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
    + destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & _).
      apply qname_strip_length in HF; cbn in HF; lia.
    + cbn in Hm; destruct (gds_lookup Θ u); [ cbn in Hm; discriminate | discriminate ].
  - set (mq := {| q_unit := u; q_chain := ch |}).
    assert (Hp : {| q_unit := u; q_chain := ch ++ y :: nil |} = qname_in mq y) by reflexivity.
    rewrite Hp in Hm.
    destruct (gc_module_body _ _ _ _ _ Hm) as [Φ Hb].
    destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hm) as (Tq & Φq & Hlq & _ & Hmq).
    destruct (gm_submodule_entry _ _ _ _ _ _ _ _ Hmq) as (pv & Φ' & He).
    destruct (loc_grouped _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq) nil y _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
    cbn [List.app] in H0.
    assert (He0 : gc_entry Θ Ξ (qname_in mq y0) = Some (ge_ind pv0 (qname_app mq (y0 :: nil)) 0 D Φ0))
      by (apply (proj2 (loc_entry _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq) _ _)); exact H0).
    cbn [List.app]; rewrite <- qname_app_in, qname_app_nil in He0 |- *.
    destruct (gc_entry_ind _ _ _ _ _ _ _ _ He0) as [_ Hm0].
    rewrite ind_lookup_unfold, Hm0; reflexivity.
Qed.

(** The module expression of the module of a member denotes the member's
    type former. *)
Lemma mdenote_mind_path : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D Γ R, ind_mlookup Θ Ξ p = Some (pq, k, D) ->
    mdenote Θ Ξ Γ (qname_mod p) R -> R = ds_ind nil pq k nil.
Proof.
  intros * Hg * Hl Hm.
  destruct (ind_mparent _ _ Hg _ _ _ _ Hl) as (mq & y & Tq & Φq & pv & Φ' & -> & Hlq & He).
  rewrite qname_mod_in in Hm.
  apply (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm).
  pose proof (proj2 (loc_closed _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq))) as Hc.
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hc) He) as (Φ0 & Hp).
  eapply dn_mem; [ exact (mdenote_of_loc _ _ Hg _ _ _ _ Γ (mod_qname_qname_mod mq) Hlq) | reflexivity
                 | cbn; rewrite Hp; reflexivity | constructor | reflexivity ].
Qed.
