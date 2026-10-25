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
Lemma gc_resolve_frame : forall Θ mp K U Ξ p E,
    gc_resolve Θ ((mp, K, U) :: Ξ) p = Some E ->
    (exists ip, p = qname_app mp ip /\ gm_resolve (gu_mod U) ip = Some E) \/
    gc_resolve Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_resolve, gc_resolve_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_resolve_frame_here : forall Θ mp K U Ξ ip,
    gc_resolve Θ ((mp, K, U) :: Ξ) (qname_app mp ip) = gm_resolve (gu_mod U) ip.
Proof. intros; unfold gc_resolve, gc_resolve_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_module_frame : forall Θ mp K U Ξ p r,
    gc_module Θ ((mp, K, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_module Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_module, gc_module_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_module_frame_here : forall Θ mp K U Ξ x ip,
    gc_module Θ ((mp, K, U) :: Ξ) (qname_app mp (x :: ip)) = gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_module, gc_module_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_body_frame : forall Θ mp K U Ξ p r,
    gc_body Θ ((mp, K, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_subbody (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_body Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_body in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_body_frame_here : forall Θ mp K U Ξ x ip,
    gc_body Θ ((mp, K, U) :: Ξ) (qname_app mp (x :: ip)) = gm_subbody (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_body; cbn; rewrite qname_strip_app; reflexivity. Qed.

(** Every frame of a well-formed stack belongs to a unit not filed. *)
Lemma wf_gstack_frames : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp K U, List.In (mp, K, U) Ξ -> gds_lookup Θ (q_unit mp) = None.
Proof.
  induction 1 as [| | Θ Ξ mq Kq Δ Φ HΞ IH HV Hff]; intros mp K0 V0 Hin; try (cbn in Hin; contradiction).
  destruct Hin as [[= <- <- <-] | Hin]; [| eauto ].
  destruct Ξ as [| [[mr Kr] W] Ξ']; cbn in Hff.
  - exact (proj1 Hff).
  - destruct Hff as (x & -> & _); cbn; apply (IH mr Kr W); left; reflexivity.
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
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
    destruct ip as [| z ip]; try discriminate; first [ injection H as <- _; eauto | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gm_subbody_snoc : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y, gm_submodule T Φ x (ip ++ y :: nil) = gm_submodule T' Φ' y nil /\
      gm_subbody T Φ x (ip ++ y :: nil) = gm_subbody T' Φ' y nil.
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; split; reflexivity | exact (IH _ _ _ _ _ _ H y) ]).
Qed.

Lemma gm_subbody_resolve : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall z, gm_resolve Φ (x :: ip ++ z :: nil) = gm_resolve Φ' (z :: nil).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H z; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H z) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H z) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
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
    parameters extend [T], its module's body coherent with them.  A
    definition with a module part has a type and a term closed over [T],
    the [Π] and the [λ] over it, and its module part is an alias whose
    parameters extend [T]. *)
Fixpoint gm_coh (T : ctx) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_open Φ0 _ _ => gm_coh T Φ0
  | gm_ext Φ0 _ (ge_def _ _ A _) => gm_coh T Φ0 /\ exists A0, A = ctx_pi T A0
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body sm Φ'))) => gm_coh T Φ0 /\ tele_ass Δ /\ gm_coh (Δ ++ T) Φ'
  | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_alias _))) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  | gm_ext Φ0 _ (ge_ind _ _ _ D Φ') =>
      gm_coh T Φ0 /\ (exists Δ0, ind_uparams D = Δ0 ++ T /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ'
  | gm_ext Φ0 _ (ge_def_mod _ A M U) =>
      gm_coh T Φ0 /\ (exists A0 M0, A = ctx_pi T A0 /\ M = ctx_fn T M0) /\
      exists Δ0 E, U = gu_mk (Δ0 ++ T) (md_alias E) /\ tele_ass Δ0
  | gm_ext Φ0 _ (ge_record _ p R Φ') =>
      gm_coh T Φ0 /\ (exists Δ0, record_params R = Δ0 ++ T /\ tele_ass Δ0) /\ gm_coh (record_mod_tele p R) Φ'
  end.

(** A record's module telescope extends what its parameters extend, by
    assumptions: the parameters' own and then the value. *)
Lemma record_mod_tele_split : forall p R Δ T, record_params R = Δ ++ T -> tele_ass Δ ->
    record_mod_tele p R = (ce_ass (record_self p R) :: Δ) ++ T /\ tele_ass (ce_ass (record_self p R) :: Δ).
Proof.
  intros * HP HΔ; unfold record_mod_tele; rewrite HP; split; [ reflexivity | constructor; eauto ].
Qed.

Lemma gm_coh_subbody : forall Φ T x ip T' Φ',
    gm_coh T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * Hc H; cbn in Hc, H; [ discriminate | | exact (IH _ _ _ _ _ _ Hc H) ].
  destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? pr Rr ΦR];
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
  - destruct Hc as (Hc1 & (Δ & HΔe & HΔ) & Hc2).
    destruct (record_mod_tele_split pr Rr _ _ HΔe HΔ) as [HT HΔs].
    destruct ip as [| w ip].
    + injection H as <- <-; split; [ exact Hc2 | eauto ].
    + destruct (IH _ _ _ _ _ _ Hc2 H) as (Hc' & Δ' & -> & HΔ').
      split; [ exact Hc' | exists (Δ' ++ ce_ass (record_self pr Rr) :: Δ); rewrite HT, app_assoc;
                           split; [ reflexivity | apply Forall_app; auto ] ].
Qed.

Lemma gm_coh_child : forall Φ T y r,
    gm_coh T Φ -> gm_submodule T Φ y nil = Some r ->
    (exists Δ oD, r = mr_body (Δ ++ T) oD /\ tele_ass Δ) \/
    (exists U Δ, r = mr_alias U /\ gu_params U = Δ ++ T /\ tele_ass Δ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc H; cbn in Hc, H; [ discriminate | | eauto ].
  destruct (String.eqb y z).
  - destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? pr Rr ΦR]; [ discriminate | | | | discriminate | | ].
    + injection H as <-; destruct Hc as (_ & HΔ & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
    + injection H as <-; destruct Hc as (_ & (Δ0 & -> & HΔ) & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & _ & Δ0 & E0 & [= -> ->] & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
    + injection H as <-; destruct Hc as (_ & (Δ0 & HΔe & HΔ) & _); left.
      destruct (record_mod_tele_split pr Rr _ _ HΔe HΔ) as [HT HΔs]; rewrite HT; eauto.
  - destruct E as [b pv A B | ? [Δ [? Φ0 | E0]] | ? ? ? ? ? | ? Aa Ma [Δa [? Φa | Ea]] | ? pr Rr ΦR]; eapply IH; try eassumption; apply Hc.
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

(** A telescope of assumptions over the frames' parameters [T] extends [T]
    by assumptions. *)
Lemma params_split : forall (P Δ T : ctx), P = Δ ++ T -> tele_ass P -> exists Δ0, P = Δ0 ++ T /\ tele_ass Δ0.
Proof.
  intros * Hp Ha; exists Δ; split; [ exact Hp |].
  rewrite Hp in Ha; apply Forall_app in Ha as [Ha _]; exact Ha.
Qed.

Lemma wf_gmod_coh :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> forall Ξ' mp' K' Δ Φ, Ξ = (mp', K', gu_body Δ Φ) :: Ξ' ->
     match E with
     | ge_def _ _ A _ => exists A0, A = ctx_pi (Δ ++ gs_tele Ξ') A0
     | ge_mod _ (gu_mk Δ1 (md_body sm Φ1)) => tele_ass Δ1 /\ gm_coh (Δ1 ++ Δ ++ gs_tele Ξ') Φ1
     | ge_mod _ (gu_mk Δ1 (md_alias _)) => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
     | ge_ind _ _ _ D Φ1 =>
         (exists Δ0, ind_uparams D = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ1
     | ge_def_mod _ A M U =>
         (exists A0 M0, A = ctx_pi (Δ ++ gs_tele Ξ') A0 /\ M = ctx_fn (Δ ++ gs_tele Ξ') M0) /\
         exists Δ0 E, U = gu_mk (Δ0 ++ Δ ++ gs_tele Ξ') (md_alias E) /\ tele_ass Δ0
     | ge_record _ p R Φ1 =>
         (exists Δ0, record_params R = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0) /\ gm_coh (record_mod_tele p R) Φ1
     end) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> tele_ass Δ /\ gm_coh (Δ ++ gs_tele Ξ) Φ).
Proof.
  apply global_wf_mut_ind; intros; subst; cbn.
  - eauto.
  - match goal with IH : tele_ass ?Δ' /\ _ |- _ => destruct IH as [HΔ Hc] end.
    cbn in Hc; split; [ exact HΔ | exact Hc ].
  - exists Δ; cbn; auto.
  - (* the module of the first member of a group, before its members *)
    split; [| exact I ].
    match goal with Hp : ind_uparams ?D = ?Δd ++ _ |- _ => exact (uparams_split _ _ _ Hp ltac:(assumption)) end.
  - (* the module of a later member, before its members *)
    match goal with Heq : (_, _, _) :: _ = (_, _, _) :: _ |- _ => injection Heq; intros; subst end.
    split; [| exact I ].
    match goal with Hp : ind_uparams ?D = ?Δd ++ _ |- _ => exact (uparams_split _ _ _ Hp ltac:(assumption)) end.
  - (* a declared member with the body of its module, over its uniform parameters *)
    match goal with IH : tele_ass ?Δu /\ gm_coh _ _, Hp : ind_uparams _ = _ |- _ =>
      destruct IH as [HΔu Hc]; cbn in Hp; rewrite Hp; split; [ exists Δu; split; [ reflexivity | exact HΔu ] | exact Hc ] end.
  - (* a definition with a module part *)
    split; [ do 2 eexists; split; reflexivity | do 2 eexists; split; [ reflexivity | assumption ] ].
  - (* a record, before the members of its module *)
    split; [| exact I ].
    match goal with Hp : record_params ?R = ?Δd ++ _ |- _ => exact (params_split _ _ _ Hp ltac:(assumption)) end.
  - (* a record with the body of its module, over its parameters and a value *)
    match goal with IH : tele_ass (_ :: ?Δu) /\ gm_coh _ _, Hp : record_params _ = _ |- _ =>
      destruct IH as [HΔu Hc]; cbn in Hp; unfold record_mod_tele; rewrite Hp;
      split; [ exists Δu; split; [ reflexivity | inversion HΔu; assumption ] | exact Hc ] end.
  - split; [ assumption | exact I ].
  - split; [ assumption | exact I ].
  - split; [ constructor; [ eexists; reflexivity | assumption ] | exact I ].
  - match goal with IH : tele_ass Δ /\ _ |- _ => destruct IH as [HΔ Hc] end.
    split; [ exact HΔ |].
    match goal with IHE : forall _ _ _ _ _, _ = _ -> _ |- _ => specialize (IHE _ _ _ _ _ eq_refl); cbn in IHE end.
    destruct E as [b pv A B | ? [Δ1 [? Φ1 | E1]] | ? ? ? D1 Φ1 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; cbn; try split; auto; apply IHE.
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
  induction 1 as [| | Θ Ξ mp Kp Δ Φ HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; try discriminate.
  destruct (qname_strip mp p); [| eauto ].
  injection Hf as <- <- <-.
  exact (proj2 (proj2 wf_gmod_coh _ _ _ _ _ _ HΦ)).
Qed.

Lemma wf_gdeps_coh : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall fp U, gds_lookup Θ fp = Some U -> gm_coh (gu_params U) (gu_mod U).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Kp Δ Φ HΞ IH HΦ Hff]; intros fp U Hl; cbn in Hl; [ discriminate | | eauto ].
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
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
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
  induction 1 as [| | Θ Ξ mp Kp Vp VΦ HΞ IH HV Hff]; intros * Hf Hin ch; cbn in Hf |- *; [ discriminate | discriminate |].
  destruct (qname_strip mp p) as [r |] eqn:Hs.
  - injection Hf; intros; subst.
    apply qname_strip_app_inv in Hs; subst p.
    rewrite qname_app_app, qname_strip_app; reflexivity.
  - pose proof (IH _ _ _ _ _ Hf Hin ch) as Hf'.
    destruct (qname_strip mp (qname_app p ch)) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [[mq Kq'] W] Ξ'']; [ discriminate |].
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
  induction Ξ as [| [[mp Kp'] V] Ξ' IH]; cbn; [ reflexivity |].
  assert (Hne : path_beq (q_unit mp) (q_unit (qname_app p ch)) = false).
  { destruct (path_beq (q_unit mp) (q_unit (qname_app p ch))) eqn:Hb; [| reflexivity ].
    apply path_beq_true in Hb; cbn in Hb.
    pose proof (Hfr mp Kp' V (or_introl eq_refl)) as Hn; rewrite Hb in Hn; congruence. }
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
  - destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate; eauto.
  - destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
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
    destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate; eauto.
  - revert H; induction Φ as [| Φ IH z E0 | Φ IH c]; intros H; cbn in H |- *; [ discriminate | | exact (IH H) ].
    destruct (String.eqb x z); [| exact (IH H) ].
    destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
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
    + destruct E0 as [? ? ? ? | pm [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | pm Aa Ma [Δa [? Φa | Ea]] | pm Rr ΦR]; try discriminate.
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
        exists nil, x, T, (gm_ext Φ z (ge_def_mod pm Aa Ma (gu_mk Δa (md_alias Ea)))); split; [ reflexivity |]; split; [ reflexivity |].
        cbn; rewrite Exz; reflexivity.
      * destruct ip as [| w ip]; [ discriminate |].
        destruct (IH _ _ _ _ _ H) as (pre & y & T' & Φ' & Heq & Hb & Hs).
        exists (x :: pre), y, T', Φ'; split; [ rewrite Heq; reflexivity |]; split; [| exact Hs ].
        cbn; rewrite Exz.
        destruct pre as [| v pre]; cbn in Hb |- *; [ injection Hb as <- <-; reflexivity | exact Hb ].
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
  destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ H ch Hch).
  - destruct ip as [| w ip]; [| discriminate ]; destruct ch as [| v ch]; [ contradiction |]; cbn; repeat split; reflexivity.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ H ch Hch).
  - destruct ip as [| w ip]; [| discriminate ]; destruct ch as [| v ch]; [ contradiction |]; cbn; repeat split; reflexivity.
  - destruct ip as [| w ip]; [ discriminate |]; exact (IH _ _ _ _ _ H ch Hch).
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
  induction 1 as [| | Θ Ξ mp Kp Vp VΦ HΞ IH HV Hff]; intros * Hf Hin; cbn in Hf; [ discriminate | discriminate |].
  destruct (qname_strip mp p) as [r |] eqn:Hs.
  - injection Hf; intros; subst.
    exists mp; split; [ apply qname_strip_app_inv; exact Hs |].
    intros ip'; cbn; rewrite qname_strip_app; reflexivity.
  - destruct (IH _ _ _ _ _ Hf Hin) as (Fp & -> & HF).
    exists Fp; split; [ reflexivity |]; intros ip'.
    pose proof (HF ip') as Hf'.
    cbn; destruct (qname_strip mp (qname_app Fp (x :: ip'))) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [[mq Kq'] W] Ξ'']; [ discriminate |].
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
  destruct E as [? ? ? ? | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
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
      gc_resolve Θ Ξ (qname_app p ch) = None /\ gs_find_ind Ξ (qname_app p ch) = None.
Proof.
  intros * Hg * H ch Hch.
  pose proof Hg as Hs.
  pose proof H as H0; unfold gc_module, gc_module_u in H0.
  destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] Tf] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_submodule_head _ _ _ _ _ H0) ch) as Ef'.
    destruct (gm_submodule_alias_app _ _ _ _ _ H0 ch Hch) as (H1 & H2 & H3).
    rewrite (gs_find_ind_none Ξ) by (intros ? ? Hc; rewrite Ef' in Hc; discriminate).
    unfold gc_module, gc_module_u, gc_body, gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ef'; cbn.
    repeat split; assumption.
  - destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    rewrite (gs_find_ind_none Ξ) by (intros ? ? Hc; rewrite Ef' in Hc; discriminate).
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
  destruct E as [? ? ? ? | U | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; [ reflexivity | discriminate | discriminate | discriminate | discriminate ].
Qed.

Lemma gm_submodule_alias_resolve : forall Φ T x ip U,
    gm_submodule T Φ x ip = Some (mr_alias U) -> gm_resolve Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ z E0 | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ H) ].
  destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
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
  destruct (gc_module_alias_app _ _ Hg _ _ Ha ch Hne) as (H1 & _ & H3 & H4).
  destruct Hx as [(T & oD & HT) | [(U' & HU) | [(E & HE) | (D & HD)]]]; try congruence.
  rewrite ind_lookup_unfold, ind_mlookup_unfold, H4, H1 in HD; discriminate.
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
  induction 1 as [| | Θ Ξ mf Kf Δf Φf HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; [ discriminate | discriminate |].
  destruct (qname_strip mf mp) as [ip |] eqn:Hs.
  - injection Hf as HU Hip HT; subst ip U T0.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst mf.
    destruct Ξ as [| [[mq Kq'] V] Ξ']; cbn in Hff |- *.
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
  induction 1 as [| | Θ Ξ mf Kf Δf Φf HΞ IH HΦ Hff]; intros * Hf y Hin ch; cbn in Hf |- *; [ discriminate | discriminate |].
  destruct (qname_strip mf mp) as [r |] eqn:Hs.
  - injection Hf as HU Hr HT; subst r U T0.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst mf.
    rewrite qname_strip_app; reflexivity.
  - pose proof (IH _ _ _ Hf _ Hin ch) as Hf'.
    destruct (qname_strip mf (qname_app mp (y :: ch))) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [[mq Kq'] W] Ξ'']; [ discriminate |].
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
  induction 1 as [| | Θ Ξ mf Kf Δf Φf HΞ IH HΦ Hff]; intros * Hf y; cbn in Hf |- *; [ discriminate | discriminate |].
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
      gc_body Θ Ξ (qname_app mp (y :: ch)) = gm_subbody T Φ y ch.
Proof.
  intros * Hg * Hfr y Hin ch; unfold gc_frame in Hfr.
  destruct (gs_find_tele Ξ mp) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
  injection Hfr as <- <-.
  pose proof (gs_find_tele_frame_app _ _ Hg _ _ _ Ef y Hin ch) as Ef'.
  unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u, gc_module, gc_module_u, gc_body;
    rewrite !gs_find_tele_find, Ef'; cbn.
  repeat split; reflexivity.
Qed.

Lemma gm_subbody_entry_app : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y ch, gm_entry Φ (x :: ip ++ y :: ch) = gm_entry Φ' (y :: ch).
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y ch; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y ch) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y ch) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
    (destruct ip as [| w ip]; cbn; [ injection H as <- <-; reflexivity | specialize (IH _ _ _ _ _ _ H y ch); cbn in IH; exact IH ]).
Qed.

(** What is stored below a closed module is what its body says. *)
Theorem closed_read_entry : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    forall y ch, gc_entry Θ Ξ (qname_app p (y :: ch)) = gm_entry Φ (y :: ch).
Proof.
  intros * Hg * H y ch.
  pose proof H as H0; unfold gc_body in H0.
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
      gc_body Θ Ξ (qname_app p (y :: ch)) = gm_subbody T Φ y ch.
Proof.
  intros * Hg * [Hl | Hl] y Hin ch; [ exact (gc_frame_below _ _ Hg _ _ _ Hl _ Hin ch) |].
  destruct (gc_body_module _ _ _ _ _ Hl) as [oD Hm].
  destruct (closed_read _ _ Hg _ _ _ _ Hl Hm (y :: ch)) as (H1 & H2 & H3).
  pose proof (closed_read_entry _ _ Hg _ _ _ Hl y ch) as H4.
  repeat split; [ exact H4 | exact (H3 ltac:(discriminate)) | exact H1 | exact H2 ].
Qed.

(** An open frame names nothing it does not declare. *)
Lemma gc_entry_frame_name : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall mp T Φ, gc_frame Ξ mp = Some (T, Φ) ->
    forall y E, gc_entry Θ Ξ (qname_in mp y) = Some E -> List.In y (gm_names Φ).
Proof.
  induction 1 as [| | Θ Ξ mf Kf Δf Φf HΞ IH HΦ Hff]; intros * Hfr y E He; unfold gc_frame in Hfr; cbn in Hfr; try discriminate.
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
  induction 1 as [| | Θ Ξ mf Kf Δf Φf HΞ IH HΦ Hff]; intros * Hf; cbn in Hf; try discriminate.
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
      - rewrite (closed_read_entry _ _ Hg _ _ _ Hl y nil) in He.
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

Lemma gm_entry_subbody_record : forall Φ T y pv pr R Φ',
    gm_entry Φ (y :: nil) = Some (ge_record pv pr R Φ') ->
    gm_subbody T Φ y nil = Some (record_mod_tele pr R, Φ') /\
    gm_submodule T Φ y nil = Some (mr_body (record_mod_tele pr R) None).
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
  destruct (loc_read _ _ Hg _ _ _ Hl _ Hin nil) as (_ & _ & Hm & Hb).
  destruct (gm_entry_subbody_mod _ T _ _ _ _ _ He) as [Hb' Hm'].
  rewrite qname_in_app, Hb, Hm; split; assumption.
Qed.

(** The module of a stored inductive type is stored at its path, over the
    declaration's uniform parameters. *)
Lemma loc_child_ind : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ y pv pq k D ΦD, loc Θ Ξ p T Φ ->
    gm_entry Φ (y :: nil) = Some (ge_ind pv pq k D ΦD) -> gc_body Θ Ξ (qname_in p y) = Some (ind_uparams D, ΦD).
Proof.
  intros * Hg * Hl He.
  destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin).
  destruct (loc_read _ _ Hg _ _ _ Hl _ Hin nil) as (_ & _ & _ & Hb).
  rewrite qname_in_app, Hb; exact (proj1 (gm_entry_subbody_ind _ T _ _ _ _ _ _ He)).
Qed.

(** The module of a stored record type is stored at its path, over the
    record's parameters and a value of it. *)
Lemma loc_child_record : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ y pv pr R ΦR, loc Θ Ξ p T Φ ->
    gm_entry Φ (y :: nil) = Some (ge_record pv pr R ΦR) -> gc_body Θ Ξ (qname_in p y) = Some (record_mod_tele pr R, ΦR).
Proof.
  intros * Hg * Hl He.
  destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin).
  destruct (loc_read _ _ Hg _ _ _ Hl _ Hin nil) as (_ & _ & _ & Hb).
  rewrite qname_in_app, Hb; exact (proj1 (gm_entry_subbody_record _ T _ _ _ _ _ He)).
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
  - left; unfold gc_frame; rewrite Hf.
    destruct U as [Δ [[|] Φ0 | E]], (gs_find_ind Ξ mp), (gs_find_record Ξ mp); try discriminate; exact Hu.
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

(** ** The Open Frame of a Member's Module

    The open frame of the module of a member of a group of inductive types
    is at the member's own path, and the group its kind names is read
    where the frame is open: through the frame itself for the first
    member, through the first member's entry below it for a later one. *)

(** A member of a group is stored at the path its declaration gives it,
    and the group at its first member. *)
Record ind_selfpath (pq : qname) (k : nat) (D : ind_decl) (p : qname) : Prop := mk_ind_selfpath
  { (** The member's path is [p] *)
    isp_path : ind_mpath D k = Some p
    (** The group is named by its first member's path *)
  ; isp_group : k = 0 -> pq = p
    (** The member is a declared one *)
  ; isp_decl : k < ind_ndecl D }.

(** A member at its own path is a member of the group. *)
Lemma ind_selfpath_member : forall pq k D p, ind_selfpath pq k D p -> exists Mk, ind_member D k = Some Mk.
Proof.
  intros * Hsp; pose proof (isp_decl _ _ _ _ Hsp) as Hk; pose proof (ind_ndecl_le D) as Hle.
  unfold ind_member; destruct (List.nth_error (ind_members D) k) as [Mk |] eqn:Hm; [ eauto |].
  apply List.nth_error_None in Hm; lia.
Qed.

Lemma ind_selfpath_decl : forall pq k D M p, ind_member D k = Some M -> im_head M = mh_decl p -> (k = 0 -> pq = p) ->
    k < ind_ndecl D -> ind_selfpath pq k D p.
Proof. intros * HM Hh Hk Hlt; constructor; [ unfold ind_mpath, im_path; rewrite HM, Hh; reflexivity | exact Hk | exact Hlt ]. Qed.

(** A declared member, and the module of one, is at its own path, and its
    group is read where it is checked, but for the first member, whose
    group is its own. *)
Lemma wf_gmod_kind :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> forall pv pq k D Φ, E = ge_ind pv pq k D Φ ->
     ind_selfpath pq k D mp /\ (k = 0 \/ ind_lookup Θ Ξ pq = Some D)) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> forall pq k D, K = fk_ind pq k D ->
     ind_selfpath pq k D mp /\ (k = 0 \/ ind_lookup Θ Ξ pq = Some D)).
Proof.
  apply global_wf_mut_ind; intros; try discriminate.
  - (* the first member of a group *)
    match goal with Heq : ge_ind _ _ _ _ _ = ge_ind _ _ _ _ _ |- _ => injection Heq as <- <- <- <- <- end.
    split; [ eapply ind_selfpath_decl; [ eassumption | eassumption | reflexivity |] | left; reflexivity ].
    match goal with Ho : ind_order_ok ?D, HM : ind_member ?D 0 = Some ?M, Hh : im_head ?M = mh_decl _ |- _ =>
      apply (proj1 (Ho _ _ HM)); unfold im_is_decl; rewrite Hh; reflexivity end.
  - (* a later member *)
    match goal with Heq : ge_ind _ _ _ _ _ = ge_ind _ _ _ _ _ |- _ => injection Heq as <- <- <- <- <- end.
    split; [ eapply ind_selfpath_decl; [ eassumption | eassumption | intros; lia | eassumption ] | right; assumption ].
  - (* a member with the body of its module *)
    match goal with Heq : ge_ind _ _ _ _ _ = ge_ind _ _ _ _ _ |- _ => injection Heq as <- <- <- <- <- end.
    match goal with IH : forall _ _ _, fk_ind _ _ _ = fk_ind _ _ _ -> _ |- _ => exact (IH _ _ _ eq_refl) end.
  - (* the module of a member, before its members *)
    match goal with Heq : fk_ind _ _ _ = fk_ind _ _ _ |- _ => injection Heq as <- <- <- end.
    match goal with IH : forall _ _ _ _ _, ge_ind _ _ _ _ _ = ge_ind _ _ _ _ _ -> _ |- _ => exact (IH _ _ _ _ _ eq_refl) end.
  - (* one more member of a module *)
    match goal with IH : forall _ _ _, ?K = fk_ind _ _ _ -> _, Heq : ?K = fk_ind _ _ _ |- _ => exact (IH _ _ _ Heq) end.
Qed.

(** The open frame of a member's module, in the stack. *)
Lemma gs_find_ind_split : forall Ξ p pq k D, gs_find_ind Ξ p = Some (pq, k, D) ->
    exists Ξ1 U Ξ0, Ξ = Ξ1 ++ (p, fk_ind pq k D, U) :: Ξ0 /\ gs_find_tele Ξ p = Some (U, nil, gs_tele Ξ0).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros * H; cbn in H; [ discriminate |].
  destruct (qname_strip mp p) as [[| ? ?] |] eqn:Hs; [| discriminate |].
  - destruct K as [| pq' k' D' | ]; [ discriminate | | discriminate ]; injection H as -> -> ->.
    pose proof Hs as Hs'; apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst.
    exists nil, U, Ξ; split; [ reflexivity | cbn; rewrite Hs'; reflexivity ].
  - destruct (IH _ _ _ _ H) as (Ξ1 & U' & Ξ0 & -> & Ht); exists ((mp, K, U) :: Ξ1), U', Ξ0.
    split; [ reflexivity | cbn; rewrite Hs; exact Ht ].
Qed.

(** The open frame of a record's module, in the stack. *)
Lemma gs_find_record_split : forall Ξ p R, gs_find_record Ξ p = Some R ->
    exists Ξ1 U Ξ0, Ξ = Ξ1 ++ (p, fk_record R, U) :: Ξ0 /\ gs_find_tele Ξ p = Some (U, nil, gs_tele Ξ0).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros * H; cbn in H; [ discriminate |].
  destruct (qname_strip mp p) as [[| ? ?] |] eqn:Hs; [| discriminate |].
  - destruct K as [| | R']; [ discriminate | discriminate |]; injection H as ->.
    pose proof Hs as Hs'; apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst.
    exists nil, U, Ξ; split; [ reflexivity | cbn; rewrite Hs'; reflexivity ].
  - destruct (IH _ _ H) as (Ξ1 & U' & Ξ0 & -> & Ht); exists ((mp, K, U) :: Ξ1), U', Ξ0.
    split; [ reflexivity | cbn; rewrite Hs; exact Ht ].
Qed.

(** The module of a member is over the group's uniform parameters, in an
    enclosing frame. *)
Lemma wf_gmod_ind_uparams : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
    forall pq k D, K = fk_ind pq k D -> ind_uparams D = Δ ++ gs_tele Ξ /\ Ξ <> nil.
Proof.
  induction 1; intros * HK; try discriminate; [ injection HK as -> -> ->; split; [ assumption | discriminate ] | eauto ].
Qed.

(** Below a well-formed stack's frames, a suffix is well formed, and what
    it reads the whole stack reads. *)
Lemma wf_gstack_app_inv : forall Θ Ξ1 Ξ0, ⊢ᵍ Θ ⍮ Ξ1 ++ Ξ0 -> ⊢ᵍ Θ ⍮ Ξ0 /\ gc_sub Θ Ξ0 Θ (Ξ1 ++ Ξ0).
Proof.
  intros Θ Ξ1; induction Ξ1 as [| [[mp K] U] Ξ1 IH]; intros Ξ0 H; cbn in *; [ split; [ exact H | apply gc_sub_refl ] |].
  destruct (wf_gstack_cons_inv _ _ _ _ _ H) as (H1 & _ & Hf); destruct (IH _ H1) as [H0 Hs].
  split; [ exact H0 | eapply gc_sub_trans; [ exact Hs | apply gc_sub_push; exact Hf ] ].
Qed.

(** The open frame of a member's module is at the member's own path. *)
Lemma frame_ind_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D, gs_find_ind Ξ p = Some (pq, k, D) ->
    ind_selfpath pq k D p.
Proof.
  intros * Hg * Hf; destruct (gs_find_ind_split _ _ _ _ _ Hf) as (Ξ1 & U & Ξ0 & -> & _).
  destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 _].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ -> HΦ] & _).
  exact (proj1 ((proj2 wf_gmod_kind) _ _ _ _ _ _ HΦ _ _ _ eq_refl)).
Qed.

(** The group an open frame's kind names is read where the frame is
    open. *)
Lemma frame_ind_lookup : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D, gs_find_ind Ξ p = Some (pq, k, D) ->
    ind_lookup Θ Ξ pq = Some D.
Proof.
  intros * Hg * Hf.
  destruct k as [| k].
  - rewrite (isp_group _ _ _ _ (frame_ind_selfpath _ _ Hg _ _ _ _ Hf) eq_refl), ind_lookup_unfold, ind_mlookup_unfold, Hf.
    reflexivity.
  - destruct (gs_find_ind_split _ _ _ _ _ Hf) as (Ξ1 & U & Ξ0 & HΞ & _); rewrite HΞ in Hg |- *.
    destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 Hs].
    destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ -> HΦ] & Hff).
    destruct (proj2 ((proj2 wf_gmod_kind) _ _ _ _ _ _ HΦ _ _ _ eq_refl)) as [Hk | Hl]; [ discriminate |].
    exact (ind_lookup_gc_sub _ _ _ _ _ _ (gc_sub_trans _ _ _ _ _ _ (gc_sub_push _ _ _ _ _ Hff) Hs) Hl).
Qed.

(** The open frame of a member's module is over the group's uniform
    parameters. *)
Lemma frame_ind_uparams : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D T Φ, gs_find_ind Ξ p = Some (pq, k, D) ->
    gc_frame Ξ p = Some (T, Φ) -> T = ind_uparams D.
Proof.
  intros * Hg * Hf Hfr; destruct (gs_find_ind_split _ _ _ _ _ Hf) as (Ξ1 & U & Ξ0 & HΞ & Ht).
  unfold gc_frame in Hfr; rewrite Ht in Hfr; rewrite HΞ in Hg.
  destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 _].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ0 -> HΦ] & _).
  injection Hfr as <- <-; symmetry; exact (proj1 (wf_gmod_ind_uparams _ _ _ _ _ _ HΦ _ _ _ eq_refl)).
Qed.

(** The open frame of a member's module is a member of the frame below it. *)
Lemma frame_ind_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p r, gs_find_ind Ξ p = Some r -> exists mq y, p = qname_in mq y.
Proof.
  intros * Hg * Hf; destruct r as [[pq k] D].
  destruct (gs_find_ind_split _ _ _ _ _ Hf) as (Ξ1 & U & Ξ0 & HΞ & _); rewrite HΞ in Hg.
  destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 _].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ0 -> HΦ] & Hff).
  destruct (wf_gmod_ind_uparams _ _ _ _ _ _ HΦ _ _ _ eq_refl) as [_ Hne].
  destruct Ξ0 as [| [[mq Kq] V] Ξ0]; [ contradiction |].
  destruct Hff as (x & -> & _); eauto.
Qed.

(** A member whose module's frame is open: the frame, its body so far
    where the member's path is located, and the member of the declaration
    the frame carries. *)
Lemma frame_ind_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D,
    gs_find_ind Ξ p = Some (pq, k, D) ->
    exists U T0 T Φ Mk, gs_find_tele Ξ p = Some (U, nil, T0) /\ gc_frame Ξ p = Some (T, Φ) /\
      gc_loc Θ Ξ p = Some (T, Φ) /\ ind_member D k = Some Mk.
Proof.
  intros * Hg * Hf.
  destruct (gs_find_ind_tele _ _ _ Hf) as (U & T0 & Ht).
  pose proof Ht as Ht'.
  destruct (gs_find_tele_body _ _ Hg _ _ _ _ Ht) as (Δ & Φ & ->).
  assert (Hfr : gc_frame Ξ p = Some (Δ ++ T0, Φ)) by (unfold gc_frame; rewrite Ht; reflexivity).
  pose proof (isp_decl _ _ _ _ (frame_ind_selfpath _ _ Hg _ _ _ _ Hf)) as Hk.
  pose proof (ind_ndecl_le D) as Hle.
  destruct (List.nth_error (ind_members D) k) as [Mk |] eqn:Hm;
    [| apply List.nth_error_None in Hm; lia ].
  do 5 eexists; split; [ exact Ht' |].
  split; [ exact Hfr | split; [ unfold gc_loc; rewrite Hfr; reflexivity | exact Hm ] ].
Qed.

(** The module of a record type is over the record's parameters and then
    a value of it, in an enclosing frame. *)
Lemma wf_gmod_record_params : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
    forall R, K = fk_record R ->
    exists Δr, Δ = ce_ass (record_self mp R) :: Δr /\ record_params R = Δr ++ gs_tele Ξ /\ Ξ <> nil.
Proof.
  induction 1; intros * HK; try discriminate; [ injection HK as ->; eexists; split; [ reflexivity | split; [ assumption | discriminate ] ] | eauto ].
Qed.

(** The open frame of a record's module is a member of an enclosing
    frame. *)
Lemma frame_record_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p R, gs_find_record Ξ p = Some R -> exists mq y, p = qname_in mq y.
Proof.
  intros * Hg * Hf.
  destruct (gs_find_record_split _ _ _ Hf) as (Ξ1 & U & Ξ0 & HΞ & _); rewrite HΞ in Hg.
  destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 _].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ0 -> HΦ] & Hff).
  destruct (wf_gmod_record_params _ _ _ _ _ _ HΦ _ eq_refl) as (_ & _ & _ & Hne).
  destruct Ξ0 as [| [[mq Kq] V] Ξ0]; [ contradiction |].
  destruct Hff as (x & -> & _); eauto.
Qed.

(** A record whose module's frame is open: the frame, its body so far
    where the record's path is located. *)
Lemma frame_record_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p R,
    gs_find_record Ξ p = Some R ->
    exists U T0 T Φ, gs_find_tele Ξ p = Some (U, nil, T0) /\ gc_frame Ξ p = Some (T, Φ) /\ gc_loc Θ Ξ p = Some (T, Φ).
Proof.
  intros * Hg * Hf.
  destruct (gs_find_record_tele _ _ _ Hf) as (U & T0 & Ht).
  pose proof Ht as Ht'.
  destruct (gs_find_tele_body _ _ Hg _ _ _ _ Ht) as (Δ & Φ & ->).
  assert (Hfr : gc_frame Ξ p = Some (Δ ++ T0, Φ)) by (unfold gc_frame; rewrite Ht; reflexivity).
  do 4 eexists; split; [ exact Ht' | split; [ exact Hfr | unfold gc_loc; rewrite Hfr; reflexivity ] ].
Qed.

(** ** What a Module Expression Denotes Is Unique *)

(** The parent of an open frame named [y] is an open frame, in which [y]
    is fresh. *)
Lemma frame_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y U T0,
    gs_find_tele Ξ (qname_in mq y) = Some (U, nil, T0) ->
    exists T' Φ', gc_frame Ξ mq = Some (T', Φ') /\ gm_fresh y Φ'.
Proof.
  intros * Hg * Ef.
  destruct (gs_find_tele_frame _ _ Hg _ _ _ Ef) as [(Hc & _) | (c & y' & V & T1 & Hc & HV & Hy & _)];
    cbn in Hc; [ destruct (q_chain mq); discriminate |].
  apply List.app_inj_tail in Hc as [<- <-].
  destruct (gs_find_tele_body _ _ Hg _ _ _ _ HV) as (Δv & Φv & ->).
  cbn [q_unit qname_in] in HV; replace (q_abs (q_unit mq) (q_chain mq)) with mq in HV by (destruct mq; reflexivity).
  exists (Δv ++ T1), Φv; split; [ unfold gc_frame; rewrite HV; reflexivity | exact Hy ].
Qed.

(** A unit's path is no member's module: what it denotes is the unit. *)
Lemma mdenote_unit_inv : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ fp R, mdenote Θ Ξ Γ (me_unit fp) R ->
    exists T Φ, gc_unit Θ Ξ (me_unit fp) = Some (T, Φ) /\ R = ds_closed nil (q_abs fp nil) T Φ nil.
Proof.
  intros * Hg * Hm; inversion Hm as [? ? ? T Φ Hq Hu | ? ? ? ? ? ? ? ? ? Hq Hk | | | | | ? ? ? ? ? ? Hq Hk]; subst.
  - cbn in Hq; injection Hq as <-; eauto.
  - exfalso; cbn in Hq; injection Hq as <-.
    destruct (frame_ind_parent _ _ Hg _ _ Hk) as (mq & y & Hy).
    apply (f_equal q_chain) in Hy; cbn in Hy; exact (app_cons_not_nil _ _ _ Hy).
  - exfalso; cbn in Hq; injection Hq as <-.
    destruct (frame_record_parent _ _ Hg _ _ Hk) as (mq & y & Hy).
    apply (f_equal q_chain) in Hy; cbn in Hy; exact (app_cons_not_nil _ _ _ Hy).
Qed.

(** The frames outside an open frame named [y] are its parent's
    telescope. *)
Lemma frame_child_outer : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y U T0 Tq Φq,
    gs_find_tele Ξ (qname_in mq y) = Some (U, nil, T0) -> gc_frame Ξ mq = Some (Tq, Φq) -> T0 = Tq.
Proof.
  intros * Hg * Ef Hfq; unfold gc_frame in Hfq.
  destruct (gs_find_tele_frame _ _ Hg _ _ _ Ef) as [(Hc & _) | (c & y' & V & T1 & Hc & HV & _ & ->)];
    cbn in Hc; [ destruct (q_chain mq); discriminate |].
  apply List.app_inj_tail in Hc as [<- <-].
  cbn [q_unit qname_in] in HV; replace (q_abs (q_unit mq) (q_chain mq)) with mq in HV by (destruct mq; reflexivity).
  rewrite HV in Hfq; destruct V as [Δv [[|] Φv | Ev]]; try discriminate; injection Hfq as <- _; reflexivity.
Qed.

(** The open frame of a record's module: its parameters, the record's own
    and then a value of it, over the frames outside it. *)
Lemma frame_record_split : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p R U T0, gs_find_record Ξ p = Some R ->
    gs_find_tele Ξ p = Some (U, nil, T0) ->
    exists Δr, gu_params U = ce_ass (record_self p R) :: Δr /\ record_params R = Δr ++ T0.
Proof.
  intros * Hg * Hf Ht; destruct (gs_find_record_split _ _ _ Hf) as (Ξ1 & U' & Ξ0 & HΞ & Ht').
  rewrite Ht in Ht'; injection Ht' as -> ->.
  rewrite HΞ in Hg; destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 _].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ0 -> HΦ] & _).
  destruct (wf_gmod_record_params _ _ _ _ _ _ HΦ _ eq_refl) as (Δr & -> & HP & _).
  exists Δr; split; [ reflexivity | exact HP ].
Qed.

Lemma frame_child_tele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y Tx Φx Tq Φq,
    gc_frame Ξ (qname_in mq y) = Some (Tx, Φx) -> gc_frame Ξ mq = Some (Tq, Φq) -> exists Δ, Tx = Δ ++ Tq.
Proof.
  intros * Hg * Hfx Hfq; unfold gc_frame in Hfx, Hfq.
  destruct (gs_find_tele Ξ (qname_in mq y)) as [[[[Δx [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
  injection Hfx as <- _.
  destruct (gs_find_tele_frame _ _ Hg _ _ _ Ef) as [(Hc & _) | (c & y' & V & T1 & Hc & HV & _ & ->)];
    cbn in Hc; [ destruct (q_chain mq); discriminate |].
  apply List.app_inj_tail in Hc as [<- <-].
  cbn [q_unit qname_in] in HV; replace (q_abs (q_unit mq) (q_chain mq)) with mq in HV by (destruct mq; reflexivity).
  rewrite HV in Hfq; destruct V as [Δv [[|] Φv | Ev]]; try discriminate; injection Hfq as <- _.
  exists Δx; reflexivity.
Qed.

(** An open frame inside another: its parent is an open frame, of any
    kind, in which its name is fresh. *)
Lemma gc_unit_mem_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H0 y T Φ,
    gc_unit Θ Ξ (me_mem H0 y) = Some (T, Φ) ->
    exists mq T' Φ', mod_qname H0 = Some mq /\ gc_frame Ξ mq = Some (T', Φ') /\ gm_fresh y Φ'.
Proof.
  intros * Hg * Hu.
  destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hl | (_ & Hc & _)]); cbn in Hq;
    destruct (mod_qname H0) as [mq |] eqn:Hq0; try discriminate; injection Hq as <-; cbn in *.
  - unfold gc_frame in Hl.
    change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y) in Hl.
    destruct (gs_find_tele Ξ (qname_in mq y)) as [[[U [| ? ?]] T0] |] eqn:Ef;
      try (destruct U as [? [[|] ? | ?]]); try discriminate.
    destruct (frame_parent _ _ Hg _ _ _ _ Ef) as (T' & Φ' & Hf & Hy); exists mq, T', Φ'; auto.
  - destruct (q_chain mq); discriminate.
Qed.

(** An open frame that is the module of no member and of no record type
    is a unit. *)
Lemma gc_unit_frame : forall Θ Ξ H mq T Φ, mod_qname H = Some mq -> gc_frame Ξ mq = Some (T, Φ) ->
    gs_find_ind Ξ mq = None -> gs_find_record Ξ mq = None -> gc_unit Θ Ξ H = Some (T, Φ).
Proof.
  intros * Hq Hf Hk Hr; unfold gc_unit, gc_frame in *; rewrite Hq.
  destruct (gs_find_tele Ξ mq) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |]; try discriminate; rewrite Hk, Hr; exact Hf.
Qed.

(** A loaded unit or an open frame is the module of no record type. *)
Lemma gc_unit_not_record : forall Θ Ξ H mq T Φ, mod_qname H = Some mq -> gc_unit Θ Ξ H = Some (T, Φ) ->
    gs_find_record Ξ mq = None.
Proof.
  intros * Hq Hu; unfold gc_unit in Hu; rewrite Hq in Hu.
  destruct (gs_find_tele Ξ mq) as [[[U [| ? ?]] T0] |] eqn:Ef.
  - destruct U as [? [[|] ? | ?]], (gs_find_ind Ξ mq), (gs_find_record Ξ mq); congruence.
  - apply gs_find_record_none; intros ? ? Hc; congruence.
  - apply gs_find_record_none; intros ? ? Hc; congruence.
Qed.

(** A loaded unit or an open frame is the module of no member. *)
Lemma gc_unit_not_ind : forall Θ Ξ H mq T Φ, mod_qname H = Some mq -> gc_unit Θ Ξ H = Some (T, Φ) ->
    gs_find_ind Ξ mq = None.
Proof.
  intros * Hq Hu; unfold gc_unit in Hu; rewrite Hq in Hu.
  destruct (gs_find_tele Ξ mq) as [[[U [| ? ?]] T0] |] eqn:Ef.
  - destruct U as [? [[|] ? | ?]], (gs_find_ind Ξ mq); congruence.
  - apply gs_find_ind_none; intros ? ? Hc; congruence.
  - apply gs_find_ind_none; intros ? ? Hc; congruence.
Qed.

(** What the path of a loaded unit, of an open frame, or of the open frame
    of a member's or a record's module denotes: its stored unit, the
    member, or the record type. *)
Lemma frame_denote_unique : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H Γ R p,
    mod_qname H = Some p -> mdenote Θ Ξ Γ H R ->
    (forall T Φ, gc_unit Θ Ξ H = Some (T, Φ) -> R = ds_closed nil p T Φ nil) /\
    (forall pq k D Mk T Φ, gs_find_ind Ξ p = Some (pq, k, D) -> ind_member D k = Some Mk ->
       gc_loc Θ Ξ p = Some (T, Φ) -> R = ind_former_desc pq k D Mk (ds_closed nil p T Φ nil)) /\
    (forall Rr T Φ, gs_find_record Ξ p = Some Rr ->
       gc_loc Θ Ξ p = Some (T, Φ) -> R = record_former_desc p Rr (ds_closed nil p T Φ nil)).
Proof.
  intros Θ Ξ Hg; induction H as [fp | x | H0 IH y | H0 IH N | U]; intros * Hq Hm; inversion Hm; subst;
    try (cbn in Hq; discriminate).
  (* a unit *)
  all: try match goal with Hu' : gc_unit _ _ ?H = Some _, Hq' : mod_qname ?H = Some _ |- _ =>
         rewrite Hq in Hq'; injection Hq' as <-;
         split; [ intros T0 Φ0 Hu; rewrite Hu in Hu'; injection Hu' as <- <-; reflexivity |];
         split; [ intros * Hk; rewrite (gc_unit_not_ind _ _ _ _ _ _ Hq Hu') in Hk; discriminate
                | intros * Hk; rewrite (gc_unit_not_record _ _ _ _ _ _ Hq Hu') in Hk; discriminate ] end.
  (* the open frame of a member's module *)
  all: try match goal with Hk' : gs_find_ind _ ?p' = Some _, Hq' : mod_qname _ = Some ?p' |- _ =>
         rewrite Hq in Hq'; injection Hq' as <-;
         split; [ intros ? ? Hu; rewrite (gc_unit_not_ind _ _ _ _ _ _ Hq Hu) in Hk'; discriminate |];
         split; [ intros * Hk HMk Hl; rewrite Hk in Hk'; injection Hk' as <- <- <-; congruence
                | intros * Hk; rewrite (gs_find_ind_not_record _ _ _ Hk') in Hk; discriminate ] end.
  (* the open frame of a record's module *)
  all: try match goal with Hk' : gs_find_record _ ?p' = Some _, Hq' : mod_qname _ = Some ?p' |- _ =>
         rewrite Hq in Hq'; injection Hq' as <-;
         split; [ intros ? ? Hu; rewrite (gc_unit_not_record _ _ _ _ _ _ Hq Hu) in Hk'; discriminate |];
         split; [ intros * Hk; rewrite (gs_find_ind_not_record _ _ _ Hk) in Hk'; discriminate
                | intros * Hk Hl; rewrite Hk in Hk'; injection Hk' as <-; congruence ] end.
  (* a selection [H0.y]: no frame is at its path, as [y] is fresh in the frame at [H0]'s *)
  cbn in Hq; destruct (mod_qname H0) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y).
  assert (Hno : forall U T0, gs_find_tele Ξ (qname_in mq y) = Some (U, nil, T0) -> False).
  { intros U T0 Ef; destruct (frame_parent _ _ Hg _ _ _ _ Ef) as (T' & Φ' & Hf & Hy).
    match goal with H1 : mdenote _ _ _ H0 ?R0, Hmd : ds_mod ?R0 = Some _, He : ds_entry _ _ = Some _ |- _ =>
      destruct (IH _ _ _ eq_refl H1) as (IH1 & IH2 & IH3);
      destruct (gs_find_ind Ξ mq) as [[[pq k] D] |] eqn:Hk;
      [ destruct (frame_ind_loc _ _ Hg _ _ _ _ Hk) as (U2 & T02 & T2 & Φ2 & Mk2 & Ht2 & Hf2 & Hl2 & HMk2);
        rewrite (IH2 _ _ _ _ _ _ eq_refl HMk2 Hl2) in Hmd; cbn [ind_former_desc ds_mod] in Hmd;
        rewrite Hf in Hf2; injection Hf2 as <- <-
      | destruct (gs_find_record Ξ mq) as [Rr |] eqn:Hr;
        [ destruct (frame_record_loc _ _ Hg _ _ Hr) as (U2 & T02 & T2 & Φ2 & Ht2 & Hf2 & Hl2);
          rewrite (IH3 _ _ _ eq_refl Hl2) in Hmd; cbn [record_former_desc ds_mod] in Hmd;
          rewrite Hf in Hf2; injection Hf2 as <- <-
        | rewrite (IH1 _ _ (gc_unit_frame _ _ _ _ _ _ Hq0 Hf Hk Hr)) in Hmd; cbn in Hmd ] ];
      injection Hmd as <-; cbn in He; rewrite (gm_prefix_upto_fresh _ _ Hy) in He; discriminate
    end. }
  split; [| split ].
  - intros T Φ Hu; exfalso; unfold gc_unit in Hu; cbn [mod_qname] in Hu; rewrite Hq0 in Hu.
    change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y) in Hu.
    destruct (gs_find_tele Ξ (qname_in mq y)) as [[[U [| ? ?]] T0] |] eqn:Ef; try discriminate; [ exact (Hno _ _ eq_refl) |].
    cbn in Hu; destruct (q_chain mq); discriminate.
  - intros * Hk; exfalso; destruct (gs_find_ind_tele _ _ _ Hk) as (U' & T0' & Ef); exact (Hno _ _ Ef).
  - intros * Hk; exfalso; destruct (gs_find_record_tele _ _ _ Hk) as (U' & T0' & Ef); exact (Hno _ _ Ef).
Qed.

Lemma unit_denote_unique : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H Γ R p T Φ,
    mod_qname H = Some p -> gc_unit Θ Ξ H = Some (T, Φ) -> mdenote Θ Ξ Γ H R -> R = ds_closed nil p T Φ nil.
Proof. intros * Hg * Hq Hu Hm; exact (proj1 (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm) _ _ Hu). Qed.

Theorem mdenote_functional_all : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> forall R', mdenote Θ Ξ Γ H R' -> R = R') /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> forall R', udenote Θ Ξ Γ o U R' -> R = R') /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> forall R', edenote Θ Ξ Γ o E R' -> R = R') /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall Φx', body_xp Θ Ξ Γ Φ Φx' -> Φx = Φx') /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> forall gs', items_gen Θ Ξ Γ H its gs' -> gs = gs').
Proof.
  intros Θ Ξ Hg; apply mdenote_all_ind.
  - intros * Hq Hu R' Hm'; symmetry; exact (unit_denote_unique _ _ Hg _ _ _ _ _ _ Hq Hu Hm').
  - intros * Hq Hk HMk Hl R' Hm'; symmetry;
      exact (proj1 (proj2 (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm')) _ _ _ _ _ _ Hk HMk Hl).
  - intros * Hl Hu IH R' Hm'; inversion Hm'; subst; try (cbn in *; discriminate).
    match goal with Hl' : _ ∋ # _ ≔ₘ _ |- _ => rewrite (ctx_lookup_mod_functional _ _ _ _ Hl Hl') in IH end; eauto.
  - intros * Hu IH R' Hm'; inversion Hm'; subst; try (cbn in *; discriminate); eauto.
  - intros * Hm IH Ha R' Hm'; inversion Hm'; subst; try (cbn in *; discriminate).
    match goal with H1 : mdenote _ _ _ H _ |- _ => rewrite <- (IH _ H1) in * end; congruence.
  - intros * Hm IH Hmd He Hed IHe Hr R' Hm'; inversion Hm'; subst.
    + match goal with Hu' : gc_unit _ _ _ = Some _, Hq' : mod_qname _ = Some _ |- _ =>
        exact (unit_denote_unique _ _ Hg _ _ _ _ _ _ Hq' Hu' ltac:(eapply dn_mem; eassumption)) end.
    + match goal with Hk' : gs_find_ind _ _ = Some _, HMk' : ind_member _ _ = Some _,
                      Hl' : gc_loc _ _ _ = Some _, Hq' : mod_qname _ = Some _ |- _ =>
        exact (proj1 (proj2 (frame_denote_unique _ _ Hg _ _ _ _ Hq' ltac:(eapply dn_mem; eassumption))) _ _ _ _ _ _
                 Hk' HMk' Hl') end.
    + match goal with H1 : mdenote _ _ _ H _ |- _ => rewrite <- (IH _ H1) in * end.
      match goal with H1 : ds_mod R0 = _ |- _ => rewrite Hmd in H1; injection H1 as <- end.
      match goal with H1 : ds_entry R0m y = _ |- _ => rewrite He in H1; injection H1 as <- <- <- end.
      match goal with H1 : edenote _ _ _ _ _ _ |- _ => rewrite <- (IHe _ H1) in * end.
      congruence.
    + match goal with Hk' : gs_find_record _ _ = Some _,
                      Hl' : gc_loc _ _ _ = Some _, Hq' : mod_qname _ = Some _ |- _ =>
        exact (proj2 (proj2 (frame_denote_unique _ _ Hg _ _ _ _ Hq' ltac:(eapply dn_mem; eassumption))) _ _ _
                 Hk' Hl') end.
  - intros * Hq Hk Hl R' Hm'; symmetry;
      exact (proj2 (proj2 (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm')) _ _ _ Hk Hl).
  - intros * Hx IH Hb R' Hu'; inversion Hu'; subst.
    match goal with H1 : body_xp _ _ _ _ _ |- _ => rewrite <- (IH _ H1) in * end; congruence.
  - intros * Hm IH Hmd R' Hu'; inversion Hu'; subst.
    match goal with H1 : mdenote _ _ _ _ _ |- _ => rewrite <- (IH _ H1) in * end; congruence.
  - intros * He; inversion He; reflexivity.
  - intros * Hu IH R' He; inversion He; subst; eauto.
  - intros * HMk Hpm Hl R' He; inversion He; subst; congruence.
  - intros * Hu IH R' He; inversion He; subst; f_equal; eauto.
  - intros * Hl R' He; inversion He; subst; congruence.
  - intros * Hx; inversion Hx; reflexivity.
  - intros * Hx IH Φx' Hx'; inversion Hx'; subst; f_equal; eauto.
  - intros * Hx IH Hm IHm Hmd Hgn IHg Hok Φx' Hx'; inversion Hx'; subst.
    match goal with H1 : body_xp _ _ _ Φ _ |- _ => pose proof (IH _ H1) as E; subst end.
    match goal with H1 : items_gen _ _ _ _ _ _ |- _ => rewrite (IHg _ H1) end; reflexivity.
  - intros * Hg'; inversion Hg'; reflexivity.
  - (* the module itself, by an alias *)
    intros * Hgn IH gs' Hg'; inversion Hg'; subst; f_equal; eauto.
  - intros * Hm IHm Hgn IH gs' Hg'; inversion Hg'; subst;
      match goal with H1 : mdenote _ _ _ (me_mem _ _) _ |- _ => pose proof (IHm _ H1) as E end;
      try discriminate E; try (subst; contradiction); try (subst; cbn in *; discriminate).
    injection E as <- <-; f_equal; eauto.
  - intros * Hm IHm Hk Hgn IH gs' Hg'; inversion Hg'; subst;
      match goal with H1 : mdenote _ _ _ (me_mem _ _) _ |- _ => pose proof (IHm _ H1) as E end; subst;
      try (cbn in Hk; contradiction);
      try (match goal with Ht : ds_ty ?R1 = Some _ |- _ => destruct R1; cbn in Hk, Ht; first [ contradiction | discriminate ] end).
    f_equal; eauto.
  - (* a member with a term part and a module part *)
    intros * Hm IHm Hty Hmd Hgn IH gs' Hg'; inversion Hg'; subst;
      match goal with H1 : mdenote _ _ _ (me_mem _ _) _ |- _ =>
        assert_fails (constr_eq H1 Hm); pose proof (IHm _ H1) as E end; subst.
    + cbn in Hmd; discriminate.
    + match goal with Hk : ds_is_mod ?R1 |- _ => destruct R1; cbn in Hk, Hty; first [ contradiction | discriminate ] end.
    + f_equal; [ f_equal; congruence | eauto ].
Qed.

(** ** Bodies Stored at Paths Are What Paths Denote *)

(** Where a body module that is not the module of an inductive type or of
    a record type is stored: an open frame of a module, or a closed
    module. *)
Definition loc_mod (Θ : gdeps) (Ξ : gstack) (p : qname) (T : ctx) (Φ : gmod) : Prop :=
  (gc_frame Ξ p = Some (T, Φ) /\ gs_find_ind Ξ p = None /\ record_lookup Θ Ξ p = None) \/
  (gc_body Θ Ξ p = Some (T, Φ) /\ gc_module Θ Ξ p = Some (mr_body T None) /\ record_lookup Θ Ξ p = None).

Lemma loc_mod_loc : forall Θ Ξ p T Φ, loc_mod Θ Ξ p T Φ -> loc Θ Ξ p T Φ.
Proof. intros * [[H _] | [H _]]; [ left | right ]; exact H. Qed.

(** What a body stored at a path is, as the path denotes it: the type
    former of the member or the record type whose module it is, with the
    body as its module part; or the stored module itself. *)
Definition loc_desc (Θ : gdeps) (Ξ : gstack) (p : qname) (T : ctx) (Φ : gmod) (R : mdesc) : Prop :=
  match ind_mlookup Θ Ξ p with
  | Some (pq, k, D) => exists Mk, ind_member D k = Some Mk /\ R = ind_former_desc pq k D Mk (ds_closed nil p T Φ nil)
  | None =>
      match record_lookup Θ Ξ p with
      | Some Rr => R = record_former_desc p Rr (ds_closed nil p T Φ nil)
      | None => R = ds_closed nil p T Φ nil
      end
  end.

(** The frame a lookup reads in is found at its own path. *)
Lemma gs_find_tele_found : forall Ξ p U ip T, gs_find_tele Ξ p = Some (U, ip, T) ->
    exists F, qname_strip F p = Some ip /\ gs_find_tele Ξ F = Some (U, nil, T).
Proof.
  induction Ξ as [| [[mf Kf'] V] Ξ IH]; intros * Hf; cbn in Hf |- *; [ discriminate |].
  destruct (qname_strip mf p) as [r |] eqn:Hs.
  - injection Hf as <- <- <-; exists mf; split; [ exact Hs | rewrite qname_strip_refl; reflexivity ].
  - destruct (IH _ _ _ _ Hf) as (F & HF & HFf); exists F; split; [ exact HF |].
    destruct (qname_strip mf F) as [r |] eqn:Hr; [| exact HFf ].
    exfalso; apply qname_strip_app_inv in Hr, HF; subst; rewrite qname_app_app, qname_strip_app in Hs; discriminate.
Qed.

(** A path read at a frame's own path is that frame's. *)
Lemma gs_find_tele_own : forall Ξ pf U T, gs_find_tele Ξ pf = Some (U, nil, T) -> exists K, List.In (pf, K, U) Ξ.
Proof.
  induction Ξ as [| [[mf Kf] V] Ξ IH]; intros * Hf; cbn in Hf; [ discriminate |].
  destruct (qname_strip mf pf) as [r |] eqn:Hs.
  - injection Hf as HU Hr HT; subst; exists Kf; left.
    apply qname_strip_app_inv in Hs; rewrite qname_app_nil in Hs; subst; reflexivity.
  - destruct (IH _ _ _ Hf) as (K & Hin); exists K; right; exact Hin.
Qed.

(** A body module that is the module of no member: a submodule, or the
    module of a record type. *)
Lemma gm_subbody_entry_inv : forall Φ T x T' Φ',
    gm_subbody T Φ x nil = Some (T', Φ') -> gm_submodule T Φ x nil = Some (mr_body T' None) ->
    (exists pv Δ sm, gm_entry Φ (x :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) /\ T' = Δ ++ T) \/
    (exists pv pr R, gm_entry Φ (x :: nil) = Some (ge_record pv pr R Φ') /\ T' = record_mod_tele pr R).
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hb Hm; cbn in Hb, Hm |- *; [ discriminate | | eauto ].
  destruct (String.eqb x z); [| eauto ].
  destruct E as [? ? ? ? | pv [Δ [sm Φ0 | E0]] | ? ? D Φ0 | ? Δa pa Nsa | pv pr Rr Φ0]; try discriminate.
  - injection Hb as <- <-; left; eauto.
  - injection Hb as <- <-; right; eauto.
Qed.

Lemma body_closed_entry_mod : forall Φ k y pv Δ sm Φ',
    body_closed k Φ -> gm_entry Φ (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm Φ'))) -> sm = sm_closed.
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc He; cbn in Hc, He; [ discriminate | | contradiction ].
  destruct Hc as [Hc HE]; destruct (String.eqb y z); [ injection He as ->; exact (proj1 HE) | eauto ].
Qed.

(** A module below a path is read in the body stored at the path: an open
    frame, or a body module, perhaps of an inductive type. *)
Lemma parent_loc_any : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y T Φ oDy,
    gc_body Θ Ξ (qname_in mq y) = Some (T, Φ) -> gc_module Θ Ξ (qname_in mq y) = Some (mr_body T oDy) ->
    exists Tq Φq, loc Θ Ξ mq Tq Φq /\ gm_subbody Tq Φq y nil = Some (T, Φ) /\ gm_submodule Tq Φq y nil = Some (mr_body T oDy).
Proof.
  intros * Hg * Hb Hm.
  assert (Hent : forall Tq Φq, loc Θ Ξ mq Tq Φq -> gm_subbody Tq Φq y nil = Some (T, Φ) ->
                   gm_submodule Tq Φq y nil = Some (mr_body T oDy) ->
                   exists (_ _ : unit), loc Θ Ξ mq Tq Φq /\ gm_subbody Tq Φq y nil = Some (T, Φ) /\
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
      destruct (Hent Tq Φq) as (pv & Δ & Hl & He & HT); [| exact Hby | exact Hm |].
      { right; unfold gc_body; rewrite Efq; exact Hbq. }
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
        unfold gc_body; rewrite Ef0; cbn; rewrite El; reflexivity. }
      exists (gu_params Uf), (gu_mod Uf); auto.
    + rewrite Hmy in Hm.
      pose proof (gs_find_tele_filed _ _ Hg {| q_unit := q_unit mq; q_chain := nil |} _ El (x :: ip)) as Ef0.
      assert (Hmq : mq = qname_app {| q_unit := q_unit mq; q_chain := nil |} (x :: ip)) by (destruct mq; cbn in *; subst; reflexivity).
      rewrite <- Hmq in Ef0.
      destruct (Hent Tq Φq) as (pv & Δ & Hl & He & HT); [| exact Hby | exact Hm |].
      { right; unfold gc_body; rewrite Ef0; cbn; rewrite El, Hc; exact Hbq. }
      exists Tq, Φq; auto.
Qed.

Lemma parent_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y T Φ,
    gc_body Θ Ξ (qname_in mq y) = Some (T, Φ) -> gc_module Θ Ξ (qname_in mq y) = Some (mr_body T None) ->
    record_lookup Θ Ξ (qname_in mq y) = None ->
    exists Tq Φq pv Δ, loc Θ Ξ mq Tq Φq /\
      gm_entry Φq (y :: nil) = Some (ge_mod pv (gu_mk Δ (md_body sm_closed Φ))) /\ T = Δ ++ Tq.
Proof.
  intros * Hg * Hb Hm Hr.
  destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hm) as (Tq & Φq & Hl & Hb' & Hm').
  destruct (gm_subbody_entry_inv _ _ _ _ _ Hb' Hm') as [(pv & Δ & sm & He & ->) | (pv & pr & R & He & _)].
  - pose proof (proj2 (loc_closed _ _ Hg _ _ _ Hl)) as Hc.
    rewrite (body_closed_entry_mod _ _ _ _ _ _ _ Hc He) in He; eauto 7.
  - exfalso; apply (proj2 (loc_entry _ _ Hg _ _ _ Hl _ _)) in He.
    unfold record_lookup in Hr; rewrite (gc_entry_record_frame_none _ _ _ _ He), He in Hr; discriminate.
Qed.

(** Filed units are body units. *)
Lemma wf_gds_body : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall fp U, gds_lookup Θ fp = Some U -> exists Δ Φ, U = gu_body Δ Φ.
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Kp Δ Φ HΞ IH HΦ Hff]; intros fp U Hl; cbn in Hl; [ discriminate | | eauto ].
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

(** ** An Inductive Type Is Stored at its Own Path *)

(** [gm_selfpath p Φ]: every inductive member and every record type filed
    in the body [Φ], stored at [p], is stored at its own path. *)
Definition gm_selfpath (p : qname) (Φ : gmod) : Prop :=
  (forall ip pv pq k D Φ', gm_entry Φ ip = Some (ge_ind pv pq k D Φ') -> ind_selfpath pq k D (qname_app p ip)) /\
  (forall ip pv pr R Φ', gm_entry Φ ip = Some (ge_record pv pr R Φ') -> pr = qname_app p ip).

Lemma gm_selfpath_nil : forall p, gm_selfpath p gm_nil.
Proof. intros p; split; intros ip * H; destruct ip; discriminate. Qed.

Lemma gm_selfpath_ext : forall p Φ x E, gm_selfpath p Φ ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> ind_selfpath pq k D (qname_in p x)) ->
    (forall pv pr R Φ', E = ge_record pv pr R Φ' -> pr = qname_in p x) ->
    (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_selfpath (qname_in p x) Φ') ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> gm_selfpath (qname_in p x) Φ') ->
    (forall pv pr R Φ', E = ge_record pv pr R Φ' -> gm_selfpath (qname_in p x) Φ') ->
    gm_selfpath p (Φ ⊳ x ↦ E).
Proof.
  intros * [HΦi HΦr] HE HER HM HI HR; split; intros ip * He; cbn in He.
  - destruct ip as [| y ip]; [ discriminate |].
    destruct (String.eqb_spec y x) as [-> |]; [| exact (HΦi _ _ _ _ _ _ He) ].
    rewrite <- qname_app_in.
    destruct ip as [| z ip']; [ injection He as ->; rewrite qname_app_nil; eapply HE; reflexivity |].
    destruct E as [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ? ?]; try discriminate.
    + eapply (proj1 (HM _ _ _ _ eq_refl)); exact He.
    + eapply (proj1 (HI _ _ _ _ _ eq_refl)); exact He.
    + eapply (proj1 (HR _ _ _ _ eq_refl)); exact He.
  - destruct ip as [| y ip]; [ discriminate |].
    destruct (String.eqb_spec y x) as [-> |]; [| exact (HΦr _ _ _ _ _ He) ].
    rewrite <- qname_app_in.
    destruct ip as [| z ip']; [ injection He as ->; rewrite qname_app_nil; eapply HER; reflexivity |].
    destruct E as [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ? ?]; try discriminate.
    + eapply (proj2 (HM _ _ _ _ eq_refl)); exact He.
    + eapply (proj2 (HI _ _ _ _ _ eq_refl)); exact He.
    + eapply (proj2 (HR _ _ _ _ eq_refl)); exact He.
Qed.

Lemma wf_gmod_selfpath :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E ->
     (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> ind_selfpath pq k D mp /\ gm_selfpath mp Φ') /\
     (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_selfpath mp Φ') /\
     (forall pv pr R Φ', E = ge_record pv pr R Φ' -> pr = mp /\ gm_selfpath mp Φ')) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
     gm_selfpath mp Φ /\ (forall pq k D, K = fk_ind pq k D -> ind_selfpath pq k D mp)).
Proof.
  apply global_wf_mut_ind; intros.
  all: try solve [ split; [| split ]; intros * Heq; discriminate ].
  (* a record, before the members of its module, and with its body *)
  all: try solve [ split; [| split ]; intros * Heq; try discriminate;
                   lazymatch type of Heq with ge_record _ _ _ _ = _ => idtac end; injection Heq as <- <- <- <-;
                   split; [ reflexivity |];
                   first [ apply gm_selfpath_nil | match goal with IH : gm_selfpath _ _ /\ _ |- _ => exact (proj1 IH) end ] ].
  (* the module of a record, before its members *)
  all: try solve [ split; [ apply gm_selfpath_nil | intros * Heq; discriminate ] ].
  - (* a nested module *)
    split; [| split ]; intros * Heq; [ discriminate | injection Heq as <- <- <- <-; match goal with IH : _ /\ _ |- _ => exact (proj1 IH) end
                                    | discriminate ].
  - (* the first member of a group, before the members of its module *)
    split; [| split ]; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate | discriminate ].
    split; [ eapply ind_selfpath_decl; [ eassumption | eassumption | reflexivity |] | apply gm_selfpath_nil ].
    match goal with Ho : ind_order_ok ?D, HM : ind_member ?D 0 = Some ?M, Hh : im_head ?M = mh_decl _ |- _ =>
      apply (proj1 (Ho _ _ HM)); unfold im_is_decl; rewrite Hh; reflexivity end.
  - (* a later member, before the members of its module *)
    split; [| split ]; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate | discriminate ].
    split; [ eapply ind_selfpath_decl; [ eassumption | eassumption | intros; lia | eassumption ] | apply gm_selfpath_nil ].
  - (* a member with the body of its module *)
    split; [| split ]; intros * Heq; [| discriminate | discriminate ]; injection Heq as <- <- <- <- <-.
    match goal with IH : gm_selfpath _ _ /\ _ |- _ => destruct IH as [HΦ HK] end.
    split; [ exact (HK _ _ _ eq_refl) | exact HΦ ].
  - (* the module of a member, before its members *)
    split; [ apply gm_selfpath_nil | intros * Heq; injection Heq; intros; subst ].
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => exact (proj1 (proj1 IH _ _ _ _ _ eq_refl)) end.
  - (* an entry *)
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => rename IH into H2 end.
    match goal with IH : gm_selfpath _ _ /\ _ |- _ => destruct IH as [HΦ HK] end.
    split; [| exact HK ].
    apply gm_selfpath_ext; [ assumption | | | | |].
    + intros * ->; exact (proj1 (proj1 H2 _ _ _ _ _ eq_refl)).
    + intros * ->; exact (proj1 (proj2 (proj2 H2) _ _ _ _ eq_refl)).
    + intros * ->; exact (proj1 (proj2 H2) _ _ _ _ eq_refl).
    + intros * ->; exact (proj2 (proj1 H2 _ _ _ _ _ eq_refl)).
    + intros * ->; exact (proj2 (proj2 (proj2 H2) _ _ _ _ eq_refl)).
Qed.

Lemma wf_gstack_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall fp U, gds_lookup Θ fp = Some U -> gm_selfpath (q_abs fp nil) (gu_mod U)) /\
    (forall mp K U, List.In (mp, K, U) Ξ -> gm_selfpath mp (gu_mod U)).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Kp Δ Φ HΞ IH HΦ Hff].
  - split; intros * H; [ discriminate | contradiction ].
  - destruct IH as [IHΘ IHΞ]; split; [| intros * [] ].
    intros fp U Hl; cbn in Hl; destruct (path_beq fp fq) eqn:Hb; [| exact (IHΘ _ _ Hl) ].
    injection Hl as <-; apply path_beq_true in Hb; subst; exact (IHΞ _ _ _ (or_introl eq_refl)).
  - destruct IH as [IHΘ IHΞ]; split; [ exact IHΘ |].
    intros mp' K' U [[= <- <- <-] | Hin];
      [ exact (proj1 ((proj2 wf_gmod_selfpath) _ _ _ _ _ _ HΦ)) | exact (IHΞ _ _ _ Hin) ].
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
    destruct (gs_find_tele_own _ _ _ _ HFf) as (K & Hin).
    exact (proj1 (HΞ _ _ _ Hin) _ _ _ _ _ _ He).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    pose proof (proj1 (HΘ _ _ Hl) _ _ _ _ _ _ He) as Hsp; destruct p; exact Hsp.
Qed.

(** A record type is stored at its own path. *)
Lemma gc_entry_record_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pv pr R Φ,
    gc_entry Θ Ξ p = Some (ge_record pv pr R Φ) -> pr = p.
Proof.
  intros * Hg * He; destruct (wf_gstack_selfpath _ _ Hg) as [HΘ HΞ].
  unfold gc_entry, gc_entry_u in He; rewrite gs_find_tele_find in He.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |] eqn:Ef; cbn in He.
  - destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & HFf).
    apply qname_strip_app_inv in HF as ->.
    destruct (gs_find_tele_own _ _ _ _ HFf) as (K & Hin).
    exact (proj2 (HΞ _ _ _ Hin) _ _ _ _ _ He).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    pose proof (proj2 (HΘ _ _ Hl) _ _ _ _ _ He) as Hsp; destruct p; exact Hsp.
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
      | ge_record _ _ _ Φ' => gm_entry Φ' (pre ++ y :: nil)
      | _ => None
      end.
Proof. intros; cbn; rewrite String.eqb_refl; destruct pre; reflexivity. Qed.

Lemma gm_grouped_ext : forall p Φ x E, gm_fresh x Φ -> gm_grouped p Φ ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' ->
       exists y0 pv0 Φ0, pq = qname_in p y0 /\ gm_entry (Φ ⊳ x ↦ E) (y0 :: nil) = Some (ge_ind pv0 pq 0 D Φ0)) ->
    (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_grouped (qname_in p x) Φ') ->
    (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> gm_grouped (qname_in p x) Φ') ->
    (forall pv pr R Φ', E = ge_record pv pr R Φ' -> gm_grouped (qname_in p x) Φ') ->
    gm_grouped p (Φ ⊳ x ↦ E).
Proof.
  intros * Hf HΦ HE HM HI HR pre y * He.
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
      destruct E as [? ? ? ? | pv1 [Δ1 [sm1 Φ1 | E1]] | pv1 pq1 k1 D1 Φ1 | ? ? ? ? | ? ? ? ?]; try discriminate.
      * destruct (HM _ _ _ _ eq_refl _ _ _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
        exists y0, pv0, Φ0; split; [ rewrite qname_app_in; reflexivity | rewrite gm_entry_inner; exact H0 ].
      * destruct (HI _ _ _ _ _ eq_refl _ _ _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
        exists y0, pv0, Φ0; split; [ rewrite qname_app_in; reflexivity | rewrite gm_entry_inner; exact H0 ].
      * destruct (HR _ _ _ _ eq_refl _ _ _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
        exists y0, pv0, Φ0; split; [ rewrite qname_app_in; reflexivity | rewrite gm_entry_inner; exact H0 ].
    + assert (He0 : gm_entry Φ ((z :: pre) ++ y :: nil) = Some (ge_ind pv pq k D Φ')).
      { cbn [List.app] in He |- *; cbn in He; destruct (String.eqb_spec z x) as [| _ ]; [ contradiction | exact He ]. }
      destruct (HΦ _ _ _ _ _ _ _ He0) as (y0 & pv0 & Φ0 & -> & H0).
      exists y0, pv0, Φ0; split; [ reflexivity | apply gm_entry_ext_fresh; assumption ].
Qed.

(** [ind_beside Ξ mp pq k D]: the declared member [k] of the group [D] at
    [pq], checked at [mp] over the stack [Ξ], is the group's first member,
    at its own path, or is checked in the frame its first member is filed
    in. *)
Definition ind_beside (Ξ : gstack) (mp pq : qname) (k : nat) (D : ind_decl) : Prop :=
  (k = 0 /\ pq = mp) \/
  exists mq y y0 Kq Δ Φ0 Ξ0 pv0 Φm, Ξ = (mq, Kq, gu_body Δ Φ0) :: Ξ0 /\ mp = qname_in mq y /\ pq = qname_in mq y0 /\
    gm_entry Φ0 (y0 :: nil) = Some (ge_ind pv0 pq 0 D Φm).

Lemma wf_gmod_grouped :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E ->
     (forall pv pq k D Φ', E = ge_ind pv pq k D Φ' -> gm_grouped mp Φ' /\ ind_beside Ξ mp pq k D) /\
     (forall pv Δ sm Φ', E = ge_mod pv (gu_mk Δ (md_body sm Φ')) -> gm_grouped mp Φ') /\
     (forall pv pr R Φ', E = ge_record pv pr R Φ' -> gm_grouped mp Φ')) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
     gm_grouped mp Φ /\ (forall pq k D, K = fk_ind pq k D -> ind_beside Ξ mp pq k D)).
Proof.
  apply global_wf_mut_ind; intros.
  all: try solve [ split; [| split ]; intros * Heq; discriminate ].
  (* a record, before the members of its module, and with its body *)
  all: try solve [ split; [| split ]; intros * Heq; try discriminate;
                   lazymatch type of Heq with ge_record _ _ _ _ = _ => idtac end; injection Heq as <- <- <- <-;
                   first [ apply gm_grouped_nil | match goal with IH : gm_grouped _ _ /\ _ |- _ => exact (proj1 IH) end ] ].
  (* the module of a record, before its members *)
  all: try solve [ split; [ apply gm_grouped_nil | intros * Heq; discriminate ] ].
  - (* a nested module *)
    split; [| split ]; intros * Heq; [ discriminate | injection Heq as <- <- <- <-; match goal with IH : _ /\ _ |- _ => exact (proj1 IH) end
                                    | discriminate ].
  - (* the first member of a group, before the members of its module *)
    split; [| split ]; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate | discriminate ].
    split; [ apply gm_grouped_nil | left; split; reflexivity ].
  - (* a later member, before the members of its module *)
    split; [| split ]; intros * Heq; [ injection Heq as <- <- <- <- <- | discriminate | discriminate ].
    split; [ apply gm_grouped_nil | right; do 9 eexists; split; [ reflexivity | split; [ reflexivity | split; [ reflexivity | eassumption ] ] ] ].
  - (* a member with the body of its module *)
    split; [| split ]; intros * Heq; [| discriminate | discriminate ]; injection Heq as <- <- <- <- <-.
    match goal with IH : gm_grouped _ _ /\ _ |- _ => destruct IH as [HΦ HK] end.
    split; [ exact HΦ | exact (HK _ _ _ eq_refl) ].
  - (* the module of a member, before its members *)
    split; [ apply gm_grouped_nil | intros * Heq; injection Heq; intros; subst ].
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => exact (proj2 (proj1 IH _ _ _ _ _ eq_refl)) end.
  - (* an entry *)
    match goal with IH : (forall _ _ _ _ _, _ = _ -> _) /\ _ |- _ => rename IH into H2 end.
    match goal with IH : gm_grouped _ _ /\ _ |- _ => destruct IH as [HΦ HK] end.
    split; [| exact HK ].
    apply gm_grouped_ext; [ assumption | assumption | | | |].
    + intros * ->; destruct (proj1 H2 _ _ _ _ _ eq_refl) as [_ [[-> ->] | (mq & y & y0 & Kq & Δ0 & Φ0 & Ξ0 & pv0 & Φm & HΞ & _ & -> & Hen)]].
      * do 3 eexists; split; [ reflexivity | cbn; rewrite String.eqb_refl; reflexivity ].
      * injection HΞ as <- _ _ <- _.
        do 3 eexists; split; [ reflexivity | apply gm_entry_ext_fresh; [ assumption | exact Hen ] ].
    + intros * ->; exact (proj1 (proj2 H2) _ _ _ _ eq_refl).
    + intros * ->; exact (proj1 (proj1 H2 _ _ _ _ _ eq_refl)).
    + intros * ->; exact (proj2 (proj2 H2) _ _ _ _ eq_refl).
Qed.

Lemma wf_gstack_grouped : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall fp U, gds_lookup Θ fp = Some U -> gm_grouped (q_abs fp nil) (gu_mod U)) /\
    (forall mp K U, List.In (mp, K, U) Ξ -> gm_grouped mp (gu_mod U)).
Proof.
  induction 1 as [| Θ fq V Hg IH | Θ Ξ mp Kp Δ Φ HΞ IH HΦ Hff].
  - split; intros * H; [ discriminate | contradiction ].
  - destruct IH as [IHΘ IHΞ]; split; [| intros * [] ].
    intros fp U Hl; cbn in Hl; destruct (path_beq fp fq) eqn:Hb; [| exact (IHΘ _ _ Hl) ].
    injection Hl as <-; apply path_beq_true in Hb; subst; exact (IHΞ _ _ _ (or_introl eq_refl)).
  - destruct IH as [IHΘ IHΞ]; split; [ exact IHΘ |].
    intros mp' K' U [[= <- <- <-] | Hin];
      [ exact (proj1 ((proj2 wf_gmod_grouped) _ _ _ _ _ _ HΦ)) | exact (IHΞ _ _ _ Hin) ].
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
    destruct (gs_find_tele_own _ _ _ _ HFf) as (K & Hin); exact (HΞ _ _ _ Hin). }
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

(** A member is stored at the path its declaration gives it. *)
Lemma ind_mlookup_selfpath : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D,
    ind_mlookup Θ Ξ p = Some (pq, k, D) -> ind_selfpath pq k D p.
Proof.
  intros * Hg * Hl; destruct (ind_mlookup_entry _ _ _ _ _ _ Hl) as [(pv & Φ & He) | Hf].
  - exact (gc_entry_selfpath _ _ Hg _ _ _ _ _ _ He).
  - exact (frame_ind_selfpath _ _ Hg _ _ _ _ Hf).
Qed.

(** The group a member names is found. *)
Lemma ind_mlookup_group : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p pq k D,
    ind_mlookup Θ Ξ p = Some (pq, k, D) -> ind_lookup Θ Ξ pq = Some D.
Proof.
  intros * Hg * Hl.
  destruct (ind_mlookup_module _ _ _ _ Hl) as [[T Hm] | Hf]; [| exact (frame_ind_lookup _ _ Hg _ _ _ _ Hf) ].
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
    destruct (loc_grouped _ _ Hg _ _ _ Hlq nil y _ _ _ _ _ He) as (y0 & pv0 & Φ0 & -> & H0).
    cbn [List.app] in H0.
    assert (He0 : gc_entry Θ Ξ (qname_in mq y0) = Some (ge_ind pv0 (qname_app mq (y0 :: nil)) 0 D Φ0))
      by (apply (proj2 (loc_entry _ _ Hg _ _ _ Hlq _ _)); exact H0).
    cbn [List.app]; rewrite <- qname_app_in, qname_app_nil in He0 |- *.
    destruct (gc_entry_ind _ _ _ _ _ _ _ _ He0) as [_ Hm0].
    rewrite ind_lookup_unfold, Hm0; reflexivity.
Qed.

(** A body module stored at a path is no open frame there. *)
Lemma gc_body_not_frame : forall Θ Ξ p TΦ, gc_body Θ Ξ p = Some TΦ -> gc_frame Ξ p = None.
Proof.
  intros * Hb; unfold gc_body, gc_frame in *.
  destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |]; congruence.
Qed.

(** A chain of selections from a unit naming where a body module is stored
    denotes the module whose module part that body is, with no argument:
    the stored unit, or the member of a group whose module the body is. *)
(** An open frame that is the module of no member names none. *)
Lemma frame_mlookup_none : forall Θ Ξ mp TΦ, gc_frame Ξ mp = Some TΦ -> gs_find_ind Ξ mp = None -> ind_mlookup Θ Ξ mp = None.
Proof.
  intros * Hf Hk; rewrite ind_mlookup_unfold, Hk; unfold gc_frame in Hf.
  destruct (gs_find_tele Ξ mp) as [[[U ip] T0] |] eqn:Ef; [| discriminate ].
  destruct ip; [ rewrite (gc_module_frame_own _ _ _ _ _ Ef); reflexivity |].
  destruct U as [? [[|] ? | ?]]; discriminate.
Qed.

(** An open frame's own path names no entry. *)
Lemma gc_frame_entry_none : forall Θ Ξ p TΦ, gc_frame Ξ p = Some TΦ -> gc_entry Θ Ξ p = None.
Proof.
  intros * Hf; unfold gc_frame in Hf; unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U [| ? ?]] T0] |]; cbn; [ apply gm_entry_nil | |];
    [ destruct U as [? [[|] ? | ?]] |]; discriminate.
Qed.

(** What a stored entry that is no record names as a record: nothing. *)
Lemma record_lookup_entry_other : forall Θ Ξ p E, gc_entry Θ Ξ p = Some E ->
    (forall pv pr R Φ, E <> ge_record pv pr R Φ) -> record_lookup Θ Ξ p = None.
Proof.
  intros * He Hn; unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ He), He.
  destruct E as [| | | | pv pr R Φ]; try reflexivity; exfalso; exact (Hn _ _ _ _ eq_refl).
Qed.

Theorem mdenote_of_loc_any : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H mp T Φ Γ,
    mod_qname H = Some mp -> loc Θ Ξ mp T Φ ->
    exists R, mdenote Θ Ξ Γ H R /\ ds_mod R = Some (ds_closed nil mp T Φ nil) /\ loc_desc Θ Ξ mp T Φ R.
Proof.
  intros Θ Ξ Hg.
  (* an open frame: a unit, the module of a member, or of a record *)
  assert (Hfr : forall H mp T Φ Γ, mod_qname H = Some mp -> gc_frame Ξ mp = Some (T, Φ) ->
            exists R, mdenote Θ Ξ Γ H R /\ ds_mod R = Some (ds_closed nil mp T Φ nil) /\ loc_desc Θ Ξ mp T Φ R).
  { intros * Hq Hf; unfold loc_desc; destruct (gs_find_ind Ξ mp) as [[[pq k] D] |] eqn:Hk.
    - destruct (frame_ind_loc _ _ Hg _ _ _ _ Hk) as (U & T0 & T' & Φ' & Mk & Ht & Hf' & Hl & HMk).
      rewrite Hf in Hf'; injection Hf' as <- <-.
      exists (ind_former_desc pq k D Mk (ds_closed nil mp T Φ nil)); split; [ eapply dn_ind_frame; eassumption |].
      split; [ reflexivity |]; rewrite ind_mlookup_unfold, Hk.
      exists Mk; split; [ exact HMk | reflexivity ].
    - rewrite (frame_mlookup_none _ _ _ _ Hf Hk); unfold record_lookup.
      destruct (gs_find_record Ξ mp) as [Rr |] eqn:Hr.
      + destruct (frame_record_loc _ _ Hg _ _ Hr) as (U & T0 & T' & Φ' & Ht & Hf' & Hl).
        rewrite Hf in Hf'; injection Hf' as <- <-.
        exists (record_former_desc mp Rr (ds_closed nil mp T Φ nil)); split; [ eapply dn_record_frame; eassumption |].
        split; reflexivity.
      + rewrite (gc_frame_entry_none Θ _ _ _ Hf).
        exists (ds_closed nil mp T Φ nil); split; [ exact (dn_unit _ _ _ _ _ _ _ Hq (gc_unit_frame _ _ _ _ _ _ Hq Hf Hk Hr)) |].
        split; reflexivity. }
  induction H as [fp | x | H0 IH y | H0 IH N | U]; intros * Hq Hl; cbn in Hq; try discriminate.
  - injection Hq as <-; destruct Hl as [Hl | Hb]; [ exact (Hfr (me_unit fp) _ _ _ Γ eq_refl Hl) |].
    unfold gc_body in Hb; destruct (gs_find_tele Ξ (q_abs fp nil)) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
    + exfalso; destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & _).
      apply qname_strip_length in HF; cbn in HF; lia.
    + cbn in Hb |- *; destruct (gds_lookup Θ fp) as [Uf |] eqn:El; [| discriminate ].
      destruct (wf_gds_body _ _ Hg _ _ El) as (Δ & Φ0 & ->); cbn in Hb; injection Hb as <- <-.
      exists (ds_closed nil (q_abs fp nil) Δ Φ0 nil); split; [| split; [ reflexivity |] ].
      * apply dn_unit; [ reflexivity |]; unfold gc_unit; cbn [mod_qname]; rewrite Ef; cbn; rewrite El; reflexivity.
      * unfold loc_desc; rewrite ind_mlookup_unfold, (gs_find_ind_none _ _ ltac:(intros ? ? Hc; rewrite Ef in Hc; discriminate)).
        unfold gc_module, gc_module_u; rewrite Ef; cbn; rewrite El.
        unfold record_lookup; rewrite (gs_find_record_none _ _ ltac:(intros ? ? Hc; rewrite Ef in Hc; discriminate)).
        unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find, Ef; cbn; rewrite El, gm_entry_nil; reflexivity.
  - destruct (mod_qname H0) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
    change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y) in *.
    destruct Hl as [Hl | Hb]; [ apply Hfr; [ cbn; rewrite Hq0; reflexivity | exact Hl ] |].
    destruct (gc_body_module _ _ _ _ _ Hb) as [oD Hm].
    destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hm) as (Tq & Φq & Hlq & Hbq & Hmq).
    destruct (IH _ _ _ Γ eq_refl Hlq) as (R0 & Hm0 & Hmd0 & _).
    pose proof (proj2 (loc_closed _ _ Hg _ _ _ Hlq)) as Hcq.
    pose proof (ind_mlookup_body _ _ _ _ _ Hm) as Hml.
    destruct oD as [[[pq k] D] |].
    + (* the module of a member of a group *)
      destruct (gm_submodule_entry _ _ _ _ _ _ _ _ Hmq) as (pv & Φ' & He).
      destruct (gm_entry_subbody_ind _ Tq _ _ _ _ _ _ He) as [Hb' _]; rewrite Hb' in Hbq; injection Hbq as <- <-.
      destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hcq) He) as (Φ0 & Hp).
      pose proof (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hml) as Hsp.
      destruct (ind_selfpath_member _ _ _ _ Hsp) as [Mk HMk].
      assert (Hl : gc_loc Θ Ξ (qname_in mq y) = Some (ind_uparams D, Φ'))
        by (unfold gc_loc; rewrite (gc_body_not_frame _ _ _ _ Hb), Hb; reflexivity).
      exists (ind_former_desc pq k D Mk (ds_closed nil (qname_in mq y) (ind_uparams D) Φ' nil)); split; [| split ].
      * eapply dn_mem with (R := ind_former_desc pq k D Mk (ds_closed nil (qname_in mq y) (ind_uparams D) Φ' nil));
          [ exact Hm0 | exact Hmd0 | cbn; rewrite Hp; reflexivity | | reflexivity ].
        cbn [ge_read ds_epath]; econstructor; [ exact HMk | exact (isp_path _ _ _ _ Hsp) | exact Hl ].
      * reflexivity.
      * unfold loc_desc; rewrite Hml.
        exists Mk; split; [ exact HMk | reflexivity ].
    + destruct (gm_subbody_entry_inv _ _ _ _ _ Hbq Hmq) as [(pv & Δ & sm & He & ->) | (pv & pr & Rr & He & ->)].
      * (* a body module *)
        rewrite (body_closed_entry_mod _ _ _ _ _ _ _ Hcq He) in He.
        destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hcq) He) as (Φ0 & Hp).
        assert (Hr : record_lookup Θ Ξ (qname_in mq y) = None).
        { apply (record_lookup_entry_other _ _ _ _ (proj2 (loc_entry _ _ Hg _ _ _ Hlq _ _) He)); intros * [=]. }
        exists (ds_closed nil (qname_in mq y) (Δ ++ Tq) Φ nil); split;
          [| split; [ reflexivity | unfold loc_desc; rewrite Hml, Hr; reflexivity ] ].
        eapply dn_mem with (R0 := R0) (Γy := nil) (rd := rd_closed nil nil (apps (a_mem (qname_mod mq) y) nil))
          (E := ge_read Tq (ge_mod pv (gu_mk Δ (md_body sm_closed Φ)))) (R := ds_closed nil (qname_in mq y) (Δ ++ Tq) Φ nil).
        -- exact Hm0.
        -- exact Hmd0.
        -- cbn; rewrite Hp; reflexivity.
        -- cbn [ge_read ds_epath]; apply en_mod.
           eapply un_body; [ apply body_xp_noopen, (body_closed_entry_noopen _ _ _ _ _ _ _ Hcq He) | reflexivity ].
        -- reflexivity.
      * (* the module of a record type *)
        destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hcq) He) as (Φ0 & Hp).
        pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hlq _ _) He) as Hge.
        assert (Hr : record_lookup Θ Ξ (qname_in mq y) = Some Rr)
          by (unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ Hge), Hge; reflexivity).
        assert (Hl : gc_loc Θ Ξ (qname_in mq y) = Some (record_mod_tele pr Rr, Φ))
          by (unfold gc_loc; rewrite (gc_body_not_frame _ _ _ _ Hb), Hb; reflexivity).
        exists (record_former_desc (qname_in mq y) Rr (ds_closed nil (qname_in mq y) (record_mod_tele pr Rr) Φ nil));
          split; [| split ].
        -- eapply dn_mem with (R0 := R0) (Γy := nil) (rd := rd_closed nil nil (apps (a_mem (qname_mod mq) y) nil))
             (E := ge_read Tq (ge_record pv pr Rr Φ))
             (R := record_former_desc (qname_in mq y) Rr (ds_closed nil (qname_in mq y) (record_mod_tele pr Rr) Φ nil)).
           ++ exact Hm0.
           ++ exact Hmd0.
           ++ cbn; rewrite Hp; reflexivity.
           ++ cbn [ge_read ds_epath]; apply en_record; exact Hl.
           ++ reflexivity.
        -- reflexivity.
        -- unfold loc_desc; rewrite Hml, Hr; reflexivity.
Qed.

(** Where a body module that is the module of no member and of no record
    type is stored, its path denotes that body, with no argument. *)
Theorem mdenote_of_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H mp T Φ Γ,
    mod_qname H = Some mp -> loc_mod Θ Ξ mp T Φ -> mdenote Θ Ξ Γ H (ds_closed nil mp T Φ nil).
Proof.
  intros * Hg * Hq Hl.
  destruct (mdenote_of_loc_any _ _ Hg _ _ _ _ Γ Hq (loc_mod_loc _ _ _ _ _ Hl)) as (R & Hm & _ & HR).
  unfold loc_desc in HR.
  replace (ind_mlookup Θ Ξ mp) with (@None indref) in HR.
  - destruct Hl as [(_ & _ & Hr) | (_ & _ & Hr)]; rewrite Hr in HR; subst R; exact Hm.
  - destruct Hl as [(Hf & Hk & _) | (_ & Hm' & _)]; symmetry;
      [ exact (frame_mlookup_none _ _ _ _ Hf Hk) | exact (ind_mlookup_body _ _ _ _ _ Hm') ].
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

(** Whether a description reads a closed body: a closed module, or a
    definition with a module part whose module part does. *)
Fixpoint ds_closedb (R : mdesc) : bool :=
  match R with
  | ds_closed _ _ _ _ _ => true
  | ds_dm _ _ _ Rm => ds_closedb Rm
  | _ => false
  end.

(** [dsg Θ1 Ξ1 Θ2 Ξ2 R1 R2]: [R1], read in the smaller context, grows into
    [R2] in the bigger one. *)
Inductive dsg (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : mdesc -> mdesc -> Prop :=
(** A description reading no closed body stays as it is *)
| dsg_same : forall R, ds_closedb R = false -> dsg Θ1 Ξ1 Θ2 Ξ2 R R
(** A closed description is related through its storage, at the same path
    in both *)
| dsg_closed : forall Θ' T Φ1 Φ2 Ns p,
    loc Θ1 Ξ1 p T Φ1 -> loc Θ2 Ξ2 p T Φ2 ->
    dsg Θ1 Ξ1 Θ2 Ξ2 (ds_closed Θ' p T Φ1 Ns) (ds_closed Θ' p T Φ2 Ns)
(** A definition with a module part keeps its term part and grows its
    module part *)
| dsg_dm : forall Θd A M R1 R2,
    dsg Θ1 Ξ1 Θ2 Ξ2 R1 R2 -> dsg Θ1 Ξ1 Θ2 Ξ2 (ds_dm Θd A M R1) (ds_dm Θd A M R2).

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
  induction R as [A om | Δ Φ | Θ0 p0 T Φ Ns | Θ0 A M Rm IH]; intros N R' Ha; cbn in Ha.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; reflexivity.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; [ injection Ha as <-; reflexivity | discriminate ].
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; reflexivity.
  - destruct (ds_at Rm N) as [Rm' |] eqn:Ea; [| discriminate ].
    destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; cbn; exact (IH _ _ Ea).
Qed.

Lemma ds_closedb_sub : forall R σ, ds_closedb (ds_sub R σ) = ds_closedb R.
Proof. induction R; intros; cbn; auto. Qed.

Lemma ds_closedb_self : forall M R, ds_closedb (ds_self M R) = ds_closedb R.
Proof. intros M [? [] | | |]; reflexivity. Qed.

Lemma ds_closedb_ats : forall Ns R R', ds_ats R Ns = Some R' -> ds_closedb R' = ds_closedb R.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; reflexivity |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  rewrite (IH _ _ Ha); exact (ds_closedb_at _ _ _ E).
Qed.

Lemma ds_closedb_up : forall Θ' R, ds_closedb (ds_up Θ' R) = ds_closedb R.
Proof. intros Θ' R; induction R; cbn; auto. Qed.

Lemma ds_closedb_ats_read : forall Ns R R', ds_ats_read R Ns = Some R' -> ds_closedb R' = ds_closedb R.
Proof.
  intros * Ha; destruct (ds_ats_read_inv _ _ _ Ha) as [Ha' | (A & M & Rm & B & M' & Rm' & -> & -> & _ & E)];
    [ exact (ds_closedb_ats _ _ _ Ha') | exact (ds_closedb_ats _ _ _ E) ].
Qed.

Lemma ds_closedb_read : forall rd R R', ds_read rd R = Some R' -> ds_closedb R' = ds_closedb R.
Proof.
  intros [Θ' Φ' | Θ' Ns M] * Hr; cbn in Hr.
  { destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite ds_closedb_up; apply ds_closedb_sub. }
  destruct (ds_ats_read R Ns) as [R1 |] eqn:E; cbn in Hr; [| discriminate ]; injection Hr as <-.
  rewrite ds_closedb_up, <- (ds_closedb_ats_read _ _ _ E); destruct Θ', Ns; first [ reflexivity | apply ds_closedb_self ].
Qed.

Lemma entry_term_open : forall o E R, entry_term o E = Some R -> ds_closedb R = false.
Proof.
  intros o [| | ? ? k D ? | |] R He; cbn in He; try discriminate; try (injection He as <-; reflexivity).
  - destruct (ind_member D k); cbn in He; [ injection He as <-; reflexivity | discriminate ].
  - destruct o; cbn in He; [ injection He as <-; reflexivity | discriminate ].
Qed.

(** What [gc_loc] finds is stored at the path. *)
Lemma gc_loc_loc : forall Θ Ξ p T Φ, gc_loc Θ Ξ p = Some (T, Φ) -> loc Θ Ξ p T Φ.
Proof.
  intros * Hl; unfold gc_loc in Hl; destruct (gc_frame Ξ p) eqn:Hf; [ left; congruence | right; exact Hl ].
Qed.

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
  Proof. intros; apply dsg_same; assumption. Qed.

  (** A description reading no closed body grows into itself only. *)
  Lemma dsg_open_eq : forall R R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R R2 -> ds_closedb R = false -> R2 = R.
  Proof. induction 1; cbn; intros Hc; [ reflexivity | discriminate | rewrite IHdsg by exact Hc; reflexivity ]. Qed.

  (** An abstracted description grows into one abstracted alike. *)
  Lemma dsg_up_inv : forall Θd R R2, (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_up Θd R) R2 ->
      exists R', R2 = ds_up Θd R' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R R'.
  Proof.
    intros Θd R; induction R as [A om | Δ Φ Φx | Θ' p T Φ Ns | Θ' A M Rm IH]; intros R2 Hd;
      cbn [ds_up] in Hd; inversion Hd; subst.
    - exists (ds_term A om); split; [ reflexivity | apply dsg_same; rewrite <- (ds_closedb_up Θd); assumption ].
    - exists (ds_open Δ Φ Φx); split; [ reflexivity | apply dsg_same; rewrite <- (ds_closedb_up Θd); assumption ].
    - exists (ds_closed Θ' p T Φ Ns); split; [ reflexivity | apply dsg_same; rewrite <- (ds_closedb_up Θd); assumption ].
    - eexists (ds_closed Θ' p T _ Ns); split; [ reflexivity | apply dsg_closed; assumption ].
    - exists (ds_dm Θ' A M Rm); split; [ reflexivity | apply dsg_same; rewrite <- (ds_closedb_up Θd); assumption ].
    - match goal with Hd' : dsg _ _ _ _ (ds_up Θd Rm) ?R2' |- _ => destruct (IH _ Hd') as (Rm' & -> & HRm) end.
      exists (ds_dm Θ' A M Rm'); split; [ reflexivity | apply dsg_dm; exact HRm ].
  Qed.

  (** A stored body is stored in the bigger context, perhaps grown: an open
      frame stays one or is closed into a body module. *)
  Lemma loc_grow : forall p T Φ1, loc Θ1 Ξ1 p T Φ1 -> exists Φ2, loc Θ2 Ξ2 p T Φ2.
  Proof.
    intros * [Hl | Hl].
    - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hl) as (Φ2 & [[Hl2 _] | [Hb2 _]]); exists Φ2; [ left | right ]; assumption.
    - destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hl) as (Φ2 & Hb2 & _); exists Φ2; right; exact Hb2.
  Qed.

  (** A description grows into one description at most. *)
  Lemma dsg_functional : forall R R2 R2', (dsg Θ1 Ξ1 Θ2 Ξ2) R R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) R R2' -> R2 = R2'.
  Proof.
    intros R R2 R2' Hd; revert R2'; induction Hd as [R Hc | Θ' T Φ1 Φ2 Ns p H1 H2 | Θd A M R1 R2 Hd IH]; intros R2' Hd'.
    - symmetry; exact (dsg_open_eq _ _ Hd' Hc).
    - inversion Hd'; subst; [ discriminate |].
      match goal with H2' : loc Θ2 Ξ2 p T _ |- _ => destruct (loc_functional _ _ _ _ _ _ _ H2 H2') as [_ <-] end; reflexivity.
    - inversion Hd'; subst; [| f_equal; eauto ].
      cbn in *; rewrite (dsg_open_eq _ _ Hd ltac:(assumption)); reflexivity.
  Qed.

  Lemma dsg_ty : forall R1 R2 A, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_ty R1 = Some A -> ds_ty R2 = Some A.
  Proof.
    intros * [R1 _ | ? ? ? ? ? ? _ _ | ? ? ? ? ? _] Ht; cbn in *; try discriminate; assumption.
  Qed.

  Lemma dsg_red : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_red R1 = ds_red R2.
  Proof. intros * []; reflexivity. Qed.

  Lemma dsg_tele : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_tele R1 = ds_tele R2.
  Proof. intros * []; reflexivity. Qed.

  Lemma dsg_is_mod : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_is_mod R1 -> ds_is_mod R2.
  Proof. intros * Hd Him; destruct Hd; first [ exact Him | exact I ]. Qed.

  (** The module part of a description reading no closed body, in the
      bigger context. *)
  Lemma dsg_mod_same : forall R1 R1m, ds_closedb R1 = false -> ds_mod R1 = Some R1m ->
      exists R2m, ds_mod R1 = Some R2m /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1m R2m.
  Proof.
    induction R1 as [| | | Θd A M R1 IH]; intros R1m Hc Hm; cbn in *; try discriminate;
        try (injection Hm as <-; eexists; split; [ reflexivity | apply dsg_refl; exact Hc ]).
    exact (IH _ Hc Hm).
  Qed.

  Lemma dsg_mod : forall R1 R2 R1m, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_mod R1 = Some R1m ->
      exists R2m, ds_mod R2 = Some R2m /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1m R2m.
  Proof.
    intros R1 R2 R1m Hd; revert R1m; induction Hd as [R1 Hc | Θ' T Φ1 Φ2 Ns p H1 H2 | Θd A M R1 R2 Hd IH];
      intros R1m Hm; cbn in *.
    - exact (dsg_mod_same _ _ Hc Hm).
    - injection Hm as <-; eexists; split; [ reflexivity |]; apply dsg_closed; assumption.
    - exact (IH _ Hm).
  Qed.

  Lemma dsg_mtele : forall R1 R2 T, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_mtele R1 = Some T -> ds_mtele R2 = Some T.
  Proof.
    intros * Hd Ht; unfold ds_mtele in *.
    destruct (ds_mod R1) as [R1m |] eqn:Hm; [| discriminate ].
    destruct (dsg_mod _ _ _ Hd Hm) as (R2m & -> & Hdm); rewrite <- (dsg_tele _ _ Hdm); exact Ht.
  Qed.

  Lemma dsg_at : forall R1 R2 N R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_at R1 N = Some R1' -> exists R2', ds_at R2 N = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    intros R1 R2 N R1' Hd; revert R1'; induction Hd as [R Hc | Θ' T Φ1 Φ2 Ns p H1 H2 | Θd A M R1 R2 Hd IH]; intros R1' Ha.
    - eexists; split; [ exact Ha | apply dsg_refl; rewrite (ds_closedb_at _ _ _ Ha); exact Hc ].
    - cbn in *; destruct (tele_split (rev Θ')) as [((?, ?), ?) | ?]; injection Ha as <-;
        (eexists; split; [ reflexivity | apply dsg_closed; assumption ]).
    - cbn in *; destruct (ds_at R1 N) as [R1a |] eqn:Ea; [| discriminate ].
      destruct (IH _ eq_refl) as (R2a & -> & Hda).
      destruct (tele_split (rev Θd)) as [((?, ?), ?) | ?]; injection Ha as <-;
        (eexists; split; [ reflexivity | first [ apply dsg_dm; exact Hda | exact Hda ] ]).
  Qed.

  Lemma dsg_ats : forall Ns R1 R2 R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_ats R1 Ns = Some R1' -> exists R2', ds_ats R2 Ns = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    induction Ns as [| N Ns IH]; intros * Hd Ha; cbn in *; [ injection Ha as <-; eauto |].
    destruct (ds_at R1 N) as [R1a |] eqn:Ea; [| discriminate ].
    destruct (dsg_at _ _ _ _ Hd Ea) as (R2a & -> & Hda); eauto.
  Qed.

  Lemma dsg_up : forall Θ' R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_up Θ' R1) (ds_up Θ' R2).
  Proof.
    intros Θ' R1 R2 Hd; induction Hd as [R Hc | Θ0 T Φ1 Φ2 Ns p H1 H2 | Θd A M R1 R2 Hd IH];
      [ apply dsg_refl; rewrite ds_closedb_up; exact Hc | cbn; apply dsg_closed; assumption | cbn; apply dsg_dm; exact IH ].
  Qed.

  Lemma dsg_sub : forall σ R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_sub R1 σ) (ds_sub R2 σ).
  Proof.
    intros σ R1 R2 Hd; induction Hd as [R Hc | Θ0 T Φ1 Φ2 Ns p H1 H2 | Θd A M R1 R2 Hd IH];
      [ apply dsg_refl; rewrite ds_closedb_sub; exact Hc | cbn; apply dsg_closed; assumption | cbn; apply dsg_dm; exact IH ].
  Qed.

  Lemma dsg_self : forall M R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_self M R1) (ds_self M R2).
  Proof.
    intros * [R Hc | Θ0 T Φ1 Φ2 Ns p H1 H2 | Θd A M0 R1 R2 Hd];
      [ apply dsg_refl; rewrite ds_closedb_self; exact Hc | cbn; apply dsg_closed; assumption | cbn; apply dsg_dm; exact Hd ].
  Qed.

  Lemma dsg_named : forall Θ Ns M R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_named Θ Ns M R1) (ds_named Θ Ns M R2).
  Proof. intros [|] [|] * Hd; cbn [ds_named]; first [ exact Hd | apply dsg_self; exact Hd ]. Qed.

  Lemma dsg_ats_read : forall Ns R1 R2 R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_ats_read R1 Ns = Some R1' ->
      exists R2', ds_ats_read R2 Ns = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    intros * Hd Ha; destruct Hd as [R Hc | Θ0 T Φ1 Φ2 Ns0 p H1 H2 | Θd A M R1 R2 Hd].
    - eexists; split; [ exact Ha | apply dsg_refl; rewrite (ds_closedb_ats_read _ _ _ Ha); exact Hc ].
    - exact (dsg_ats _ _ _ _ ltac:(apply dsg_closed; eassumption) Ha).
    - destruct Θd as [| e Θd]; [| exact (dsg_ats _ _ _ _ (dsg_dm _ _ _ _ _ _ _ _ _ Hd) Ha) ].
      cbn [ds_ats_read] in Ha |- *.
      destruct (ds_ats_tm (ds_term A (Some M)) Ns) as [[B [M' |] | | |] |]; try discriminate.
      destruct (ds_ats R1 Ns) as [R1a |] eqn:Ea; [| discriminate ]; injection Ha as <-.
      destruct (dsg_ats _ _ _ _ Hd Ea) as (R2a & -> & Hda); eexists; split; [ reflexivity | apply dsg_dm; exact Hda ].
  Qed.

  Lemma dsg_read : forall rd R1 R2 R1', (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_read rd R1 = Some R1' -> exists R2', ds_read rd R2 = Some R2' /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1' R2'.
  Proof.
    intros [Θ' Φ' | Θ' Ns M] * Hd Hr; cbn in *.
    - destruct (gm_fill Φ') as [σ |]; cbn in *; [ injection Hr as <- | discriminate ].
      eexists; split; [ reflexivity | apply dsg_up, dsg_sub; exact Hd ].
    - destruct (ds_ats_read R1 Ns) as [R1a |] eqn:Ea; [| discriminate ]; injection Hr as <-.
      destruct (dsg_ats_read _ _ _ _ Hd Ea) as (R2a & -> & Hda); eexists; split; [ reflexivity | apply dsg_up, dsg_named; exact Hda ].
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

  Lemma gc_loc_grow : forall p T Φ1, gc_loc Θ1 Ξ1 p = Some (T, Φ1) ->
      exists Φ2, gc_loc Θ2 Ξ2 p = Some (T, Φ2) /\ loc Θ1 Ξ1 p T Φ1 /\ loc Θ2 Ξ2 p T Φ2.
  Proof.
    intros * Hl.
    assert (H1 : loc Θ1 Ξ1 p T Φ1) by (unfold gc_loc in Hl; destruct (gc_frame Ξ1 p) eqn:E;
      [ injection Hl as ->; left; exact E | right; exact Hl ]).
    destruct (loc_grow _ _ _ H1) as (Φ2 & H2); exists Φ2; split; [| split; assumption ].
    apply (gc_loc_of_loc _ _ Hg2 _ _ _ H2).
  Qed.

  (** A type former's description, its module part stored at [pm], grows
      into the one whose module part is stored there in the bigger
      context. *)
  Lemma former_grow : forall A M pm Tm Φm1, gc_loc Θ1 Ξ1 pm = Some (Tm, Φm1) ->
      exists Φm2, gc_loc Θ2 Ξ2 pm = Some (Tm, Φm2) /\
        (dsg Θ1 Ξ1 Θ2 Ξ2) (ds_dm nil A M (ds_closed nil pm Tm Φm1 nil)) (ds_dm nil A M (ds_closed nil pm Tm Φm2 nil)).
  Proof.
    intros * Hl; destruct (gc_loc_grow _ _ _ Hl) as (Φm2 & Hl2 & H1 & H2).
    exists Φm2; split; [ exact Hl2 | apply dsg_dm, dsg_closed; assumption ].
  Qed.

  Theorem mdenote_grow_all :
    (forall Γ H R1, mdenote Θ1 Ξ1 Γ H R1 -> exists R2, mdenote Θ2 Ξ2 Γ H R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2) /\
    (forall Γ o U R1, udenote Θ1 Ξ1 Γ o U R1 -> o = None \/ unit_oa U ->
       exists R2, udenote Θ2 Ξ2 Γ o U R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2) /\
    (forall Γ o E R1, edenote Θ1 Ξ1 Γ o E R1 -> o = None \/ entry_oa E ->
       exists R2, edenote Θ2 Ξ2 Γ o E R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2) /\
    (forall Γ Φ Φx, body_xp Θ1 Ξ1 Γ Φ Φx -> body_xp Θ2 Ξ2 Γ Φ Φx) /\
    (forall Γ H its gs, items_gen Θ1 Ξ1 Γ H its gs -> items_gen Θ2 Ξ2 Γ H its gs).
  Proof.
    apply mdenote_all_ind.
    - (* a unit or an open frame *)
      intros Γ H p0 T Φ Hq0 Hu.
      pose proof (gc_unit_not_ind _ _ _ _ _ _ Hq0 Hu) as Hk1.
      pose proof (gc_unit_not_record _ _ _ _ _ _ Hq0 Hu) as Hr1.
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hl | (_ & Hc & Hb & Hm)]); rewrite Hq0 in Hq; injection Hq as <-.
      + destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hl) as (Φ' & [(Hl' & Hk' & Hr') | (Hb' & Hm' & Hr')]).
        * rewrite Hk1 in Hk'; rewrite Hr1 in Hr'.
          exists (ds_closed nil p0 T Φ' nil); split; [ apply dn_unit; [ exact Hq0 | exact (gc_unit_frame _ _ _ _ _ _ Hq0 Hl' Hk' Hr') ] |].
          apply dsg_closed; left; eassumption.
        * rewrite Hk1 in Hm'; rewrite Hr1 in Hr'.
          exists (ds_closed nil p0 T Φ' nil); split; [ apply (mdenote_of_loc _ _ Hg2 _ p0); [ exact Hq0 | right; split; [| split ]; assumption ] |].
          apply dsg_closed; [ left | right ]; eassumption.
      + destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hb) as (Φ' & Hb' & _).
        pose proof (gc_sub_module _ _ _ _ _ _ Hs Hm) as Hm'.
        pose proof (gc_body_root_record _ _ _ _ _ Hb' Hc) as Hr'.
        exists (ds_closed nil p0 T Φ' nil); split; [ apply (mdenote_of_loc _ _ Hg2 _ p0); [ exact Hq0 | right; split; [| split ]; assumption ] |].
        apply dsg_closed; right; eassumption.
    - (* the open frame of a member's module: still one, or closed into the
         member's module; its term part is the same *)
      intros Γ H p pq k D Mk Tm Φm Hq Hk HMk Hl.
      destruct (frame_ind_loc _ _ Hg1 _ _ _ _ Hk) as (U & T0 & T & Φ & Mk0 & _ & Hf & HlE & _).
      rewrite HlE in Hl; injection Hl as <- <-.
      destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hf) as (Φ' & [(Hl' & Hk' & _) | (Hb' & Hm' & _)]).
      + (* still open *)
        rewrite <- Hk' in Hk.
        exists (ind_former_desc pq k D Mk (ds_closed nil p T Φ' nil)); split.
        * eapply dn_ind_frame; [ exact Hq | exact Hk | exact HMk | unfold gc_loc; rewrite Hl'; reflexivity ].
        * apply dsg_dm, dsg_closed; left; assumption.
      + (* closed into the member's module *)
        rewrite Hk in Hm'.
        destruct (mdenote_of_loc_any _ _ Hg2 _ _ _ _ Γ Hq (or_intror Hb')) as (R & HmR & _ & HR).
        unfold loc_desc in HR; rewrite (ind_mlookup_body _ _ _ _ _ Hm') in HR.
        destruct HR as (Mk' & HMk' & ->).
        rewrite HMk in HMk'; injection HMk' as <-.
        exists (ind_former_desc pq k D Mk (ds_closed nil p T Φ' nil)); split;
          [ exact HmR | apply dsg_dm, dsg_closed; [ left | right ]; assumption ].
    - intros * Hl Hu IH; destruct (IH (or_introl eq_refl)) as (R2 & Hu2 & Hd); exists R2; split; [ econstructor; eassumption | exact Hd ].
    - intros * Hu IH; destruct (IH (or_introl eq_refl)) as (R2 & Hu2 & Hd); exists R2; split; [ econstructor; eassumption | exact Hd ].
    - intros * Hm IH Ha; destruct IH as (R2 & Hm2 & Hd).
      destruct (dsg_at _ _ _ _ Hd Ha) as (R2' & Ha2 & Hd'); exists R2'; split; [ econstructor; eassumption | exact Hd' ].
    - (* a selection *)
      intros Γ H y R0 R0m Γy E rd R R' Hm IH Hmd He Hed IHe Hr.
      destruct IH as (R0' & Hm2 & Hd0).
      destruct (dsg_mod _ _ _ Hd0 Hmd) as (R0m' & Hmd2 & Hdm).
      destruct Hdm as [R0m Hc | Θ' T Φ1 Φ2 Ns p H1 H2 | Θ0 A0 M0 R0a R0b _]; [| | cbn in He; discriminate ].
      + destruct IHe as (R2 & Hed2 & Hd2); [ left; destruct R0m; try discriminate; reflexivity |].
        destruct (dsg_read _ _ _ _ Hd2 Hr) as (R2' & Hr2 & Hd2').
        exists R2'; split; [ econstructor; eassumption | exact Hd2' ].
      + cbn in He; destruct (gm_prefix_upto Φ1 y) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
        injection He as <- <- <-.
        pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= -> <-] & _).
        destruct (loc_entry_grow _ _ _ _ _ _ _ H1 H2 Hp) as (Φ0' & E2 & Hp2 & Hgr).
        assert (HE : exists R2, edenote Θ2 Ξ2 (nil ++ Γ) (Some (qname_in p x)) (ge_read T E2) R2 /\ (dsg Θ1 Ξ1 Θ2 Ξ2) R R2).
        { destruct E1 as [b pv A B | pv [Δ [sm Φy1 | E']] | pv pq k D ΦD | pv Aa Ma Ua | pv pr Rr ΦR]; cbn in Hgr.
          - subst E2; apply IHe; right; exact I.
          - destruct E2 as [| pv' [Δ' [sm' Φy2 | ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?]; cbn in Hgr; try discriminate; try contradiction.
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
            + cbn; apply dsg_closed; right;
                [ exact (proj1 (loc_child_mod _ _ Hg1 _ _ _ H1 _ _ _ _ _ He1))
                | exact (proj1 (loc_child_mod _ _ Hg2 _ _ _ H2 _ _ _ _ _ He2)) ].
          - subst E2; apply IHe; right; exact I.
          - destruct E2 as [| ? [? [? ?| ?]] | pv' pq' k' D' ΦD' | ? ? ? ? | ? ? ?]; cbn in Hgr; try discriminate; try contradiction.
            destruct Hgr as (<- & <- & <- & <-).
            cbn [ge_read] in Hed |- *; inversion Hed; subst.
            match goal with Hl : gc_loc _ _ ?pm = Some (?Tm, ?Φm), HMk : ind_member D k = Some ?Mk |- _ =>
              destruct (former_grow (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (a_ind pq k) _ _ _ Hl)
                as (Φm2 & Hl2 & Hdg) end.
            eexists; split; [ econstructor; eassumption | exact Hdg ].
          - subst E2; apply IHe; right; exact I.
          - (* a record: its type former, at its path in both *)
            destruct E2 as [| ? [? [? ?| ?]] | | | pv' pr' Rr' ΦR']; cbn in Hgr; try discriminate; try contradiction.
            destruct Hgr as (<- & <- & <-).
            cbn [ge_read] in Hed |- *; inversion Hed; subst.
            match goal with Hl : gc_loc _ _ ?pm = Some (?Tm, ?Φm) |- _ =>
              destruct (former_grow (ctx_pi (record_params Rr) (record_sort Rr)) (a_record (qname_in p x)) _ _ _ Hl)
                as (Φm2 & Hl2 & Hdg) end.
            eexists; split; [ econstructor; eassumption | exact Hdg ]. }
        destruct HE as (R2 & Hed2 & Hd2).
        destruct (dsg_read _ _ _ _ Hd2 Hr) as (R2' & Hr2 & Hd2').
        exists R2'; split; [| exact Hd2' ].
        eapply dn_mem; [ exact Hm2 | exact Hmd2 | cbn; rewrite Hp2; reflexivity | exact Hed2 | exact Hr2 ].
    - (* the open frame of a record's module: still one, or closed into the record's module *)
      intros Γ H p R Tm Φm Hq Hk Hl.
      destruct (frame_record_loc _ _ Hg1 _ _ Hk) as (U & T0 & T & Φ & _ & Hf & HlE).
      rewrite HlE in Hl; injection Hl as <- <-.
      assert (Hki : gs_find_ind Ξ1 p = None).
      { destruct (gs_find_ind Ξ1 p) as [r |] eqn:Hi; [| reflexivity ].
        rewrite (gs_find_ind_not_record _ _ _ Hi) in Hk; discriminate. }
      destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hf) as (Φ' & [(Hl' & _ & Hr') | (Hb' & Hm' & Hr')]).
      + (* still open *)
        rewrite <- Hr' in Hk.
        exists (record_former_desc p R (ds_closed nil p T Φ' nil)); split.
        * eapply dn_record_frame; [ exact Hq | exact Hk | unfold gc_loc; rewrite Hl'; reflexivity ].
        * apply dsg_dm, dsg_closed; left; assumption.
      + (* closed into the record's module *)
        rewrite Hk in Hr'; rewrite Hki in Hm'.
        destruct (mdenote_of_loc_any _ _ Hg2 _ _ _ _ Γ Hq (or_intror Hb')) as (R0 & HmR & _ & HR).
        unfold loc_desc in HR; rewrite (ind_mlookup_body _ _ _ _ _ Hm'), Hr' in HR; subst R0.
        exists (record_former_desc p R (ds_closed nil p T Φ' nil)); split;
          [ exact HmR | apply dsg_dm, dsg_closed; [ left | right ]; assumption ].
    - intros * Hx IH Hb Ho; exists R; split; [ econstructor; [ exact IH | exact Hb ] |].
      apply dsg_refl; destruct sm; cbn in Hb; [ injection Hb as <-; reflexivity |].
      destruct Ho as [-> | []]; discriminate.
    - intros * Hm IH Hmd _; destruct IH as (R2 & Hm2 & Hd).
      destruct (dsg_mod _ _ _ Hd Hmd) as (R2m & Hmd2 & Hdm).
      exists (ds_up Δ R2m); split; [ econstructor; eassumption | apply dsg_up; exact Hdm ].
    - intros; eexists; split; [ constructor | apply dsg_refl; reflexivity ].
    - intros * Hu IH Ho; destruct IH as (R2 & Hu2 & Hd); [ exact Ho | exists R2; split; [ constructor; exact Hu2 | exact Hd ] ].
    - (* an inductive type: its type former, its module part grown *)
      intros * HMk Hpm Hl Ho.
      destruct (former_grow (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (a_ind pq k) _ _ _ Hl)
        as (Φm2 & Hl2 & Hdg).
      eexists; split; [ econstructor; eassumption | exact Hdg ].
    - (* a definition with a module part: its module part grows *)
      intros * Hu IH Ho; destruct IH as (R2 & Hu2 & Hd); [ right; exact I |].
      exists (ds_dm nil A M R2); split; [ constructor; exact Hu2 | apply dsg_dm; exact Hd ].
    - (* a record type: its type former, its module part grown *)
      intros * Hl Ho.
      destruct (former_grow (ctx_pi (record_params R) (record_sort R)) (a_record p) _ _ _ Hl) as (Φm2 & Hl2 & Hdg).
      eexists; split; [ econstructor; eassumption | exact Hdg ].
    - intros; constructor.
    - intros; constructor; assumption.
    - intros * Hx IH Hm IHm Hmd Hgn IHg Hok.
      destruct IHm as (R2 & Hm2 & Hd).
      destruct (dsg_mod _ _ _ Hd Hmd) as (R2m & Hmd2 & _).
      econstructor; eassumption.
    - intros; constructor.
    - intros; constructor; assumption.
    - intros * Hm IHm Hgn IH; destruct IHm as (R2 & Hm2 & Hd); inversion Hd; subst.
      econstructor; eassumption.
    - intros * Hm IHm Hk Hgn IH; destruct IHm as (R2 & Hm2 & Hd).
      econstructor; [ exact Hm2 | exact (dsg_is_mod _ _ Hd Hk) | exact IH ].
    - intros * Hm IHm Hty Hmd Hgn IH; destruct IHm as (R2 & Hm2 & Hd).
      destruct (dsg_mod _ _ _ Hd Hmd) as (R2m & Hmd2 & _).
      econstructor; [ exact Hm2 | exact (dsg_ty _ _ _ Hd Hty) | exact Hmd2 | exact IH ].
  Qed.

  (** A description grown stands for the same unit. *)
  Lemma dsg_unit : forall R1 R2, (dsg Θ1 Ξ1 Θ2 Ξ2) R1 R2 -> ds_unit R1 = ds_unit R2.
  Proof. intros * [R1 _ | Θ0 T Φ1 Φ2 Ns p _ _ | Θd A M R1 R2 _]; [ reflexivity | destruct Θ0; reflexivity | reflexivity ]. Qed.

End Grow.

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

(** A module applied to arguments denotes what it denotes, at them. *)
Lemma mdenote_apps_inv : forall Θ Ξ Γ Ns H R, mdenote Θ Ξ Γ (me_apps H Ns) R ->
    exists R0, mdenote Θ Ξ Γ H R0 /\ ds_ats R0 Ns = Some R.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm; cbn in Hm |- *; [ eauto |].
  destruct (IH _ _ Hm) as (R1 & Hm1 & Ha).
  inversion Hm1; subst; try (unfold gc_unit in *; cbn in *; discriminate).
  match goal with Hat : ds_at ?R0 N = Some R1 |- _ => exists R0; rewrite Hat end.
  split; assumption.
Qed.

