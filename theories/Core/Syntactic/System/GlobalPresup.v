(** * Presupposition

    Presupposition is proved for all twelve judgments at once.  A global is used
    at its resolved type without premising that it is a type, and a definition's
    type is not checked separately from its body; that each is a type is what
    presupposition of the entry's own derivation gives, and that derivation is
    part of [⊢ᵍ], so the induction has to range over the global judgments too.

    Every entry is closed and every path absolute, so a global context only
    ever grows by embedding: everything that resolves keeps resolving to the
    same entry ([gc_sub]), and a judgment moves along an embedding unchanged
    ([emb_preserves_wf]).  The induction over the global judgments is stated
    once, for an arbitrary notion [V] of a valid entry ([global_induction]):
    each entry is valid in every context its insertion context embeds into.
    Presupposition is its instance at syntactic typing; the two semantic models
    are the others. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export DescTyping.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Embeddings

    [Emb Θ1 Ξ1 Θ2 Ξ2]: the target is well formed and everything that resolves
    at the source resolves, to the same entry, at the target. *)

Record Emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { em_wf : ⊢ᵍ Θ2 ⍮ Ξ2
  ; em_res : gc_sub Θ1 Ξ1 Θ2 Ξ2 }.

Lemma Emb_refl : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> Emb Θ Ξ Θ Ξ.
Proof. intros; constructor; [ assumption | apply gc_sub_refl ]. Qed.

(** An embedding preceded by a growth of resolution. *)
Lemma Emb_pre : forall Θ1 Ξ1 Θ Ξ Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> Emb Θ1 Ξ1 Θ2 Ξ2.
Proof. intros * H [Hg He]; constructor; [ assumption | eapply gc_sub_trans; eassumption ]. Qed.

(** What a module expression denotes grows along an embedding. *)
Lemma emb_mdenote : forall Θ1 Ξ1 Θ2 Ξ2, ⊢ᵍ Θ1 ⍮ Ξ1 -> Emb Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ H R, mdenote Θ1 Ξ1 Γ H R -> exists R2, mdenote Θ2 Ξ2 Γ H R2 /\ dsg Θ1 Ξ1 Θ2 Ξ2 R R2.
Proof. intros * Hg1 [Hg2 Hs]; exact (proj1 (mdenote_grow_all _ _ _ _ Hg1 Hg2 Hs)). Qed.

Lemma emb_body_xp : forall Θ1 Ξ1 Θ2 Ξ2, ⊢ᵍ Θ1 ⍮ Ξ1 -> Emb Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ Φ Φx, body_xp Θ1 Ξ1 Γ Φ Φx -> body_xp Θ2 Ξ2 Γ Φ Φx.
Proof. intros * Hg1 [Hg2 Hs]; exact (proj1 (proj2 (proj2 (proj2 (mdenote_grow_all _ _ _ _ Hg1 Hg2 Hs))))). Qed.

(** Every mention of what a module expression denotes, moved along an
    embedding: its term part and its module telescope stay. *)
Ltac emb_mdenote Hg1 He :=
  repeat match goal with
  | Hm : mdenote _ _ ?G ?H0 ?R |- _ =>
      let R2 := fresh "R2" in
      let Hm2 := fresh "Hm2" in
      let Hd := fresh "Hd" in
      destruct (emb_mdenote _ _ _ _ Hg1 He _ _ _ Hm) as (R2 & Hm2 & Hd); clear Hm;
      repeat match goal with
      | Ht : ds_ty _ _ R = Some _ |- _ => pose proof (dsg_ty _ _ _ _ (em_res _ _ _ _ He) _ _ _ Hd Ht); clear Ht
      | Ht : ds_mtele _ _ R = Some _ |- _ => pose proof (dsg_mtele _ _ _ _ (em_res _ _ _ _ He) _ _ _ Hd Ht); clear Ht
      | Ht : ds_red R = Some _ |- _ => rewrite (dsg_red _ _ _ _ _ _ Hd) in Ht
      | Ht : forall M, ds_red R = Some M -> _ |- _ => rewrite (dsg_red _ _ _ _ _ _ Hd) in Ht
      | Ht : ds_mod _ _ R = Some _ |- _ =>
          let Rm := fresh "Rm" in
          let Hdm := fresh "Hdm" in
          destruct (dsg_mod _ _ _ _ (em_res _ _ _ _ He) _ _ _ Hd Ht) as (Rm & ? & Hdm); clear Ht;
          try rewrite (dsg_unit _ _ _ _ _ _ Hdm)
      end
  end;
  repeat match goal with
  | Hd1 : dsg _ _ _ _ ?R ?R2, Hd2 : dsg _ _ _ _ ?R ?R2' |- _ =>
      assert_fails (constr_eq R2 R2'); pose proof (dsg_functional _ _ _ _ _ _ _ Hd1 Hd2) as <-; clear Hd2
  end.

(** A judgment moves along an embedding unchanged. *)
Theorem emb_preserves_wf : forall Θ1 Ξ1 Θ2 Ξ2,
    Emb Θ1 Ξ1 Θ2 Ξ2 ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A') /\
    (forall Γ Ψ Ψ', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Γ U U', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ᵘ U ≈ U' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Γ H H', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ᵐ H ≈ H' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵐ H ≈ H').
Proof.
  intros * He; pose proof He as [Hg Hs].
  assert (H :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ = Θ1 -> Ξ = Ξ1 -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A') /\
    (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵤ U) /\
    (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵐ H ≈ H')).
  { apply syntactic_wf_mut_ind; intros; subst;
      repeat match goal with IH : ?x = ?x -> ?x' = ?x' -> _ |- _ => specialize (IH eq_refl eq_refl) end;
      try solve [ econstructor; eauto using gc_sub_resolve, ind_lookup_gc_sub, gc_sub_ind_alias ].
    all: try match goal with
      | Hm : mdenote ?T1 ?X1 _ _ _ |- _ =>
          assert (Hg1 : ⊢ᵍ T1 ⍮ X1)
            by (eapply ctx_wf_gctx; first [ eassumption | eapply presup_modexp_eq_ctx | eapply presup_ext_eq_ctx | eapply presup_unit_eq_ctx ]; eassumption);
          emb_mdenote Hg1 He
      | Hx : body_xp ?T1 ?X1 _ _ _ |- _ =>
          assert (Hg1 : ⊢ᵍ T1 ⍮ X1)
            by (eapply ctx_wf_gctx; first [ eapply presup_ext_eq_ctx | eapply presup_unit_eq_ctx ]; eassumption)
      end.
    all: repeat match goal with Hx : body_xp ?T1 ?X1 _ _ _, Hg1 : ⊢ᵍ ?T1 ⍮ ?X1 |- _ =>
                  pose proof (emb_body_xp _ _ _ _ Hg1 He _ _ _ Hx); clear Hx end.
    all: try solve [
      match goal with Hu : gc_unit ?T1 ?X1 (me_unit ?fp) = Some ?TΦ, HΓ : ⊢ ?T1 ⍮ ?X1 ⍮ ?G |- _ =>
        destruct TΦ; destruct (emb_mdenote _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) He G _ _ (dn_unit _ _ G (me_unit fp) _ _ _ eq_refl Hu)) as (R2 & Hm2 & _);
        inversion Hm2; subst; eapply wf_me_unit; [ eauto | eassumption ]
      end ].
    all: solve [ econstructor; eauto ]. }
  destruct H as (Hc & He' & Hq & Hst & _ & Hx & Hu & Hm).
  repeat split; intros; eauto.
Qed.

(** ** The Induction over Insertion, for an Abstract Notion of Validity *)

(** The entries an entry contributes, read below its own path. *)
Definition ge_entries (E : gentry) (ip : list String.string) : option gentry :=
  match E with
  | ge_def _ _ _ _ => match ip with nil => Some E | _ => None end
  | ge_mod _ U => gm_resolve (gu_mod U) ip
  | ge_ind _ _ _ Φ => gm_resolve Φ ip
  | ge_ind_alias _ _ _ _ => None
  end.

(** The entries an entry stores, read below its own path: itself, and
    the entries of its body. *)
Definition ge_subentry (E : gentry) (ip : list String.string) : option gentry :=
  match ip with
  | nil => Some E
  | _ :: _ =>
      match E with
      | ge_mod _ (gu_mk _ (md_body _ Φ)) => gm_entry Φ ip
      | ge_ind _ _ _ Φ => gm_entry Φ ip
      | _ => None
      end
  end.

Lemma gm_entry_ext_here : forall Φ x E ip, gm_entry (Φ ⊳ x ↦ E) (x :: ip) = ge_subentry E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [Δ' [? Φ' | E']] | ? ? ? Φ' | ? ? ? ?]; reflexivity.
Qed.

Lemma gm_entry_ext_inv : forall Φ x E ip E0,
    gm_entry (Φ ⊳ x ↦ E) ip = Some E0 ->
    (exists ip', ip = x :: ip' /\ ge_subentry E ip' = Some E0) \/ gm_entry Φ ip = Some E0.
Proof.
  intros * H.
  destruct ip as [| y ip']; [ cbn in H; discriminate |].
  destruct (String.eqb_spec y x) as [-> |].
  - left; exists ip'; split; [ reflexivity |]; rewrite <- (gm_entry_ext_here Φ x); exact H.
  - right; cbn in H; destruct (String.eqb_spec y x) as [Heq | ?]; [ contradiction | exact H ].
Qed.

Lemma gc_entry_frame : forall Θ mp U Ξ p E,
    gc_entry Θ ((mp, U) :: Ξ) p = Some E ->
    (exists ip, p = qname_app mp ip /\ gm_entry (gu_mod U) ip = Some E) \/ gc_entry Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_entry, gc_entry_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_entry_frame_here : forall Θ mp U Ξ ip,
    gc_entry Θ ((mp, U) :: Ξ) (qname_app mp ip) = gm_entry (gu_mod U) ip.
Proof. intros; unfold gc_entry, gc_entry_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gm_resolve_ext_here : forall Φ x E ip,
    gm_resolve (Φ ⊳ x ↦ E) (x :: ip) = ge_entries E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [Δ' [? Φ' | E']] | ? ? ? Φ' | ? ? ? ?]; cbn; rewrite ?gm_resolve_nil; reflexivity.
Qed.

Lemma gm_resolve_ext_inv : forall Φ x E ip E0,
    gm_resolve (Φ ⊳ x ↦ E) ip = Some E0 ->
    (exists ip', ip = x :: ip' /\ ge_entries E ip' = Some E0) \/ gm_resolve Φ ip = Some E0.
Proof.
  intros * H.
  destruct ip as [| y ip']; [ cbn in H; discriminate |].
  destruct (String.eqb_spec y x) as [-> |].
  - left; exists ip'; split; [ reflexivity |]; rewrite <- (gm_resolve_ext_here Φ x); exact H.
  - right; cbn in H; destruct (String.eqb_spec y x) as [Heq | ?]; [ contradiction | exact H ].
Qed.


(** The inductive aliases an entry contributes, read below its own path:
    itself, if it is one, and those of its body. *)
Definition ge_ind_targets (E : gentry) (ip : list String.string) : option ind_alias_view :=
  match ip, E with
  | nil, _ => ge_ind_target E
  | _ :: _, ge_mod _ (gu_mk _ (md_body sm Φ)) => gm_ind_target Φ ip
  | _ :: _, ge_ind _ _ _ Φ => gm_ind_target Φ ip
  | _, _ => None
  end.

Lemma gm_ind_target_ext_here : forall Φ x E ip,
    gm_ind_target (Φ ⊳ x ↦ E) (x :: ip) = ge_ind_targets E ip.
Proof.
  intros; unfold gm_ind_target, ge_ind_targets; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [? [? ? | ?]] | ? ? ? ? | ? ? ? ?]; reflexivity.
Qed.

Lemma gm_ind_target_ext_inv : forall Φ x E ip v,
    gm_ind_target (Φ ⊳ x ↦ E) ip = Some v ->
    (exists ip', ip = x :: ip' /\ ge_ind_targets E ip' = Some v) \/ gm_ind_target Φ ip = Some v.
Proof.
  intros * H.
  destruct ip as [| y ip']; [ unfold gm_ind_target in H; cbn in H; discriminate |].
  destruct (String.eqb_spec y x) as [-> |].
  - left; exists ip'; split; [ reflexivity |]; rewrite <- (gm_ind_target_ext_here Φ x); exact H.
  - right; unfold gm_ind_target in *; cbn in H; destruct (String.eqb_spec y x) as [Heq | ?]; [ contradiction | exact H ].
Qed.

Lemma gm_ind_target_nil : forall Φ, gm_ind_target Φ nil = None.
Proof. intros; unfold gm_ind_target; rewrite gm_entry_nil; reflexivity. Qed.

Lemma ind_alias_lookup_frame : forall Θ mp U Ξ p v,
    ind_alias_lookup Θ ((mp, U) :: Ξ) p = Some v ->
    (exists ip, p = qname_app mp ip /\ gm_ind_target (gu_mod U) ip = Some v) \/
    ind_alias_lookup Θ Ξ p = Some v.
Proof.
  intros * H; unfold ind_alias_lookup, ind_alias_lookup_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma ind_alias_lookup_frame_here : forall Θ mp U Ξ ip,
    ind_alias_lookup Θ ((mp, U) :: Ξ) (qname_app mp ip) = gm_ind_target (gu_mod U) ip.
Proof. intros; unfold ind_alias_lookup, ind_alias_lookup_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma ind_alias_lookup_file : forall Θ fp U p,
    ind_alias_lookup ((fp, U) :: Θ) nil p = ind_alias_lookup Θ ((q_abs fp nil, U) :: nil) p.
Proof.
  intros; unfold ind_alias_lookup, ind_alias_lookup_u; cbn [gs_find gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl; reflexivity.
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** A filed unit has the modules its closed frame had: the declarations of
    inductive types among them. *)
Lemma ind_lookup_file : forall Θ fp U p,
    ind_lookup ((fp, U) :: Θ) nil p = ind_lookup Θ ((q_abs fp nil, U) :: nil) p.
Proof.
  intros; unfold ind_lookup, ind_lookup_u, gc_module, gc_module_u; cbn [gs_find_tele gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl.
    destruct (q_chain p) as [| x ip]; cbn; [ reflexivity | rewrite List.app_nil_r; reflexivity ].
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** The module an entry is, read at its own path, over the telescope [T]. *)
Definition ge_module (T : ctx) (E : gentry) : option modres :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body sm _)) => Some (mr_body (Δ ++ T) None)
  | ge_mod _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')))
  | ge_ind _ _ D _ => Some (mr_body (ind_uparams D) (Some D))
  | ge_ind_alias _ Δ p Ns => Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))))
  end.

Lemma gm_submodule_ext_here_nil : forall T Φ x E, gm_submodule T (Φ ⊳ x ↦ E) x nil = ge_module T E.
Proof. intros; cbn; rewrite String.eqb_refl; destruct E as [| ? [Δ [? ? | ?]] | ? ? ? ? | ? ? ? ?]; reflexivity. Qed.

(** The body an entry is, read at its own path, over the telescope [T]. *)
Definition ge_selfbody (T : ctx) (E : gentry) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ | ge_mod _ (gu_mk _ (md_alias _)) | ge_ind_alias _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body sm Φ)) => Some (Δ ++ T, Φ)
  | ge_ind _ _ D Φ => Some (ind_uparams D, Φ)
  end.

Lemma gm_subbody_ext_here_nil : forall T Φ x E, gm_subbody T (Φ ⊳ x ↦ E) x nil = ge_selfbody T E.
Proof. intros; cbn; rewrite String.eqb_refl; destruct E as [| ? [Δ [? ? | ?]] | ? ? ? ? | ? ? ? ?]; reflexivity. Qed.

(** The submodules an entry contributes, read below its own path, for an
    entry checked over the telescope [T]. *)
Definition ge_submodule (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option modres :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body sm Φ)) => gm_submodule (Δ ++ T) Φ x ip
  | ge_mod _ (gu_mk Δ (md_alias E')) => None
  | ge_ind _ _ D Φ => gm_submodule (ind_uparams D) Φ x ip
  | ge_ind_alias _ Δ p Ns => None
  end.

Lemma gm_submodule_ext_here : forall T Φ x E z ip r,
    ge_submodule T E z ip = Some r -> gm_submodule T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? | ? ? ? ?]; cbn in H; [ discriminate | exact H | exact H | exact H | exact H ].
Qed.

Lemma gm_submodule_ext_inv : forall T Φ x E y ip r,
    gm_submodule T (Φ ⊳ x ↦ E) y ip = Some r ->
    (y = x /\ ip = nil /\ ge_module T E = Some r) \/
    (exists z ip', y = x /\ ip = z :: ip' /\ ge_submodule T E z ip' = Some r) \/
    gm_submodule T Φ y ip = Some r.
Proof.
  intros * H; cbn in H; destruct (String.eqb_spec y x) as [-> |]; [| right; right; exact H ].
  destruct ip as [| z ip'].
  - left; split; [ reflexivity | split; [ reflexivity |] ].
    rewrite <- (gm_submodule_ext_here_nil T Φ x); cbn; rewrite String.eqb_refl; exact H.
  - right; left; exists z, ip'; split; [ reflexivity | split; [ reflexivity |] ].
    destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? | ? ? ? ?]; cbn in *; try discriminate; exact H.
Qed.

(** The body modules an entry contributes, read below its own path. *)
Definition ge_subbody (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ U => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  | ge_ind _ _ D Φ => gm_subbody (ind_uparams D) Φ x ip
  | ge_ind_alias _ _ _ _ => None
  end.

Lemma gm_subbody_ext_here : forall T Φ x E z ip r,
    ge_subbody T E z ip = Some r -> gm_subbody T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? | ? ? ? ?]; cbn in H; [ discriminate | exact H | | exact H | discriminate ].
  destruct z; discriminate.
Qed.

(** [Ctb Θ2 Ξ2 T mp E]: the target [Θ2 ⍮ Ξ2] has, at the path [mp], what
    the entry [E], checked over the telescope [T], contributes: its
    definitions, its module and its submodules, its body and its sub-bodies,
    these perhaps grown. *)
Definition Ctb (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (mp : qname) (E : gentry) : Prop :=
  (forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> gc_resolve Θ2 Ξ2 (qname_app mp ip) = Some E0) /\
  (forall r, ge_module T E = Some r -> gc_module Θ2 Ξ2 mp = Some r) /\
  (forall x (ip : list String.string) r, ge_submodule T E x ip = Some r ->
     gc_module Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) /\
  (forall T' Φ, ge_selfbody T E = Some (T', Φ) ->
     exists Φ', gc_body Θ2 Ξ2 mp = Some (T', Φ') /\ gm_grows Φ Φ') /\
  (forall x (ip : list String.string) T' Φ, ge_subbody T E x ip = Some (T', Φ) ->
     exists Φ', gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some (T', Φ') /\ gm_grows Φ Φ') /\
  (forall (ip : list String.string) v, ge_ind_targets E ip = Some v -> ind_alias_lookup Θ2 Ξ2 (qname_app mp ip) = Some v) /\
  (forall (ip : list String.string) E0, ge_subentry E ip = Some E0 ->
     exists E0', gc_entry Θ2 Ξ2 (qname_app mp ip) = Some E0' /\ entry_grows E0 E0').

(** What a frame extended by an entry contributes, at an embedding of it. *)
Lemma Ctb_frame : forall Θ mp Δ Φ x E Ξ Θ2 Ξ2,
    gc_sub Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ) Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mp x) E.
Proof.
  intros * Hs; repeat split.
  - intros ip0 E1 HE1; rewrite qname_app_in; apply (gc_sub_resolve _ _ _ _ _ _ Hs).
    rewrite gc_resolve_frame_here; cbn [gu_mod]; rewrite gm_resolve_ext_here; exact HE1.
  - intros r Hr0; rewrite <- (qname_app_nil (qname_in _ _)), qname_app_in; apply (gc_sub_module _ _ _ _ _ _ Hs).
    rewrite gc_module_frame_here; cbn [gu_mod gu_params]; rewrite gm_submodule_ext_here_nil; exact Hr0.
  - intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_sub_module _ _ _ _ _ _ Hs).
    rewrite gc_module_frame_here; cbn [gu_mod gu_params]; apply gm_submodule_ext_here; exact Hr0.
  - intros T' Φ' Hr0; rewrite <- (qname_app_nil (qname_in _ _)), qname_app_in; apply (gc_sub_body _ _ _ _ _ _ _ Hs).
    rewrite gc_body_frame_here; cbn [gu_mod gu_params]; rewrite gm_subbody_ext_here_nil; exact Hr0.
  - intros z ip0 T' Φ' Hr0; rewrite qname_app_in; apply (gc_sub_body _ _ _ _ _ _ _ Hs).
    rewrite gc_body_frame_here; cbn [gu_mod gu_params]; apply gm_subbody_ext_here; exact Hr0.
  - intros ip0 v Hv; rewrite qname_app_in; apply (gc_sub_ind_alias _ _ _ _ _ _ Hs).
    rewrite ind_alias_lookup_frame_here; cbn [gu_mod]; rewrite gm_ind_target_ext_here; exact Hv.
  - intros ip0 E0 HE0; rewrite qname_app_in; apply (gc_sub_entry _ _ _ _ _ _ Hs).
    rewrite gc_entry_frame_here; cbn [gu_mod]; rewrite gm_entry_ext_here; exact HE0.
Qed.

(** Pushing a nested module's frame embeds into any context that has its
    entries, submodules and bodies where the frame says. *)
Lemma gc_sub_nested : forall Θ Ξ mp pv Δ' Φ' Θ2 Ξ2,
    gc_sub Θ Ξ Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (gs_tele Ξ) mp (ge_body pv Δ' Φ') ->
    gc_sub Θ ((mp, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * Hs (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia & Hen); split; [| split; [| split; [| split; [| split ] ] ] ].
  - intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      eauto using gc_sub_resolve.
  - intros p r Hr; destruct (gc_module_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      eauto using gc_sub_module.
  - intros p T Φ Hr; destruct (gc_body_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      eauto using gc_sub_body.
  - intros p v Hr; destruct (ind_alias_lookup_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      [| eauto using gc_sub_ind_alias ].
    destruct ip as [| z ip]; [ cbn [gu_mod] in Hm; rewrite gm_ind_target_nil in Hm; discriminate |].
    apply Hia; exact Hm.
  - intros p T Φ Hr; unfold gc_frame in Hr; cbn in Hr.
    destruct (qname_strip mp p) as [ip |] eqn:Hst.
    + destruct ip as [| ? ?]; [| discriminate ]; injection Hr as <- <-.
      apply qname_strip_app_inv in Hst; rewrite qname_app_nil in Hst; subst p.
      destruct (Hb0 (Δ' ++ gs_tele Ξ) Φ' eq_refl) as (Φ'' & HΦ'' & _).
      exists Φ''; right; split; [ exact HΦ'' | exact (Hm0 (mr_body (Δ' ++ gs_tele Ξ) None) eq_refl) ].
    + eapply gc_sub_frame_loc; [ exact Hs | unfold gc_frame; exact Hr ].
  - intros p E Hr; destruct (gc_entry_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      [| eauto using gc_sub_entry ].
    destruct ip as [| z ip]; [ rewrite gm_entry_nil in Hm; discriminate |].
    apply Hen; exact Hm.
Qed.

Lemma Emb_nested : forall Θ Ξ mp pv Δ' Φ' Θ2 Ξ2,
    Emb Θ Ξ Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (gs_tele Ξ) mp (ge_body pv Δ' Φ') ->
    Emb Θ ((mp, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof. intros * [Hg Hs] Hc; constructor; [ exact Hg | exact (gc_sub_nested _ _ _ _ _ _ _ _ Hs Hc) ]. Qed.

(** Declaring an entry in the innermost frame embeds into any context that
    has what the entry contributes, where the frame says. *)
Lemma Emb_entry : forall Θ mq Δ Φ0 Ξ y E Θ2 Ξ2,
    Emb Θ ((mq, gu_body Δ Φ0) :: Ξ) Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mq y) E ->
    Emb Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ E)) :: Ξ) Θ2 Ξ2.
Proof.
  intros * [Hg Hs] (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia & Hen); constructor; [ assumption | split; [| split; [| split; [| split; [| split ] ] ] ] ].
  - intros p E0 Hr; unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; cbn [gu_mod] in Hr.
      destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ].
      * rewrite <- qname_app_in; exact (Hin _ _ HE).
      * apply (gc_sub_resolve _ _ _ _ _ _ Hs); rewrite gc_resolve_frame_here; exact HΦ.
    + apply (gc_sub_resolve _ _ _ _ _ _ Hs); unfold gc_resolve, gc_resolve_u; cbn; rewrite Hst; exact Hr.
  - intros p r Hr; unfold gc_module, gc_module_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; destruct ip as [| x ip]; [ discriminate |]; cbn [gu_mod gu_params] in Hr.
      destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(-> & -> & HE) | [(z & ip' & -> & -> & HE) | HΦ]].
      * rewrite <- (qname_app_in mq y nil), qname_app_nil; exact (Hm0 _ HE).
      * rewrite <- qname_app_in; exact (Hmod _ _ _ HE).
      * apply (gc_sub_module _ _ _ _ _ _ Hs); rewrite gc_module_frame_here; exact HΦ.
    + apply (gc_sub_module _ _ _ _ _ _ Hs); unfold gc_module, gc_module_u; cbn; rewrite Hst; exact Hr.
  - intros p T Φ Hr; unfold gc_body in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; destruct ip as [| x ip]; [ discriminate |]; cbn [gu_mod gu_params gm_subbody] in Hr.
      destruct (String.eqb_spec x y) as [-> |].
      * destruct ip as [| z ip'].
        -- rewrite <- (qname_app_in mq y nil), qname_app_nil; apply Hb0.
           rewrite <- (gm_subbody_ext_here_nil _ Φ0 y); cbn; rewrite String.eqb_refl; exact Hr.
        -- rewrite <- qname_app_in; apply Hbod.
           destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? | ? ? ? ?]; cbn in *; try discriminate; exact Hr.
      * apply (gc_sub_body _ _ _ _ _ _ _ Hs); rewrite gc_body_frame_here; exact Hr.
    + apply (gc_sub_body _ _ _ _ _ _ _ Hs); unfold gc_body; cbn; rewrite Hst; exact Hr.
  - intros p v Hr; unfold ind_alias_lookup, ind_alias_lookup_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; cbn [gu_mod] in Hr.
      destruct (gm_ind_target_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ].
      * rewrite <- qname_app_in; exact (Hia _ _ HE).
      * apply (gc_sub_ind_alias _ _ _ _ _ _ Hs); rewrite ind_alias_lookup_frame_here; exact HΦ.
    + apply (gc_sub_ind_alias _ _ _ _ _ _ Hs); unfold ind_alias_lookup, ind_alias_lookup_u; cbn; rewrite Hst; exact Hr.
  - intros p T Φ Hr; unfold gc_frame in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + destruct ip as [| ? ?]; [| discriminate ]; injection Hr as <- <-.
      eapply gc_sub_frame_loc; [ exact Hs | unfold gc_frame; cbn; rewrite Hst; reflexivity ].
    + eapply gc_sub_frame_loc; [ exact Hs | unfold gc_frame; cbn; rewrite Hst; exact Hr ].
  - intros p E0 Hr; unfold gc_entry, gc_entry_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; cbn [gu_mod] in Hr.
      destruct (gm_entry_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ].
      * rewrite <- qname_app_in; exact (Hen _ _ HE).
      * apply (gc_sub_entry _ _ _ _ _ _ Hs); rewrite gc_entry_frame_here; exact HΦ.
    + apply (gc_sub_entry _ _ _ _ _ _ Hs); unfold gc_entry, gc_entry_u; cbn; rewrite Hst; exact Hr.
Qed.

(** An inductive type contributes what it did before one more member. *)
Lemma Ctb_ind_ext : forall Θ2 Ξ2 T mp pv pq D Φ x b pv' A B,
    gm_fresh x Φ -> Ctb Θ2 Ξ2 T mp (ge_ind pv pq D (Φ ⊳ x ↦ ge_def b pv' A B)) -> Ctb Θ2 Ξ2 T mp (ge_ind pv pq D Φ).
Proof.
  intros * Hf (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia & Hen); repeat split.
  - intros ip E0 HE; apply Hin; cbn [ge_entries] in HE |- *; apply gm_resolve_ext_fresh; assumption.
  - exact Hm0.
  - intros z ip r Hr; apply Hmod; cbn [ge_submodule] in Hr |- *; apply gm_submodule_ext_fresh; assumption.
  - intros T' Φ' HB; cbn [ge_selfbody] in HB; injection HB as <- <-.
    destruct (Hb0 _ _ eq_refl) as (Φ'' & HΦ'' & Hg); exists Φ''; split; [ exact HΦ'' |].
    eapply gm_grows_trans; [| exact Hg ]; apply gmg_ext; [ constructor | assumption ].
  - intros z ip T' Φ' HB; apply Hbod; cbn [ge_subbody] in HB |- *; apply gm_subbody_ext_fresh; assumption.
  - intros [| z ip] v Hv; [ discriminate |]; apply Hia; cbn [ge_ind_targets] in Hv |- *.
    apply gm_ind_target_ext_fresh; assumption.
  - intros [| z ip] E0 HE.
    + injection HE as <-; destruct (Hen nil _ eq_refl) as (E0' & HE0' & Hgr).
      exists E0'; split; [ exact HE0' |].
      destruct E0' as [| ? [? [? ?| ?]] | ? ? ? ? | ? ? ? ?]; cbn in Hgr |- *; try discriminate; exact Hgr.
    + apply Hen; cbn [ge_subentry] in HE |- *; apply gm_entry_ext_fresh; assumption.
Qed.

(** The telescope of the frames' parameters is a well-formed context: the
    innermost frame's module was checked over it, one frame out, and pushing
    the frame is an embedding. *)
Lemma wf_gs_tele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ.
Proof.
  intros Θ [| [mp U] Ξ] Hg; [ constructor; exact Hg |].
  destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (Hs0 & HU & Hff).
  assert (HP : ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ)
    by exact (wf_gmod_ctx _ _ _ _ _ (wf_gunit_mod _ _ _ _ HU)).
  destruct (emb_preserves_wf Θ Ξ Θ ((mp, U) :: Ξ)) as (Hc & _).
  - constructor; [ exact Hg | apply gc_sub_push; exact Hff ].
  - exact (Hc _ HP).
Qed.


(** What the derivation of a declaration gives, at any global context: its
    parameters, sort and the types of its constructors' arguments are well
    formed. *)
Definition decl_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : Prop :=
  tele_ass (ind_params D) /\ decl_mvc D /\ ind_nu D <= ind_np D /\
  ⊢ Θ ⍮ Ξ ⍮ ind_params D /\
  ind_sort_univ (ind_sort D) /\
  (exists i, Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort D : Typeω@i) /\
  (exists n, Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort_lvl (ind_sort D) : Level@n) /\
  (forall c gs gs1 A gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_arg A :: gs2 ->
     Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D
       ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ) /\
  (forall c gs gs1 t gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.length (ptyp_ps t) = ind_nn D) /\
  (forall c gs gs1 t gs2 k P T, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.nth_error (ptyp_ps t) k = Some P ->
     List.nth_error (tele_insts (ind_nparams D)
                       (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + ind_nn D))) (ptyp_ps t)) k
       = Some T ->
     Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ ind_params D ⊢ P : T) /\
  (forall Δ1 T Δ2, ind_nparams D = Δ1 ++ ce_ass T :: Δ2 ->
     Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ) /\
  List.NoDup (List.map fst (ind_cons D)) /\
  (forall c gs gs1 t gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
     ptyp_simple t = true /\
     forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ ind_params D
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + ind_nn D)]ʷ).

Lemma decl_typed_emb : forall Θ Ξ Θ2 Ξ2 D, Emb Θ Ξ Θ2 Ξ2 -> decl_typed Θ Ξ D -> decl_typed Θ2 Ξ2 D.
Proof.
  intros * He (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & [i Hi] & [n Hn] & HA & HPl & HP & HN & Hnd & Hsh).
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _).
  repeat split; eauto.
  all: match goal with Hi : In _ _, He' : _ = _ ++ ca_rec _ :: _ |- _ =>
         destruct (Hsh _ _ _ _ _ Hi He') as [Hs1 Hs2]; eauto end.
Qed.

(** ** The Types of a Declaration Are Types

    The type of the type former, of a constructor and of a recursive
    argument, at a declaration [decl_typed] says is well formed. *)

Lemma params_split : forall D, ind_params D = ind_nparams D ++ ind_uparams D.
Proof. intros; unfold ind_nparams, ind_uparams; symmetry; apply List.firstn_skipn. Qed.

(** The uniform parameters of a typed declaration are a well-formed
    telescope of assumptions. *)
Lemma decl_typed_uparams : forall Θ Ξ D, decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D /\ tele_ass (ind_uparams D).
Proof.
  intros * (Ha & _ & _ & HP & _).
  rewrite params_split in Ha, HP; split; [ exact (ctx_app_wf_right _ _ _ _ HP) |].
  apply Forall_app in Ha as [_ Ha]; exact Ha.
Qed.

Lemma ind_sort_univ_wk : forall S φ, ind_sort_univ S -> ind_sort_univ S[φ]ʷ /\ (ind_sort_lvl S)[φ]ʷ = ind_sort_lvl S[φ]ʷ.
Proof. intros * [[i ->] | [t ->]]; cbn; unfold ind_sort_univ; split; eauto. Qed.

Lemma sort_large : forall Θ Ξ Γ S A n,
    ind_sort_univ S -> Θ ⍮ Ξ ⍮ Γ ⊢ ind_sort_lvl S : Level@n -> Θ ⍮ Ξ ⍮ Γ ⊢ A : S ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j.
Proof. intros * [[i ->] | [t ->]] HL HA; [ eauto | exists 0; eapply wf_exp_suniv_large; eassumption ]. Qed.

Lemma wf_wk_shiftn_app' : forall Θ Ξ E T, ⊢ Θ ⍮ Ξ ⍮ E ++ T -> Θ ⍮ Ξ ⍮ E ++ T ⊢ʷ wk_shiftn (List.length E) : T.
Proof. intros; apply wf_wk_shiftn_app; [ assumption | eapply ctx_app_wf_tail; eassumption ]. Qed.

(** The sort, and its level, under the binders [E] above the uniform
    parameters. *)
Lemma sort_under : forall Θ Ξ D E,
    decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ E ++ ind_uparams D ->
    (exists i, Θ ⍮ Ξ ⍮ E ++ ind_uparams D ⊢ (ind_sort D)[wk_shiftn (List.length E)]ʷ : Typeω@i) /\
    (exists n, Θ ⍮ Ξ ⍮ E ++ ind_uparams D ⊢ ind_sort_lvl (ind_sort D)[wk_shiftn (List.length E)]ʷ : Level@n) /\
    ind_sort_univ (ind_sort D)[wk_shiftn (List.length E)]ʷ.
Proof.
  intros * (_ & _ & _ & _ & HS & [i Hi] & [n Hn] & _) HE.
  pose proof (wf_wk_shiftn_app' _ _ _ _ HE) as Hw.
  destruct (ind_sort_univ_wk (ind_sort D) (wk_shiftn (List.length E)) HS) as [HS' Hl].
  split; [| split; [| exact HS' ] ].
  - exists i; exact (wk_preserves_exp _ _ _ _ _ _ _ Hi Hw).
  - exists n; rewrite <- Hl; exact (wk_preserves_exp _ _ _ _ _ _ _ Hn Hw).
Qed.

(** The variables [#(|Φ| + |Δ| - 1)], …, [#|Φ|] are of the types of the
    closed telescope [Δ] under [Φ], one by one. *)
Lemma wf_vars_tele : forall Θ Ξ Φ Δ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> ⊢ Θ ⍮ Ξ ⍮ Φ ++ Δ ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      Θ ⍮ Ξ ⍮ Φ ++ Δ ⊢ N : T.
Proof.
  intros * Hass Hs Hmv HΔ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped k A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev, Nat.add_0_r in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  replace (A[sb_of_list Id (List.firstn k (vars_from (List.length Φ) (List.length Δ)))])
    with (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ).
  - apply wf_vlookup; [ exact HΔ |].
    replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ List.rev l2))
      by (rewrite List.length_app, List.length_rev; lia).
    replace (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ)
      with (A[↑]ʷ[wk_shiftn (List.length (Φ ++ List.rev l2))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, List.length_rev; lia).
    rewrite HΔeq, List.app_assoc.
    apply ctx_lookup_app_r; constructor.
  - rewrite <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |].
    intros x Hx; rewrite sb_of_list_firstn_vars by lia; cbn; f_equal; lia.
Qed.

(** A term of a [Π] over a closed telescope applies to terms of its types. *)
Lemma wf_apps_closed_pi : forall Θ Ξ Δ B i Ψ M Ms,
    tele_ass Δ -> ctx_scoped 0 Δ -> exp_scoped (List.length Δ) B -> Θ ⍮ Ξ ⍮ Δ ⊢ B : Typeω@i ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ -> Θ ⍮ Ξ ⍮ Ψ ⊢ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof.
  intros * Hass Hs HsB HB HΨ HM Hl HMs.
  assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ Δ ++ ⋅) by (rewrite List.app_nil_r; eapply presup_exp_ctx; exact HB).
  pose proof (wf_wk_shiftn_app Θ Ξ Ψ ⋅) as Hw; rewrite List.app_nil_r in Hw.
  specialize (Hw HΨ ltac:(constructor; eapply ctx_wf_gctx; eassumption)).
  assert (HΔΨ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Ψ).
  { pose proof (wk_preserves_ext _ _ _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΔ0) Hw) as Hx.
    rewrite tele_closed_wk in Hx by exact Hs; eapply ext_eq_ctx_left; exact Hx. }
  eapply wf_apps_ctx_pi; [ exact Hass | exact HΔΨ | | exact HM | exact Hl | exact HMs ].
  pose proof (wf_wk_ext _ _ Δ _ _ _ Hw) as Hq.
  rewrite tele_closed_wk in Hq by exact Hs; specialize (Hq HΔΨ HΔ0).
  rewrite <- (exp_scoped_wk_id B (List.length Δ + 0) (wk_qn (List.length Δ) (wk_shiftn (List.length Ψ))))
    by (rewrite Nat.add_0_r; assumption || (intros; apply wk_qn_fix with (n := 0); [ lia | lia ])).
  assert (HB0 : Θ ⍮ Ξ ⍮ Δ ++ ⋅ ⊢ B : Typeω@i) by (rewrite List.app_nil_r; exact HB).
  exact (wk_preserves_exp _ _ _ _ _ _ _ HB0 Hq).
Qed.

Lemma ind_sort_shift_typed : forall Θ Ξ D,
    decl_typed Θ Ξ D -> exists i, Θ ⍮ Ξ ⍮ ind_params D ⊢ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ : Typeω@i.
Proof.
  intros * HD; pose proof HD as (_ & _ & _ & HΔ & _).
  rewrite params_split in HΔ |- *.
  destruct (sort_under _ _ _ _ HD HΔ) as ([i Hi] & _); rewrite length_nparams in Hi; eauto.
Qed.

Lemma ind_ty_typed0 : forall Θ Ξ D, decl_typed Θ Ξ D -> exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ind_ty D : Typeω@j.
Proof.
  intros * HD; destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
  unfold ind_ty; eapply ctx_pi_wf0; exact Hi.
Qed.

Lemma ind_ty_typed : forall Θ Ξ Γ D,
    decl_typed Θ Ξ D -> decl_closed D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty D : Typeω@j.
Proof.
  intros * HD Hc HΓ; destruct (ind_ty_typed0 _ _ _ HD) as [j Hj]; exists j.
  eapply closed_weaken_exp; [ exact HΓ | exact Hj | apply decl_closed_ind_ty, Hc | exact I ].
Qed.

(** The type former applied to terms of the parameters' types, of which the
    type is the sort at them. *)
Lemma wf_ind_apps : forall Θ Ξ Ψ p D Ms,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Ψ ->
    List.length Ms = ind_np D ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts (ind_params D) Id Ms) k = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind p) Ms : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms].
Proof.
  intros * HD Hc Hl HΨ HMl HMs.
  destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
  pose proof Hc as (Hass & Hle & Hs & HsS & _).
  eapply wf_apps_closed_pi; [ exact Hass | exact Hs | | exact Hi | exact HΨ | | exact HMl | exact HMs ].
  - eapply exp_scoped_wk; [ exact HsS |]; intros x Hx; unfold wk_shiftn, ind_nn; unfold ind_np in *; lia.
  - eapply wf_ind; eassumption.
Qed.

(** The sort at variables, or at terms of variables, is the sort shifted. *)
Lemma sort_at_vars : forall D Ms j,
    exp_mvc 0 (ind_sort D) -> exp_scoped (ind_nu D) (ind_sort D) -> ind_nu D <= ind_np D ->
    List.length Ms = ind_nn D ->
    (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id (vars_from j (ind_nu D) ++ Ms)]
    = (ind_sort D)[wk_shiftn j]ʷ.
Proof.
  intros * Hm Hs Hle Hl.
  rewrite exp_sub_wk, <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact Hs | exact Hm |].
  intros x Hx; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite sb_of_list_app, <- Hl, Nat.add_comm, sb_of_list_ge, sb_of_list_vars by exact Hx; cbn; f_equal; lia.
Qed.

(** The type at the uniform parameters and the non-uniform ones [Ps] of
    the context [Tb] over the parameters, moved into the context [E] over
    them by [wk_pat pat], is a type. *)
Lemma rec_leaf_typed : forall Θ Ξ p D E Tb pat Ps,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ ind_params D -> List.length pat = List.length E -> pat_nargs pat = List.length Tb ->
    Θ ⍮ Ξ ⍮ E ++ ind_params D ⊢ʷ wk_pat pat : Tb ++ ind_params D ->
    List.length Ps = ind_nn D ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length Tb + ind_nn D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tb ++ ind_params D ⊢ P : T) ->
    exists j, Θ ⍮ Ξ ⍮ E ++ ind_params D
      ⊢ apps (a_ind p) (ind_uvars D (List.length pat) ++ List.map (fun P => P[wk_pat pat]ʷ) Ps) : Typeω@j.
Proof.
  intros * HD Hc Hl HΨ Hpat Hpn Hφ HPl HP.
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _).
  pose proof Hc as (_ & _ & Hs & HsS & _).
  unfold ind_uvars.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (E ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
  assert (HlE : List.length (E ++ ind_nparams D) = List.length pat + ind_nn D)
    by (rewrite List.length_app, length_nparams, Hpat; reflexivity).
  assert (Huvars : vars_from (List.length pat + ind_nn D) (ind_nu D) = vars_from (List.length (E ++ ind_nparams D)) (List.length (ind_uparams D)))
    by (rewrite HlE, length_ind_uparams by exact Hle; reflexivity).
  assert (Hus : ctx_scoped 0 (ind_uparams D)).
  { rewrite params_split in Hs; apply ctx_scoped_app in Hs as [_ Hs]; exact Hs. }
  assert (Huass : tele_ass (ind_uparams D)) by (apply Forall_skipn'; exact Hass).
  assert (Humv : ctx_mvc (ind_uparams D)) by (apply Forall_skipn'; exact Hmv).
  pose proof (wf_ind_apps _ _ _ p D (vars_from (List.length pat + ind_nn D) (ind_nu D) ++ List.map (fun P => P[wk_pat pat]ʷ) Ps) HD Hc Hl HΨ)
    as HR.
  rewrite sort_at_vars in HR by (try rewrite List.length_map; assumption).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, <- params_split, HlE in Hn; rewrite HlE in HSu.
  eapply sort_large; [ exact HSu | exact Hn |].
  apply HR.
  - rewrite List.length_app, List.length_map, HPl; rewrite length_vars_from.
    unfold ind_nn in *; unfold ind_np in *; lia.
  - rewrite params_split; intros k N T HN HT.
    rewrite tele_insts_app in HT; [| exact Huass | rewrite length_vars_from, length_ind_uparams by exact Hle; reflexivity ].
    assert (Hl1 : List.length (vars_from (List.length pat + ind_nn D) (ind_nu D)) = ind_nu D) by apply length_vars_from.
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) = ind_nu D)
      by (rewrite length_tele_insts by exact Huass; rewrite Hl1, length_ind_uparams by exact Hle; lia).
    destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      rewrite List.app_assoc; rewrite Huvars in HN, HT.
      eapply wf_vars_tele; [ exact Huass | exact Hus | exact Humv | exact HE | exact HN | exact HT ].
    + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite Hl1 in HN; rewrite Hl2 in HT.
      apply nth_error_map_inv in HN as (P & HPk & ->).
      set (s := List.length Tb + ind_nn D).
      assert (Hti : tele_insts (ind_nparams D) (sb_of_list Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
                    = List.map (fun T => T[wk_pat pat]ʷ) (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn s)) Ps)).
      { rewrite <- !map_sub_of_wk; symmetry.
        eapply (tele_insts_sub_mvc _ (ind_nu D));
          [ apply decl_closed_nparams_ass, Hc | apply Forall_firstn'; exact Hmv | apply decl_closed_nparams_scoped, Hc |].
        intros x Hx; rewrite sb_of_list_vars by exact Hx; cbn.
        unfold s; rewrite <- Hpn.
        replace (x + (pat_nargs pat + ind_nn D)) with (pat_nargs pat + (ind_nn D + x)) by lia.
        rewrite wk_pat_ge; f_equal; lia. }
      rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      rewrite <- params_split.
      exact (wk_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ HPk HT0) Hφ).
Qed.

Lemma doms_ctx_cons : forall B Bs, doms_ctx (B :: Bs) = doms_ctx Bs ++ ce_ass B :: nil.
Proof. reflexivity. Qed.

Lemma ptyp_tele_pi : forall B t, ptyp_tele (pt_pi B t) = ptyp_tele t ++ ce_ass B :: nil.
Proof. reflexivity. Qed.

(** The type of a shape is a type: by its domains, each at the sort, and
    its leaf. *)
Lemma rec_shape_typed : forall Θ Ξ p D t E Tb pat,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ ind_params D -> List.length pat = List.length E -> pat_nargs pat = List.length Tb ->
    Θ ⍮ Ξ ⍮ E ++ ind_params D ⊢ʷ wk_pat pat : Tb ++ ind_params D ->
    List.length (ptyp_ps t) = ind_nn D ->
    (forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ Tb ++ ind_params D
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length Tb + ind_nn D)]ʷ) ->
    (forall k P T, List.nth_error (ptyp_ps t) k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + List.length Tb + ind_nn D))) (ptyp_ps t)) k
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ Tb ++ ind_params D ⊢ P : T) ->
    exists j, Θ ⍮ Ξ ⍮ E ++ ind_params D ⊢ ptyp_ty p D pat t : Typeω@j.
Proof.
  intros Θ Ξ p D t; induction t as [k Ps | k Ps | B t IH]; intros * HD Hc Hl HΨ Hpat Hpn Hφ HPl HB HP; cbn [ptyp_ty].
  1, 2: eapply rec_leaf_typed; eassumption.
  pose proof (HB nil B (ptyp_doms t) eq_refl) as HB0; cbn [doms_ctx List.rev List.map List.app List.length] in HB0.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (Tb ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact (wf_wk_cod _ _ _ _ _ Hφ)).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, <- params_split, List.length_app, length_nparams in Hn; rewrite List.length_app, length_nparams in HSu.
  destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j1 Hj1].
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj1 Hφ) as Hj1'; cbn in Hj1'.
  destruct (IH (ce_ass B[wk_pat pat]ʷ :: E) (ce_ass B :: Tb) (false :: pat) HD Hc Hl) as [j2 Hj2].
  - cbn [List.app]; econstructor; exact Hj1'.
  - cbn; lia.
  - cbn; lia.
  - cbn [List.app wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj1 | exact Hj1' ].
  - exact HPl.
  - intros Bs1 B' Bs2 E'; specialize (HB (B :: Bs1) B' Bs2 ltac:(cbn; rewrite E'; reflexivity)).
    rewrite doms_ctx_cons, <- List.app_assoc in HB; cbn [List.app List.length] in HB |- *.
    replace (List.length Bs1 + S (List.length Tb) + ind_nn D) with (S (List.length Bs1) + List.length Tb + ind_nn D) by lia; exact HB.
  - intros k P T HPk HT; specialize (HP k P T HPk).
    unfold ptyp_depth in HP, HT; cbn [ptyp_doms List.length] in HP.
    rewrite ptyp_tele_pi, <- List.app_assoc in HP; cbn [List.app List.length] in HT |- *.
    apply HP; cbn [ptyp_ps].
    replace (S (length (ptyp_doms t)) + length Tb + ind_nn D) with (length (ptyp_doms t) + S (length Tb) + ind_nn D) by lia; exact HT.
  - exists (max j1 j2); eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact Hj2 ].
Qed.

(** The arguments before a constructor's argument are a well-formed
    context, which [wk_pat] sends to the one of the non-recursive arguments
    before it. *)
Lemma cargs_ctx_wf : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D /\ ⊢ Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D /\
      Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D ⊢ʷ wk_pat (cargs_pat gs1) : cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hc Hl Hin gs1; induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - pose proof HD as (_ & _ & _ & HΔ & _).
    split; [ exact HΔ | split; [ exact HΔ | exact (wf_wk_id _ _ _ HΔ) ] ].
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    destruct (IH _ Heq) as (HΨ & HSt & Hφ).
    rewrite cargs_ctx_snoc, cargs_pat_snoc.
    pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _ & HA & HPl & HP & _).
    destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app].
    + rewrite cargs_strat_snoc_arg.
      specialize (HA _ _ _ _ _ Hin Heq).
      assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
        by (rewrite <- List.app_assoc, <- params_split; exact HSt).
      destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
      rewrite <- List.app_assoc, <- params_split, List.length_app, length_nparams in Hn; rewrite List.length_app, length_nparams in HSu.
      destruct (sort_large _ _ _ _ _ _ HSu Hn HA) as [j Hj].
      pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj Hφ) as Hj'; cbn in Hj'.
      split; [ econstructor; exact Hj' | split; [ econstructor; exact Hj |] ].
      cbn [wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj | exact Hj' ].
    + rewrite cargs_strat_snoc_rec.
      pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
      destruct (rec_shape_typed _ _ p D Ps (cargs_ctx p D gs1) (cargs_strat gs1) (cargs_pat gs1) HD Hc Hl HΨ
                  ltac:(rewrite length_cargs_pat, length_cargs_ctx; reflexivity) (pat_nargs_cargs_pat gs1) Hφ
                  (HPl _ _ _ _ _ Hin Heq) (proj2 (Hsh _ _ _ _ _ Hin Heq)) (fun k P T => HP _ _ _ _ _ k P T Hin Heq)) as [j Hj].
      split; [ econstructor; exact Hj | split; [ exact HSt |] ].
      cbn [wk_pat]; eapply wf_wk_compose; [ apply wf_wk_shift; econstructor; exact Hj | exact Hφ ].
Qed.



(** ** The Shapes of the Recursive Arguments, Domain by Domain *)

Lemma doms_ctx_length : forall Bs, List.length (doms_ctx Bs) = List.length Bs.
Proof. intros; unfold doms_ctx; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma doms_ctx_app : forall Bs1 Bs2, doms_ctx (Bs1 ++ Bs2) = doms_ctx Bs2 ++ doms_ctx Bs1.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma repeat_false_cons : forall n (l : list bool), List.repeat false n ++ false :: l = false :: List.repeat false n ++ l.
Proof. induction n as [| n IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma sh_ctx_snoc : forall Bs pat B,
    sh_ctx pat (Bs ++ B :: nil) = ce_ass B[wk_pat (List.repeat false (List.length Bs) ++ pat)]ʷ :: sh_ctx pat Bs.
Proof.
  induction Bs as [| B0 Bs IH]; intros; cbn [sh_ctx List.app List.length List.repeat]; [ reflexivity |].
  rewrite IH, repeat_false_cons; reflexivity.
Qed.

Lemma length_sh_ctx : forall Bs pat, List.length (sh_ctx pat Bs) = List.length Bs.
Proof. induction Bs as [| B Bs IH]; intros; cbn [sh_ctx]; [ reflexivity |]; rewrite List.length_app, IH; cbn; lia. Qed.

Lemma ptyp_ps_skip : forall k t, ptyp_ps (ptyp_skip k t) = ptyp_ps t.
Proof. induction k as [| k IH]; intros [k0 Ps | k0 Ps | B t]; cbn; auto. Qed.

Lemma ptyp_doms_skip : forall k t, ptyp_doms (ptyp_skip k t) = List.skipn k (ptyp_doms t).
Proof. induction k as [| k IH]; intros [k0 Ps | k0 Ps | B t]; cbn; auto. Qed.

Lemma pat_nargs_falses : forall k pat, pat_nargs (List.repeat false k ++ pat) = k + pat_nargs pat.
Proof. induction k as [| k IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma doms_split_nth : forall (Bs : list exp) k B, List.nth_error Bs k = Some B ->
    Bs = List.firstn k Bs ++ B :: List.skipn (S k) Bs /\ List.firstn (S k) Bs = List.firstn k Bs ++ B :: nil.
Proof.
  induction Bs as [| B0 Bs IH]; intros [| k] B H; simpl in H; try discriminate.
  - injection H as ->; simpl; split; reflexivity.
  - destruct (IH _ _ H) as [H1 H2]; split; simpl; f_equal; [ exact H1 | exact H2 ].
Qed.

(** The non-recursive arguments before an argument of a constructor are a
    well-formed context over the parameters. *)
Lemma cargs_strat_wf : forall Θ Ξ D c gs, decl_typed Θ Ξ D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 gs2, gs = gs1 ++ gs2 -> ⊢ Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hin gs1; induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - pose proof HD as (_ & _ & _ & HΔ & _); exact HΔ.
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    pose proof (IH _ Heq) as HSt.
    destruct g as [A | t]; [| rewrite cargs_strat_snoc_rec; exact HSt ].
    rewrite cargs_strat_snoc_arg.
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & HA & _).
    specialize (HA _ _ _ _ _ Hin Heq).
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- List.app_assoc, <- params_split; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- List.app_assoc, <- params_split, List.length_app, length_nparams in Hn; rewrite List.length_app, length_nparams in HSu.
    destruct (sort_large _ _ _ _ _ _ HSu Hn HA) as [j Hj].
    econstructor; exact Hj.
Qed.

(** The domains of a recursive argument's shape before the [k]-th, over
    the non-recursive arguments before it: a well-formed context. *)
Lemma doms_prefix_wf : forall Θ Ξ D c gs, decl_typed Θ Ξ D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> forall k, k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hin gs1 t gs2 Heq; induction k as [| k IH]; intros Hk.
  - cbn [List.firstn doms_ctx List.map List.rev List.app]; exact (cargs_strat_wf _ _ _ _ _ HD Hin gs1 _ Heq).
  - pose proof (IH ltac:(lia)) as HSt.
    destruct (List.nth_error (ptyp_doms t) k) as [B |] eqn:HB; [| apply List.nth_error_None in HB; lia ].
    destruct (doms_split_nth _ _ _ HB) as [Hsp Hf].
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
    destruct (Hsh _ _ _ _ _ Hin Heq) as [_ HBt].
    pose proof (HBt _ _ _ Hsp) as HB0.
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc, <- params_split; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc, <- params_split in Hn.
    replace (List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D))
      with (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1) + ind_nn D) in Hn, HSu
      by (rewrite !List.length_app, doms_ctx_length, length_nparams; lia).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j Hj].
    rewrite Hf, doms_ctx_app; cbn [doms_ctx List.map List.rev List.app].
    econstructor; exact Hj.
Qed.

(** The domains of a recursive argument's shape before the [k]-th: a
    well-formed context over the arguments before it, which [wk_pat] sends
    to the one over the non-recursive arguments before it. *)
Lemma shape_prefix_wf : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> forall k, k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D /\
      ⊢ Θ ⍮ Ξ ⍮ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D /\
      Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
        ⊢ʷ wk_pat (List.repeat false k ++ cargs_pat gs1) : doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hc Hl Hin gs1 t gs2 Heq; induction k as [| k IH]; intros Hk.
  - cbn [List.firstn sh_ctx doms_ctx List.map List.rev List.app List.repeat].
    exact (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 _ Heq).
  - destruct (IH ltac:(lia)) as (HΨ & HSt & Hφ).
    destruct (List.nth_error (ptyp_doms t) k) as [B |] eqn:HB; [| apply List.nth_error_None in HB; lia ].
    destruct (doms_split_nth _ _ _ HB) as [Hsp Hf].
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
    destruct (Hsh _ _ _ _ _ Hin Heq) as [_ HBt].
    pose proof (HBt _ _ _ Hsp) as HB0.
    assert (Lk : List.length (List.firstn k (ptyp_doms t)) = k) by (rewrite List.length_firstn; lia).
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc, <- params_split; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc, <- params_split in Hn.
    replace (List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D))
      with (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1) + ind_nn D) in Hn, HSu
      by (rewrite !List.length_app, doms_ctx_length, length_nparams; lia).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j Hj].
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj Hφ) as Hj'; cbn in Hj'.
    rewrite Hf, sh_ctx_snoc, doms_ctx_app, Lk; cbn [doms_ctx List.map List.rev List.app].
    split; [ econstructor; exact Hj' | split; [ econstructor; exact Hj |] ].
    cbn [List.repeat List.app wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj | exact Hj' ].
Qed.

(** The rest of a recursive argument's type after [k] domains of its shape
    is a type, under those domains. *)
Lemma shape_rest_wf : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t).
Proof.
  intros * HD Hc Hl Hin gs1 t gs2 k Heq Hk.
  destruct (shape_prefix_wf _ _ _ _ _ _ HD Hc Hl Hin _ _ _ Heq k Hk) as (HΨ & HSt & Hφ).
  pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & HPl & HP & _ & _ & Hsh).
  destruct (Hsh _ _ _ _ _ Hin Heq) as [_ HBt].
  assert (Lk : List.length (List.firstn k (ptyp_doms t)) = k) by (rewrite List.length_firstn; lia).
  assert (Ht : ptyp_doms t = List.firstn k (ptyp_doms t) ++ ptyp_doms (ptyp_skip k t))
    by (rewrite ptyp_doms_skip, List.firstn_skipn; reflexivity).
  destruct (rec_shape_typed _ _ p D (ptyp_skip k t) (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1)
              (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1) (List.repeat false k ++ cargs_pat gs1) HD Hc Hl)
    as [j Hj].
  - rewrite <- List.app_assoc; exact HΨ.
  - rewrite !List.length_app, List.repeat_length, length_sh_ctx, length_cargs_pat, length_cargs_ctx; lia.
  - rewrite pat_nargs_falses, pat_nargs_cargs_pat, List.length_app, doms_ctx_length; lia.
  - rewrite <- !List.app_assoc; exact Hφ.
  - rewrite ptyp_ps_skip; exact (HPl _ _ _ _ _ Hin Heq).
  - intros Bs1 B Bs2 HBs.
    pose proof (HBt (List.firstn k (ptyp_doms t) ++ Bs1) B Bs2 ltac:(rewrite Ht at 1; rewrite HBs, <- List.app_assoc; reflexivity)) as H.
    rewrite doms_ctx_app, <- List.app_assoc in H.
    rewrite <- List.app_assoc, !List.length_app, doms_ctx_length.
    replace (List.length Bs1 + (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1)) + ind_nn D)
      with (List.length (List.firstn k (ptyp_doms t) ++ Bs1) + List.length (cargs_strat gs1) + ind_nn D)
      by (rewrite List.length_app; lia).
    exact H.
  - intros m P T HPm HT.
    rewrite ptyp_ps_skip in HPm, HT.
    assert (Hd : ptyp_depth (ptyp_skip k t) + List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1)
                 = ptyp_depth t + List.length (cargs_strat gs1))
      by (unfold ptyp_depth; rewrite ptyp_doms_skip, List.length_app, doms_ctx_length, List.length_skipn; lia).
    rewrite Hd in HT.
    pose proof (HP _ _ _ _ _ m P T Hin Heq HPm HT) as H.
    unfold ptyp_tele in H |- *; rewrite Ht, doms_ctx_app, <- List.app_assoc in H.
    rewrite <- List.app_assoc; exact H.
  - rewrite <- List.app_assoc in Hj; econstructor; exact Hj.
Qed.

Corollary shape_rest_wf' : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t).
Proof. intros * HD Hc Hl Hcon; eapply shape_rest_wf; [ exact HD | exact Hc | exact Hl | exact (cons_lookup_in _ _ _ Hcon) ]. Qed.

(** The type of a constructor is a type. *)
Lemma con_cod_typed : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    exists j, Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ⊢ apps (a_ind p) (ind_pvars D (List.length gs)) : Typeω@j.
Proof.
  intros * HD Hc Hl Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ & _ & _).
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _).
  pose proof Hc as (_ & _ & Hs & HsS & _).
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
  assert (HlE : List.length (cargs_ctx p D gs ++ ind_nparams D) = List.length gs + ind_nn D)
    by (rewrite List.length_app, length_cargs_ctx, length_nparams; reflexivity).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, <- params_split, HlE in Hn; rewrite HlE in HSu.
  pose proof (wf_ind_apps _ _ _ p D (ind_pvars D (List.length gs)) HD Hc Hl HΨ) as HR.
  assert (Hpv : ind_pvars D (List.length gs) = vars_from (List.length gs + ind_nn D) (ind_nu D) ++ vars_from (List.length gs) (ind_nn D)).
  { unfold ind_pvars; rewrite vars_from_app; f_equal; unfold ind_nn; lia. }
  assert (Hty : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id (ind_pvars D (List.length gs))]
                = (ind_sort D)[wk_shiftn (List.length gs + ind_nn D)]ʷ)
    by (rewrite Hpv; apply sort_at_vars; [ assumption | assumption | assumption | apply length_vars_from ]).
  rewrite Hty in HR.
  { eapply sort_large; [ exact HSu | exact Hn |]; apply HR.
    - unfold ind_pvars; apply length_vars_from.
    - intros k N T HN HT.
      replace (ind_pvars D (List.length gs)) with (vars_from (List.length (cargs_ctx p D gs)) (List.length (ind_params D))) in HN, HT
        by (unfold ind_pvars, ind_np; rewrite length_cargs_ctx; reflexivity).
      eapply wf_vars_tele; [ exact Hass | exact Hs | exact Hmv | exact HΨ | exact HN | exact HT ]. }
Qed.

Lemma con_ty_typed0 : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@j.
Proof.
  intros * HD Hc Hl Hcon.
  destruct (con_cod_typed _ _ _ _ _ _ HD Hc Hl Hcon) as [j Hj].
  destruct (ctx_pi_wf0 _ _ _ _ _ Hj) as [j' Hj']; exists j'.
  unfold con_ty; rewrite <- ctx_pi_app; exact Hj'.
Qed.

Lemma con_ty_typed : forall Θ Ξ Γ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ con_ty p D gs : Typeω@j.
Proof.
  intros * HD Hc Hl Hcon HΓ; destruct (con_ty_typed0 _ _ _ _ _ _ HD Hc Hl Hcon) as [j Hj]; exists j.
  eapply closed_weaken_exp; [ exact HΓ | exact Hj | eapply decl_closed_con_ty; [ exact Hc | apply cons_lookup_in; exact Hcon ] | exact I ].
Qed.

(** The motive's instance at the non-uniform parameters and the scrutinee
    is a substitution into the motive's context. *)
Lemma wf_elim_inst_sub : forall Θ Ξ Γ p D Ps M,
    decl_closed D -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) : elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hc HPl HPs HM HΨ.
  pose proof Hc as (Hass & Hle & _).
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
  assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps))))
    by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
  apply wf_sub_of_list_id; [| exact HΨ | rewrite length_elim_mctx, List.length_app, HNl; cbn; lia |].
  - unfold elim_mctx; constructor; [ eauto | exact Hrass ].
  - intros k N T HN HT.
    unfold elim_mctx in HT.
    change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub, length_nparams; exact HNl).
    assert (Hl2 : List.length (tele_insts (tele_sub (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps))) Id
                                (List.skipn (ind_nu D) Ps)) = ind_nn D)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_nparams, HNl; lia).
    destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (List.firstn (ind_nu D) Ps))) in HT
        by apply sb_compose_id_right.
      apply (HPs (ind_nu D + k)).
      * rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN.
      * rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite params_split, tele_insts_app;
          [| apply Forall_skipn'; exact Hass | rewrite HUl, length_ind_uparams by exact Hle; reflexivity ].
        rewrite List.nth_error_app2
          by (rewrite length_tele_insts by (apply Forall_skipn'; exact Hass); rewrite HUl, length_ind_uparams by exact Hle; lia).
        rewrite length_tele_insts by (apply Forall_skipn'; exact Hass); rewrite HUl, length_ind_uparams by exact Hle.
        rewrite Nat.min_id; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
    + rewrite List.nth_error_app2 in HN, HT by lia; rewrite HNl in HN; rewrite Hl2 in HT.
      destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
      rewrite <- HNl, map_shift_sb_of_list, vars_from_sb_of_list.
      rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id, List.firstn_skipn; exact HM.
Qed.


Section Induction.
  (** [V Θ Ξ E]: the (closed) entry [E] is valid at [Θ ⍮ Ξ]; [VD Θ Ξ D]: so
      is the declaration [D] of an inductive type. *)
  Variable V : gdeps -> gstack -> gentry -> Prop.
  Variable VD : gdeps -> gstack -> ind_decl -> Prop.

  (** An inductive alias is valid as the definition it δ-unfolds to. *)
  Definition alias_def (Δ : ctx) (p : qname) (Ns : list exp) (D : ind_decl) : gentry :=
    ge_def false false (ctx_pi Δ (ind_ty_at D Ns)) (Some (ctx_fn Δ (apps (a_ind p) Ns))).

  (** The canonical path of a valid inductive alias names an inductive type,
      whose uniform parameters its arguments are for, and the alias is valid
      as the definition it δ-unfolds to. *)
  Definition alias_ok (Θ2 : gdeps) (Ξ2 : gstack) (Δ : ctx) (p : qname) (Ns : list exp) : Prop :=
    exists D, ind_lookup Θ2 Ξ2 p = Some D /\ List.length Ns <= ind_nu D /\ V Θ2 Ξ2 (alias_def Δ p Ns D).

  Definition GV (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
    (forall p E, gc_resolve Θ1 Ξ1 p = Some E -> V Θ2 Ξ2 E) /\
    (forall p D, ind_lookup Θ1 Ξ1 p = Some D -> VD Θ2 Ξ2 D) /\
    (forall pq Δ p Ns, ind_alias_lookup Θ1 Ξ1 pq = Some (Δ, p, Ns) -> alias_ok Θ2 Ξ2 Δ p Ns).

  (** Everything resolving at [Θ ⍮ Ξ] is valid wherever [Θ ⍮ Ξ] embeds. *)
  Definition Good (Θ : gdeps) (Ξ : gstack) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 -> GV Θ Ξ Θ2 Ξ2.

  (** How a definition and an axiom are made valid: from their derivation at
      the insertion context, given that its globals are valid.  A definition
      is checked in a closed telescope [T]: the frames' parameters, or the
      uniform parameters of the inductive type whose module it is a member
      of. *)
  Hypothesis Hdef : forall Θ Ξ T A M b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ T ⊢ M : A -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
  Hypothesis Hax : forall Θ Ξ A i b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
  (** And a declaration of an inductive type. *)
  Hypothesis Hind : forall Θ Ξ D Θ2 Ξ2,
      decl_typed Θ Ξ D -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> VD Θ2 Ξ2 D.

  (** What an entry contributes is valid wherever the context it is checked
      in embeds and the entry's contributions are found. *)
  Definition GoodE (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 -> Ctb Θ2 Ξ2 (gs_tele Ξ) mp E ->
      (forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> V Θ2 Ξ2 E0) /\
      (forall T D, ge_module (gs_tele Ξ) E = Some (mr_body T (Some D)) -> VD Θ2 Ξ2 D) /\
      (forall x (ip : list String.string) T D, ge_submodule (gs_tele Ξ) E x ip = Some (mr_body T (Some D)) -> VD Θ2 Ξ2 D) /\
      (forall (ip : list String.string) Δ p Ns, ge_ind_targets E ip = Some (Δ, p, Ns) -> alias_ok Θ2 Ξ2 Δ p Ns).

  Definition GoodM (Θ : gdeps) (Ξ : gstack) (mp : qname) (Δ : ctx) (Φ : gmod) : Prop :=
    forall Θ2 Ξ2, Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 ->
      (forall ip E0, gm_resolve Φ ip = Some E0 -> V Θ2 Ξ2 E0) /\
      (forall x ip T D, gm_submodule (Δ ++ gs_tele Ξ) Φ x ip = Some (mr_body T (Some D)) -> VD Θ2 Ξ2 D) /\
      (forall ip Δa p Ns, gm_ind_target Φ ip = Some (Δa, p, Ns) -> alias_ok Θ2 Ξ2 Δa p Ns).

  Theorem global_induction_all :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Good Θ Ξ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Good Θ Ξ) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Good Θ Ξ) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Good Θ Ξ) /\
    (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Good Θ Ξ) /\
    (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Good Θ Ξ) /\
    (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Good Θ Ξ) /\
    (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Good Θ Ξ) /\
    (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> GoodE Θ Ξ mp E) /\
    (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> GoodM Θ Ξ mp Δ Φ) /\
    (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> Good Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - (* a definition or an axiom *)
      intros Θ2 Ξ2 He _; split; [| split; [ discriminate | split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; discriminate ] ] ].
      intros [| ? ?] E0 HE; cbn in HE; inversion HE; subst.
      match goal with HM : forall M, ?o = Some M -> _ |- _ =>
        destruct o as [M0 |]; cbn; [ specialize (HM M0 eq_refl) | clear HM ] end; eauto.
    - (* a nested module *)
      intros Θ2 Ξ2 He Hc.
      destruct (H0 _ _ (Emb_nested _ _ _ _ _ _ _ _ He Hc)) as (HE & HU & HA).
      split; [ exact HE | split; [ intros ? ? Hx; discriminate | split; [ exact HU |] ] ].
      intros [| z ip] ? ? ? Hx; [ discriminate | exact (HA _ _ _ _ Hx) ].
    - (* an alias: it contributes no entry and no declaration *)
      intros ? ? _ _; split; [ intros ip ? Hx; cbn in Hx; discriminate | split; [ discriminate | split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; discriminate ] ] ].
    - (* an inductive type, before the members of its module *)
      intros Θ2 Ξ2 He _; split; [ intros [| ? ?] ? Hx; discriminate | split; [| split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; [ discriminate | unfold ge_ind_targets, gm_ind_target in Hx; discriminate ] ] ] ].
      intros T D0 [= _ <-].
      eapply Hind; [| eassumption | exact He ].
      repeat match goal with H : decl_mvc _ |- _ => destruct H as (? & ? & ?) end.
      repeat split; eauto.
    - (* one more member of the module of an inductive type *)
      rename H0 into IHE, H2 into IHM.
      intros Θ2 Ξ2 He (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia & Hen).
      assert (Hc : Ctb Θ2 Ξ2 (gs_tele ((mq, gu_body Δ Φ0) :: Ξ)) (qname_in mq y) (ge_ind pv (qname_in mq y) D Φ))
        by (eapply Ctb_ind_ext; [ eassumption | repeat split; eassumption ]).
      destruct (IHE _ _ He Hc) as (HΦE & HΦD & HΦU & HΦA).
      assert (He' : Emb Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv (qname_in mq y) D Φ)) :: Ξ) Θ2 Ξ2)
        by (apply Emb_entry; [ exact He | exact Hc ]).
      split; [| split; [ exact HΦD | split ] ].
      + intros ip E0 Hr; cbn [ge_entries] in Hr.
        destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ]; [| exact (HΦE _ _ HΦ) ].
        destruct ip'; cbn in HE; [ injection HE as <- | discriminate ].
        eapply Hdef; [ eassumption | exact IHM | exact He' ].
      + intros z ip T D0 Hr; cbn [ge_submodule] in Hr.
        destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(_ & _ & HE) | [(? & ? & _ & _ & HE) | HΦ]];
          [ discriminate | discriminate | exact (HΦU _ _ _ _ HΦ) ].
      + intros [| z ip] Δa pa Nsa Hx; [ discriminate |]; cbn [ge_ind_targets] in Hx.
        destruct (gm_ind_target_ext_inv _ _ _ _ _ Hx) as [(ip' & Hip & HE) | HΦ].
        * destruct ip'; discriminate.
        * exact (HΦA (z :: ip) _ _ _ HΦ).
    - (* an inductive alias: valid as the definition it unfolds to *)
      intros Θ2 Ξ2 He _.
      split; [ intros [| ? ?] ? Hx; discriminate | split; [ intros ? ? Hx; cbn in Hx; discriminate | split; [ intros ? ? ? ? Hx; cbn in Hx; discriminate |] ] ].
      intros [| ? ?] Δa pa Nsa Hx; [| discriminate ]; cbn in Hx; injection Hx as <- <- <-.
      match goal with HD : ind_lookup _ _ _ = Some ?D1 |- _ =>
        exists D1; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ He) HD) | split; [ assumption |] ] end.
      unfold alias_def; eapply Hdef; [ eassumption | | exact He ].
      match goal with H : Good _ _ |- _ => exact H end.
    - (* the empty module *)
      intros ? ? _; split; [ intros [| ? ?] ? Hx; discriminate | split; [ intros ? ? ? ? Hx; discriminate |] ].
      intros [| ? ?] ? ? ? Hx; unfold gm_ind_target in Hx; discriminate.
    - (* extending a module *)
      rename H0 into IHΦ, H2 into IHE.
      intros Θ2 Ξ2 He.
      assert (He' : Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Emb_pre; [ apply gc_sub_grow; eassumption | exact He ]).
      destruct (IHΦ _ _ He') as (HΦE & HΦU & HΦA).
      destruct (IHE _ _ He' (Ctb_frame _ _ _ _ _ _ _ _ _ (em_res _ _ _ _ He))) as (HEE & HEM & HEU & HEA).
      split; [| split ].
      + intros ip E0 Hr; destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ']; eauto.
      + intros z ip T D Hr.
        destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(_ & _ & HE) | [(? & ? & _ & _ & HE) | HΦ']]; eauto.
      + intros ip Δa pa Nsa Hx.
        destruct (gm_ind_target_ext_inv _ _ _ _ _ Hx) as [(ip' & -> & HE) | HΦ']; eauto.
    - (* nothing filed *)
      intros ? ? _; split; [ intros p E Hr; unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr; discriminate
                           | split; [ intros p D Hr; unfold ind_lookup, ind_lookup_u, gc_module, gc_module_u in Hr; cbn in Hr; discriminate
                                    | intros pq ? ? ? Hr; unfold ind_alias_lookup, ind_alias_lookup_u in Hr; cbn in Hr; discriminate ] ].
    - (* a filed unit: it resolves as its closed frame did *)
      rename H into Hg, H0 into IHU.
      intros Θ2 Ξ2 He.
      destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (_ & _ & [Hn _]).
      destruct (IHU _ _ (Emb_pre _ _ _ _ _ _ (gc_sub_file _ _ U Hn) He)) as (HR & HI & HA).
      split; [ intros p E Hr; rewrite gc_resolve_file in Hr; eauto | split ].
      + intros p D Hr; rewrite ind_lookup_file in Hr; eauto.
      + intros pq ? ? ? Hr; rewrite ind_alias_lookup_file in Hr; eauto.
    - (* a frame *)
      rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He.
      assert (HeΞ : Emb Θ Ξ Θ2 Ξ2) by (eapply Emb_pre; [ apply gc_sub_push; eassumption | exact He ]).
      destruct (IHU _ _ He) as (HUE & HUU & HUA).
      destruct (IHΞ _ _ HeΞ) as (HR & HI & HA).
      split; [| split ].
      + intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr']; eauto.
      + intros p D Hr; destruct (ind_lookup_module _ _ _ _ Hr) as [T Hm].
        destruct (gc_module_frame _ _ _ _ _ _ Hm) as [(x & ip & -> & Hm') | Hm']; [ eauto |].
        apply (HI p); exact (ind_lookup_body _ _ _ _ _ Hm').
      + intros pq ? ? ? Hr; destruct (ind_alias_lookup_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr']; eauto.
  Qed.

  Corollary global_induction : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GV Θ Ξ Θ Ξ.
  Proof.
    intros * Hg; destruct global_induction_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
    exact (H _ _ Hg _ _ (Emb_refl _ _ Hg)).
  Qed.
End Induction.

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
  { emx_wf : ⊢ᵍ Θ2 ⍮ Ξ2
  ; emx_res : gc_subx Θ1 Ξ1 Θ2 Ξ2 }.

Lemma Embx_emb : forall Θ1 Ξ1 Θ2 Ξ2, Embx Θ1 Ξ1 Θ2 Ξ2 -> Emb Θ1 Ξ1 Θ2 Ξ2.
Proof. intros * [Hg Hs]; constructor; [ exact Hg | exact (gc_subx_sub _ _ _ _ Hs) ]. Qed.

Lemma Embx_refl : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> Embx Θ Ξ Θ Ξ.
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

Lemma Embx_nested : forall Θ Ξ mp pv Δ' Φ' Θ2 Ξ2,
    Embx Θ Ξ Θ2 Ξ2 ->
    Ctbx Θ2 Ξ2 (gs_tele Ξ) mp (ge_body pv Δ' Φ') ->
    Embx Θ ((mp, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * He [Hc Hbod]; constructor; [ exact (emx_wf _ _ _ _ He) | split ].
  - exact (em_res _ _ _ _ (Emb_nested _ _ _ _ _ _ _ _ (Embx_emb _ _ _ _ He) Hc)).
  - intros p r Hr; destruct (gc_body_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'].
    + apply Hbod; exact Hm.
    + exact (gc_subx_body _ _ _ _ _ _ (emx_res _ _ _ _ He) Hr').
Qed.

Lemma Ctbx_ind_ext : forall Θ2 Ξ2 T mp pv pq D Φ x b pv' A B,
    gm_fresh x Φ -> Ctbx Θ2 Ξ2 T mp (ge_ind pv pq D (Φ ⊳ x ↦ ge_def b pv' A B)) -> Ctbx Θ2 Ξ2 T mp (ge_ind pv pq D Φ).
Proof.
  intros * Hf [Hc Hbod]; split; [ exact (Ctb_ind_ext _ _ _ _ _ _ _ _ _ _ _ _ _ Hf Hc) |].
  intros z ip r Hr; apply Hbod; cbn [ge_subbody] in Hr |- *; apply gm_subbody_ext_fresh; assumption.
Qed.

Section ModInduction.
  (** The validity of an entry, read from a source context, at a target
      it embeds into. *)
  Variable V : gdeps -> gstack -> gdeps -> gstack -> ctx -> gentry -> Prop.
  Variable F : gdeps -> gstack -> ctx -> Prop.
  (** The validity of the declaration of an inductive type. *)
  Variable VD : gdeps -> gstack -> ind_decl -> Prop.

  (** A body is valid when its definitions and aliases are, and its body
      modules and the modules of its inductive types are, over their
      telescopes; the declaration of an inductive type is valid too. *)
  Fixpoint gm_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (Φ : gmod) : Prop :=
    match Φ with
    | gm_nil => True
    | gm_open Φ0 _ _ => gm_valid Θs Ξs Θ2 Ξ2 T Φ0
    | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body sm Φ'))) =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θs Ξs Θ2 Ξ2 (Δ ++ T) Φ'
    | gm_ext Φ0 _ (ge_ind _ _ D Φ') =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D) /\ gm_valid Θs Ξs Θ2 Ξ2 (ind_uparams D) Φ'
    | gm_ext Φ0 _ (ge_ind_alias pv Δ p Ns) =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ V Θs Ξs Θ2 Ξ2 T (ge_mod pv (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns)))) /\
        V Θs Ξs Θ2 Ξ2 T (ge_ind_alias pv Δ p Ns)
    | gm_ext Φ0 _ E => gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ V Θs Ξs Θ2 Ξ2 T E
    end.

  Definition ge_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
    match E with
    | ge_mod _ (gu_mk Δ (md_body sm Φ')) => F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θs Ξs Θ2 Ξ2 (Δ ++ T) Φ'
    | ge_ind _ _ D Φ' => VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D) /\ gm_valid Θs Ξs Θ2 Ξ2 (ind_uparams D) Φ'
    (** An inductive alias is valid as the module alias it is a view as, and
        as itself, the term it δ-unfolds to. *)
    | ge_ind_alias pv Δ p Ns =>
        V Θs Ξs Θ2 Ξ2 T (ge_mod pv (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns)))) /\ V Θs Ξs Θ2 Ξ2 T E
    | _ => V Θs Ξs Θ2 Ξ2 T E
    end.

  Lemma gm_valid_ext : forall Θs Ξs Θ2 Ξ2 T Φ x E,
      gm_valid Θs Ξs Θ2 Ξ2 T (Φ ⊳ x ↦ E) <-> gm_valid Θs Ξs Θ2 Ξ2 T Φ /\ ge_valid Θs Ξs Θ2 Ξ2 T E.
  Proof. intros; destruct E as [? ? ? ? | ? [Δ [? Φ' | E']] | ? ? ? ? | ? Δa pa Nsa]; cbn; tauto. Qed.

  Fixpoint gs_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Ξ : gstack) : Prop :=
    match Ξ with
    | nil => True
    | (_, U) :: Ξ' =>
        F Θ2 Ξ2 (gu_params U ++ gs_tele Ξ') /\ gm_valid Θs Ξs Θ2 Ξ2 (gu_params U ++ gs_tele Ξ') (gu_mod U) /\
        gs_valid Θs Ξs Θ2 Ξ2 Ξ'
    end.

  Definition gds_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Θ : gdeps) : Prop :=
    forall fp U, gds_lookup Θ fp = Some U -> F Θ2 Ξ2 (gu_params U) /\ gm_valid Θs Ξs Θ2 Ξ2 (gu_params U) (gu_mod U).

  (** Everything filed or open at [Θ ⍮ Ξ] is valid wherever [Θ ⍮ Ξ] embeds,
      read from any context that has what [Θ ⍮ Ξ] has. *)
  Definition GoodV (Θ : gdeps) (Ξ : gstack) : Prop :=
    forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> forall Θs Ξs, gc_sub Θ Ξ Θs Ξs -> gds_valid Θs Ξs Θ2 Ξ2 Θ /\ gs_valid Θs Ξs Θ2 Ξ2 Ξ.

  (** A definition is checked in a closed telescope [T]: the frames'
      parameters, or the uniform parameters of the inductive type whose
      module it is a member of.  It is valid wherever what the context it is
      checked in files and has open is valid, read from there, along any
      growth; it is so read from anywhere. *)
  Hypothesis Hdef : forall Θ Ξ T A M b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> gds_valid Θ Ξ Θ2 Ξ2 Θ -> gs_valid Θ Ξ Θ2 Ξ2 Ξ ->
      forall Θs Ξs, V Θs Ξs Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
  (** The other entries are valid read from any context that has what the
      context they are checked in has. *)
  Hypothesis Hax : forall Θ Ξ A i b pv Θ2 Ξ2 Θs Ξs,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
      V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
  Hypothesis Halias : forall Θ Ξ pv Δ E Θ2 Ξ2 Θs Ξs,
      tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
      GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
      V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
  Hypothesis Hindalias : forall Θ Ξ pv Δ p Ns D Θ2 Ξ2 Θs Ξs,
      tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> List.length Ns <= ind_nu D ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
      GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
      V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns).
  Hypothesis Hnil : forall Θ Ξ Δ Θ2 Ξ2,
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
  (** A declaration, and the telescope of its uniform parameters, which its
      module's members are checked in. *)
  Hypothesis Hind : forall Θ Ξ D Θ2 Ξ2,
      decl_typed Θ Ξ D -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D).

  (** An entry, and the context it is checked in: valid read from any
      context that has it and what the context it is checked in has. *)
  Definition GoodEV (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    GoodV Θ Ξ /\
    forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> Ctbx Θ2 Ξ2 (gs_tele Ξ) mp E ->
      forall Θs Ξs, gc_sub Θ Ξ Θs Ξs -> Ctb Θs Ξs (gs_tele Ξ) mp E -> ge_valid Θs Ξs Θ2 Ξ2 (gs_tele Ξ) E.

  Definition GoodMV (Θ : gdeps) (Ξ : gstack) (mp : qname) (Δ : ctx) (Φ : gmod) : Prop :=
    GoodV Θ Ξ /\
    forall Θ2 Ξ2, Embx Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 -> Embx Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ) /\
      forall Θs Ξs, gc_sub Θ ((mp, gu_body Δ Φ) :: Ξ) Θs Ξs -> gm_valid Θs Ξs Θ2 Ξ2 (Δ ++ gs_tele Ξ) Φ.

  Theorem global_valid_all :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> GoodV Θ Ξ) /\
    (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> GoodV Θ Ξ) /\
    (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> GoodEV Θ Ξ mp E) /\
    (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> GoodMV Θ Ξ mp Δ Φ) /\
    (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GoodV Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - (* a definition or an axiom *)
      split; [ assumption |]; intros Θ2 Ξ2 He _ Θs Ξs Hs _; cbn.
      match goal with
      | HM : forall M, ?o = Some M -> _ ⍮ _ ⍮ _ ⊢ M : _, IHM : forall M, ?o = Some M -> GoodV _ _ |- _ =>
          destruct o as [M0 |]; cbn;
          [ destruct (IHM M0 eq_refl _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ];
            eapply Hdef; [ exact (HM M0 eq_refl) | exact (IHM M0 eq_refl) | exact (Embx_emb _ _ _ _ He) | exact HΘ | exact HΞ ]
          | eapply Hax; eassumption ]
      end.
    - (* a body module: valid as its frame, pushed, is *)
      destruct H0 as [HG HM]; split; [ exact HG |]; intros Θ2 Ξ2 He Hc Θs Ξs Hs Hcs; cbn.
      destruct (HM _ _ (Embx_nested _ _ _ _ _ _ _ _ He Hc) He) as [HF HΦ].
      split; [ exact HF | apply HΦ; exact (gc_sub_nested _ _ _ _ _ _ _ _ Hs Hcs) ].
    - split; [ assumption | intros Θ2 Ξ2 He _ Θs Ξs Hs _; cbn; eapply Halias; eassumption ].
    - (* an inductive type, before the members of its module *)
      split; [ assumption |]; intros Θ2 Ξ2 He _ Θs Ξs _ _; cbn.
      edestruct Hind as [HD HF]; [| eassumption | exact He |].
      { repeat match goal with H : decl_mvc _ |- _ => destruct H as (? & ? & ?) end.
        repeat split; eauto. }
      repeat split; assumption.
    - (* one more member of the module of an inductive type: valid wherever
         the context it is checked in, with the entry so far, is *)
      rename H0 into IHE, H2 into IHM.
      match goal with HM : _ ⍮ ?Ξ' ⍮ _ ⊢ _ : _ |- _ => rename HM into HMt end.
      destruct IHE as [HG IHE]; split; [ exact HG |].
      intros Θ2 Ξ2 He Hc Θs Ξs Hs Hcs.
      pose proof (Ctbx_ind_ext _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) Hc) as Hc0.
      pose proof (Ctb_ind_ext _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) Hcs) as Hcs0.
      destruct (IHE _ _ He Hc0 _ _ Hs Hcs0) as (HD & HF & HΦ).
      cbn; split; [ exact HD | split; [ exact HF | split; [ exact HΦ |] ] ].
      (* the member's context: the frame with the entry so far *)
      destruct (wf_gstack_cons_inv _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HMt))) as (_ & Hu & _).
      pose proof (wf_gunit_mod _ _ _ _ Hu) as Hm; cbn [gu_params gu_mod] in Hm.
      inversion Hm; subst.
      match goal with Hf : gm_fresh y Φ0 |- _ => rename Hf into Hfy end.
      pose proof (gc_sub_grow Θ Ξ mq Δ _ _ (ge_ind pv (qname_in mq y) D Φ) Hfy) as Hgr.
      destruct (HG _ _ He _ _ Hgr) as [HΘ HΞ].
      assert (He1 : Emb Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv (qname_in mq y) D Φ)) :: Ξ) Θ2 Ξ2)
        by (apply Emb_entry; [ exact (Embx_emb _ _ _ _ He) | exact (proj1 Hc0) ]).
      destruct (IHE _ _ He Hc0 _ _ Hgr (Ctb_frame _ _ _ _ _ _ _ _ _ (gc_sub_refl _ _))) as (HD1 & HF1 & HΦ1).
      eapply Hdef; [ exact HMt | exact IHM | exact He1 | exact HΘ |].
      cbn [gs_valid gu_params gu_mod] in HΞ |- *; destruct HΞ as (HF0 & HΦ0 & HΞ0).
      split; [ exact HF0 | split; [| exact HΞ0 ] ].
      apply gm_valid_ext; split; [ exact HΦ0 |]; cbn; repeat split; assumption.
    - (* an inductive alias: valid as the module alias it is a view as, and
         as itself *)
      split; [ assumption | intros Θ2 Ξ2 He _ Θs Ξs Hs _; cbn; split; [ eapply Halias | eapply Hindalias ]; eassumption ].
    - split; [ assumption |]; intros Θ2 Ξ2 _ He; split; [ eapply Hnil; eassumption | intros; exact I ].
    - rename H0 into IHΦ, H2 into IHE.
      destruct IHΦ as [HG IHΦ]; split; [ exact HG |].
      intros Θ2 Ξ2 He Hout.
      assert (He' : Embx Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Embx_pre; [ apply gc_subx_grow; eassumption | exact He ]).
      destruct (IHΦ _ _ He' Hout) as [HF HΦ].
      split; [ exact HF |]; intros Θs Ξs Hs.
      apply gm_valid_ext; split; [ apply HΦ; eapply gc_sub_trans; [ apply gc_sub_grow; eassumption | exact Hs ] |].
      apply (proj2 IHE _ _ He' (Ctbx_frame _ _ _ _ _ _ _ _ _ (emx_res _ _ _ _ He))).
      + eapply gc_sub_trans; [ apply gc_sub_grow; eassumption | exact Hs ].
      + exact (Ctb_frame _ _ _ _ _ _ _ _ _ Hs).
    - intros Θ2 Ξ2 _ Θs Ξs _; split; [ intros fp U Hl; discriminate | exact I ].
    - (* a filed unit: valid as its closed frame was *)
      rename H into Hg, H0 into IHU.
      match goal with |- GoodV ((?f, _) :: _) nil => rename f into fp0 end.
      intros Θ2 Ξ2 He Θs Ξs Hs; split; [| exact I ].
      destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (_ & _ & [Hn _]).
      destruct (IHU Θ2 Ξ2 ltac:(eapply Embx_pre; [ apply gc_subx_file; exact Hn | exact He ])
                  Θs Ξs ltac:(eapply gc_sub_trans; [ apply gc_sub_file; exact Hn | exact Hs ])) as [HΘ HΞ].
      intros fq W Hl; cbn in Hl; destruct (path_beq fq fp0);
        [ injection Hl as <-; cbn [gs_valid gs_tele] in HΞ; rewrite app_nil_r in HΞ; tauto | exact (HΘ _ _ Hl) ].
    - rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He Θs Ξs Hs.
      assert (He0 : Embx Θ Ξ Θ2 Ξ2) by (eapply Embx_pre; [ apply gc_subx_push; eassumption | exact He ]).
      destruct (IHΞ _ _ He0 Θs Ξs ltac:(eapply gc_sub_trans; [ apply gc_sub_push; eassumption | exact Hs ])) as [HΘ HΞ].
      split; [ exact HΘ |].
      destruct (proj2 IHU _ _ He He0) as [HF HΦ]; cbn [gs_valid]; repeat split; [ assumption | apply HΦ; exact Hs | assumption ].
  Qed.

  Corollary global_valid : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GoodV Θ Ξ.
  Proof. intros; apply global_valid_all; assumption. Qed.

  (** *** Reading validity back *)

  Lemma gm_valid_subbody : forall Φ Θs Ξs Θ2 Ξ2 T x ip T' Φ',
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> F Θ2 Ξ2 T' /\ gm_valid Θs Ξs Θ2 Ξ2 T' Φ'.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? D Φ0 | ? Δa pa Nsa]; try discriminate.
    - destruct Hv as (_ & HF & Hv); destruct ip as [| w ip].
      + injection H as <- <-; split; assumption.
      + exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & HF & Hv); destruct ip as [| w ip].
      + injection H as <- <-; split; assumption.
      + exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_body : forall Θs Ξs Θ2 Ξ2 T Φ ip T' Φ',
      F Θ2 Ξ2 T -> gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_body T Φ ip = Some (T', Φ') -> F Θ2 Ξ2 T' /\ gm_valid Θs Ξs Θ2 Ξ2 T' Φ'.
  Proof.
    intros * HF Hv H; destruct ip as [| x ip]; cbn in H;
      [ injection H as <- <-; split; assumption | exact (gm_valid_subbody _ _ _ _ _ _ _ _ _ _ Hv H) ].
  Qed.

  Lemma gm_valid_resolve : forall Φ Θs Ξs Θ2 Ξ2 T ip E,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_resolve Φ ip = Some E -> exists T', V Θs Ξs Θ2 Ξ2 T' E.
  Proof.
    fix IH 1; intros [| Φ y E0 | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ Hv H) ].
    destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y);
      [| destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? D Φ0 | ? Δa pa Nsa]; try discriminate.
    - injection H as <-; exists T; exact (proj2 Hv).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_def : forall Φ Θs Ξs Θ2 Ξ2 T z b pv A B,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> V Θs Ξs Θ2 Ξ2 T (ge_def b pv A B).
  Proof.
    induction Φ as [| Φ IH y E0 | Φ IH c]; intros * Hv H; cbn in Hv, H; [ discriminate | | eauto ].
    destruct (String.eqb z y);
      [| destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? | ? Δa pa Nsa]; try discriminate.
    injection H; intros; subst; exact (proj2 Hv).
  Qed.

  Lemma gm_valid_alias : forall Φ Θs Ξs Θ2 Ξ2 T x ip U,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_alias U) -> exists T' pv, V Θs Ξs Θ2 Ξ2 T' (ge_mod pv U).
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [? Φ0 | E0]] | ? ? D Φ0 | pm Δa pa Nsa]; try discriminate.
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ Hv H).
    - destruct ip; [| discriminate ]; injection H as <-; exists T, pm; exact (proj2 Hv).
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ Hv H).
    - destruct ip; [| discriminate ]; injection H as <-; exists T, pm; exact (proj1 (proj2 Hv)).
  Qed.

  Lemma gm_valid_ind_target : forall Φ Θs Ξs Θ2 Ξ2 T ip Δ p Ns,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_ind_target Φ ip = Some (Δ, p, Ns) -> exists T' pv, V Θs Ξs Θ2 Ξ2 T' (ge_ind_alias pv Δ p Ns).
  Proof.
    unfold gm_ind_target; fix IH 1; intros [| Φ y E0 | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y);
      [| destruct E0 as [? ? ? ? | ? [Δ0 [? Φ0 | E1]] | ? ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ0 [? Φ0 | E1]] | ? ? D Φ0 | pm Δa pa Nsa]; cbn in H; try discriminate.
    - injection H as -> -> ->; exists T, pm; exact (proj2 (proj2 Hv)).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_ind : forall Φ Θs Ξs Θ2 Ξ2 T x ip T' D,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_body T' (Some D)) -> VD Θ2 Ξ2 D.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? ? | ? Δa pa Nsa]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [? Φ0 | E0]] | ? ? D0 Φ0 | pm Δa pa Nsa]; try discriminate;
      destruct ip as [| w ip]; try discriminate.
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
    - injection H; intros; subst; exact (proj1 (proj2 Hv)).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gs_valid_find : forall Θs Ξs Θ2 Ξ2 Ξ p U ip T,
      gs_valid Θs Ξs Θ2 Ξ2 Ξ -> gs_find_tele Ξ p = Some (U, ip, T) ->
      F Θ2 Ξ2 (gu_params U ++ T) /\ gm_valid Θs Ξs Θ2 Ξ2 (gu_params U ++ T) (gu_mod U).
  Proof.
    induction Ξ as [| [mp U0] Ξ IH]; intros * Hv H; cbn in Hv, H; [ discriminate |].
    destruct (qname_strip mp p); [ injection H as <- <- <-; split; apply Hv | exact (IH _ _ _ _ (proj2 (proj2 Hv)) H) ].
  Qed.

  Lemma good_body : forall Θ Ξ Θs Ξs Θ2 Ξ2 p T Φ, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      gc_body Θ Ξ p = Some (T, Φ) -> F Θ2 Ξ2 T /\ gm_valid Θs Ξs Θ2 Ξ2 T Φ.
  Proof.
    intros * HΘ HΞ H; unfold gc_body in H.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [HF Hv]; exact (gm_valid_subbody _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [HF Hv]; exact (gm_valid_body _ _ _ _ _ _ _ _ _ HF Hv H).
  Qed.

  Lemma good_resolve : forall Θ Ξ Θs Ξs Θ2 Ξ2 p E, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      gc_resolve Θ Ξ p = Some E -> exists T, V Θs Ξs Θ2 Ξ2 T E.
  Proof.
    intros * HΘ HΞ H; unfold gc_resolve, gc_resolve_u in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ p) as [[[U ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_resolve _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_resolve _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_alias : forall Θ Ξ Θs Ξs Θ2 Ξ2 p U, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      gc_module Θ Ξ p = Some (mr_alias U) -> exists T pv, V Θs Ξs Θ2 Ξ2 T (ge_mod pv U).
  Proof.
    intros * HΘ HΞ H; unfold gc_module, gc_module_u in H.
    destruct (gs_find_tele Ξ p) as [[[Uf [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_alias _ _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv].
      destruct (q_chain p) as [| x ip]; [ discriminate |]; exact (gm_valid_alias _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_ind_alias : forall Θ Ξ Θs Ξs Θ2 Ξ2 pq Δ p Ns, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      ind_alias_lookup Θ Ξ pq = Some (Δ, p, Ns) -> exists T pv, V Θs Ξs Θ2 Ξ2 T (ge_ind_alias pv Δ p Ns).
  Proof.
    intros * HΘ HΞ H; unfold ind_alias_lookup, ind_alias_lookup_u in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ pq) as [[[U ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_ind_target _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit pq)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_ind_target _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_ind : forall Θ Ξ Θs Ξs Θ2 Ξ2 p D, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      ind_lookup Θ Ξ p = Some D -> VD Θ2 Ξ2 D.
  Proof.
    intros * HΘ HΞ H.
    destruct (ind_lookup_module _ _ _ _ H) as [T H']; unfold gc_module, gc_module_u in H'.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_ind _ _ _ _ _ _ _ _ _ _ Hv H').
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv].
      destruct (q_chain p) as [| x ip]; [ discriminate |]; exact (gm_valid_ind _ _ _ _ _ _ _ _ _ _ Hv H').
  Qed.
End ModInduction.

(** ** The Syntactic Validity of Storage

    A definition is stored generalized over the telescope of its module,
    from a typed body under it; an alias's target denotes, wherever it is
    read, a typed module description; an inductive alias names an inductive
    type at typed arguments.  The telescopes of modules are well formed, and
    declarations of inductive types typed ([decl_typed]). *)

Definition syn_F (Θ : gdeps) (Ξ : gstack) (T : ctx) : Prop := tele_ass T /\ ⊢ Θ ⍮ Ξ ⍮ T.

Definition syn_VD : gdeps -> gstack -> ind_decl -> Prop := decl_typed.

Definition syn_V (Θ : gdeps) (Ξ : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A oM =>
      exists A0, A = ctx_pi T A0 /\ (exists i, Θ ⍮ Ξ ⍮ T ⊢ A0 : Typeω@i) /\
        (forall M, oM = Some M -> exists M0, M = ctx_fn T M0 /\ Θ ⍮ Ξ ⍮ T ⊢ M0 : A0)
  | ge_mod _ (gu_mk Δa (md_alias E')) =>
      Θ ⍮ Ξ ⍮ Δa ⊢ᵐ E' ≈ E' /\ ⊢ Θ ⍮ Ξ ⍮ Δa /\
      forall Γ, ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ ->
        (exists R, mdenote Θ Ξ (Δa ++ Γ) E' R) /\
        forall R, mdenote Θ Ξ (Δa ++ Γ) E' R -> desc_ok Θ Ξ (Δa ++ Γ) R /\ exists Rm, ds_mod Θ Ξ R = Some Rm
  | ge_ind_alias _ Δa pq Ns =>
      exists D, ind_lookup Θ Ξ pq = Some D /\ ⊢ Θ ⍮ Ξ ⍮ Δa /\ args_ok Θ Ξ Δa (ind_uparams D) Ns /\
        Θ ⍮ Ξ ⍮ Δa ⊢ᵐ me_apps (qname_mod pq) Ns ≈ me_apps (qname_mod pq) Ns
  | _ => True
  end.

(** Syntactic validity does not depend on where it is read from. *)
Abbreviation syn_Vs := (fun (_ : gdeps) (_ : gstack) => syn_V).

(** Everything stored at [Θ ⍮ Ξ] is valid there. *)
Definition valid_syn (Θ : gdeps) (Ξ : gstack) : Prop :=
  gds_valid syn_Vs syn_F syn_VD Θ Ξ Θ Ξ Θ /\ gs_valid syn_Vs syn_F syn_VD Θ Ξ Θ Ξ Ξ.

Lemma gm_valid_prefix : forall V F VD Θs Ξs Θ2 Ξ2 T Φ y Φ0 E,
    gm_valid V F VD Θs Ξs Θ2 Ξ2 T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> ge_valid V F VD Θs Ξs Θ2 Ξ2 T E.
Proof.
  intros V F VD Θs Ξs Θ2 Ξ2 T; induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hv Hp; cbn in Hp; [ discriminate | |].
  - apply gm_valid_ext in Hv as [Hv HE].
    destruct (String.eqb y x); [ injection Hp as -> -> ->; exact HE | eauto ].
  - destruct (existsb _ _); [ discriminate | cbn in Hv; eauto ].
Qed.

Lemma loc_valid : forall Θ Ξ p T Φ, valid_syn Θ Ξ -> loc Θ Ξ p T Φ ->
    syn_F Θ Ξ T /\ gm_valid syn_Vs syn_F syn_VD Θ Ξ Θ Ξ T Φ.
Proof.
  intros * [HΘ HΞ] [Hl | Hl].
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hl as <- <-; exact (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef).
  - exact (good_body _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl).
Qed.


(** An axiom or an abstract definition stored in a stored body is a member
    of the body's path, at the type it is stored at: read bare, it has no
    δ-reduct. *)
Lemma filed_def_wf : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ p T Φ y Φ0 b pv A oM i,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> loc Θ Ξ p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y (ge_def b pv A oM)) ->
    (if b then oM else None) = None ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p) y : A.
Proof.
  intros Θ Ξ Hg * HΓ Hl Hp Hn HA.
  destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R1 & Hm & HR1).
  assert (Hmd : ds_mod Θ Ξ R1 = Some (ds_closed nil p T Φ nil))
    by (destruct HR1 as [-> | (-> & Hb & _)]; cbn; [ reflexivity | rewrite Hb; reflexivity ]).
  eapply wf_mem; [ exact (loc_modexp_wf _ _ _ HΓ _ _ _ Hl) | | | exact HA | ].
  - eapply dn_mem; [ exact Hm | exact Hmd | cbn; rewrite Hp; reflexivity | constructor | reflexivity ].
  - destruct b, oM; reflexivity.
  - intros M Hr0; rewrite ds_named_nil in Hr0; cbn in Hr0; rewrite Hn in Hr0; discriminate.
Qed.

Lemma ds_ats_some_red : forall Ns A M R, ds_ats (ds_term A (Some M)) Ns = Some R -> exists A' M', R = ds_term A' (Some M').
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [| discriminate ].
  destruct (fn_view M) as [M' |]; [ exact (IH _ _ _ Ha) | discriminate ].
Qed.

(** An entry of a typed closed description, read with the arguments recorded
    and abstracted over the outside parameters, is typed. *)
Lemma desc_ok_entry_closed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ ->
    forall Γ Θ' p T Φ Ns y Γy E rd R R',
    desc_ok Θ Ξ Γ (ds_closed Θ' p T Φ Ns) -> ds_entry (ds_closed Θ' p T Φ Ns) y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (Some (qname_in p y)) E R -> ds_read rd R = Some R' -> desc_ok Θ Ξ Γ R'.
Proof.
  intros Θ Ξ Hg Hv * HR He Hed Hr.
  inversion HR as [| | | Γ0 Θa T0 Φ1 Ns0 Θ0 Ξ0 p0 Hg0 Hsub Hloc Ha HsT HT HΘ' Hargs HaΘ']; subst.
  cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 x E0 | ? ? ?] |] eqn:Hp; try discriminate.
  injection He as <- <- <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
  cbn in Hr; destruct (ds_ats R Ns) as [R0 |] eqn:Hats; [| discriminate ]; injection Hr as <-.
  (* the entry as it is stored now, grown, is valid *)
  assert (Hloc' : exists Φ', loc Θ Ξ p T Φ').
  { destruct Hloc as [Hf | Hb].
    - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φ' & [Hf' | [Hb' _]]); exists Φ'; [ left | right ]; assumption.
    - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φ' & Hb' & _); exists Φ'; right; exact Hb'. }
  destruct Hloc' as (Φ' & Hloc').
  pose proof (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent) as HeΘ0.
  destruct (gc_sub_entry _ _ _ _ _ _ Hsub HeΘ0) as (E1 & HeΘ & Hgr).
  pose proof (proj1 (loc_entry _ _ Hg _ _ _ Hloc' _ _) HeΘ) as Hent1.
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hloc'))) Hent1) as (Φ0' & Hp1).
  destruct (loc_valid _ _ _ _ _ Hv Hloc') as [_ HvΦ].
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp1) as HE0.
  pose proof (gm_coh_prefix _ _ _ _ _ (loc_coh _ _ Hg0 _ _ _ Hloc) Hp) as HcE0.
  pose proof (loc_closed _ _ Hg0 _ _ _ Hloc) as [_ HcΦ].
  pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
  pose proof (closed_tele_wf _ _ _ _ HsT HT HΘ') as HTΘ.
  apply desc_ok_up; [| exact HΘ' | exact HaΘ' ].
  destruct E0 as [b pv A oM | pv [Δ [sm Φy | E'] ] | pv pq D ΦD | pv Δa pq Nsa ].
  - (* a definition: its body, applied *)
    cbn in Hgr; subst E1.
    cbn in HE0; destruct HE0 as (A0 & -> & [i HA0] & HM0).
    inversion Hed; subst.
    assert (Hom : exists om0, (if b then oM else None) = option_map (ctx_fn T) om0 /\ forall M0, om0 = Some M0 -> Θ ⍮ Ξ ⍮ T ⊢ M0 : A0).
    { destruct b; [| exists None; split; [ reflexivity | discriminate ] ].
      destruct oM as [M |]; [| exists None; split; [ reflexivity | discriminate ] ].
      destruct (HM0 M eq_refl) as (M0 & -> & HM); exists (Some M0); split; [ reflexivity | intros ? [= <-]; exact HM ]. }
    destruct Hom as (om0 & Hom & Hom0).
    rewrite Hom in Hats; change (ds_term (ctx_pi T A0) (option_map (ctx_fn T) om0)) with (ds_up T (ds_term A0 om0)) in Hats.
    destruct om0 as [M0 |].
    + (* transparent: its body *)
      destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) T (ds_term A0 (Some M0)) HTΘ Ha (args_ok_length _ _ _ _ _ Hargs) (args_ok_insts _ _ _ _ _ Hargs)) as (R1 & HR1 & Hok1).
      { constructor; [ exists i; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΘ) | intros M1 HM; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT (Hom0 _ HM) HTΘ) ]. }
      rewrite Hats in HR1; injection HR1 as <-.
      destruct (ds_ats_some_red _ _ _ _ Hats) as (A' & M' & ->); apply ds_named_cases; exact Hok1.
    + (* an axiom or abstract: its name, at the arguments *)
      destruct (ctx_pi_wf0 _ _ _ _ _ HA0) as [j Hj].
      pose proof (filed_def_wf _ _ Hg _ _ _ _ _ _ _ _ _ _ _ HΘ' Hloc' Hp1 Hom
                    (closed_weaken_exp _ _ _ _ _ HΘ' Hj (proj1 HcE) ltac:(cbn; exact I))) as Hname.
      destruct (ats_up_self_ok _ _ Hg Ns (Θ' ++ Γ) T A0 _ HTΘ Ha (args_ok_length _ _ _ _ _ Hargs) (args_ok_insts _ _ _ _ _ Hargs)
                  (ex_intro _ i (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΘ)) Hname) as (R1 & HR1 & Hok1).
      rewrite Hats in HR1; injection HR1 as <-.
      (* read bare, it is the term of no δ-reduct itself *)
      apply ds_named_cases; [| exact Hok1 ].
      destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) T (ds_term A0 None) HTΘ Ha (args_ok_length _ _ _ _ _ Hargs) (args_ok_insts _ _ _ _ _ Hargs)) as (R2 & HR2 & Hok2).
      { constructor; [ exists i; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΘ) | intros ? [=] ]. }
      rewrite Hats in HR2; injection HR2 as <-; exact Hok2.
  - (* a closed submodule: its body, at the arguments recorded *)
    destruct HcE as (-> & HsΔ & HcΦy).
    destruct E1 as [| pv1 [Δ1 [sm1 Φy1 | ?]] | | ]; cbn in Hgr; try discriminate; destruct Hgr as (<- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hx : body_xp _ _ _ Φy ?Φx |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ (body_xp_noopen Θ Ξ _ _ (body_closed_noopen _ _ HcΦy))) as <- end.
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    rewrite ds_ats_closed_nil in Hats; injection Hats as <-; cbn [List.app].
    destruct HE0 as [[HaΔT HΔT] _].
    destruct (loc_child_mod _ _ Hg0 _ _ _ Hloc _ _ _ _ _ Hent) as [Hb _].
    rewrite ds_named_fix by reflexivity.
    econstructor; [ exact Hg0 | exact Hsub | right; exact Hb | exact HaΔT
                  | exact (proj1 (gctx_closed_body _ _ _ _ _ (wf_gstack_closed _ _ Hg0) Hb)) | exact HΔT | exact HΘ'
                  | apply args_ok_ext; exact Hargs | constructor ].
  - (* an alias: the module part of what its target denotes, at the
       arguments for the telescope it is stored over *)
    cbn in Hgr; subst E1.
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    cbn [List.app] in *.
    cbn [syn_V] in HE0; destruct HE0 as [_ [HΔ Hcl]].
    rewrite gunit_scoped_mk in HcE; destruct HcE as [HsΔ HsE]; cbn [moddef_scoped] in HsE; rewrite Nat.add_0_r in HsE.
    destruct HcE0 as (Δ0 & -> & HaΔ0).
    pose proof (ctx_app_wf_tail _ _ _ _ HΘ') as HΓ.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ HΓ) as HΔΓ.
    match goal with Hm : mdenote _ _ _ E' ?R1, Hmd : ds_mod _ _ ?R1 = Some ?R1m |- _ =>
      destruct (proj2 (Hcl _ HΔΓ) _ Hm) as [Hok1 _];
      pose proof (desc_ok_mod _ _ Hg _ _ _ Hok1 Hmd) as Hok1m;
      pose proof (proj1 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ Hm _
                    (slots_ok_app _ 0 _ ltac:(intros ? ? ?; lia) ltac:(exact HsΔ)) ltac:(rewrite Nat.add_0_r; exact HsE)) as HsR1;
      rewrite Nat.add_0_r in HsR1;
      pose proof (ds_mod_scoped _ _ _ _ _ (wf_gstack_closed _ _ Hg) HsR1 Hmd) as HsR1m end.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HTΘ)) as HΔΘ.
    pose proof (desc_ok_tele_weaken _ _ Hg _ Θ' _ _ HsΔ HΔΓ HΔΘ HsR1m Hok1m) as Hok2.
    assert (HaΔ : tele_ass (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
    pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) (Δ0 ++ T) _ HΔΘ HaΔ (args_ok_length _ _ _ _ _ Hargs') (args_ok_insts _ _ _ _ _ Hargs') Hok2) as (R2 & HR2 & Hok3).
    rewrite Hats in HR2; injection HR2 as <-.
    rewrite ds_named_fix; [ exact Hok3 |]; apply ds_self_mod.
    eapply ds_ats_is_mod; [| exact Hats ]; apply ds_is_mod_up; eapply ds_mod_is_mod; eassumption.
  - (* an inductive type, stored at its own path: its type former at the
       arguments *)
    destruct E1 as [| | pv1 pq1 D1 ΦD1 |]; cbn in Hgr; try discriminate; destruct Hgr as (<- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed; subst.
    rewrite ds_ats_ind_nil in Hats; injection Hats as <-; cbn [List.app].
    rewrite ds_named_fix by reflexivity.
    destruct HE0 as (HD & [HaU HU] & _).
    destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
    assert (Hpq : pq = qname_in p y).
    { apply (gc_entry_selfpath _ _ Hg0 _ pv _ D ΦD); exact HeΘ0. }
    subst pq.
    assert (Hl : ind_lookup Θ Ξ (qname_in p y) = Some D).
    { apply (ind_lookup_gc_sub _ _ _ _ _ _ Hsub).
      destruct (gm_entry_head _ _ _ Hent) as (z & ip & [= <- <-] & Hin).
      destruct (loc_read _ _ Hg0 _ _ _ Hloc _ Hin nil) as (_ & _ & Hm & _ & _).
      apply (ind_lookup_body _ _ _ (ind_uparams D)); rewrite qname_in_app, Hm.
      exact (proj2 (gm_entry_subbody_ind _ T _ _ _ _ _ Hent)). }
    econstructor; [ exact Hl | exact HaU | apply ctx_scoped_uparams; apply (proj1 HcE) | exact HU | exact HΘ' | rewrite HΔ0; apply args_ok_ext; exact Hargs | constructor ].
  - (* an inductive alias: the type former at its arguments, over its
       telescope *)
    cbn in Hgr; subst E1.
    cbn [ge_read] in Hed; inversion Hed; subst.
    change (ds_ind Δa pq Nsa) with (ds_up Δa (ds_ind nil pq Nsa)) in Hats.
    destruct HE0 as [_ (D & Hl & HΔa & HargsA & _)].
    destruct HcE0 as (Δ0 & -> & HaΔ0).
    destruct HcE as [HsΔ HsN].
    destruct Hv as [HvΘ HvΞ].
    pose proof (good_ind _ _ _ _ _ _ _ _ _ _ _ HvΘ HvΞ Hl) as HDt; cbn [syn_VD] in HDt.
    destruct (decl_typed_uparams _ _ _ HDt) as [HU HaU].
    pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as HDc.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔa (ctx_app_wf_tail _ _ _ _ HTΘ)) as HΔΘ.
    assert (Hσ : Θ ⍮ Ξ ⍮ (Δ0 ++ T) ++ Θ' ++ Γ ⊢ˢ sb_qn (length (Δ0 ++ T)) Id : (Δ0 ++ T) ++ ⋅).
    { pose proof (wf_sub_ext _ _ (Δ0 ++ T) _ _ _ (wf_sub_to_nil _ _ _ (ctx_app_wf_tail _ _ _ _ HTΘ))) as Hx.
      rewrite tele_sub_id in Hx; apply Hx; [ exact HΔΘ | rewrite List.app_nil_r; exact HΔa ]. }
    rewrite List.app_nil_r in Hσ.
    pose proof (args_ok_sub _ _ _ _ _ _ _ HargsA Hσ) as HargsB.
    rewrite (List.map_ext_in _ (fun M => M)) in HargsB by
      (intros M HM; eapply (proj1 syn_scoped_sub_id); [ eapply List.Forall_forall in HsN; [ exact HsN | exact HM ] |
         intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ] ]).
    rewrite List.map_id in HargsB.
    assert (Hok : desc_ok Θ Ξ ((Δ0 ++ T) ++ Θ' ++ Γ) (ds_ind nil pq Nsa)).
    { econstructor; [ exact Hl | exact HaU | apply ctx_scoped_uparams; apply HDc | exact HU | exact HΔΘ | exact HargsB | constructor ]. }
    assert (HaΔ : tele_ass (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
    pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) (Δ0 ++ T) _ HΔΘ HaΔ (args_ok_length _ _ _ _ _ Hargs') (args_ok_insts _ _ _ _ _ Hargs') Hok) as (R2 & HR2 & Hok3).
    rewrite Hats in HR2; injection HR2 as <-.
    destruct (ds_ats_ind _ _ _ _ _ Hats) as (? & ? & ->); rewrite ds_named_fix by reflexivity; exact Hok3.
Qed.

(** ** Well-formed Module Expressions Denote Typed Descriptions *)

(** The unit of each slot of [Γ] denotes, where it stands, only typed
    descriptions. *)
Definition slots_typed (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  forall Γ1 U Γ0, Γ = Γ1 ++ ce_mod U :: Γ0 -> forall R, udenote Θ Ξ Γ0 None U R -> desc_ok Θ Ξ Γ0 R.

Lemma slots_typed_nil : forall Θ Ξ, slots_typed Θ Ξ nil.
Proof. intros * Γ1 U Γ0 Heq; destruct Γ1; discriminate. Qed.

Lemma slots_typed_cons : forall Θ Ξ Γ e, slots_typed Θ Ξ Γ ->
    (forall U, e = ce_mod U -> forall R, udenote Θ Ξ Γ None U R -> desc_ok Θ Ξ Γ R) -> slots_typed Θ Ξ (e :: Γ).
Proof.
  intros * HΓ He Γ1 U Γ0 Heq R HR.
  destruct Γ1 as [| e' Γ1]; cbn in Heq; injection Heq as Heq1 Heq2; subst.
  - exact (He _ eq_refl _ HR).
  - exact (HΓ _ _ _ eq_refl _ HR).
Qed.

Lemma slots_typed_app : forall Θ Ξ Ψ Γ, slots_typed Θ Ξ (Ψ ++ Γ) -> slots_typed Θ Ξ Γ.
Proof.
  intros * HΓ Γ1 U Γ0 -> R HR; apply (HΓ (Ψ ++ Γ1) U Γ0); [ rewrite <- List.app_assoc; reflexivity | exact HR ].
Qed.

(** A description of a unit, weakened past one entry. *)
Lemma desc_ok_shift : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ e U R0, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> gunit_scoped (length Γ) U ->
    udenote Θ Ξ Γ None U R0 -> desc_ok Θ Ξ Γ R0 ->
    forall R, udenote Θ Ξ (e :: Γ) None (gunit_wk U ↑) R -> desc_ok Θ Ξ (e :: Γ) R.
Proof.
  intros * Hg * He HU HR0 Hok R HR.
  rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HR _ (udenote_shift _ _ _ _ _ _ He HU HR0)).
  eapply desc_ok_sub; [ exact Hg | exact Hok | apply wf_sub_of_wk, wf_wk_shift; exact He ].
Qed.

Lemma slots_typed_lookup : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ x U, Γ ∋ #x ≔ₘ U -> ⊢ Θ ⍮ Ξ ⍮ Γ -> slots_typed Θ Ξ Γ ->
    forall R, udenote Θ Ξ Γ None U R -> desc_ok Θ Ξ Γ R.
Proof.
  intros Θ Ξ Hg; induction 1 as [U Γ | Γ n U e Hl IH]; intros HΓ Hs.
  - destruct (ctx_decomp_mod HΓ) as [HΓ0 HU].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R0 HR0] & _).
    destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (_ & HUs & _).
    eapply desc_ok_shift; [ exact Hg | exact HΓ | exact HUs | exact HR0 | exact (Hs nil U Γ eq_refl _ HR0) ].
  - pose proof (ctx_decomp_tail HΓ) as HΓ0.
    destruct (proj1 denote_exists _ _ _ HΓ0 _ _ Hl) as [R0 HR0].
    pose proof (ctx_scoped_lookup_mod _ _ _ 0 (wf_ctx_scoped _ _ _ HΓ0) Hl) as HUs; rewrite Nat.add_0_r in HUs.
    eapply desc_ok_shift; [ exact Hg | exact HΓ | exact HUs | exact HR0 |].
    exact (IH HΓ0 (slots_typed_app _ _ (e :: nil) _ Hs) _ HR0).
Qed.

(** A loaded unit or an open frame, at no argument. *)
Lemma desc_ok_unit : forall Θ Ξ Γ H p T Φ, ⊢ Θ ⍮ Ξ ⍮ Γ -> valid_syn Θ Ξ -> mod_qname H = Some p ->
    gc_unit Θ Ξ H = Some (T, Φ) -> desc_ok Θ Ξ Γ (ds_closed nil p T Φ nil).
Proof.
  intros * HΓ Hv Hq Hu.
  destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq' & Hl); rewrite Hq in Hq'; injection Hq' as <-.
  destruct (loc_valid _ _ _ _ _ Hv Hl) as [[Ha HT] _].
  econstructor; [ exact (ctx_wf_gctx _ _ _ HΓ) | apply gc_sub_refl | exact Hl | exact Ha | exact (wf_ctx_scoped _ _ _ HT) | exact HT | exact HΓ | | constructor ].
  exists T, nil; rewrite List.app_nil_r; repeat split; [ constructor | exact HΓ |].
  intros k ? ? Hk; rewrite List.nth_error_nil in Hk; discriminate.
Qed.

(** A member of a module of typed descriptions. *)
Lemma desc_ok_mem : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ H y R,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> (forall R0, mdenote Θ Ξ Γ H R0 -> desc_ok Θ Ξ Γ R0) ->
    mdenote Θ Ξ Γ (me_mem H y) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * Hg Hv * HΓ HH Hm; inversion Hm; subst.
  - eapply desc_ok_unit; eassumption.
  - match goal with Hm0 : mdenote _ _ _ H ?R0, Hd : ds_mod _ _ ?R0 = Some ?Rm, He : ds_entry ?Rm _ = Some _ |- _ =>
      pose proof (desc_ok_mod _ _ Hg _ _ _ (HH _ Hm0) Hd) as Hok;
      destruct Rm; cbn in He; try discriminate
    end.
    + eapply desc_ok_entry_open; eassumption.
    + eapply desc_ok_entry_closed; eassumption.
Qed.

Lemma body_shape_names : forall Φ Φ', body_shape Φ Φ' -> gm_names Φ = gm_names Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros [| Φ' x' E' | Φ' H' its'] Hs; cbn in Hs |- *; try contradiction; [ reflexivity | |].
  - destruct Hs as (Hs & <- & _); f_equal; apply IH; exact Hs.
  - destruct Hs as [Hs <-]; f_equal; apply IH; exact Hs.
Qed.

Lemma body_shape_l : forall Φ Φ', body_shape Φ Φ' -> body_shape Φ Φ.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros [| Φ' x' E' | Φ' H' its'] Hs; cbn in Hs |- *; try contradiction; [ exact I | |].
  - destruct Hs as (Hs & _ & HE); split; [ exact (IH _ Hs) | split; [ reflexivity |] ].
    destruct E as [? ? ? [] | | | ], E' as [? ? ? [] | | | ]; cbn in HE |- *; try contradiction; destruct_all; auto.
  - destruct Hs as [Hs _]; split; [ exact (IH _ Hs) | reflexivity ].
Qed.

Lemma body_shape_r : forall Φ Φ', body_shape Φ Φ' -> body_shape Φ' Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros [| Φ' x' E' | Φ' H' its'] Hs; cbn in Hs |- *; try contradiction; [ exact I | |].
  - destruct Hs as (Hs & _ & HE); split; [ exact (IH _ Hs) | split; [ reflexivity |] ].
    destruct E as [? ? ? [] | | | ], E' as [? ? ? [] | | | ]; cbn in HE |- *; try contradiction; destruct_all; auto.
  - destruct Hs as [Hs _]; split; [ exact (IH _ Hs) | reflexivity ].
Qed.

(** An open body unit, whose expanded body extends its context well. *)
Lemma desc_ok_body : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ Φ Φx R,
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> ⊢ Θ ⍮ Ξ ⍮ (body_ctx Φx ++ Δ) ++ Γ -> slots_typed Θ Ξ ((body_ctx Φx ++ Δ) ++ Γ) ->
    tele_ass Δ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H) ->
    body_shape Φ Φ ->
    udenote Θ Ξ Γ None (gu_open Δ Φ) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * Hg * Hx HΓ Hs Ha Hsh Hnd Ho Hsw HR.
  assert (HUw : Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_open nil Φ ≈ gu_open nil Φ).
  { apply unit_eq_of_full; eapply (unit_full_body _ _ (Δ ++ Γ) nil Φ Φx); cbn [List.app]; try assumption;
      [ rewrite <- List.app_assoc in HΓ; exact HΓ | constructor ]. }
  inversion HR; subst.
  match goal with Hx' : body_xp _ _ _ Φ ?Φ0 |- _ =>
    rewrite <- (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ Hx') in * end.
  match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
  constructor.
  - rewrite <- List.app_assoc in HΓ; exact HΓ.
  - eapply body_xp_result_noopen; exact Hx.
  - intros y Φ0 pm U Hp R0 HR0.
    destruct (gm_prefix_body_ctx _ _ _ (body_xp_result_noopen _ _ _ _ _ Hx) Hp) as (Ψ & HΨ).
    apply (Hs Ψ U (body_ctx Φ0 ++ Δ ++ Γ)); [ rewrite HΨ; cbn [body_ctx]; rewrite <- !List.app_assoc; reflexivity | exact HR0 ].
  - exact Ha.
  - exact Hsh.
  - rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd.
  - exact HUw.
Qed.

(** An alias unit of a typed target. *)
Lemma desc_ok_alias : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ E R, ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> tele_ass Δ ->
    (forall R0, mdenote Θ Ξ (Δ ++ Γ) E R0 -> desc_ok Θ Ξ (Δ ++ Γ) R0) ->
    udenote Θ Ξ Γ None (gu_mk Δ (md_alias E)) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * Hg * HΓ Ha HE HR; inversion HR; subst.
  apply desc_ok_up; [| exact HΓ | exact Ha ].
  eapply desc_ok_mod; [ exact Hg | apply HE; eassumption | eassumption ].
Qed.


(** ** [β] Keeps Descriptions Typed *)

Lemma tele_view_last : forall L X, tele_view (L ++ ce_ass X :: nil) = Some (X, L).
Proof. intros; unfold tele_view; rewrite List.rev_app_distr; cbn; rewrite List.rev_involutive; reflexivity. Qed.

Lemma desc_ok_mtele_last : forall Θ Ξ Γ X R2, ds_is_mod R2 -> desc_ok Θ Ξ Γ (ds_up (ce_ass X :: nil) R2) ->
    exists T1, ds_mtele Θ Ξ (ds_up (ce_ass X :: nil) R2) = Some (T1 ++ ce_ass X :: nil).
Proof.
  intros * Hm Hok; destruct R2 as [| Δ Φ | Θ' p T Φ Ns |]; cbn in Hm; try contradiction.
  - exists Δ; reflexivity.
  - inversion Hok as [| | | Γ0 Θa T0 Φ1 Ns0 Θ0 Ξ0 p0 Hg0 Hsub Hloc Ha HsT HT HΘ' Hargs]; subst.
    pose proof (args_ok_length _ _ _ _ _ Hargs) as Hle.
    unfold ds_mtele; cbn; destruct (Nat.leb_spec (length Ns) (length T)) as [_ | ?]; [| lia ].
    eexists; rewrite List.app_assoc; reflexivity.
Qed.

Lemma desc_ok_beta : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ X D N,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) D ≈ gu_mk (Δ ++ ce_ass X :: nil) D ->
    (forall R, udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass X :: nil) D) R -> desc_ok Θ Ξ Γ R) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    (forall R, mdenote Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) R -> desc_ok Θ Ξ Γ R) /\
    (forall R, mdenote Θ Ξ Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ) R -> desc_ok Θ Ξ Γ R).
Proof.
  intros Θ Ξ Hg * HU HUok HN.
  assert (Hl : forall R, mdenote Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) R -> desc_ok Θ Ξ Γ R).
  { intros R HR; inversion HR; subst; [ unfold gc_unit in *; cbn in *; discriminate |].
    match goal with Hm : mdenote _ _ _ (me_lit _) ?R0, Ha : ds_at ?R0 N = Some R |- _ =>
      rename Ha into Hat; inversion Hm; subst; try (cbn in *; discriminate) end.
    match goal with Hu : udenote _ _ _ None _ ?R0 |- _ =>
      pose proof (HUok _ Hu) as Hok;
      destruct (udenote_last _ _ _ _ _ _ _ Hu) as (R2 & Hu2 & ->);
      destruct (desc_ok_mtele_last _ _ _ _ _ (udenote_is_mod _ _ _ _ _ _ Hu2) Hok) as (T1 & Ht) end.
    exact (desc_ok_at _ _ Hg _ _ _ _ _ _ _ Hok Ht (tele_view_last _ _) HN Hat). }
  split; [ exact Hl |].
  intros R HR.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R1 HR1] & _).
  destruct (mdenote_beta _ _ _ _ _ _ N HU _ HR1) as (R' & H1 & H2 & _).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ H2); exact (Hl _ H1).
Qed.
(** What the unit a typed module part stands for denotes is typed: the
    module part itself, or the inductive type it is the module of. *)
Lemma ds_unit_desc_ok : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Rm, desc_ok Θ Ξ Γ Rm -> ds_canon Θ Ξ Rm -> ds_is_mod Rm ->
    ds_xp Θ Ξ Γ Rm -> forall R, mdenote Θ Ξ Γ (ds_unit Rm) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros Θ Ξ Hg * Hok Hc Hm Hxp R HR.
  pose proof (proj1 (mdenote_functional_all _ _ Hg)) as Hf.
  destruct Rm as [A om | Δ Φw Φ | [| e Θ'] p T Φ Ns | Θ0 p Ns]; cbn in Hm, Hc, Hxp, HR; try contradiction.
  - inversion HR; subst; [ cbn in *; discriminate |]; match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hx : body_xp _ _ _ Φw ?Φx, Hb : ds_body _ _ _ _ _ = Some _ |- _ =>
      rewrite <- (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hxp _ Hx) in Hb; cbn in Hb; injection Hb as <- end.
    exact Hok.
  - destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hc) as (R1 & Hm1 & [-> | (-> & Hb & D & Hl)]).
    + pose proof (mdenote_apps _ _ _ _ _ _ _ Hm1 (ds_ats_closed_nil Ns p T Φ nil)) as Hm2.
      rewrite (Hf _ _ _ HR _ Hm2); exact Hok.
    + pose proof (mdenote_apps _ _ _ _ _ _ _ Hm1 (ds_ats_ind_nil Ns p nil)) as Hm2.
      rewrite (Hf _ _ _ HR _ Hm2); cbn [List.app].
      inversion Hok as [| | | Γ0 Θa T0 Φ1 Ns0 Θ1 Ξ1 p0 Hg0 Hsub Hloc Ha HsT HT HΘ' Hargs]; subst.
      pose proof (ind_gc_body _ _ _ _ _ _ Hl Hb) as ->.
      econstructor; [ exact Hl | exact Ha | exact HsT | exact HT | exact HΘ' | exact Hargs | constructor ].
  - inversion HR; subst; [ cbn in *; discriminate |]; match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    destruct (filed_denote _ _ Hg _ _ _ ((e :: Θ') ++ Γ) Ns (gc_loc_of_loc _ _ Hg _ _ _ Hc)) as (R2 & HR2 & HR2m).
    match goal with Hm0 : mdenote _ _ _ _ ?R0, Hd : ds_mod _ _ ?R0 = Some _ |- _ =>
      rewrite (Hf _ _ _ Hm0 _ HR2), HR2m in Hd; injection Hd as <- end.
    exact Hok.
Qed.

(** Over valid storage, every unit and module expression of a judgment
    denotes typed descriptions only, and so do the slots of its context. *)
Theorem desc_typed :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> valid_syn Θ Ξ -> slots_typed Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> valid_syn Θ Ξ -> slots_typed Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> valid_syn Θ Ξ -> slots_typed Θ Ξ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> valid_syn Θ Ξ -> slots_typed Θ Ξ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> valid_syn Θ Ξ -> slots_typed Θ Ξ Γ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> valid_syn Θ Ξ ->
     slots_typed Θ Ξ Γ /\ slots_typed Θ Ξ (Ψ ++ Γ) /\ slots_typed Θ Ξ (Ψ' ++ Γ)) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> valid_syn Θ Ξ ->
     slots_typed Θ Ξ Γ /\ (forall R, udenote Θ Ξ Γ None U R -> desc_ok Θ Ξ Γ R) /\
     (forall R, udenote Θ Ξ Γ None U' R -> desc_ok Θ Ξ Γ R)) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> valid_syn Θ Ξ ->
     slots_typed Θ Ξ Γ /\ (forall R, mdenote Θ Ξ Γ H R -> desc_ok Θ Ξ Γ R) /\
     (forall R, mdenote Θ Ξ Γ H' R -> desc_ok Θ Ξ Γ R)).
Proof.
  apply syntactic_wf_mut_ind; intros;
    match goal with Hv : valid_syn _ _ |- _ =>
      repeat match goal with IH : valid_syn _ _ -> _ |- _ => specialize (IH Hv) end end;
    destruct_conjs.
  all: try match goal with |- slots_typed _ _ ?G => solve [ assumption ] end.
  all: try solve [ apply slots_typed_nil ].
  all: try solve [ apply slots_typed_cons; [ assumption | first [ intros; discriminate | intros ? [= <-]; assumption ] ] ].
  all: try match goal with |- slots_typed _ _ _ /\ _ => split; [ assumption |] end.
  all: try solve [ cbn [List.app]; split; (apply slots_typed_cons;
      [ assumption | first [ intros; discriminate | intros ? [= <-]; assumption ] ]) ].
  all: try solve [ split; assumption ].
  all: assert (Hg : ⊢ᵍ Θ ⍮ Ξ) by
    (first [ eapply ctx_wf_gctx; eassumption | eapply ctx_wf_gctx, presup_modexp_eq_ctx; eassumption
           | eapply ctx_wf_gctx, presup_unit_eq_ctx; eassumption | eapply ctx_wf_gctx, presup_ext_eq_ctx; eassumption ]).
  - (* an open body unit: each side by its own extension *)
    match goal with Hb : body_shape ?Φ ?Φ', Hnd : List.NoDup (gm_names ?Φ),
                    Hx : body_xp _ _ _ ?Φ ?Φx, Hx' : body_xp _ _ _ ?Φ' ?Φx' |- _ =>
      assert (Hnd' : List.NoDup (gm_names Φ')) by (rewrite <- (body_shape_names _ _ Hb); exact Hnd);
      pose proof (body_shape_l _ _ Hb); pose proof (body_shape_r _ _ Hb) end.
    match goal with Hb : body_shape ?Φx ?Φx', Hx : body_xp _ _ _ _ ?Φx |- _ =>
      pose proof (body_shape_l _ _ Hb); pose proof (body_shape_r _ _ Hb) end.
    split; intros R HR;
      match goal with
      | Hx : body_xp _ _ _ ?Φ ?Φx, Hu : udenote _ _ _ _ (gu_open _ ?Φ) _,
        HX : wf_ext_eq _ _ _ (body_ctx ?Φx ++ ?Δ) _, Hs : slots_typed _ _ ((body_ctx ?Φx ++ ?Δ) ++ _),
        Ho : forall k Ψ H, nth_error (body_opens ?Φ ?Φx) k = Some (Ψ, H) -> _ |- _ =>
          eapply desc_ok_body; [ exact Hg | exact Hx | exact (ext_eq_ctx_left _ _ _ _ _ HX) | exact Hs | assumption | assumption
                               | assumption | exact Ho | assumption | exact Hu ]
      end.
  - (* an alias unit *)
    split; intros R HR; eapply desc_ok_alias; try exact HR; first [ exact Hg | eapply presup_modexp_eq_ctx; eassumption | assumption ].
  - (* an alias of a literal, and the literal over both telescopes *)
    match goal with HU : wf_unit_eq _ _ (?Δ ++ ?Γ) (gu_mk ?Δ' ?D) _, Ha : tele_ass ?Δ,
                    IH : forall R, udenote _ _ (?Δ ++ ?Γ) None (gu_mk ?Δ' ?D) R -> desc_ok _ _ _ R |- _ =>
      pose proof (presup_unit_eq_ctx HU) as HΔ;
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & (R0 & HR0) & _);
      split; intros R HR;
      [ eapply desc_ok_alias; [ exact Hg | exact HΔ | exact Ha | | exact HR ];
        intros R1 HR1; inversion HR1; subst; [ unfold gc_unit in *; cbn in *; discriminate | auto ]
      | pose proof (udenote_abs _ _ _ _ _ _ HR0) as Habs; cbn [gunit_abs] in Habs;
        rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HR _ Habs);
        apply desc_ok_up; [ exact (IH _ HR0) | exact HΔ | exact Ha ] ]
    end.
  - (* a loaded unit or an open frame *)
    split; intros R0 HR0; inversion HR0; subst; eapply desc_ok_unit; eassumption.
  - (* a slot *)
    split; intros R HR; inversion HR; subst; first [ eapply desc_ok_unit; eassumption |
      match goal with Hl : ctx_lookup_mod _ ?U0 _, HU : udenote _ _ _ _ ?U0 _ |- _ =>
        exact (slots_typed_lookup _ _ Hg _ _ _ Hl H H0 _ HU) end ].
  - (* a literal *)
    pose proof (presup_unit_eq_ctx H).
    split; intros R HR; inversion HR; subst; first [ eapply desc_ok_unit; eassumption | auto ].
  - (* a member *)
    pose proof (presup_modexp_eq_ctx H0).
    split; intros R0 HR0; [ exact (desc_ok_mem _ _ Hg H6 _ _ _ _ H9 H7 HR0) | exact (desc_ok_mem _ _ Hg H6 _ _ _ _ H9 H8 HR0) ].
  - (* an application *)
    pose proof (presup_modexp_eq_ctx H0).
    split; intros R0 HR0; inversion HR0; subst; [ eapply desc_ok_unit; eassumption | | eapply desc_ok_unit; eassumption |].
    + match goal with Hm : mdenote _ _ _ H ?R1, Ha : ds_at ?R1 _ = Some _ |- _ =>
        rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ H2) in Ha;
        exact (desc_ok_at _ _ Hg _ _ _ _ _ _ _ (H19 _ H2) H3 H4 H7 Ha) end.
    + match goal with Hm : mdenote _ _ _ H' ?R1, Ha : ds_at ?R1 _ = Some _ |- _ =>
        rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ H11) in Ha;
        exact (desc_ok_at _ _ Hg _ _ _ _ _ _ _ (H20 _ H11) H12 H13 H16 Ha) end.
  - (* a slot is its unit *)
    split; intros R HR; inversion HR; subst; first [ eapply desc_ok_unit; eassumption |
      match goal with Hl : ctx_lookup_mod _ ?U0 _, HU : udenote _ _ _ _ ?U0 _ |- _ =>
        exact (slots_typed_lookup _ _ Hg _ _ _ Hl H H0 _ HU) end
      | match goal with HU : udenote _ _ _ _ _ _, Hl : ctx_lookup_mod _ _ _ |- _ =>
        exact (slots_typed_lookup _ _ Hg _ _ _ Hl H H0 _ HU) end ].
  - (* a selection is the unit its module part stands for *)
    split; [ assumption |].
    match goal with Hm : mdenote _ _ _ (me_mem _ _) ?R, Hd : ds_mod _ _ ?R = Some _,
      IH : forall R, mdenote _ _ _ (me_mem _ _) R -> desc_ok _ _ _ R,
      HH : wf_modexp_eq _ _ _ (me_mem _ _) (me_mem _ _) |- _ =>
      intros R' HR'; eapply ds_unit_desc_ok; [ exact Hg | exact (desc_ok_mod _ _ Hg _ _ _ (IH _ Hm) Hd)
        | exact (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hd) | exact (ds_mod_is_mod _ _ _ _ Hd)
        | exact (wf_mdenote_mod_xp _ _ _ _ _ _ _ HH Hm Hd) | exact HR' ]
    end.
  - (* [β] for a body *)
    match goal with HU : wf_unit_eq _ _ _ _ _, HN : wf_exp _ _ _ _ ?N, HUok : forall R, udenote _ _ _ _ _ R -> _ |- _ =>
      pose proof (desc_ok_beta _ _ Hg _ _ _ _ N HU HUok HN) as Hb end.
    rewrite gunit_sub_mk in Hb; cbn [moddef_sub] in Hb; exact Hb.
  - (* [β] for an alias *)
    match goal with HU : wf_unit_eq _ _ _ _ _, HN : wf_exp _ _ _ _ ?N, HUok : forall R, udenote _ _ _ _ _ R -> _ |- _ =>
      pose proof (desc_ok_beta _ _ Hg _ _ _ _ N HU HUok HN) as Hb end.
    rewrite gunit_sub_mk in Hb; cbn [moddef_sub] in Hb; exact Hb.
  - (* an alias with no parameter is its target *)
    split; [| assumption ].
    intros R HR; inversion HR; subst; try (cbn in *; discriminate).
    match goal with HE : wf_modexp_eq _ _ _ E E |- _ => eapply (desc_ok_alias _ _ Hg _ nil E); [ exact (presup_modexp_eq_ctx HE) | constructor | cbn; assumption | eassumption ] end.
Qed.

(** The type former at typed arguments for its first uniform parameters. *)
Lemma wf_ind_args : forall Θ Ξ Γ p D Ns,
    decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    args_ok Θ Ξ Γ (ind_uparams D) Ns ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty_at D Ns : Typeω@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns.
Proof.
  intros * HD Hl HΓ (T1 & T2 & HT & Hlen & Ha & Hs & HT2 & HN).
  destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
  pose proof HD as (_ & _ & _ & HP & _).
  assert (Hp : ind_params D = (ind_nparams D ++ T1) ++ T2) by (rewrite <- List.app_assoc, <- HT; apply params_split).
  rewrite Hp in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : ind_ty_at D Ns = (ctx_pi (ind_nparams D ++ T1) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)[sb_of_list Id Ns]).
  { unfold ind_ty_at, ind_np; rewrite Hp.
    replace (length ((ind_nparams D ++ T1) ++ T2) - length Ns) with (length (ind_nparams D ++ T1))
      by (rewrite !List.length_app in *; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ a_ind p : ctx_pi T2 (ctx_pi (ind_nparams D ++ T1) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)).
  { rewrite <- ctx_pi_app, <- Hp; eapply wf_ind; eassumption. }
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha HT2 (eq_sym Hlen) HN) as Hσ.
  rewrite Hat; split.
  - exists j; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' Hσ) as H; cbn in H; exact H.
  - eapply wf_apps_ctx_pi; [ exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

(** The term part of a typed description is of a type, and its δ-reduct of
    that type. *)
Lemma desc_ok_ty : forall Θ Ξ, valid_syn Θ Ξ -> forall Γ R A, desc_ok Θ Ξ Γ R -> ds_ty Θ Ξ R = Some A ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) /\ (forall M, ds_red R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A).
Proof.
  intros * [HΘ HΞ] * HR HA.
  destruct HR as [Γ A0 om HA0 HM | Γ Θ' pq Ns D Hl Ha Hs HT HΘ' Hargs | |]; cbn in HA |- *; try discriminate.
  - injection HA as <-; split; [ exact HA0 | exact HM ].
  - rewrite Hl in HA; injection HA as <-.
    pose proof (good_ind _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) as HD.
    destruct (wf_ind_args _ _ _ _ _ _ HD Hl HΘ' Hargs) as [[i Hi] HM].
    split.
    + exact (ctx_pi_wf _ _ _ _ _ _ HΘ' Hi).
    + intros M [= <-]; exact (ctx_fn_wf _ _ _ _ _ _ _ HΘ' Hi HM).
Qed.

(** ** What a Member Looks Up is Typed *)

(** A module part of typed descriptions, read under the parameters it is
    abstracted over. *)
Lemma desc_ok_up_inv : forall Θ Ξ Γ Δ Rm, ds_is_mod Rm -> desc_ok Θ Ξ Γ (ds_up Δ Rm) -> desc_ok Θ Ξ (Δ ++ Γ) Rm.
Proof.
  intros * Hm Hok; destruct Rm as [| Δ0 Φ | Θ' p T Φ Ns |]; cbn in Hm |- *; try contradiction.
  - assert (Ha : tele_ass (Δ0 ++ Δ)) by (inversion Hok; assumption).
    apply (desc_ok_open_root _ _ _ _ _ _ Ha) in Hok; apply (desc_ok_open_root _ _ _ _ _ _ (proj1 (proj1 (List.Forall_app _ _ _) Ha))).
    rewrite <- List.app_assoc in Hok; exact Hok.
  - assert (Ha : tele_ass (Θ' ++ Δ)) by (inversion Hok; assumption).
    apply (desc_ok_closed_root _ _ _ _ _ _ _ _ Ha) in Hok; apply (desc_ok_closed_root _ _ _ _ _ _ _ _ (proj1 (proj1 (List.Forall_app _ _ _) Ha))).
    rewrite <- List.app_assoc in Hok; exact Hok.
Qed.

Lemma desc_ok_wf_ctx : forall Θ Ξ Γ R, desc_ok Θ Ξ Γ R -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * Hok; inversion Hok; subst.
  - match goal with HA : exists i, _ |- _ => destruct HA as [i HA]; exact (presup_exp_ctx HA) end.
  - eapply ctx_app_wf_tail; eassumption.
  - eapply ctx_app_wf_tail; eapply ctx_app_wf_tail; eassumption.
  - eapply ctx_app_wf_tail; eassumption.
Qed.

(** A selection from a module part of typed descriptions. *)
Lemma desc_ok_sel : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ Rm y Γy E rd R R',
    desc_ok Θ Ξ Γ Rm -> ds_entry Rm y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (ds_epath Rm y) E R -> ds_read rd R = Some R' -> desc_ok Θ Ξ Γ R'.
Proof.
  intros * Hg Hv * Hok He Hed Hr; destruct Rm; cbn in He; try discriminate.
  - eapply desc_ok_entry_open; eassumption.
  - eapply desc_ok_entry_closed; eassumption.
Qed.

Lemma entry_term_edenote : forall Θ Ξ Γ o T E R, entry_term E = Some R -> edenote Θ Ξ Γ o (ge_read T E) R.
Proof. intros * He; destruct E as [| ? [? [? ?| ?]] | ? ? ? ? | ? ? ? ?]; cbn in He |- *; try discriminate; injection He as <-; constructor. Qed.



(** ** A Filed Member at Arguments is Typed *)

Lemma ds_ty_up : forall Θ Ξ Δ R A, ds_ty Θ Ξ R = Some A -> ds_ty Θ Ξ (ds_up Δ R) = Some (ctx_pi Δ A).
Proof.
  intros * Ht; destruct R as [A0 om | | | Θ' p Ns]; cbn in *; try discriminate.
  - injection Ht as <-; reflexivity.
  - destruct (ind_lookup Θ Ξ p); [| discriminate ]; injection Ht as <-; rewrite ctx_pi_app; reflexivity.
Qed.

(** A term of the type a description abstracted over [Δa] has, applied to
    arguments for the outermost parameters of [Δa], is of the type the
    description at the arguments has. *)
Lemma ats_up_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa R A0 M,
    ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> tele_ass Δa -> length Ns <= length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    ds_ty Θ Ξ R = Some A0 -> (exists i, Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ A0 : Typeω@i) -> Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δa A0 ->
    exists R' A', ds_ats (ds_up Δa R) Ns = Some R' /\ ds_ty Θ Ξ R' = Some A' /\ Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns : A'.
Proof.
  intros Θ Ξ Hg; pose proof (wf_gstack_closed _ _ Hg) as Hc.
  induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs Ht [i HA0] HM.
  - exists (ds_up Δa R), (ctx_pi Δa A0); split; [ reflexivity | split; [ apply ds_ty_up; exact Ht | exact HM ] ].
  - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
    unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
    rewrite tele_insts_snoc in HNs.
    pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
    pose proof HΔ as HΔ0; rewrite <- List.app_assoc in HΔ, HA0; cbn [List.app] in HΔ, HA0.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [j HC]].
    pose proof (wf_sub_single _ _ _ _ _ _ HC HN) as Hs1.
    assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
    assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass C :: Γ)
      by (apply wf_sub_ext; assumption).
    destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HA0) as [k HB].
    assert (HMN : Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : (ctx_pi Δ1 A0)[Id,,N]).
    { rewrite ctx_pi_app in HM; cbn [ctx_pi] in HM.
      eapply wf_app; [ eapply lift_exp_max_left; exact HC | eapply lift_exp_max_right; exact HB | exact HM | exact HN ]. }
    rewrite ctx_pi_sub in HMN.
    cbn [ds_ats]; rewrite ds_at_up.
    apply (IH Γ (tele_sub Δ1 (Id,,N)) _ A0[sb_qn (length Δ1) (Id,,N)] (M $ N)).
    + exact HΔN.
    + apply tele_ass_sub; exact Ha1.
    + rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
    + intros k0 N1 A HN1 HA.
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
      exact (HNs (S k0) N1 A HN1 HA).
    + apply ds_ty_sub; [ exact Hc | exact Ht ].
    + exists i; exact (sub_preserves_exp _ _ _ _ _ _ _ HA0 Hσ).
    + exact HMN.
Qed.

(** The arguments a module expression is applied to, outermost last. *)
Fixpoint me_strip (H : modexp) : (modexp * list exp)%type :=
  match H with
  | me_app H0 N => let '(K, Ns) := me_strip H0 in (K, Ns ++ N :: nil)
  | _ => (H, nil)
  end.

Lemma me_strip_apps : forall Ns H, me_strip (me_apps H Ns) = (fst (me_strip H), snd (me_strip H) ++ Ns).
Proof.
  induction Ns as [| N Ns IH]; intros; cbn [me_apps]; [ destruct (me_strip H); cbn; rewrite List.app_nil_r; reflexivity |].
  rewrite IH; cbn; destruct (me_strip H); cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma me_strip_qname : forall p, me_strip (qname_mod p) = (qname_mod p, nil).
Proof.
  intros [u ch]; unfold qname_mod; cbn [q_unit q_chain]; revert u.
  induction ch as [| y ch IH] using List.rev_ind; intros u; [ reflexivity |].
  rewrite me_mems_app; cbn; reflexivity.
Qed.

Lemma me_apps_qname_inj : forall p Ns p' Ns', me_apps (qname_mod p) Ns = me_apps (qname_mod p') Ns' -> p = p' /\ Ns = Ns'.
Proof.
  intros * E; apply (f_equal me_strip) in E; rewrite !me_strip_apps, !me_strip_qname in E; cbn in E.
  injection E as Ep <-; split; [| reflexivity ].
  apply (f_equal mod_qname) in Ep; rewrite !mod_qname_qname_mod in Ep; injection Ep as ->; reflexivity.
Qed.

Lemma me_apps_qname_lit : forall p Ns U, me_apps (qname_mod p) Ns <> me_lit U.
Proof.
  intros * E; apply (f_equal me_strip) in E; rewrite me_strip_apps, me_strip_qname in E; cbn in E.
  injection E as Ep _; apply (f_equal mod_qname) in Ep; rewrite mod_qname_qname_mod in Ep; discriminate.
Qed.



(** Any term of the type of an inductive type's type former, applied to
    arguments for its first uniform parameters. *)
Lemma wf_ind_args_gen : forall Θ Ξ Γ D Ns M,
    decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> args_ok Θ Ξ Γ (ind_uparams D) Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_ty_at D nil -> Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns : ind_ty_at D Ns.
Proof.
  intros * HD HΓ (T1 & T2 & HT & Hlen & Ha & Hs & HT2 & HN) HM0.
  destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
  pose proof HD as (_ & _ & _ & HP & _).
  assert (Hp : ind_params D = (ind_nparams D ++ T1) ++ T2) by (rewrite <- List.app_assoc, <- HT; apply params_split).
  rewrite Hp in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : ind_ty_at D Ns = (ctx_pi (ind_nparams D ++ T1) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)[sb_of_list Id Ns]).
  { unfold ind_ty_at, ind_np; rewrite Hp.
    replace (length ((ind_nparams D ++ T1) ++ T2) - length Ns) with (length (ind_nparams D ++ T1))
      by (rewrite !List.length_app in *; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi T2 (ctx_pi (ind_nparams D ++ T1) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)).
  { rewrite <- ctx_pi_app, <- Hp.
    unfold ind_ty_at, ind_np in HM0; rewrite Nat.sub_0_r, List.firstn_all in HM0; cbn [sb_of_list List.length] in HM0.
    rewrite exp_sub_id in HM0; exact HM0. }
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha HT2 (eq_sym Hlen) HN) as Hσ.
  rewrite Hat; eapply wf_apps_ctx_pi; [ exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

Lemma ds_ats_term_none : forall Θ Ξ Ns A om R1, ds_ats (ds_term A om) Ns = Some R1 ->
    exists R1', ds_ats (ds_term A None) Ns = Some R1' /\ ds_ty Θ Ξ R1' = ds_ty Θ Ξ R1.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha |- *; [ injection Ha as <-; eexists; split; reflexivity |].
  destruct (pi_view A) as [[X C] |]; [| discriminate ].
  destruct om as [M |]; [ destruct (fn_view M) as [M' |]; [| discriminate ] |]; exact (IH _ _ _ Ha).
Qed.




(** ** Typed Descriptions Grow with the Global Context *)

Lemma args_ok_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ T Ns, Emb Θ1 Ξ1 Θ2 Ξ2 -> args_ok Θ1 Ξ1 Γ T Ns -> args_ok Θ2 Ξ2 Γ T Ns.
Proof.
  intros * He (T1 & T2 & HT & Hl & Ha & Hs & HT2 & HN).
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _).
  exists T1, T2; split; [ exact HT |]; split; [ exact Hl |]; split; [ exact Ha |]; split; [ exact Hs |].
  split; [ exact (Hc _ HT2) | intros; apply Ht; eauto ].
Qed.

(** What a description grows into, read at a bigger global context, is
    typed there. *)
Lemma desc_ok_grow : forall Θ1 Ξ1 Θ2 Ξ2, ⊢ᵍ Θ1 ⍮ Ξ1 -> Emb Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ R1, desc_ok Θ1 Ξ1 Γ R1 -> forall R2, dsg Θ1 Ξ1 Θ2 Ξ2 R1 R2 -> desc_ok Θ2 Ξ2 Γ R2.
Proof.
  intros * Hg1 He; pose proof (em_wf _ _ _ _ He) as Hg2; pose proof (em_res _ _ _ _ He) as Hs.
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _ & _ & _ & Hu & _).
  induction 1 as [Γ A om HA HM | Γ Θ' pq Ns D Hl Ha Hsc HT HΘ' Hargs HaΘ | Γ Δ Φw Φ HΦ Hn Hent IH HaΔ Hsh Hnd HUw
                 | Γ Θ' T Φ Ns Θ0 Ξ0 p Hg0 Hs0 Hloc Ha Hsc HT HΘ' Hargs HaΘ];
    intros R2 [[<- Hcb] | (Θ'' & T' & Φ1 & Φ2 & Ns' & p' & Heq1 & -> & Hl1 & Hl2)]; try discriminate.
  - constructor; [ destruct HA as [i HA]; exists i; apply Ht, HA | intros M HM0; apply Ht, HM, HM0 ].
  - econstructor; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) | exact Ha | exact Hsc | apply Hc, HT | apply Hc, HΘ'
                  | exact (args_ok_emb _ _ _ _ _ _ _ He Hargs) | exact HaΘ ].
  - constructor; [ apply Hc, HΦ | exact Hn | | exact HaΔ | exact Hsh | exact Hnd | apply Hu, HUw ].
    intros y Φ0 pm U Hp R HR.
    destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
    rewrite HΨ in HΦ; cbn [body_ctx] in HΦ.
    pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ; exact HΦ)) as HΦ0.
    cbn [List.app] in HΦ0; destruct (ctx_decomp_mod HΦ0) as [_ HU].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R1 HR1] & _).
    destruct (proj1 (proj2 (mdenote_grow_all _ _ _ _ Hg1 Hg2 Hs)) _ _ _ _ HR1 (or_introl eq_refl)) as (R1' & HR1' & Hd).
    rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg2)) _ _ _ _ HR _ HR1').
    exact (IH _ _ _ _ Hp _ HR1 _ Hd).
  - injection Heq1 as <- <- <- <- <-.
    econstructor; [ exact Hg2 | apply gc_sub_refl | exact Hl2 | exact Ha | exact Hsc
                  | apply Hc, HT | apply Hc, HΘ' | exact (args_ok_emb _ _ _ _ _ _ _ He Hargs) | exact HaΘ ].
Qed.

(** ** Presupposition of Typing, over Valid Storage *)

Corollary mem_desc_ok : forall Θ Ξ Γ H H' x R, valid_syn Θ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
    mdenote Θ Ξ Γ (me_mem H x) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * Hv HH Hm.
  pose proof (presup_modexp_eq_ctx HH) as HΓ.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH Hv) as (_ & HR & _).
  exact (desc_ok_mem _ _ (ctx_wf_gctx _ _ _ HΓ) Hv _ _ _ _ HΓ HR Hm).
Qed.

Lemma presup_exp_typ_v : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    valid_syn Θ Ξ ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  induction 1; intros Hv;
    repeat match goal with IH : valid_syn _ _ -> _ |- _ => specialize (IH Hv) end;
    assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2; destruct_conjs.
  (* a member: the type the unit binds it at *)
  all: try match goal with
    | Hm : mdenote _ _ _ (me_mem ?H0 _) ?R, Ht : ds_ty _ _ ?R = Some _, HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H0 ≈ _ |- _ =>
        exact (proj1 (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht))
    end.
  (* inductive types: the declaration's types are types, and the motive at
     the scrutinee *)
  all: try match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, HΓ : ⊢ _ ⍮ _ ⍮ ?Γ |- _ =>
        pose proof (good_ind _ _ _ _ _ _ _ _ _ _ _ (proj1 Hv) (proj2 Hv) Hl) as HDt; cbn [syn_VD] in HDt;
        pose proof (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HΓ) Hl) as HDc
    end.
  all: try solve [ eapply ind_ty_typed; eassumption | eapply con_ty_typed; eassumption ].
  all: try solve [
    match goal with
    | HA : wf_exp _ _ (elim_mctx _ _ _ ++ _) _ ?A |- exists _, _ ⍮ _ ⍮ _ ⊢ ?A[_] : _ =>
        eexists; eapply (sub_preserves_exp _ _ _ _ _ _ _ HA); eapply wf_elim_inst_sub; eauto using ext_eq_ctx_left
    end ].
  all: mauto 3.
  all: eexists; mauto 3.
Qed.

(** ** Storage is Valid *)

(** A module expression over a closed telescope denotes the same on top of
    any context, mentioning nothing of it. *)
Lemma mdenote_tele_weaken : forall Θ Ξ Δa Γ E E' R,
    Θ ⍮ Ξ ⍮ Δa ⊢ᵐ E ≈ E' -> ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> mdenote Θ Ξ Δa E R ->
    mdenote Θ Ξ (Δa ++ Γ) E R /\ ds_scoped (length Δa) R.
Proof.
  intros * HE HΓ Hm.
  pose proof (presup_modexp_eq_ctx HE) as HΔ.
  pose proof (ctx_wf_gctx _ _ _ HΔ) as Hg.
  pose proof (wf_ctx_scoped _ _ _ HΔ) as Hs.
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HE) as (_ & HsE & _).
  pose proof (proj1 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ Hm _ (slots_ok_ctx _ Hs) HsE) as HsR.
  pose proof (ctx_app_wf_tail _ _ _ _ HΓ) as HΓ0.
  assert (Hw : Θ ⍮ Ξ ⍮ Γ ⊢ˢ ι (wk_shiftn (length Γ)) : ⋅).
  { apply wf_sub_of_wk; rewrite <- (List.app_nil_r Γ) at 1; apply wf_wk_shiftn_app;
      [ rewrite List.app_nil_r; exact HΓ0 | constructor; exact Hg ]. }
  assert (Hσ : Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ˢ sb_qn (length Δa) (ι (wk_shiftn (length Γ))) : Δa ++ ⋅).
  { pose proof (wf_sub_ext _ _ Δa _ _ _ Hw) as Hx; rewrite tele_sub_closed in Hx by exact Hs.
    apply Hx; [ exact HΓ | rewrite List.app_nil_r; exact HΔ ]. }
  rewrite List.app_nil_r in Hσ.
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HE Hm Hσ) as Hm'.
  assert (Hfix : forall x, x < length Δa -> sb_qn (length Δa) (ι (wk_shiftn (length Γ))) x = se_var x)
    by (intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ]).
  rewrite (proj1 (proj2 syn_scoped_sub_id) _ _ _ HsE Hfix), (ds_sub_fix _ _ _ HsR Hfix) in Hm'.
  split; assumption.
Qed.

Lemma syn_valid_here : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GoodV syn_Vs syn_F syn_VD Θ Ξ -> valid_syn Θ Ξ.
Proof. intros * Hg HG; exact (HG _ _ (Embx_refl _ _ Hg) _ _ (gc_sub_refl _ _)). Qed.

Lemma syn_tele_ass : forall Θ Ξ Θ2 Ξ2, GoodV syn_Vs syn_F syn_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof.
  intros * HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [_ HΞ].
  destruct Ξ as [| [mp U] Ξ]; [ constructor | exact (proj1 (proj1 HΞ)) ].
Qed.

Lemma syn_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV syn_Vs syn_F syn_VD Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid syn_Vs syn_F syn_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid syn_Vs syn_F syn_VD Θ Ξ Θ2 Ξ2 Ξ ->
    forall (Θs : gdeps) (Ξs : gstack), syn_V Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM HG He _ _ Θs Ξs.
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) as Hg.
  destruct (presup_exp_typ_v HM (syn_valid_here _ _ Hg HG)) as [i HA].
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  exists A; split; [ reflexivity |]; split; [ exists i; apply Ht, HA |].
  intros ? [= <-]; exists M; split; [ reflexivity | apply Ht, HM ].
Qed.

Lemma syn_ax : forall Θ Ξ A i b pv Θ2 Ξ2 (Θs : gdeps) (Ξs : gstack),
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV syn_Vs syn_F syn_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    syn_V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA _ He _; destruct (emb_preserves_wf _ _ _ _ (Embx_emb _ _ _ _ He)) as (_ & Ht & _).
  exists A; split; [ reflexivity |]; split; [ exists i; apply Ht, HA | discriminate ].
Qed.

(** An alias: what its target denotes, wherever it is read, is typed. *)
Lemma syn_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 (Θs : gdeps) (Ξs : gstack),
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV syn_Vs syn_F syn_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    syn_V Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * HaΔ Hx HE HG He _; cbn [syn_V].
  pose proof (Embx_emb _ _ _ _ He) as He'.
  pose proof (em_wf _ _ _ _ He') as Hg2.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  pose proof (syn_valid_here _ _ Hg HG) as Hv.
  destruct (emb_preserves_wf _ _ _ _ He') as (Hc & _ & _ & _ & _ & _ & Hme).
  pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as HΔ.
  split; [ exact (Hme _ _ _ HE) |].
  split; [ exact (Hc _ HΔ) |].
  intros Γ HΓ.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HE Hv) as (_ & HR & _).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HE) as (_ & (R1 & R1m & HR1 & HR1m) & _).
  destruct (proj1 (mdenote_grow_all _ _ _ _ Hg Hg2 (em_res _ _ _ _ He')) _ _ _ HR1) as (R2 & HR2 & Hd).
  pose proof (desc_ok_grow _ _ _ _ Hg He' _ _ (HR _ HR1) _ Hd) as Hok2.
  destruct (dsg_mod _ _ _ _ (em_res _ _ _ _ He') _ _ _ Hd HR1m) as (R2m & HR2m & _).
  pose proof (Hme _ _ _ HE) as HE2.
  destruct (mdenote_tele_weaken _ _ _ _ _ _ _ HE2 HΓ HR2) as (HR2' & HsR2).
  split; [ exists R2; exact HR2' |].
  intros R Hm.
  rewrite (proj1 (mdenote_functional_all _ _ Hg2) _ _ _ Hm _ HR2').
  split; [| exists R2m; exact HR2m ].
  pose proof (desc_ok_tele_weaken _ _ Hg2 (Δ ++ gs_tele Ξ) Γ nil R2) as Hw.
  rewrite !List.app_nil_r in Hw.
  apply Hw; [ exact (wf_ctx_scoped _ _ _ (Hc _ HΔ)) | exact (Hc _ HΔ) | exact HΓ | exact HsR2 | exact Hok2 ].
Qed.

(** An inductive alias: its arguments, as its module view types them. *)
Lemma syn_ind_alias : forall Θ Ξ pv Δ p Ns D Θ2 Ξ2 (Θs : gdeps) (Ξs : gstack),
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> List.length Ns <= ind_nu D ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    GoodV syn_Vs syn_F syn_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    syn_V Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns).
Proof.
  intros * HaΔ Hx Hl Hle _ HE HG He _; cbn [syn_V].
  pose proof (Embx_emb _ _ _ _ He) as He'.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  pose proof (syn_valid_here _ _ Hg HG) as Hv.
  destruct (emb_preserves_wf _ _ _ _ He') as (Hc & _ & _ & _ & _ & _ & Hme).
  pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as HΔ.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HE Hv) as (_ & HR & _).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HE) as (_ & (R1 & _ & HR1 & _) & _).
  destruct (mdenote_apps_inv _ _ _ _ _ _ HR1) as (R0 & HR0 & Ha).
  rewrite (mdenote_ind_path _ _ Hg _ _ _ _ Hl HR0), ds_ats_ind_nil in Ha; cbn in Ha; injection Ha as <-.
  pose proof (HR _ HR1) as Hok; inversion Hok as [| Γ0 Θ' pq Ns' D' Hl' _ _ _ _ Hargs | |]; subst.
  rewrite Hl in Hl'; injection Hl' as <-.
  exists D; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ He') Hl) |].
  split; [ exact (Hc _ HΔ) | split; [ exact (args_ok_emb _ _ _ _ _ _ _ He' Hargs) | exact (Hme _ _ _ HE) ] ].
Qed.

Lemma syn_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV syn_Vs syn_F syn_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    syn_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HG He.
  split; [ apply List.Forall_app; split; [ exact HΔ | exact (syn_tele_ass _ _ _ _ HG He) ] |].
  exact (proj1 (emb_preserves_wf _ _ _ _ (Embx_emb _ _ _ _ He)) _ HC).
Qed.

Lemma syn_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV syn_Vs syn_F syn_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    syn_VD Θ2 Ξ2 D /\ syn_F Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * HD _ He.
  pose proof (decl_typed_emb _ _ _ _ _ (Embx_emb _ _ _ _ He) HD) as HD2.
  destruct (decl_typed_uparams _ _ _ HD2) as [HU HaU].
  split; [ exact HD2 | split; assumption ].
Qed.

(** Everything stored in a well-formed global context is valid there. *)
Theorem gctx_valid_syn : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ.
Proof.
  intros * Hg; apply (syn_valid_here _ _ Hg).
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
           (global_valid_all syn_Vs syn_F syn_VD syn_def syn_ax syn_alias syn_ind_alias syn_nil syn_ind)))))))))) _ _ Hg).
Qed.

(** A term a well-formed module expression looks up is typed at the type
    the lookup reads: the premises of [wf_mem] on the type and on the
    δ-reduct hold of every description looked up ([mem_desc_ok]).  The
    checker supplies them so, without reading a body again. *)
Corollary wf_mem_desc : forall Θ Ξ Γ H x R A,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A.
Proof.
  intros * HH Hm Ht.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv.
  destruct (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht) as [[i Hi] HM].
  eapply wf_mem; [ exact HH | exact Hm | exact Ht | exact Hi | exact HM ].
Qed.

(** ** Telescopes Below a Stored Body *)

(** An alias just below a stored body, an open frame or a closed module,
    is stored over the body's telescope extended. *)
Lemma loc_alias_params : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ y U, gc_loc Θ Ξ p = Some (T, Φ) ->
    gc_module Θ Ξ (qname_in p y) = Some (mr_alias U) -> exists Δ, gu_params U = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hl Hm; unfold gc_loc in Hl; destruct (gc_frame Ξ p) as [r |] eqn:Hf.
  - injection Hl as ->; unfold gc_frame in Hf.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hf as <- <-.
    unfold gc_module, gc_module_u in Hm.
    destruct (gs_find_tele_child _ _ Hg _ _ _ Ef y) as [(V & T1 & Ef') | Ef']; rewrite Ef' in Hm; [ discriminate |].
    destruct (gm_coh_child _ _ _ _ (wf_gstack_coh _ _ Hg _ _ _ _ Ef) Hm) as [(? & ? & [=] & _) | (U' & Δ' & [= <-] & HU & HΔ)].
    eauto.
  - destruct (gc_body_module _ _ _ _ _ Hl) as [oD Hmd].
    rewrite qname_in_app in Hm; exact (wf_gc_alias_params _ _ Hg _ _ _ _ _ Hmd Hm).
Qed.

(** A stored body just below a stored body is over the body's telescope
    extended. *)
Lemma loc_child_tele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ y T' Φ', gc_loc Θ Ξ p = Some (T, Φ) ->
    gc_loc Θ Ξ (qname_in p y) = Some (T', Φ') -> exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hl Hl'; unfold gc_loc in Hl; destruct (gc_frame Ξ p) as [r |] eqn:Hf.
  - injection Hl as ->; unfold gc_frame in Hf.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hf as <- <-.
    destruct (gs_find_tele_child _ _ Hg _ _ _ Ef y) as [(V & T1 & Ef') | Ef'].
    + unfold gc_loc, gc_frame, gc_body in Hl'; rewrite Ef' in Hl'.
      destruct V as [Δv [[|] Φv | Ev]]; try discriminate; injection Hl' as <- <-.
      assert (Hv : loc Θ Ξ (qname_in p y) (Δv ++ T1) Φv) by (left; unfold gc_frame; rewrite Ef'; reflexivity).
      destruct (gs_find_tele_frame _ _ Hg _ _ _ Ef') as [(Hc & _) | (c & y' & V' & T2 & Hc & HV & _ & ->)];
        cbn in Hc; [ destruct (q_chain p); discriminate |].
      apply List.app_inj_tail in Hc as [<- <-].
      cbn [q_unit qname_in] in HV; replace (q_abs (q_unit p) (q_chain p)) with p in HV by (destruct p; reflexivity).
      rewrite Ef in HV; injection HV as <- <-; cbn [gu_params] in Hv |- *.
      destruct (loc_valid _ _ _ _ _ (gctx_valid_syn _ _ Hg) Hv) as [[Ha _] _].
      exists Δv; split; [ reflexivity | unfold tele_ass in Ha; exact (proj1 (proj1 (List.Forall_app _ _ _) Ha)) ].
    + unfold gc_loc, gc_frame, gc_body in Hl'; rewrite Ef' in Hl'; cbn [gu_params gu_mod] in Hl'.
      exact (proj2 (gm_coh_subbody _ _ _ _ _ _ (wf_gstack_coh _ _ Hg _ _ _ _ Ef) Hl')).
  - destruct (gc_body_module _ _ _ _ _ Hl) as [oD Hmd].
    unfold gc_loc in Hl'; rewrite (gc_module_child_not_frame _ _ Hg _ _ _ Hmd) in Hl'.
    destruct (gc_body_module _ _ _ _ _ Hl') as [oD' Hmd'].
    rewrite qname_in_app in Hmd'; exact (wf_gc_child _ _ Hg _ _ _ _ _ _ Hmd Hmd').
Qed.

(** The telescope of a stored body is one of assumptions. *)
Lemma gc_loc_tele_ass : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, gc_loc Θ Ξ p = Some (T, Φ) -> tele_ass T.
Proof.
  intros * Hg * Hl.
  assert (Hv : loc Θ Ξ p T Φ) by (unfold gc_loc in Hl; destruct (gc_frame Ξ p) eqn:E;
    [ injection Hl as ->; left; exact E | right; exact Hl ]).
  exact (proj1 (proj1 (loc_valid _ _ _ _ _ (gctx_valid_syn _ _ Hg) Hv))).
Qed.

(** ** What Resolution Hands Back is Well Typed *)

Definition entry_typed (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Typeω@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod _ _ | ge_ind _ _ _ _ | ge_ind_alias _ _ _ _ => True
  end.

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop := GV entry_typed decl_typed Θ Ξ Θ Ξ.

Theorem presup_exp_typ : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * H; exact (presup_exp_typ_v H (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx H)))).
Qed.

Lemma entry_typed_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> Good entry_typed decl_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM HG He.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | intros ? [= <-]; apply Ht; eapply ctx_fn_wf0; eassumption ].
Qed.

Lemma entry_typed_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> Good entry_typed decl_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | discriminate ].
Qed.

Lemma entry_typed_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> Good entry_typed decl_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> decl_typed Θ2 Ξ2 D.
Proof. intros * HD _ He; eapply decl_typed_emb; eassumption. Qed.

(** ** The Mutual Theorem *)

Theorem presup_global :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> GoodE entry_typed decl_typed Θ Ξ mp E) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> GoodM entry_typed decl_typed Θ Ξ mp Δ Φ) /\
  (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> Good entry_typed decl_typed Θ Ξ).
Proof.
  destruct (global_induction_all entry_typed decl_typed entry_typed_def entry_typed_ax entry_typed_ind)
    as (H1 & H2 & H3 & H4 & _ & H5 & H6 & H7 & H8 & H9 & H10).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 H10))))))))).
Qed.

Corollary gctx_rwf : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> rwf Θ Ξ.
Proof. exact (global_induction entry_typed decl_typed entry_typed_def entry_typed_ax entry_typed_ind). Qed.

(** What a use of a global needs: its type and body, in any well-formed
    context. *)
Corollary wf_glob_typ : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * HΓ Hl; destruct (proj1 (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl) as [[i HA] _].
  exists i; eapply closed_weaken_exp;
    [ assumption | exact HA | eapply wf_gc_resolve_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A (Some M)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hl; destruct (proj1 (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl) as [_ HM].
  eapply closed_weaken_exp;
    [ assumption | apply HM; reflexivity
    | eapply wf_gc_resolve_body_closed; eassumption
    | eapply wf_gc_resolve_type_closed; eassumption ].
Qed.

(** What a use of an inductive alias needs: its canonical path names an
    inductive type, its arguments are for uniform parameters, and the
    term it δ-unfolds to is typed, in any well-formed context. *)
Corollary wf_ind_alias : forall Θ Ξ Γ pq Δ p Ns,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_alias_lookup Θ Ξ pq = Some (Δ, p, Ns) ->
    exists D, ind_lookup Θ Ξ p = Some D /\ List.length Ns <= ind_nu D /\
      (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ (ind_ty_at D Ns) : Typeω@i) /\
      Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ (apps (a_ind p) Ns) : ctx_pi Δ (ind_ty_at D Ns).
Proof.
  intros * HΓ Hl.
  destruct (proj2 (proj2 (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ))) _ _ _ _ Hl) as (D & HD & Hle & [i HA] & HM).
  destruct (wf_ind_alias_closed _ _ _ _ _ _ _ _ HΓ Hl HD) as [HsA HsM].
  exists D; split; [ exact HD | split; [ exact Hle | split ] ].
  - exists i; eapply closed_weaken_exp; [ assumption | exact HA | exact HsA | exact I ].
  - eapply closed_weaken_exp; [ assumption | apply HM; reflexivity | exact HsM | exact HsA ].
Qed.
