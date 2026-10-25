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
From Mctt.Core.Syntactic.System.Global Require Export DescTyping.
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
      | Ht : ds_ty R = Some _ |- _ => pose proof (dsg_ty _ _ _ _ _ _ _ Hd Ht); clear Ht
      | Ht : ds_mtele R = Some _ |- _ => pose proof (dsg_mtele _ _ _ _ _ _ _ Hd Ht); clear Ht
      | Ht : ds_red R = Some _ |- _ => rewrite (dsg_red _ _ _ _ _ _ Hd) in Ht
      | Ht : forall M, ds_red R = Some M -> _ |- _ => rewrite (dsg_red _ _ _ _ _ _ Hd) in Ht
      | Ht : ds_mod R = Some _ |- _ =>
          let Rm := fresh "Rm" in
          let Hdm := fresh "Hdm" in
          destruct (dsg_mod _ _ _ _ _ _ _ Hd Ht) as (Rm & ? & Hdm); clear Ht;
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
      try solve [ econstructor; eauto using gc_sub_resolve, ind_lookup_gc_sub, ind_mlookup_gc_sub, record_lookup_gc_sub ].
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
        destruct TΦ; destruct (emb_mdenote _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) He G _ _ (mdenote_unit _ _ G (me_unit fp) _ _ _ eq_refl Hu)) as (R2 & Hm2 & _);
        inversion Hm2; subst; [ eapply wf_me_unit; [ eauto | eassumption ] | |];
        (* a unit is the module of no member and of no record type *)
        exfalso;
        [ match goal with Hk : gs_find_ind _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
            cbn in Hq; injection Hq as <-; destruct (frame_ind_parent _ _ Hg _ _ Hk) as ([? cq] & ? & Hp) end
        | match goal with Hk : gs_find_record _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
            cbn in Hq; injection Hq as <-; destruct (frame_record_parent _ _ Hg _ _ Hk) as ([? cq] & ? & Hp) end ];
        unfold qname_in in Hp; cbn in Hp; injection Hp as _ Hc; destruct cq; discriminate
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
  | ge_ind _ _ _ _ Φ => gm_resolve Φ ip
  | ge_def_mod _ _ _ _ => None
  | ge_record _ _ _ Φ => gm_resolve Φ ip
  end.

(** The entries an entry stores, read below its own path: itself, and
    the entries of its body. *)
Definition ge_subentry (E : gentry) (ip : list String.string) : option gentry :=
  match ip with
  | nil => Some E
  | _ :: _ =>
      match E with
      | ge_mod _ (gu_mk _ (md_body _ Φ)) => gm_entry Φ ip
      | ge_ind _ _ _ _ Φ => gm_entry Φ ip
      | ge_record _ _ _ Φ => gm_entry Φ ip
      | _ => None
      end
  end.

Lemma gm_entry_ext_here : forall Φ x E ip, gm_entry (Φ ⊳ x ↦ E) (x :: ip) = ge_subentry E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? Φ' | ? ? ? [? [? ? | ?]] | ? ? ? ?]; reflexivity.
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

Lemma gc_entry_frame : forall Θ mp K U Ξ p E,
    gc_entry Θ ((mp, K, U) :: Ξ) p = Some E ->
    (exists ip, p = qname_app mp ip /\ gm_entry (gu_mod U) ip = Some E) \/ gc_entry Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_entry, gc_entry_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_entry_frame_here : forall Θ mp K U Ξ ip,
    gc_entry Θ ((mp, K, U) :: Ξ) (qname_app mp ip) = gm_entry (gu_mod U) ip.
Proof. intros; unfold gc_entry, gc_entry_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gm_resolve_ext_here : forall Φ x E ip,
    gm_resolve (Φ ⊳ x ↦ E) (x :: ip) = ge_entries E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? Φ' | ? ? ? [? [? ? | ?]] | ? ? ? ?]; cbn; rewrite ?gm_resolve_nil; reflexivity.
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


(** A filed unit has the modules its closed frame had: the declarations of
    inductive types among them. *)
Lemma ind_mlookup_file : forall Θ fp U p,
    ind_mlookup ((fp, U) :: Θ) nil p = ind_mlookup Θ ((q_abs fp nil, fk_module, U) :: nil) p.
Proof.
  intros; rewrite !ind_mlookup_unfold, gs_find_ind_module_frame; cbn [gs_find_ind].
  replace (match qname_strip (q_abs fp nil) p with Some _ => @None indref | None => None end) with (@None indref)
    by (destruct (qname_strip _ _); reflexivity).
  unfold gc_module, gc_module_u; cbn [gs_find_tele gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl.
    destruct (q_chain p) as [| x ip]; cbn; [ reflexivity | rewrite List.app_nil_r; reflexivity ].
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

Lemma ind_lookup_file : forall Θ fp U p,
    ind_lookup ((fp, U) :: Θ) nil p = ind_lookup Θ ((q_abs fp nil, fk_module, U) :: nil) p.
Proof. intros; rewrite !ind_lookup_unfold, ind_mlookup_file; reflexivity. Qed.

(** The module an entry is, read at its own path, over the telescope [T]. *)
Definition ge_module (T : ctx) (E : gentry) : option modres :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body sm _)) => Some (mr_body (Δ ++ T) None)
  | ge_mod _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')))
  | ge_ind _ pq k D _ => Some (mr_body (ind_uparams D) (Some (pq, k, D)))
  | ge_def_mod _ _ _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')))
  | ge_def_mod _ _ _ (gu_mk _ (md_body _ _)) => None
  | ge_record _ p R _ => Some (mr_body (record_mod_tele p R) None)
  end.

Lemma gm_submodule_ext_here_nil : forall T Φ x E, gm_submodule T (Φ ⊳ x ↦ E) x nil = ge_module T E.
Proof. intros; cbn; rewrite String.eqb_refl; destruct E as [| ? [Δ [? ? | ?]] | ? ? ? ? ? | ? ? ? [? [? ? | ?]] | ? ? ? ?]; reflexivity. Qed.

(** The body an entry is, read at its own path, over the telescope [T]. *)
Definition ge_selfbody (T : ctx) (E : gentry) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ | ge_mod _ (gu_mk _ (md_alias _)) | ge_def_mod _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body sm Φ)) => Some (Δ ++ T, Φ)
  | ge_ind _ _ _ D Φ => Some (ind_uparams D, Φ)
  | ge_record _ p R Φ => Some (record_mod_tele p R, Φ)
  end.

Lemma gm_subbody_ext_here_nil : forall T Φ x E, gm_subbody T (Φ ⊳ x ↦ E) x nil = ge_selfbody T E.
Proof. intros; cbn; rewrite String.eqb_refl; destruct E as [| ? [Δ [? ? | ?]] | ? ? ? ? ? | ? ? ? [? [? ? | ?]] | ? ? ? ?]; reflexivity. Qed.

(** The submodules an entry contributes, read below its own path, for an
    entry checked over the telescope [T]. *)
Definition ge_submodule (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option modres :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body sm Φ)) => gm_submodule (Δ ++ T) Φ x ip
  | ge_mod _ (gu_mk Δ (md_alias E')) => None
  | ge_ind _ _ _ D Φ => gm_submodule (ind_uparams D) Φ x ip
  | ge_def_mod _ _ _ _ => None
  | ge_record _ p R Φ => gm_submodule (record_mod_tele p R) Φ x ip
  end.

Lemma gm_submodule_ext_here : forall T Φ x E z ip r,
    ge_submodule T E z ip = Some r -> gm_submodule T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? ? | ? ? ? [? [? ? | ?]] | ? ? ? ?]; cbn in H; [ discriminate | exact H | exact H | exact H | discriminate | discriminate | exact H ].
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
    destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? ? | ? ? ? [? [? ? | ?]] | ? ? ? ?]; cbn in *; try discriminate; exact H.
Qed.

(** The body modules an entry contributes, read below its own path. *)
Definition ge_subbody (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ U => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  | ge_ind _ _ _ D Φ => gm_subbody (ind_uparams D) Φ x ip
  | ge_def_mod _ _ _ _ => None
  | ge_record _ p R Φ => gm_subbody (record_mod_tele p R) Φ x ip
  end.

Lemma gm_subbody_ext_here : forall T Φ x E z ip r,
    ge_subbody T E z ip = Some r -> gm_subbody T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? ? | ? ? ? [? [? ? | ?]] | ? ? ? ?]; cbn in H; [ discriminate | exact H | | exact H | discriminate | discriminate | exact H ].
  destruct z; discriminate.
Qed.

(** [Ctb Θ2 Ξ2 T mp E]: the target [Θ2 ⍮ Ξ2] has, at the path [mp], what
    the entry [E], checked over the telescope [T], contributes: its
    definitions, its module and its submodules, its body and its sub-bodies,
    these perhaps grown. *)
Record Ctb (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (mp : qname) (E : gentry) : Prop := mk_Ctb
  { ctb_entries : forall (ip : list String.string) E0, ge_entries E ip = Some E0 ->
      gc_resolve Θ2 Ξ2 (qname_app mp ip) = Some E0
  ; ctb_module : forall r, ge_module T E = Some r -> gc_module Θ2 Ξ2 mp = Some r
  ; ctb_submodule : forall x (ip : list String.string) r, ge_submodule T E x ip = Some r ->
      gc_module Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r
  ; ctb_selfbody : forall T' Φ, ge_selfbody T E = Some (T', Φ) ->
      exists Φ', gc_body Θ2 Ξ2 mp = Some (T', Φ') /\ gm_grows Φ Φ'
  ; ctb_subbody : forall x (ip : list String.string) T' Φ, ge_subbody T E x ip = Some (T', Φ) ->
      exists Φ', gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some (T', Φ') /\ gm_grows Φ Φ'
  ; ctb_subentry : forall (ip : list String.string) E0, ge_subentry E ip = Some E0 ->
      exists E0', gc_entry Θ2 Ξ2 (qname_app mp ip) = Some E0' /\ entry_grows E0 E0' }.

(** What a frame extended by an entry contributes, at an embedding of it. *)
Lemma Ctb_frame : forall Θ mp K Δ Φ x E Ξ Θ2 Ξ2,
    gc_sub Θ ((mp, K, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ) Θ2 Ξ2 ->
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
  - intros ip0 E0 HE0; rewrite qname_app_in; apply (gc_sub_entry _ _ _ _ _ _ Hs).
    rewrite gc_entry_frame_here; cbn [gu_mod]; rewrite gm_entry_ext_here; exact HE0.
Qed.

(** The entry the open frame at [mp] closes into, of the frame's kind: a
    body module, the module of a member of a group, or a record type at
    [mp]. *)
Definition frame_entry (pv : bool) (mp : qname) (K : frame_kind) (Δ : ctx) (Φ : gmod) : gentry :=
  match K with
  | fk_module => ge_body pv Δ Φ
  | fk_ind pq k D => ge_ind pv pq k D Φ
  | fk_record R => ge_record pv mp R Φ
  end.

(** The member a frame's kind names, if any. *)
Definition kind_ref (K : frame_kind) : option (qname * nat * ind_decl) :=
  match K with
  | fk_module | fk_record _ => None
  | fk_ind pq k D => Some (pq, k, D)
  end.

(** The record type a frame's kind names, if any. *)
Definition kind_record (K : frame_kind) : option record_decl :=
  match K with
  | fk_module | fk_ind _ _ _ => None
  | fk_record R => Some R
  end.

(** The parameters of the frame at [mp] of its kind over [T]: any for a
    module, the group's uniform ones for the module of a member, the
    record's own and then a value of it for the module of a record type. *)
Definition kind_tele (mp : qname) (K : frame_kind) (Δ T : ctx) : Prop :=
  match K with
  | fk_module => True
  | fk_ind _ _ D => ind_uparams D = Δ ++ T
  | fk_record R => exists Δr, Δ = ce_ass (record_self mp R) :: Δr /\ record_params R = Δr ++ T
  end.

Lemma gs_find_ind_own : forall mp K U Ξ, gs_find_ind ((mp, K, U) :: Ξ) mp = kind_ref K.
Proof. intros; cbn; rewrite qname_strip_refl; destruct K; reflexivity. Qed.

Lemma gs_find_record_own : forall mp K U Ξ, gs_find_record ((mp, K, U) :: Ξ) mp = kind_record K.
Proof. intros; cbn; rewrite qname_strip_refl; destruct K; reflexivity. Qed.

(** Where the entry a frame closes into is, the record type its kind names
    is read. *)
Lemma frame_entry_record_lookup : forall Θ Ξ pv mp K Δ Φ p E',
    gc_entry Θ Ξ p = Some E' -> entry_grows (frame_entry pv mp K Δ Φ) E' -> record_lookup Θ Ξ p = kind_record K.
Proof.
  intros * He Hg; unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ He), He.
  destruct K as [| pq k D | R]; cbn in Hg |- *.
  - destruct E' as [| ? [? [? ?| ?]] | | | ]; cbn in Hg; try discriminate; reflexivity.
  - destruct E' as [| ? [? [? ?| ?]] | | | ]; cbn in Hg; try discriminate; try contradiction; reflexivity.
  - destruct E' as [| ? [? [? ?| ?]] | | | pv' pr' R' Φ']; cbn in Hg; try discriminate; try contradiction.
    destruct Hg as (_ & _ & ->); reflexivity.
Qed.

(** Where a record entry is contributed, its record type is found. *)
Lemma Ctb_record_lookup : forall Θ2 Ξ2 T mp pv pr R Φ,
    Ctb Θ2 Ξ2 T mp (ge_record pv pr R Φ) -> record_lookup Θ2 Ξ2 mp = Some R.
Proof.
  intros * Hc; destruct (ctb_subentry _ _ _ _ _ Hc nil _ eq_refl) as (E' & HE & Hg); rewrite qname_app_nil in HE.
  destruct E' as [| ? [? [? ?| ?]] | | | pv' pr' R' Φ']; cbn in Hg; try discriminate; try contradiction.
  destruct Hg as (_ & _ & <-); exact (gc_entry_record _ _ _ _ _ _ _ HE).
Qed.

(** What the entry a frame closes into contributes is the frame's body, at
    the frame's telescope. *)
Lemma frame_entry_reads : forall pv mp K Δ Φ T, kind_tele mp K Δ T ->
    (forall ip, ge_entries (frame_entry pv mp K Δ Φ) ip = gm_resolve Φ ip) /\
    ge_module T (frame_entry pv mp K Δ Φ) = Some (mr_body (Δ ++ T) (kind_ref K)) /\
    (forall x ip, ge_submodule T (frame_entry pv mp K Δ Φ) x ip = gm_submodule (Δ ++ T) Φ x ip) /\
    ge_selfbody T (frame_entry pv mp K Δ Φ) = Some (Δ ++ T, Φ) /\
    (forall x ip, ge_subbody T (frame_entry pv mp K Δ Φ) x ip = gm_subbody (Δ ++ T) Φ x ip) /\
    (forall x ip, ge_subentry (frame_entry pv mp K Δ Φ) (x :: ip) = gm_entry Φ (x :: ip)).
Proof.
  intros * HK; destruct K as [| pq k D | R]; cbn in HK |- *;
    [| rewrite HK | destruct HK as (Δr & -> & HK); unfold record_mod_tele; rewrite HK ]; repeat split; reflexivity.
Qed.

(** Pushing a nested module's frame, of either kind, embeds into any
    context that has its entries, submodules and bodies where the frame
    says. *)
Lemma gc_sub_nested : forall Θ Ξ mp pv K Δ' Φ' Θ2 Ξ2,
    gc_sub Θ Ξ Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (gs_tele Ξ) mp (frame_entry pv mp K Δ' Φ') ->
    kind_tele mp K Δ' (gs_tele Ξ) ->
    gc_sub Θ ((mp, K, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * Hs [Hin Hm0 Hmod Hb0 Hbod Hen] HK.
  destruct (frame_entry_reads pv _ _ _ Φ' _ HK) as (Rin & Rm0 & Rmod & Rb0 & Rbod & Ren).
  constructor.
  - intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      [ apply Hin; rewrite Rin; exact Hm | eauto using gc_sub_resolve ].
  - intros p r Hr; destruct (gc_module_frame _ _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      [ apply Hmod; rewrite Rmod; exact Hm | eauto using gc_sub_module ].
  - intros p T Φ Hr; destruct (gc_body_frame _ _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      [ apply Hbod; rewrite Rbod; exact Hm | eauto using gc_sub_body ].
  - intros p T Φ Hr; unfold gc_frame in Hr; cbn in Hr.
    destruct (qname_strip mp p) as [ip |] eqn:Hst.
    + destruct ip as [| ? ?]; [| discriminate ]; injection Hr as <- <-.
      apply qname_strip_app_inv in Hst; rewrite qname_app_nil in Hst; subst p.
      destruct (Hb0 (Δ' ++ gs_tele Ξ) Φ' Rb0) as (Φ'' & HΦ'' & _).
      destruct (Hen nil _ eq_refl) as (E0' & HE0' & Hgr); rewrite qname_app_nil in HE0'.
      exists Φ''; right; split; [ exact HΦ'' | split; [ rewrite gs_find_ind_own; exact (Hm0 _ Rm0) |] ].
      rewrite gs_find_record_own; exact (frame_entry_record_lookup _ _ _ _ _ _ _ _ _ HE0' Hgr).
    + destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs ltac:(unfold gc_frame; exact Hr)) as (Φ'' & H'').
      exists Φ''; cbn [gs_find_ind gs_find_record]; rewrite Hst; exact H''.
  - intros p E Hr; destruct (gc_entry_frame _ _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      [| eauto using gc_sub_entry ].
    destruct ip as [| z ip]; [ rewrite gm_entry_nil in Hm; discriminate |].
    apply Hen; rewrite Ren; exact Hm.
  - intros p r Hr; cbn [gs_find_ind] in Hr.
    destruct (qname_strip mp p) as [[| ? ?] |] eqn:Hst; [| discriminate | exact (gc_sub_frame_ind _ _ _ _ _ _ Hs Hr) ].
    apply qname_strip_app_inv in Hst; rewrite qname_app_nil in Hst; subst p.
    destruct K as [| pq k D | R]; [ discriminate | | discriminate ]; injection Hr as <-.
    exact (ind_mlookup_body _ _ _ _ _ (Hm0 _ Rm0)).
  - intros p R Hr; cbn [gs_find_record] in Hr.
    destruct (qname_strip mp p) as [[| ? ?] |] eqn:Hst; [| discriminate | exact (gc_sub_frame_record _ _ _ _ _ _ Hs Hr) ].
    apply qname_strip_app_inv in Hst; rewrite qname_app_nil in Hst; subst p.
    destruct (Hen nil _ eq_refl) as (E0' & HE0' & Hgr); rewrite qname_app_nil in HE0'.
    rewrite (frame_entry_record_lookup _ _ _ _ _ _ _ _ _ HE0' Hgr).
    destruct K as [| pq k D | R']; cbn in Hr |- *; [ discriminate | discriminate | exact Hr ].
Qed.

Lemma Emb_nested : forall Θ Ξ mp pv K Δ' Φ' Θ2 Ξ2,
    Emb Θ Ξ Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (gs_tele Ξ) mp (frame_entry pv mp K Δ' Φ') ->
    kind_tele mp K Δ' (gs_tele Ξ) ->
    Emb Θ ((mp, K, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof. intros * [Hg Hs] Hc HK; constructor; [ exact Hg | exact (gc_sub_nested _ _ _ _ _ _ _ _ _ Hs Hc HK) ]. Qed.

(** Declaring an entry in the innermost frame embeds into any context that
    has what the entry contributes, where the frame says. *)
Lemma Emb_entry : forall Θ mq K Δ Φ0 Ξ y E Θ2 Ξ2,
    Emb Θ ((mq, K, gu_body Δ Φ0) :: Ξ) Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mq y) E ->
    Emb Θ ((mq, K, gu_body Δ (Φ0 ⊳ y ↦ E)) :: Ξ) Θ2 Ξ2.
Proof.
  intros * [Hg Hs] [Hin Hm0 Hmod Hb0 Hbod Hen]; constructor; [ assumption | constructor ].
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
           destruct E as [| ? [Δ' [? Φ' | E']] | ? ? ? ? ? | ? ? ? [? [? ? | ?]] | ? ? ? ?]; cbn in *; try discriminate; exact Hr.
      * apply (gc_sub_body _ _ _ _ _ _ _ Hs); rewrite gc_body_frame_here; exact Hr.
    + apply (gc_sub_body _ _ _ _ _ _ _ Hs); unfold gc_body; cbn; rewrite Hst; exact Hr.
  - intros p T Φ Hr; rewrite (gs_find_ind_unit _ _ _ (gu_body Δ Φ0)), (gs_find_record_unit _ _ _ (gu_body Δ Φ0)).
    unfold gc_frame in Hr; cbn in Hr.
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
  - intros p r Hr; rewrite (gs_find_ind_unit _ _ _ (gu_body Δ Φ0)) in Hr; exact (gc_sub_frame_ind _ _ _ _ _ _ Hs Hr).
  - intros p R Hr; rewrite (gs_find_record_unit _ _ _ (gu_body Δ Φ0)) in Hr; exact (gc_sub_frame_record _ _ _ _ _ _ Hs Hr).
Qed.


(** The views of a group with its members as variables ([grp_sctx]), as
    [wf_gentry_ind_nil] checks them: each view's instance is [IsS] there,
    read at the group's own path; the instance is typed, and the view
    equations hold, there.  Once the group is filed, [grp_sb] sends them to
    the group's uniform parameters (the [decl_typed_view_*] lemmas below). *)
Record views_self_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (IsS : nat -> list exp) : Prop := mk_views_self_typed
  { (** Each view's uniform arguments are its [IsS] instance with the
        members sent to the group's own type formers ([grp_sb]) *)
    views_self_typed_link : forall mp, ind_mpath D 0 = Some mp ->
      forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
        Is = List.map (fun I => I[grp_sb mp D]) (IsS k)
    (** Each instance argument is typed at the container's uniform
        telescope, over the members as variables *)
  ; views_self_typed_is : forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> nth_error (IsS k) j = Some I ->
      nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
      Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T
    (** The view a view maps a container view to has, as instance, the
        container view's arguments at this view's instance *)
  ; views_self_typed_view_is : forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
      ind_lookup Θ Ξ q'' = Some D'' ->
      nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
      nth_error (IsS v) j' = Some C ->
      nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
      nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
      Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]
    (** A mapped member's non-uniform parameters are the container
        member's at the instance *)
  ; views_self_typed_nparams : forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv ->
      Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))
    (** A mapped member's constructor arguments are the container
        member's at the instance *)
  ; views_self_typed_args : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
        ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs
    (** The shapes' domains of corresponding recursive arguments agree at
        the instance *)
  ; views_self_typed_doms : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      d < ptyp_depth t ->
      exists i, Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                  ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
        ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
        ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i
    (** The parameters of corresponding recursive arguments are typed and
        agree at the instance *)
  ; views_self_typed_ps : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      ind_member D (ptyp_mem t) = Some Mj ->
      nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
      nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                   (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
      Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
        ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
        : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ /\
      Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
        ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
        ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
        : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
    (** The container's sort at the instance is below the group's *)
  ; views_self_typed_sort : forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' ->
      Θ ⍮ Ξ ⍮ grp_sctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ }.

(** What the derivation of a group gives, at any global context: the
    premises of [wf_gentry_ind_nil] but the telescope of the frames.  The
    uniform parameters and the sort are well formed; of each member, its
    non-uniform parameters and the types of its constructors' arguments;
    each view is of a declared member of a filed group at typed uniform
    arguments, and its parts are those of the container's member at them
    (the view equations), with the group's members as variables
    ([decl_typed_selfs]). *)
Record decl_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : Prop := mk_decl_typed
  { (** The uniform parameters are assumptions *)
    decl_typed_ass : tele_ass (ind_uparams D)
    (** No free module variable occurs in the declaration *)
  ; decl_typed_mvc : decl_mvc D
    (** The uniform parameters are a well-formed context *)
  ; decl_typed_uparams_field : ⊢ Θ ⍮ Ξ ⍮ ind_uparams D
    (** The declared members come first, then the views *)
  ; decl_typed_order : ind_order_ok D
    (** The sort is a universe *)
  ; decl_typed_sort_univ : ind_sort_univ (ind_sort D)
    (** The sort is a type over the uniform parameters *)
  ; decl_typed_sort : exists i, Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort D : Typeω@i
    (** The sort's level is a level over the uniform parameters *)
  ; decl_typed_sort_lvl : exists n, Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort_lvl (ind_sort D) : Level@n
    (** Each member's non-uniform parameters are assumptions *)
  ; decl_typed_nparams_ass : forall k Mk, ind_member D k = Some Mk -> tele_ass (im_nparams Mk)
    (** Each member's constructor names are distinct *)
  ; decl_typed_nodup : forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))
    (** Each non-uniform parameter is in the sort, under those before it *)
  ; decl_typed_nparams : forall k Mk Δ1 T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass T :: Δ2 ->
      Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ
    (** Each non-recursive constructor argument is in the sort, under the
        arguments before it *)
  ; decl_typed_args : forall k Mk c gs gs1 A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg A :: gs2 ->
      Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk
        ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + im_nn Mk)]ʷ
    (** Each domain of a recursive argument's shape is in the sort, under
        the domains before it *)
  ; decl_typed_doms : forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
      gs = gs1 ++ ca_rec t :: gs2 -> ptyp_doms t = Bs1 ++ B :: Bs2 ->
      Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk
        ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ
    (** Each recursive argument gives its member as many parameters as it
        has *)
  ; decl_typed_plen : forall k Mk c gs, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> cargs_plen D gs
    (** Each parameter of a recursive argument is typed at its member's
        non-uniform telescope *)
  ; decl_typed_rec_ps : forall k Mk c gs gs1 t gs2 Mj j P T, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
      gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
      nth_error (ptyp_ps t) j = Some P ->
      nth_error (tele_insts (im_nparams Mj)
                   (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn Mk))) (ptyp_ps t)) j
        = Some T ->
      Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk ⊢ P : T
    (** Each view is of a declared member of a filed group, at as many
        uniform arguments as it has, with a map of one entry per container
        member taking the viewed member to the view itself, and the viewed
        member's constructors, their arguments corresponding *)
  ; decl_typed_view : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      exists D' Mk', ind_lookup Θ Ξ qc = Some D' /\ ind_member D' k' = Some Mk' /\ k' < ind_ndecl D' /\
        List.length Is = ind_nu D' /\ List.length vm = List.length (ind_members D') /\
        List.nth_error vm k' = Some k /\
        List.map fst (im_cons Mk) = List.map fst (im_cons Mk') /\
        (forall c gs' gs, ind_con Mk' c = Some gs' -> ind_con Mk c = Some gs -> cargs_corr vm gs' gs)
    (** The members have a rank *)
  ; decl_typed_rank : exists rk, view_rank_ok Θ Ξ D rk
    (** Each view's map takes the container's members to members of the
        same shapes *)
  ; decl_typed_vwrap : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      exists D', ind_lookup Θ Ξ qc = Some D' /\ vwrap_ok D D' vm
    (** The views agree on their maps *)
  ; decl_typed_view_maps_coherent : view_maps_coherent Θ Ξ D
    (** A view maps a declared container member to a view of that member
        at its own uniform arguments *)
  ; decl_typed_view_decl : forall k Mk qc k' Is vm D' i' Mi' v pm', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_decl pm' ->
      nth_error vm i' = Some v ->
      exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm'
    (** A view maps a container view to a view of the same member, at as
        many uniform arguments *)
  ; decl_typed_view_view : forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'', ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
      nth_error vm i' = Some v ->
      exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\
        List.length X = List.length Is''
    (** The view equations hold with the members as variables *)
  ; decl_typed_selfs : exists IsS, views_self_typed Θ Ξ D IsS }.

(** The container of a view found at a context the group's embeds into is
    the one found at the group's. *)
Lemma decl_typed_container : forall Θ Ξ Θ2 Ξ2 D, gc_sub Θ Ξ Θ2 Ξ2 -> decl_typed Θ Ξ D ->
    forall k Mk qc k' Is vm D2, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ2 Ξ2 qc = Some D2 -> ind_lookup Θ Ξ qc = Some D2.
Proof.
  intros * Hs HD * Hk Hh Hl2; destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D' & Mk' & Hl & _).
  rewrite (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) in Hl2; injection Hl2 as <-; exact Hl.
Qed.

(** The views' maps agree at a context the group's embeds into, its views'
    containers being the ones found at the group's. *)
Lemma view_maps_coherent_gc_sub : forall Θ Ξ Θ2 Ξ2 D,
    (forall k Mk qc k' Is vm D2, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ2 Ξ2 qc = Some D2 -> ind_lookup Θ Ξ qc = Some D2) ->
    view_maps_coherent Θ Ξ D -> view_maps_coherent Θ2 Ξ2 D.
Proof.
  unfold view_maps_coherent; intros * Hcont Hc * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); eapply Hc; eassumption.
Qed.

Lemma decl_typed_emb : forall Θ Ξ Θ2 Ξ2 D, Emb Θ Ξ Θ2 Ξ2 -> decl_typed Θ Ξ D -> decl_typed Θ2 Ξ2 D.
Proof.
  intros * He HD; pose proof (em_res _ _ _ _ He) as Hs.
  pose proof (decl_typed_container _ _ _ _ _ Hs HD) as Hcont.
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & Hq & Hst & Hx & _).
  destruct HD as [Ha Hmv HU Ho Hsu [i Hi] [n Hn] Hna Hnd HN HA HB Hpl HP Hv Hrk Hvw Hvc Hvd Hvv [IsS Hself]].
  constructor; try assumption.
  - exact (Hc _ HU).
  - exists i; exact (Ht _ _ _ Hi).
  - exists n; exact (Ht _ _ _ Hn).
  - intros; apply Ht; eapply HN; eassumption.
  - intros; apply Ht; eapply HA; eassumption.
  - intros; apply Ht; eapply HB; eassumption.
  - intros; apply Ht; eapply HP; eassumption.
  - intros * Hk Hh; destruct (Hv _ _ _ _ _ _ Hk Hh) as (D' & Mk' & Hl & Hrest).
    exists D', Mk'; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) | exact Hrest ].
  - destruct Hrk as [rk [Hr0 Hr1]]; exists rk; constructor; [ exact Hr0 |].
    intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; eapply Hr1; eassumption.
  - intros * Hk Hh; destruct (Hvw _ _ _ _ _ _ Hk Hh) as (D' & Hl & Hw).
    exists D'; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) | exact Hw ].
  - exact (view_maps_coherent_gc_sub _ _ _ _ _ Hcont Hvc).
  - intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; eapply Hvd; eassumption.
  - intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; eapply Hvv; eassumption.
  - destruct Hself as [Hlk Hvi Hvvi Hvn Hva Hvdm Hvp Hvs]; exists IsS; constructor; [ exact Hlk | .. ].
    + intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; apply Ht; eapply Hvi; eassumption.
    + intros * Hk Hh Hl Hi' Hh' Hl'' Hvi' HMv HhMv.
      pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); pose proof (Hcont _ _ _ _ _ _ _ HMv HhMv Hl'').
      intros; apply Hq; eapply (Hvvi k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm'); eassumption.
    + intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; apply Hx; eapply (Hvn k Mk qc k' Is vm); eassumption.
    + intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; apply Hx;
        eapply (Hva k Mk qc k' Is vm); eassumption.
    + intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros.
      edestruct (Hvdm k Mk qc k' Is vm) as [j Hj]; [ eassumption .. |]; exists j; apply Hq; exact Hj.
    + intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros.
      edestruct (Hvp k Mk qc k' Is vm) as [Hj1 Hj2]; [ eassumption .. |].
      split; [ apply Ht; exact Hj1 | apply Hq; exact Hj2 ].
    + intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; apply Hst; eapply Hvs; eassumption.
Qed.

(** The premises of [wf_gentry_ind_nil] make a typed group: the view
    equations are at the path of its first member. *)
Ltac build_decl_typed :=
  match goal with
  | HM0 : ind_member ?D 0 = Some ?M0, Hh : im_head ?M0 = mh_decl ?mp |- decl_typed _ _ ?D =>
      let Hmp := fresh "Hmp" in
      assert (Hmp : forall mp', ind_mpath D 0 = Some mp' -> mp' = mp)
        by (let Hp := fresh in intros mp' Hp; unfold ind_mpath in Hp; rewrite HM0 in Hp; unfold im_path in Hp;
            rewrite Hh in Hp; injection Hp as <-; reflexivity);
      constructor; try assumption; try (eexists; eassumption);
        [ .. | eexists; constructor ];
        intros; repeat match goal with Hp : ind_mpath D 0 = Some _ |- _ => apply Hmp in Hp; subst end;
        first [ solve [ eauto ] | solve [ split; eauto ] | eexists; eauto ]
  end.

(** ** The Types of a Group Are Types

    The type of a type former, of a constructor and of a recursive
    argument, at a group [decl_typed] says is well formed, the groups found
    being typed too ([decls_typed]): a view is a member of another group. *)

(** Every group filed in the global context is typed. *)
Definition decls_typed (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall pq D, ind_lookup Θ Ξ pq = Some D -> decl_typed Θ Ξ D.

(** The uniform parameters of a typed group are a well-formed telescope of
    assumptions. *)
Lemma decl_typed_uparams : forall Θ Ξ D, decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D /\ tele_ass (ind_uparams D).
Proof. intros * HD; split; [ exact (decl_typed_uparams_field _ _ _ HD) | exact (decl_typed_ass _ _ _ HD) ]. Qed.

(** A substitution read back from a list of terms: each term at the
    instance of the type of its variable. *)
Lemma wf_sub_of_list_inv : forall Θ Ξ Γ Δ Γ0 σ Ms,
    tele_ass Δ -> List.length Ms = List.length Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list σ Ms : Δ ++ Γ0 ->
    forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : T.
Proof.
  intros * Hass Hl Hσ k N T HN HT.
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (Hlk : Δ ++ Γ0 ∋ #(List.length l2) : A[wk_shiftn (List.length l2 + 1)]ʷ).
  { rewrite HΔeq, <- List.app_assoc.
    replace (List.length l2) with (0 + List.length (List.rev l2)) at 1 by (rewrite List.length_rev; lia).
    replace (A[wk_shiftn (List.length l2 + 1)]ʷ) with (A[↑]ʷ[wk_shiftn (List.length (List.rev l2))]ʷ).
    - apply ctx_lookup_app_r; constructor.
    - rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_rev; lia. }
  pose proof (wf_sub_apply _ _ _ _ _ Hσ _ _ Hlk) as H.
  change (exp_sub (a_var ?x) ?s) with (sentry_exp (s x)) in H.
  rewrite (sb_of_list_nth _ _ _ N) in H by lia.
  replace (List.length Ms - 1 - List.length l2) with k in H by lia.
  rewrite (List.nth_error_nth _ _ _ HN) in H; cbn in H.
  replace (A[sb_of_list σ (List.firstn k Ms)]) with (A[wk_shiftn (List.length l2 + 1)]ʷ[sb_of_list σ Ms]); [ exact H |].
  rewrite exp_sub_wk; apply exp_sub_sb_eq; intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite <- (List.firstn_skipn k Ms) at 1; rewrite sb_of_list_app.
  replace (x + (List.length l2 + 1)) with (List.length (List.skipn k Ms) + x) by (rewrite List.length_skipn; lia).
  rewrite sb_of_list_ge; reflexivity.
Qed.

(** Equal telescopes of assumptions: each context is a substitution into
    the other, by the identity. *)
Lemma ctxsub_ext : forall Θ Ξ Γ Ψ Ψ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> tele_ass Ψ -> Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ˢ Id : Ψ ++ Γ.
Proof.
  induction 1 as [| | | |]; intros Hass.
  - cbn; apply wf_sub_id; assumption.
  - inversion_clear Hass as [| ? ? _ Hass'].
    cbn [List.app]; eapply wf_sub_id_extend; [ apply IHwf_ext_eq; exact Hass' | eassumption | eassumption |].
    eapply wf_subtyp_refl; [ eapply ctxsub_exp; [ apply IHwf_ext_eq; exact Hass' | eassumption ] |].
    eapply wf_exp_eq_sym, ctxsub_exp_eq; [ apply IHwf_ext_eq; exact Hass' | eassumption ].
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
Qed.

Lemma ctxsub_ext_rev : forall Θ Ξ Γ Ψ Ψ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> tele_ass Ψ -> Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ˢ Id : Ψ' ++ Γ.
Proof.
  induction 1 as [| | | |]; intros Hass.
  - cbn; apply wf_sub_id; assumption.
  - inversion_clear Hass as [| ? ? _ Hass'].
    cbn [List.app]; eapply wf_sub_id_extend; [ apply IHwf_ext_eq; exact Hass' | eassumption | eassumption |].
    eapply wf_subtyp_refl; mauto 3.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
Qed.

(** Terms typed at the instances of a telescope are typed at those of an
    equal one. *)
Lemma tele_insts_conv : forall Θ Ξ Γ Δ Δ' Ms,
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Ms = List.length Δ ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts Δ' Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T.
Proof.
  intros * HΔ Ha Ha' Hl HMs.
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha (ext_eq_ctx_left _ _ _ _ _ HΔ) Hl HMs) as Hσ.
  pose proof (wf_sub_compose _ _ _ _ _ _ _ (ctxsub_ext_rev _ _ _ _ _ HΔ Ha) Hσ) as Hσ'.
  rewrite sb_compose_id_left in Hσ'.
  eapply wf_sub_of_list_inv; [ exact Ha' | rewrite <- (ext_eq_length _ _ _ _ _ HΔ); exact Hl | exact Hσ' ].
Qed.

(** The instances of the uniform parameters: a substitution into them. *)
Lemma wf_uparams_sub : forall Θ Ξ Ψ D Us,
    decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ Ψ -> List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ U : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list Id Us : ind_uparams D.
Proof.
  intros * HD HΨ Hl HUs; rewrite <- (List.app_nil_r (ind_uparams D)).
  eapply wf_sub_of_list; [ exact (decl_typed_ass _ _ _ HD) | rewrite List.app_nil_r; exact (decl_typed_uparams_field _ _ _ HD)
                         | exact (wf_sub_to_nil _ _ _ HΨ) | exact Hl | exact HUs ].
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
  intros * HD HE.
  destruct (decl_typed_sort _ _ _ HD) as [i Hi]; destruct (decl_typed_sort_lvl _ _ _ HD) as [n Hn]; pose proof (decl_typed_sort_univ _ _ _ HD) as HS.
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

(** The parameters of a member are a well-formed telescope: its
    non-uniform ones one by one, each at the sort. *)
Lemma member_params_wf : forall Θ Ξ D k Mk, decl_typed Θ Ξ D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ im_params D Mk.
Proof.
  intros * HD Hk; unfold im_params.
  assert (H : forall Δ2 Δ1, im_nparams Mk = Δ1 ++ Δ2 -> ⊢ Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D).
  { induction Δ2 as [| e Δ2 IH]; intros Δ1 Heq; [ exact (decl_typed_uparams_field _ _ _ HD) |].
    pose proof (decl_typed_nparams_ass _ _ _ HD _ _ Hk) as Ha; rewrite Heq in Ha.
    apply List.Forall_app in Ha as [_ Ha]; inversion Ha as [| ? ? [T ->] _]; subst.
    pose proof (IH (Δ1 ++ ce_ass T :: nil) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as HΔ.
    pose proof (decl_typed_nparams _ _ _ HD _ _ _ _ _ Hk Heq) as HT.
    destruct (sort_under _ _ _ _ HD HΔ) as (_ & [n Hn] & HSu).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HT) as [j Hj].
    cbn [List.app]; econstructor; exact Hj. }
  exact (H _ nil eq_refl).
Qed.

(** The sort over the parameters of a member. *)
Lemma member_sort_typed : forall Θ Ξ D k Mk, decl_typed Θ Ξ D -> ind_member D k = Some Mk ->
    (exists i, Θ ⍮ Ξ ⍮ im_params D Mk ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Typeω@i) /\
    (exists n, Θ ⍮ Ξ ⍮ im_params D Mk ⊢ ind_sort_lvl (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Level@n) /\
    ind_sort_univ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ.
Proof. intros * HD Hk; exact (sort_under _ _ _ _ HD (member_params_wf _ _ _ _ _ HD Hk)). Qed.

Lemma ind_ty_typed0 : forall Θ Ξ D k Mk, decl_typed Θ Ξ D -> ind_member D k = Some Mk ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ind_ty D Mk : Typeω@j.
Proof.
  intros * HD Hk; destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([i Hi] & _).
  unfold ind_ty; eapply ctx_pi_wf0; exact Hi.
Qed.

Lemma ind_ty_typed : forall Θ Ξ Γ D k Mk,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty D Mk : Typeω@j.
Proof.
  intros * HD Hc Hk HΓ; destruct (ind_ty_typed0 _ _ _ _ _ HD Hk) as [j Hj]; exists j.
  eapply closed_weaken_exp; [ exact HΓ | exact Hj | eapply decl_closed_ind_ty; eassumption | exact I ].
Qed.

(** The type former of a declared member applied to terms of the
    parameters' types, of which the type is the sort at them. *)
Lemma wf_ind_apps : forall Θ Ξ Ψ p D j Mj Ms,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> j < ind_ndecl D ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ -> List.length Ms = im_np D Mj ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts (im_params D Mj) Id Ms) k = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind p j) Ms : (ind_sort D)[wk_shiftn (im_nn Mj)]ʷ[sb_of_list Id Ms].
Proof.
  intros * HD Hc Hl Hj Hlt HΨ HMl HMs.
  destruct (member_sort_typed _ _ _ _ _ HD Hj) as ([i Hi] & _).
  eapply wf_apps_closed_pi;
    [ eapply decl_closed_params_ass; eassumption | eapply decl_closed_params; eassumption | | exact Hi | exact HΨ
    | | rewrite length_im_params; exact HMl | exact HMs ].
  - eapply exp_scoped_wk; [ exact (decl_closed_sort _ Hc) |]; intros x Hx; rewrite length_im_params; unfold wk_shiftn, im_np; lia.
  - eapply wf_ind; eassumption.
Qed.

(** The sort at the uniform parameters [Us] and any non-uniform ones is
    the sort at [Us]. *)
Lemma sort_at_args : forall D M Us Ns,
    decl_closed D -> List.length Ns = im_nn M ->
    (ind_sort D)[wk_shiftn (im_nn M)]ʷ[sb_of_list Id (Us ++ Ns)] = (ind_sort D)[sb_of_list Id Us].
Proof.
  intros * Hc Hl.
  rewrite exp_sub_wk; eapply exp_scoped_sub_agree; [ exact (decl_closed_sort _ Hc) |].
  intros x Hx; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite sb_of_list_app, <- Hl, Nat.add_comm, sb_of_list_ge; reflexivity.
Qed.

(** The sort at variables is the sort shifted. *)
(** A term scoped by [n] variables, at [n] variables, is shifted. *)
Lemma exp_at_vars : forall n M j, exp_scoped n M -> exp_mvc 0 M -> M[sb_of_list Id (vars_from j n)] = M[wk_shiftn j]ʷ.
Proof.
  intros * Hs Hm; rewrite <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact Hs | exact Hm |].
  intros x Hx; cbn [sb_of_wk]; rewrite sb_of_list_vars by exact Hx; cbn; f_equal; lia.
Qed.

(** A [Π] over [Θa] then a telescope [T2] of assumptions, given arguments
    for all of [T2]: the [Π] over [Θa], instantiated at them. *)
Lemma ds_ats_up_term_none : forall Ns T2 Θa A, tele_ass T2 -> length T2 = length Ns ->
    ds_ats (ds_up (Θa ++ T2) (ds_term A None)) Ns = Some (ds_term (ctx_pi Θa A)[sb_of_list Id Ns] None).
Proof.
  induction Ns as [| N Ns IH]; intros * HT Hl.
  - destruct T2; [| cbn in Hl; discriminate ]; cbn; rewrite app_nil_r, exp_sub_id; reflexivity.
  - destruct (List.exists_last (l := T2)) as (T2' & e & ->); [ intros ->; cbn in Hl; discriminate |].
    unfold tele_ass in HT; apply List.Forall_app in HT as [HT' He]; inversion He as [| ? ? [B ->] _]; subst.
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [ds_ats]; rewrite app_assoc, ds_at_up, tele_sub_app, List.length_app, sb_qn_plus; cbn [ds_sub option_map].
    rewrite (IH _ _ _ (tele_ass_sub _ _ HT') ltac:(rewrite length_tele_sub; lia)).
    rewrite <- ctx_pi_sub, exp_sub_sub.
    do 2 f_equal; apply exp_sub_sb_eq; cbn [sb_of_list].
    replace (length T2') with (length Ns) by lia.
    etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ].
Qed.

(** A type former applied, read as a term part at arguments
    ([ds_ats_tm]): of the type an axiom of its type has at them, applied
    to them. *)
Lemma ds_ats_tm_head : forall Ns A M B, app_const M = true -> ds_ats (ds_term A None) Ns = Some (ds_term B None) ->
    ds_ats_tm (ds_term A (Some M)) Ns = Some (ds_term B (Some (apps M Ns))).
Proof.
  induction Ns as [| N Ns IH]; intros * Hc Ha; cbn in Ha |- *; [ injection Ha as <-; reflexivity |].
  destruct (pi_view A) as [[X C] |]; [| discriminate ].
  rewrite (app_const_fn_view _ Hc), Hc.
  apply IH; [ cbn; exact Hc | exact Ha ].
Qed.

(** The type former of a member at arguments for its outermost parameters,
    read as a definition's term part is ([ds_ats_tm]): its type at them,
    the type former applied to them.  This is the [Π] of its type
    instantiated at them. *)
Lemma ds_ats_tm_ind : forall D Mk pq k Ns, tele_ass (ind_uparams D) -> length Ns <= length (ind_uparams D) ->
    ds_ats_tm (ds_term (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (Some (a_ind pq k))) Ns =
    Some (ds_term (ind_ty_at D Mk Ns) (Some (apps (a_ind pq k) Ns))).
Proof.
  intros * Ha Hl.
  set (U1 := List.firstn (length (ind_uparams D) - length Ns) (ind_uparams D)).
  set (U2 := List.skipn (length (ind_uparams D) - length Ns) (ind_uparams D)).
  assert (HU : ind_uparams D = U1 ++ U2) by (symmetry; apply List.firstn_skipn).
  assert (Hl2 : length U2 = length Ns) by (subst U2; rewrite List.length_skipn; lia).
  assert (Hp : im_params D Mk = (im_nparams Mk ++ U1) ++ U2) by (unfold im_params; rewrite HU, List.app_assoc; reflexivity).
  rewrite HU in Ha; unfold tele_ass in Ha; apply List.Forall_app in Ha as [_ Ha2].
  apply ds_ats_tm_head; [ reflexivity |].
  change (ds_term (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) None)
    with (ds_up (im_params D Mk) (ds_term (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ None)).
  rewrite Hp, (ds_ats_up_term_none _ _ _ _ Ha2 Hl2); do 2 f_equal.
  unfold ind_ty_at; rewrite <- length_im_params, Hp.
  replace (length ((im_nparams Mk ++ U1) ++ U2) - length Ns) with (length (im_nparams Mk ++ U1))
    by (rewrite !List.length_app; lia).
  rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity.
Qed.

(** Likewise the type former of a record type. *)
Lemma ds_ats_tm_record : forall R p Ns, tele_ass (record_params R) -> length Ns <= length (record_params R) ->
    ds_ats_tm (ds_term (ctx_pi (record_params R) (record_sort R)) (Some (a_record p))) Ns =
    Some (ds_term (record_ty_at R Ns) (Some (apps (a_record p) Ns))).
Proof.
  intros * Ha Hl.
  set (U1 := List.firstn (length (record_params R) - length Ns) (record_params R)).
  set (U2 := List.skipn (length (record_params R) - length Ns) (record_params R)).
  assert (HU : record_params R = U1 ++ U2) by (symmetry; apply List.firstn_skipn).
  assert (Hl2 : length U2 = length Ns) by (subst U2; rewrite List.length_skipn; lia).
  rewrite HU in Ha; unfold tele_ass in Ha; apply List.Forall_app in Ha as [_ Ha2].
  apply ds_ats_tm_head; [ reflexivity |].
  change (ds_term (ctx_pi (record_params R) (record_sort R)) None) with (ds_up (record_params R) (ds_term (record_sort R) None)).
  rewrite HU, (ds_ats_up_term_none _ _ _ _ Ha2 Hl2); do 2 f_equal.
Qed.

Lemma sort_at_vars : forall D j,
    decl_closed D -> decl_mvc D -> (ind_sort D)[sb_of_list Id (vars_from j (ind_nu D))] = (ind_sort D)[wk_shiftn j]ʷ.
Proof. intros * Hc Hm; apply exp_at_vars; [ exact (decl_closed_sort _ Hc) | exact (decl_mvc_sort _ Hm) ]. Qed.

(** ** The Views of a Filed Group

    Once a group is filed at the path [p] of its first member, [grp_sb p D]
    sends its members as variables to its type formers at the uniform
    parameters; the group's own data, moved under the [Self]s by
    [self_wk], comes back unchanged. *)

Lemma length_grp_sb_list : forall p D,
    List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D))) = ind_ndecl D.
Proof. intros; rewrite List.length_map, List.length_seq; reflexivity. Qed.

Lemma self_wk_grp_sb : forall p D k, sb_eq (ι (self_wk D k) ⨟ sb_qn k (grp_sb p D)) Id.
Proof.
  intros p D k x; cbn [sb_compose sb_of_wk sentry_sub]; unfold self_wk.
  destruct (Nat.lt_ge_cases x k) as [Hx | Hx].
  - rewrite wk_qn_lt, sb_qn_lt by assumption; reflexivity.
  - rewrite wk_qn_ge by assumption; rewrite sb_qn_ge by (unfold wk_shiftn; lia).
    unfold wk_shiftn, grp_sb.
    replace (x - k + ind_ndecl D + k - k)
      with (List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D))) + (x - k))
      by (rewrite length_grp_sb_list; lia).
    rewrite sb_of_list_ge; cbn; f_equal; lia.
Qed.

Lemma exp_self_wk_grp_sb : forall p D k A, A[self_wk D k]ʷ[sb_qn k (grp_sb p D)] = A.
Proof. intros; rewrite exp_sub_wk, (exp_sub_sb_eq _ _ _ (self_wk_grp_sb p D k)); apply exp_sub_id. Qed.

Lemma tele_self_wk_grp_sb : forall p D k Δ, tele_sub (tele_wk Δ (self_wk D k)) (sb_qn k (grp_sb p D)) = Δ.
Proof.
  intros; rewrite <- tele_sub_of_wk, tele_sub_sub.
  rewrite (tele_sub_sb_eq _ _ _ (self_wk_grp_sb p D k)); apply tele_sub_id.
Qed.

(** The instance of a container at the view's arguments with the members as
    variables [L], followed by [grp_sb], is the instance at the arguments,
    on a term over the container's uniform parameters and [n] binders. *)
Lemma sb_qn_list_grp_sb : forall n L τ x, x < n + List.length L ->
    sentry_sub (sb_qn n (sb_of_list Id L) x) (sb_qn n τ) = sb_qn n (sb_of_list Id (List.map (fun M => M[τ]) L)) x.
Proof.
  intros * Hx; destruct (Nat.lt_ge_cases x n) as [Hn | Hn].
  - rewrite !sb_qn_lt by assumption; cbn; rewrite sb_qn_lt by assumption; reflexivity.
  - rewrite !sb_qn_ge by assumption.
    rewrite <- (sb_of_list_lt_compose L τ (x - n)) by lia.
    rewrite (sb_of_list_nth L Id (x - n) a_True) by lia; cbn [sentry_wk sentry_sub].
    f_equal; apply exp_shiftn_sub_qn0.
Qed.

Lemma exp_list_grp_sb : forall n L τ X, exp_scoped (n + List.length L) X ->
    X[sb_qn n (sb_of_list Id L)][sb_qn n τ] = X[sb_qn n (sb_of_list Id (List.map (fun M => M[τ]) L))].
Proof.
  intros * HX; rewrite exp_sub_sub; eapply exp_scoped_sub_agree; [ exact HX |].
  intros x Hx; cbn [sb_compose]; apply sb_qn_list_grp_sb; exact Hx.
Qed.

Lemma tele_list_grp_sb : forall n L τ Δ, ctx_scoped (n + List.length L) Δ ->
    tele_sub (tele_sub Δ (sb_qn n (sb_of_list Id L))) (sb_qn n τ) = tele_sub Δ (sb_qn n (sb_of_list Id (List.map (fun M => M[τ]) L))).
Proof.
  intros * HΔ; rewrite tele_sub_sub; eapply tele_scoped_sub_agree; [ exact HΔ |].
  intros x Hx; cbn [sb_compose]; apply sb_qn_list_grp_sb; exact Hx.
Qed.

Lemma apps_exp_app : forall Ms Ns M, apps_exp M (Ms ++ Ns) = apps_exp (apps_exp M Ms) Ns.
Proof. induction Ms as [| N Ms IH]; intros; cbn; [ reflexivity | apply IH ]. Qed.

Lemma firstn_S_nth_error : forall {A} (l : list A) n x,
    List.nth_error l n = Some x -> List.firstn (S n) l = List.firstn n l ++ x :: nil.
Proof.
  intros A l; induction l as [| y l IH]; intros [| n] x H; cbn in H; try discriminate.
  - injection H as ->; reflexivity.
  - rewrite !List.firstn_cons, (IH _ _ H); reflexivity.
Qed.

Lemma grp_selfs_from_snoc : forall D l M j,
    grp_selfs_from D j (l ++ M :: nil) = ce_ass (self_ty D M)[wk_shiftn (j + List.length l)]ʷ :: grp_selfs_from D j l.
Proof.
  intros D l; induction l as [| M0 l IH]; intros; cbn [List.app grp_selfs_from List.length].
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH; cbn [List.app]; do 4 f_equal; lia.
Qed.

Lemma self_ty_scoped : forall D k M, decl_closed D -> ind_member D k = Some M -> exp_scoped (ind_nu D) (self_ty D M).
Proof.
  intros * Hc Hk; pose proof (decl_closed_members _ Hc _ _ Hk) as HM; unfold self_ty.
  apply ctx_pi_scoped; [ exact (member_closed_nparams _ _ HM) |].
  eapply exp_scoped_wk; [ exact (decl_closed_sort _ Hc) |]; intros x Hx; unfold wk_shiftn, im_nn; lia.
Qed.

Lemma self_ty_mvc : forall D k M, decl_closed D -> decl_mvc D -> ind_member D k = Some M -> exp_mvc 0 (self_ty D M).
Proof.
  intros * Hc Hm Hk; pose proof (decl_closed_members _ Hc _ _ Hk) as HM; unfold self_ty.
  destruct (decl_mvc_members _ Hm _ _ Hk) as (HnM & _ & _).
  apply ctx_pi_mvc; [ exact (member_closed_ass _ _ HM) | exact HnM |].
  eapply exp_mvc_mono; [| apply exp_mvc_wk; exact (decl_mvc_sort _ Hm) ]; lia.
Qed.

(** The type former of a declared member at the uniform parameters is of
    the member's type with the members as variables. *)
Lemma self_typed : forall Θ Ξ p D j Mj,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> j < ind_ndecl D ->
    Θ ⍮ Ξ ⍮ ind_uparams D ⊢ apps (a_ind p j) (vars_from 0 (ind_nu D)) : self_ty D Mj.
Proof.
  intros * HD Hc Hl Hj Hlt.
  pose proof (decl_typed_uparams_field _ _ _ HD) as HU.
  destruct (member_sort_typed _ _ _ _ _ HD Hj) as ([i Hi] & _).
  pose proof (member_params_wf _ _ _ _ _ HD Hj) as HP; unfold im_params in HP, Hi.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [i' Hi'].
  pose proof (self_ty_scoped _ _ _ Hc Hj) as Hs.
  replace (self_ty D Mj) with ((self_ty D Mj)[sb_of_list Id (vars_from 0 (ind_nu D))]).
  - eapply wf_apps_closed_pi; [ exact (decl_typed_ass _ _ _ HD) | exact (decl_closed_uparams _ Hc) | exact Hs | exact Hi' | exact HU | | |].
    + pose proof (wf_ind _ _ _ _ _ _ _ HU Hl Hj Hlt) as H; unfold ind_ty, im_params in H; rewrite ctx_pi_app in H; exact H.
    + rewrite length_vars_from; reflexivity.
    + pose proof (wf_vars_tele Θ Ξ nil (ind_uparams D) (decl_typed_ass _ _ _ HD) (decl_closed_uparams _ Hc) (decl_mvc_uparams _ (decl_typed_mvc _ _ _ HD))) as H.
      cbn [List.app List.length] in H; exact (H HU).
  - rewrite (exp_at_vars _ _ _ Hs (self_ty_mvc _ _ _ Hc (decl_typed_mvc _ _ _ HD) Hj)).
    apply (exp_scoped_wk_id _ _ _ Hs); intros; unfold wk_shiftn; lia.
Qed.

(** [grp_sb] is a substitution from the uniform parameters into the
    members as variables. *)
Lemma grp_sb_typed : forall Θ Ξ p D,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ grp_sctx D ->
    Θ ⍮ Ξ ⍮ ind_uparams D ⊢ˢ grp_sb p D : grp_sctx D.
Proof.
  intros * HD Hc Hl HS.
  assert (H : forall n, n <= ind_ndecl D ->
    ⊢ Θ ⍮ Ξ ⍮ grp_selfs_from D 0 (List.firstn n (ind_members D)) ++ ind_uparams D ->
    Θ ⍮ Ξ ⍮ ind_uparams D
      ⊢ˢ sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 n))
      : grp_selfs_from D 0 (List.firstn n (ind_members D)) ++ ind_uparams D).
  { induction n as [| n IH]; intros Hn Hctx.
    - cbn; apply wf_sub_id; exact (decl_typed_uparams_field _ _ _ HD).
    - pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn;
        [| apply List.nth_error_None in HMn; lia ].
      rewrite (firstn_S_nth_error _ _ _ HMn) in Hctx |- * .
      rewrite grp_selfs_from_snoc in Hctx |- *; cbn [Nat.add] in Hctx |- *.
      rewrite List.length_firstn in Hctx |- *; replace (Nat.min n (List.length (ind_members D))) with n in * by lia.
      rewrite List.seq_S, List.map_app, sb_of_list_app; cbn [List.map sb_of_list Nat.add].
      destruct (ctx_decomp Hctx) as [Hctx' [i Hi]].
      eapply wf_sub_extend; [ apply IH; [ lia | exact Hctx' ] | exact Hi |].
      rewrite exp_sub_wk.
      rewrite (exp_sub_sb_eq _ _ Id).
      + rewrite exp_sub_id; eapply self_typed; [ exact HD | exact Hc | exact Hl | exact HMn | lia ].
      + intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        replace (x + n) with (List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 n)) + x)
          by (rewrite List.length_map, List.length_seq; lia).
        apply sb_of_list_ge. }
  exact (H _ (le_n _) HS).
Qed.

(** A member's type with the members as variables, sent by [grp_sb], is
    the member's type at the uniform parameters, the views' instances being
    [IsS] sent by it. *)
Definition grp_link (p : qname) (D : ind_decl) (IsS : nat -> list exp) : Prop :=
  forall j Mj qc kc Is vm, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    Is = List.map (fun I => I[grp_sb p D]) (IsS j).

Lemma self_mty_grp_sb : forall p D IsS j d Ns,
    decl_closed D -> decl_mvc D -> ind_order_ok D -> grp_link p D IsS ->
    (self_mty D IsS j d Ns)[sb_qn d (grp_sb p D)]
    = ind_mty p D j (vars_from d (ind_nu D)) (List.map (fun N => N[sb_qn d (grp_sb p D)]) Ns).
Proof.
  intros * Hc Hm Ho Hlk; unfold self_mty, ind_mty.
  destruct (ind_member D j) as [Mj |] eqn:Hj; [| reflexivity ].
  unfold im_ty_at, im_ref, im_pre; destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh; cbn [fst snd];
    rewrite apps_exp_sub.
  - assert (Hlt : j < ind_ndecl D) by (apply (Ho _ _ Hj); unfold im_is_decl; rewrite Hh; reflexivity).
    rewrite apps_exp_app; f_equal; cbn [exp_sub].
    rewrite sb_qn_ge by lia; replace (d + (ind_ndecl D - 1 - j) - d) with (ind_ndecl D - 1 - j) by lia.
    unfold grp_sb; rewrite (sb_of_list_nth _ _ _ a_True) by (rewrite length_grp_sb_list; lia).
    rewrite length_grp_sb_list; replace (ind_ndecl D - 1 - (ind_ndecl D - 1 - j)) with j by lia.
    rewrite (List.nth_indep _ a_True (apps (a_ind p 0) (vars_from 0 (ind_nu D)))) by (rewrite length_grp_sb_list; lia).
    rewrite (List.map_nth (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D)))), List.seq_nth by lia.
    cbn [sentry_wk sentry_exp]; rewrite apps_exp_wk, vars_from_wk_shiftn; reflexivity.
  - rewrite List.map_app; f_equal; f_equal.
    rewrite (Hlk _ _ _ _ _ _ Hj Hh), !List.map_map; apply List.map_ext_in; intros I HI.
    rewrite exp_shiftn_sub_qn0.
    assert (Hin : In I[grp_sb p D] Is)
      by (rewrite (Hlk _ _ _ _ _ _ Hj Hh); exact (List.in_map (fun I0 => I0[grp_sb p D]) _ _ HI)).
    pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hj Hh) as HsIs.
    destruct (decl_mvc_members _ Hm _ _ Hj) as (_ & HmIs & _); rewrite Hh in HmIs; cbn in HmIs.
    rewrite List.Forall_forall in HsIs, HmIs.
    symmetry; apply exp_at_vars; [ exact (HsIs _ Hin) | exact (HmIs _ Hin) ].
Qed.

Lemma sptyp_ty_grp_sb : forall p D IsS t nn pat,
    decl_closed D -> decl_mvc D -> ind_order_ok D -> grp_link p D IsS ->
    (sptyp_ty D IsS nn pat t)[sb_qn (List.length pat + nn) (grp_sb p D)] = ptyp_ty p D nn pat t.
Proof.
  intros p D IsS t; induction t as [j Ps | A t IH]; intros * Hc Hm Ho Hlk; cbn [sptyp_ty ptyp_ty].
  - rewrite self_mty_grp_sb by assumption; unfold ind_uvars; f_equal.
    rewrite List.map_map; apply List.map_ext; intros P; apply exp_self_wk_grp_sb.
  - cbn [exp_sub]; f_equal; [ apply exp_self_wk_grp_sb |].
    exact (IH nn (false :: pat) Hc Hm Ho Hlk).
Qed.

Lemma scargs_ctx_aux_grp_sb : forall p D IsS gs nn pat,
    decl_closed D -> decl_mvc D -> ind_order_ok D -> grp_link p D IsS ->
    tele_sub (scargs_ctx_aux D IsS nn pat gs) (sb_qn (List.length pat + nn) (grp_sb p D)) = cargs_ctx_aux p D nn pat gs.
Proof.
  intros p D IsS gs; induction gs as [| [A | t] gs IH]; intros * Hc Hm Ho Hlk; cbn [scargs_ctx_aux cargs_ctx_aux];
    [ reflexivity | |]; rewrite tele_sub_app; cbn [tele_sub List.length sb_qn centry_sub List.app].
  - f_equal; [ exact (IH nn (false :: pat) Hc Hm Ho Hlk) | do 2 f_equal; apply exp_self_wk_grp_sb ].
  - f_equal; [ exact (IH nn (true :: pat) Hc Hm Ho Hlk) | do 2 f_equal; apply sptyp_ty_grp_sb; assumption ].
Qed.

Corollary scargs_ctx_grp_sb : forall p D IsS Mv gs,
    decl_closed D -> decl_mvc D -> ind_order_ok D -> grp_link p D IsS ->
    tele_sub (scargs_ctx D IsS Mv gs) (sb_qn (im_nn Mv) (grp_sb p D)) = cargs_ctx p D Mv gs.
Proof. intros; exact (scargs_ctx_aux_grp_sb p D IsS gs (im_nn Mv) nil ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)). Qed.
Lemma grp_sb_ext : forall Θ Ξ p D Ψ,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> tele_ass Ψ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ grp_sctx D ->
    Θ ⍮ Ξ ⍮ tele_sub Ψ (grp_sb p D) ++ ind_uparams D ⊢ˢ sb_qn (List.length Ψ) (grp_sb p D) : Ψ ++ grp_sctx D.
Proof.
  intros * HD Hc Hl Hass HΨ.
  pose proof (grp_sb_typed _ _ _ _ HD Hc Hl (ctx_app_wf_tail _ _ _ _ HΨ)) as Hg.
  apply wf_sub_ext; [ exact Hg | | exact HΨ ].
  exact (ext_eq_ctx_left _ _ _ _ _ (sub_preserves_ext _ _ _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΨ) Hg)).
Qed.

Lemma exp_list_grp_sb0 : forall L τ X, exp_scoped (List.length L) X ->
    X[sb_of_list Id L][τ] = X[sb_of_list Id (List.map (fun M => M[τ]) L)].
Proof.
  intros * HX; rewrite exp_sub_sub; eapply exp_scoped_sub_agree; [ exact HX |].
  intros x Hx; cbn [sb_compose]; apply sb_of_list_lt_compose; exact Hx.
Qed.

(** A group found at [p] is filed at the path of its first member. *)
Lemma ind_lookup_mpath : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_mpath D 0 = Some p.
Proof.
  intros * Hg Hl; destruct (ind_lookup_mlookup _ _ _ _ Hl) as [pq Hm].
  exact (ind_selfpath_path _ _ _ _ (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hm)).
Qed.

(** What a group filed at [p] gives with its members as variables, read
    there. *)
Ltac views_filed Hg HD Hl :=
  let Hc := fresh "Hc" in let Hmp := fresh "Hmp" in let IsS := fresh "IsS" in
  let Hs := fresh "Hs" in let Hlk := fresh "Hlk" in
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc;
  pose proof (ind_lookup_mpath _ _ _ _ Hg Hl) as Hmp;
  destruct (decl_typed_selfs _ _ _ HD) as [IsS Hs];
  lazymatch type of Hl with ind_lookup _ _ ?p = Some ?D =>
    assert (Hlk : grp_link p D IsS) by exact (views_self_typed_link _ _ _ _ Hs _ Hmp) end.

(** The views' instances are typed at the uniform parameters. *)
Lemma decl_typed_view_is : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> nth_error Is j = Some I ->
      nth_error (tele_insts (ind_uparams D') Id Is) j = Some T ->
      Θ ⍮ Ξ ⍮ ind_uparams D ⊢ I : T.
Proof.
  intros * Hg HD Hl * Hk Hh Hl' HI HT; views_filed Hg HD Hl.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  rewrite (Hlk _ _ _ _ _ _ Hk Hh) in HI, HT.
  rewrite <- (tele_insts_sub (ind_uparams D') 0 Id Id (grp_sb p D) (IsS k) (decl_closed_ass _ Hc') (decl_closed_uparams _ Hc')
                ltac:(intros; lia)) in HT.
  apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
  pose proof (views_self_typed_is _ _ _ _ Hs _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' HI0 HT0) as H.
  exact (sub_preserves_exp _ _ _ _ _ _ _ H (grp_sb_typed _ _ _ _ HD Hc Hl (presup_exp_ctx H))).
Qed.

(** A view's non-uniform parameters are its container's at the view's
    instance. *)
Lemma decl_typed_view_nparams : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv ->
      Θ ⍮ Ξ ⍮ ind_uparams D ⊢ˣ im_nparams Mv ≈ tele_sub (im_nparams Mi') (sb_of_list Id Is).
Proof.
  intros * Hg HD Hl * Hk Hh Hl' Hi' Hv HMv; views_filed Hg HD Hl.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
  rewrite Hl' in Hl2; injection Hl2 as <-.
  pose proof (views_self_typed_nparams _ _ _ _ Hs _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv) as H.
  pose proof (grp_sb_typed _ _ _ _ HD Hc Hl (presup_ext_eq_ctx H)) as Hσ.
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ H Hσ) as H'.
  rewrite (tele_self_wk_grp_sb p D 0) in H'.
  rewrite (nparams_sub D' i' Mi' (IsS k) (grp_sb p D) Hc' Hi') in H'.
  - rewrite <- (Hlk _ _ _ _ _ _ Hk Hh) in H'; exact H'.
  - rewrite (Hlk _ _ _ _ _ _ Hk Hh), List.length_map in HIl; exact HIl.
Qed.

(** The sort of a view's container at the view's instance is in the
    group's. *)
Lemma decl_typed_view_sort : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' ->
      Θ ⍮ Ξ ⍮ ind_uparams D ⊢ (ind_sort D')[sb_of_list Id Is] ⊆ ind_sort D.
Proof.
  intros * Hg HD Hl * Hk Hh Hl'; views_filed Hg HD Hl.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
  rewrite Hl' in Hl2; injection Hl2 as <-.
  pose proof (views_self_typed_sort _ _ _ _ Hs _ _ _ _ _ _ _ Hk Hh Hl') as H.
  pose proof (sub_preserves_subtyp _ _ _ _ _ _ _ H (grp_sb_typed _ _ _ _ HD Hc Hl (presup_subtyp_ctx H))) as H'.
  rewrite (exp_self_wk_grp_sb p D 0), exp_list_grp_sb0 in H'.
  - rewrite <- (Hlk _ _ _ _ _ _ Hk Hh) in H'; exact H'.
  - rewrite (Hlk _ _ _ _ _ _ Hk Hh), List.length_map in HIl; rewrite HIl; exact (decl_closed_sort _ Hc').
Qed.

(** A member of a typed group at the uniform parameters [Us] and
    non-uniform ones [Ns] is of the sort at [Us]: a declared member is its
    type former at them, and a view the type former of a declared member of
    another group, at the view's instance at [Us] and [Ns], in a sort the
    group's includes. *)
Lemma ind_mty_typed : forall Θ Ξ Ψ p D j Mj Us Ns,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ Ψ ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ U : T) ->
    List.length Ns = im_nn Mj ->
    (forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (im_nparams Mj) (sb_of_list Id Us) Ns) k = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ ind_mty p D j Us Ns : (ind_sort D)[sb_of_list Id Us].
Proof.
  intros * Hg HDs Hl Hj HΨ HUl HUs HNl HNs.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (wf_uparams_sub _ _ _ _ _ HD HΨ HUl HUs) as Hσ.
  unfold ind_mty; rewrite Hj; unfold im_ty_at, im_ref, im_pre.
  destruct (im_head Mj) as [pm | qc k' Is vm] eqn:Hh; cbn [fst snd].
  - (* a declared member: its type former *)
    assert (Hlt : j < ind_ndecl D)
      by (apply (decl_typed_order _ _ _ HD _ _ Hj); unfold im_is_decl; rewrite Hh; reflexivity).
    rewrite <- (sort_at_args D Mj Us Ns Hc HNl).
    eapply wf_ind_apps; [ exact HD | exact Hc | exact Hl | exact Hj | exact Hlt | exact HΨ | |].
    + rewrite List.length_app, HUl, HNl; unfold im_np; lia.
    + unfold im_params; intros k N T HN HT.
      rewrite tele_insts_app in HT by (try exact (decl_typed_ass _ _ _ HD); exact HUl).
      assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
        by (rewrite length_tele_insts by exact (decl_typed_ass _ _ _ HD); rewrite HUl; unfold ind_nu; lia).
      destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
      * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; exact (HUs _ _ _ HN HT).
      * rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
        rewrite HUl in HN; rewrite Hl1 in HT; exact (HNs _ _ _ HN HT).
  - (* a view: the container's type former at the view's instance *)
    destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hj Hh) as (D' & Mk' & Hl' & Hk' & Hlt' & HIl & _ & Hself & _).
    pose proof (HDs _ _ Hl') as HD'.
    pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
    pose proof (decl_typed_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hj Hh Hl' Hk' Hself Hj) as HNeq.
    pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hj Hh) as HsIs.
    set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is).
    assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
    assert (HNl' : List.length Ns = im_nn Mk').
    { rewrite HNl; unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity. }
    (* the sort of the container at the instance is in the group's *)
    assert (HS : Θ ⍮ Ξ ⍮ Ψ ⊢ (ind_sort D')[sb_of_list Id Is'] ⊆ (ind_sort D)[sb_of_list Id Us]).
    { pose proof (sub_preserves_subtyp _ _ _ _ _ _ _ (decl_typed_view_sort _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ Hj Hh Hl') Hσ) as H.
      replace ((ind_sort D')[sb_of_list Id Is']) with ((ind_sort D')[sb_of_list Id Is][sb_of_list Id Us]); [ exact H |].
      rewrite exp_sub_sub; eapply exp_scoped_sub_agree; [ exact (decl_closed_sort _ Hc') |].
      intros x Hx; unfold Is'; apply sb_of_list_lt_compose; lia. }
    eapply wf_exp_subtyp'; [| exact HS ].
    rewrite <- (sort_at_args D' Mk' Is' Ns Hc' HNl').
    eapply wf_ind_apps; [ exact HD' | exact Hc' | exact Hl' | exact Hk' | exact Hlt' | exact HΨ | |].
    + rewrite List.length_app, HIl', HNl'; unfold im_np; lia.
    + unfold im_params; intros k N T HN HT.
      rewrite tele_insts_app in HT by (try exact (decl_typed_ass _ _ _ HD'); exact HIl').
      assert (Hl1 : List.length (tele_insts (ind_uparams D') Id Is') = ind_nu D')
        by (rewrite length_tele_insts by exact (decl_typed_ass _ _ _ HD'); rewrite HIl'; unfold ind_nu; lia).
      destruct (Nat.lt_ge_cases k (ind_nu D')) as [Hk | Hk].
      * (* the instance: the view's uniform arguments at [Us] *)
        rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
        unfold Is' in HN, HT.
        rewrite <- (tele_insts_sub (ind_uparams D') 0 Id Id (sb_of_list Id Us) Is (decl_typed_ass _ _ _ HD') (decl_closed_uparams _ Hc')
                      ltac:(intros; lia)) in HT.
        apply nth_error_map_inv in HN as (I & HI & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
        exact (sub_preserves_exp _ _ _ _ _ _ _ (decl_typed_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ Hj Hh Hl' HI HT0) Hσ).
      * (* the non-uniform ones: at the container's, by the view equation *)
        rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
        rewrite HIl' in HN; rewrite Hl1 in HT.
        revert HN HT; generalize (k - ind_nu D'); intros k0 HN HT.
        rewrite (tele_insts_sb_eq _ (sb_of_list Id Is') (sb_of_list Id Is' ⨟ Id)) in HT
          by (intro; symmetry; apply sb_compose_id_right).
        rewrite <- tele_insts_tele_sub in HT.
        pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as HNeq'.
        rewrite (nparams_sub D' k' Mk' Is (sb_of_list Id Us) Hc' Hk' HIl) in HNeq'; fold Is' in HNeq'.
        eapply (tele_insts_conv _ _ _ _ _ _ HNeq');
          [ apply tele_ass_sub; exact (decl_typed_nparams_ass _ _ _ HD _ _ Hj)
          | apply tele_ass_sub; exact (decl_typed_nparams_ass _ _ _ HD' _ _ Hk')
          | rewrite length_tele_sub; exact HNl | | exact HN | exact HT ].
        intros k1 N1 T1 HN1 HT1; apply (HNs _ _ _ HN1).
        rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT1 by apply sb_compose_id_right.
        exact HT1.
Qed.

(** The type at the uniform parameters and the non-uniform ones [Ps] of
    the context [Tb] over the parameters, moved into the context [E] over
    them by [wk_pat pat], is a type. *)
Lemma rec_leaf_typed : forall Θ Ξ p D k Mk j Mj E Tb pat Ps,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ind_member D j = Some Mj ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ im_params D Mk -> List.length pat = List.length E -> pat_nargs pat = List.length Tb ->
    Θ ⍮ Ξ ⍮ E ++ im_params D Mk ⊢ʷ wk_pat pat : Tb ++ im_params D Mk ->
    List.length Ps = im_nn Mj ->
    (forall i P T, List.nth_error Ps i = Some P ->
       List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (List.length Tb + im_nn Mk))) Ps) i = Some T ->
       Θ ⍮ Ξ ⍮ Tb ++ im_params D Mk ⊢ P : T) ->
    exists l, Θ ⍮ Ξ ⍮ E ++ im_params D Mk
      ⊢ ind_mty p D j (ind_uvars D (im_nn Mk) (List.length pat)) (List.map (fun P => P[wk_pat pat]ʷ) Ps) : Typeω@l.
Proof.
  intros * Hg HDs Hl Hk Hj HΨ Hpat Hpn Hφ HPl HP.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (decl_typed_mvc _ _ _ HD) as Hmv.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (E ++ im_nparams Mk) ++ ind_uparams D) by (rewrite <- List.app_assoc; exact HΨ).
  assert (HlE : List.length (E ++ im_nparams Mk) = List.length pat + im_nn Mk)
    by (rewrite List.length_app, Hpat; reflexivity).
  assert (HUs : ind_uvars D (im_nn Mk) (List.length pat) = vars_from (List.length (E ++ im_nparams Mk)) (List.length (ind_uparams D)))
    by (unfold ind_uvars; rewrite HlE; reflexivity).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, HlE in Hn; rewrite HlE in HSu.
  eapply sort_large; [ exact HSu | exact Hn |].
  rewrite <- (sort_at_vars D _ Hc Hmv); fold (ind_uvars D (im_nn Mk) (List.length pat)).
  eapply ind_mty_typed; [ exact Hg | exact HDs | exact Hl | exact Hj | exact HΨ | unfold ind_uvars; apply length_vars_from | | |].
  - rewrite HUs; unfold im_params; rewrite List.app_assoc; intros i U T HU HT.
    eapply wf_vars_tele; [ exact (decl_typed_ass _ _ _ HD) | exact (decl_closed_uparams _ Hc) | exact (decl_mvc_uparams _ Hmv) | exact HE | exact HU | exact HT ].
  - rewrite List.length_map; exact HPl.
  - intros i N T HN HT.
    apply nth_error_map_inv in HN as (P & HPk & ->).
    set (s := List.length Tb + im_nn Mk).
    assert (Hti : tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mk) (List.length pat))) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
                  = List.map (fun T => T[wk_pat pat]ʷ) (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn s)) Ps)).
    { rewrite <- !map_sub_of_wk; symmetry.
      eapply (tele_insts_sub_mvc _ (ind_nu D));
        [ eapply decl_closed_nparams_ass; eassumption | exact (proj1 (decl_mvc_members _ Hmv _ _ Hj))
        | eapply decl_closed_nparams_scoped; eassumption |].
      intros x Hx; unfold ind_uvars; rewrite sb_of_list_vars by exact Hx; cbn.
      unfold s; rewrite <- Hpn.
      replace (x + (pat_nargs pat + im_nn Mk)) with (pat_nargs pat + (im_nn Mk + x)) by lia.
      rewrite wk_pat_ge; f_equal; lia. }
    rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (wk_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ HPk HT0) Hφ).
Qed.

Lemma doms_ctx_cons : forall B Bs, doms_ctx (B :: Bs) = doms_ctx Bs ++ ce_ass B :: nil.
Proof. reflexivity. Qed.

Lemma ptyp_tele_pi : forall B t, ptyp_tele (pt_pi B t) = ptyp_tele t ++ ce_ass B :: nil.
Proof. reflexivity. Qed.

(** The type of a shape is a type: by its domains, each at the sort, and
    its leaf. *)
Lemma rec_shape_typed : forall Θ Ξ p D k Mk Mj t E Tb pat,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk ->
    ind_member D (ptyp_mem t) = Some Mj ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ im_params D Mk -> List.length pat = List.length E -> pat_nargs pat = List.length Tb ->
    Θ ⍮ Ξ ⍮ E ++ im_params D Mk ⊢ʷ wk_pat pat : Tb ++ im_params D Mk ->
    List.length (ptyp_ps t) = im_nn Mj ->
    (forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ Tb ++ im_params D Mk
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length Tb + im_nn Mk)]ʷ) ->
    (forall i P T, List.nth_error (ptyp_ps t) i = Some P ->
       List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + List.length Tb + im_nn Mk))) (ptyp_ps t)) i
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ Tb ++ im_params D Mk ⊢ P : T) ->
    exists l, Θ ⍮ Ξ ⍮ E ++ im_params D Mk ⊢ ptyp_ty p D (im_nn Mk) pat t : Typeω@l.
Proof.
  intros Θ Ξ p D k Mk Mj t; induction t as [j Ps | B t IH]; intros * Hg HDs Hl Hk Hj HΨ Hpat Hpn Hφ HPl HB HP; cbn [ptyp_ty].
  1: eapply rec_leaf_typed; eassumption.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (HB nil B (ptyp_doms t) eq_refl) as HB0; cbn [doms_ctx List.rev List.map List.app List.length] in HB0.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (Tb ++ im_nparams Mk) ++ ind_uparams D)
    by (rewrite <- List.app_assoc; exact (wf_wk_cod _ _ _ _ _ Hφ)).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, List.length_app in Hn; rewrite List.length_app in HSu.
  change (List.length (im_nparams Mk)) with (im_nn Mk) in Hn, HSu.
  destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j1 Hj1].
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj1 Hφ) as Hj1'; cbn in Hj1'.
  destruct (IH (ce_ass B[wk_pat pat]ʷ :: E) (ce_ass B :: Tb) (false :: pat) Hg HDs Hl Hk Hj) as [j2 Hj2].
  - cbn [List.app]; econstructor; exact Hj1'.
  - cbn; lia.
  - cbn; lia.
  - cbn [List.app wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj1 | exact Hj1' ].
  - exact HPl.
  - intros Bs1 B' Bs2 E'; specialize (HB (B :: Bs1) B' Bs2 ltac:(cbn; rewrite E'; reflexivity)).
    rewrite doms_ctx_cons, <- List.app_assoc in HB; cbn [List.app List.length] in HB |- *.
    replace (List.length Bs1 + S (List.length Tb) + im_nn Mk) with (S (List.length Bs1) + List.length Tb + im_nn Mk) by lia; exact HB.
  - intros i P T HPk HT; specialize (HP i P T HPk).
    unfold ptyp_depth in HP, HT; cbn [ptyp_doms List.length] in HP.
    rewrite ptyp_tele_pi, <- List.app_assoc in HP; cbn [List.app List.length] in HT |- *.
    apply HP; cbn [ptyp_ps].
    replace (S (length (ptyp_doms t)) + length Tb + im_nn Mk) with (length (ptyp_doms t) + S (length Tb) + im_nn Mk) by lia; exact HT.
  - exists (max j1 j2); eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact Hj2 ].
Qed.

(** The arguments before a constructor's argument are a well-formed
    context, which [wk_pat] sends to the one of the non-recursive arguments
    before it. *)
Lemma cargs_ctx_wf : forall Θ Ξ p D k Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D Mk gs1 ++ im_params D Mk /\ ⊢ Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk /\
      Θ ⍮ Ξ ⍮ cargs_ctx p D Mk gs1 ++ im_params D Mk ⊢ʷ wk_pat (cargs_pat gs1) : cargs_strat gs1 ++ im_params D Mk.
Proof.
  intros * Hg HDs Hl Hk Hin gs1; pose proof (HDs _ _ Hl) as HD.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - pose proof (member_params_wf _ _ _ _ _ HD Hk) as HΔ.
    split; [ exact HΔ | split; [ exact HΔ | exact (wf_wk_id _ _ _ HΔ) ] ].
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    destruct (IH _ Heq) as (HΨ & HSt & Hφ).
    rewrite cargs_ctx_snoc, cargs_pat_snoc.
    destruct g as [A | t]; cbn [cargs_ctx_aux List.app].
    + rewrite cargs_strat_snoc_arg.
      pose proof (decl_typed_args _ _ _ HD _ _ _ _ _ _ _ Hk Hin Heq) as HA.
      assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_strat gs1 ++ im_nparams Mk) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact HSt).
      destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
      rewrite <- List.app_assoc, List.length_app in Hn; rewrite List.length_app in HSu.
      change (List.length (im_nparams Mk)) with (im_nn Mk) in Hn, HSu.
      destruct (sort_large _ _ _ _ _ _ HSu Hn HA) as [j Hj].
      pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj Hφ) as Hj'; cbn in Hj'.
      split; [ econstructor; exact Hj' | split; [ econstructor; exact Hj |] ].
      cbn [wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj | exact Hj' ].
    + rewrite cargs_strat_snoc_rec.
      destruct (decl_typed_plen _ _ _ HD _ _ _ _ Hk Hin _ _ _ Heq) as (Mj & Hj & HPl).
      destruct (rec_shape_typed _ _ p D k Mk Mj t (cargs_ctx p D Mk gs1) (cargs_strat gs1) (cargs_pat gs1) Hg HDs Hl Hk Hj HΨ
                  ltac:(rewrite length_cargs_pat, length_cargs_ctx; reflexivity) (pat_nargs_cargs_pat gs1) Hφ HPl
                  (fun Bs1 B Bs2 HBs => decl_typed_doms _ _ _ HD _ _ _ _ _ _ _ _ _ _ Hk Hin Heq HBs)
                  (fun i P T => decl_typed_rec_ps _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ Hk Hin Heq Hj)) as [j Hj'].
      split; [ econstructor; exact Hj' | split; [ exact HSt |] ].
      cbn [wk_pat]; eapply wf_wk_compose; [ apply wf_wk_shift; econstructor; exact Hj' | exact Hφ ].
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
Proof. induction k as [| k IH]; intros [j0 Ps | B t]; cbn; auto. Qed.

Lemma ptyp_doms_skip : forall k t, ptyp_doms (ptyp_skip k t) = List.skipn k (ptyp_doms t).
Proof. induction k as [| k IH]; intros [j0 Ps | B t]; cbn; auto. Qed.

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
Lemma ptyp_mem_skip : forall k t, ptyp_mem (ptyp_skip k t) = ptyp_mem t.
Proof. induction k as [| k IH]; intros [j0 Ps | B t]; cbn; auto. Qed.

(** The non-recursive arguments before an argument of a constructor are a
    well-formed context over the parameters. *)
Lemma cargs_strat_wf : forall Θ Ξ D k Mk c gs, decl_typed Θ Ξ D -> ind_member D k = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    forall gs1 gs2, gs = gs1 ++ gs2 -> ⊢ Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk.
Proof.
  intros * HD Hk Hin gs1; induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - exact (member_params_wf _ _ _ _ _ HD Hk).
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    pose proof (IH _ Heq) as HSt.
    destruct g as [A | t]; [| rewrite cargs_strat_snoc_rec; exact HSt ].
    rewrite cargs_strat_snoc_arg.
    pose proof (decl_typed_args _ _ _ HD _ _ _ _ _ _ _ Hk Hin Heq) as HA.
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_strat gs1 ++ im_nparams Mk) ++ ind_uparams D)
      by (rewrite <- List.app_assoc; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- List.app_assoc, List.length_app in Hn; rewrite List.length_app in HSu.
    change (List.length (im_nparams Mk)) with (im_nn Mk) in Hn, HSu.
    destruct (sort_large _ _ _ _ _ _ HSu Hn HA) as [j Hj].
    econstructor; exact Hj.
Qed.

(** The domains of a recursive argument's shape before the [k]-th, over
    the non-recursive arguments before it: a well-formed context. *)
Lemma doms_prefix_wf : forall Θ Ξ D k0 Mk c gs, decl_typed Θ Ξ D -> ind_member D k0 = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> forall k, k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mk.
Proof.
  intros * HD Hk0 Hin gs1 t gs2 Heq; induction k as [| k IH]; intros Hk.
  - cbn [List.firstn doms_ctx List.map List.rev List.app]; exact (cargs_strat_wf _ _ _ _ _ _ _ HD Hk0 Hin gs1 _ Heq).
  - pose proof (IH ltac:(lia)) as HSt.
    destruct (List.nth_error (ptyp_doms t) k) as [B |] eqn:HB; [| apply List.nth_error_None in HB; lia ].
    destruct (doms_split_nth _ _ _ HB) as [Hsp Hf].
    pose proof (decl_typed_doms _ _ _ HD _ _ _ _ _ _ _ _ _ _ Hk0 Hin Heq Hsp) as HB0.
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_nparams Mk) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc in Hn.
    replace (List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_nparams Mk))
      with (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1) + im_nn Mk) in Hn, HSu
      by (rewrite !List.length_app, doms_ctx_length; unfold im_nn; lia).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j Hj].
    rewrite Hf, doms_ctx_app; cbn [doms_ctx List.map List.rev List.app].
    econstructor; exact Hj.
Qed.

(** The domains of a recursive argument's shape before the [k]-th: a
    well-formed context over the arguments before it, which [wk_pat] sends
    to the one over the non-recursive arguments before it. *)
Lemma shape_prefix_wf : forall Θ Ξ p D k0 Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k0 = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> forall k, k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk /\
      ⊢ Θ ⍮ Ξ ⍮ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mk /\
      Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
        ⊢ʷ wk_pat (List.repeat false k ++ cargs_pat gs1) : doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mk.
Proof.
  intros * Hg HDs Hl Hk0 Hin gs1 t gs2 Heq; pose proof (HDs _ _ Hl) as HD; induction k as [| k IH]; intros Hk.
  - cbn [List.firstn sh_ctx doms_ctx List.map List.rev List.app List.repeat].
    exact (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk0 Hin gs1 _ Heq).
  - destruct (IH ltac:(lia)) as (HΨ & HSt & Hφ).
    destruct (List.nth_error (ptyp_doms t) k) as [B |] eqn:HB; [| apply List.nth_error_None in HB; lia ].
    destruct (doms_split_nth _ _ _ HB) as [Hsp Hf].
    pose proof (decl_typed_doms _ _ _ HD _ _ _ _ _ _ _ _ _ _ Hk0 Hin Heq Hsp) as HB0.
    assert (Lk : List.length (List.firstn k (ptyp_doms t)) = k) by (rewrite List.length_firstn; lia).
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_nparams Mk) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc in Hn.
    replace (List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ im_nparams Mk))
      with (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1) + im_nn Mk) in Hn, HSu
      by (rewrite !List.length_app, doms_ctx_length; unfold im_nn; lia).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j Hj].
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj Hφ) as Hj'; cbn in Hj'.
    rewrite Hf, sh_ctx_snoc, doms_ctx_app, Lk; cbn [doms_ctx List.map List.rev List.app].
    split; [ econstructor; exact Hj' | split; [ econstructor; exact Hj |] ].
    cbn [List.repeat List.app wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj | exact Hj' ].
Qed.

(** The rest of a recursive argument's type after [k] domains of its shape
    is a type, under those domains. *)
Lemma shape_rest_wf : forall Θ Ξ p D k0 Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k0 = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
                ▹ ptyp_ty p D (im_nn Mk) (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t).
Proof.
  intros * Hg HDs Hl Hk0 Hin gs1 t gs2 k Heq Hk; pose proof (HDs _ _ Hl) as HD.
  destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk0 Hin _ _ _ Heq k Hk) as (HΨ & HSt & Hφ).
  destruct (decl_typed_plen _ _ _ HD _ _ _ _ Hk0 Hin _ _ _ Heq) as (Mj & Hj & HPl).
  assert (Lk : List.length (List.firstn k (ptyp_doms t)) = k) by (rewrite List.length_firstn; lia).
  assert (Ht : ptyp_doms t = List.firstn k (ptyp_doms t) ++ ptyp_doms (ptyp_skip k t))
    by (rewrite ptyp_doms_skip, List.firstn_skipn; reflexivity).
  destruct (rec_shape_typed _ _ p D k0 Mk Mj (ptyp_skip k t) (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D Mk gs1)
              (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1) (List.repeat false k ++ cargs_pat gs1) Hg HDs Hl Hk0)
    as [j Hj'].
  - rewrite ptyp_mem_skip; exact Hj.
  - rewrite <- List.app_assoc; exact HΨ.
  - rewrite !List.length_app, List.repeat_length, length_sh_ctx, length_cargs_pat, length_cargs_ctx; lia.
  - rewrite pat_nargs_falses, pat_nargs_cargs_pat, List.length_app, doms_ctx_length; lia.
  - rewrite <- !List.app_assoc; exact Hφ.
  - rewrite ptyp_ps_skip; exact HPl.
  - intros Bs1 B Bs2 HBs.
    pose proof (decl_typed_doms _ _ _ HD _ _ _ _ _ _ _ (List.firstn k (ptyp_doms t) ++ Bs1) B Bs2 Hk0 Hin Heq
                  ltac:(rewrite Ht at 1; rewrite HBs, <- List.app_assoc; reflexivity)) as H.
    rewrite doms_ctx_app, <- List.app_assoc in H.
    rewrite <- List.app_assoc, !List.length_app, doms_ctx_length.
    replace (List.length Bs1 + (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1)) + im_nn Mk)
      with (List.length (List.firstn k (ptyp_doms t) ++ Bs1) + List.length (cargs_strat gs1) + im_nn Mk)
      by (rewrite List.length_app; lia).
    exact H.
  - intros m P T HPm HT.
    rewrite ptyp_ps_skip in HPm, HT.
    assert (Hd : ptyp_depth (ptyp_skip k t) + List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1)
                 = ptyp_depth t + List.length (cargs_strat gs1))
      by (unfold ptyp_depth; rewrite ptyp_doms_skip, List.length_app, doms_ctx_length, List.length_skipn; lia).
    rewrite Hd in HT.
    pose proof (decl_typed_rec_ps _ _ _ HD _ _ _ _ _ _ _ _ m P T Hk0 Hin Heq Hj HPm HT) as H.
    unfold ptyp_tele in H |- *; rewrite Ht, doms_ctx_app, <- List.app_assoc in H.
    rewrite <- List.app_assoc; exact H.
  - rewrite <- List.app_assoc in Hj'; econstructor; exact Hj'.
Qed.

Corollary shape_rest_wf' : forall Θ Ξ p D k0 Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k0 = Some Mk -> ind_con Mk c = Some gs ->
    forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
                ▹ ptyp_ty p D (im_nn Mk) (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t).
Proof.
  intros * Hg HDs Hl Hk0 Hcon; eapply shape_rest_wf; [ exact Hg | exact HDs | exact Hl | exact Hk0 | exact (cons_lookup_in _ _ _ Hcon) ].
Qed.

Lemma length_ind_uvars : forall D nn k, List.length (ind_uvars D nn k) = ind_nu D.
Proof. intros; unfold ind_uvars; apply length_vars_from. Qed.

(** Under [Φ], the parameters of a member as variables: the uniform ones
    at the instances of their telescope, and the non-uniform ones at those
    of theirs at the uniform ones. *)
Lemma wf_vars_params : forall Θ Ξ D k Mk Φ,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Φ ++ im_params D Mk ->
    (forall i U T, nth_error (ind_uvars D (im_nn Mk) (List.length Φ)) i = Some U ->
       nth_error (tele_insts (ind_uparams D) Id (ind_uvars D (im_nn Mk) (List.length Φ))) i = Some T ->
       Θ ⍮ Ξ ⍮ Φ ++ im_params D Mk ⊢ U : T) /\
    (forall i N T, nth_error (vars_from (List.length Φ) (im_nn Mk)) i = Some N ->
       nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (ind_uvars D (im_nn Mk) (List.length Φ)))
                    (vars_from (List.length Φ) (im_nn Mk))) i = Some T ->
       Θ ⍮ Ξ ⍮ Φ ++ im_params D Mk ⊢ N : T).
Proof.
  intros * HD Hc Hk HΨ.
  pose proof (decl_typed_mvc _ _ _ HD) as Hmv.
  assert (Hmvp : ctx_mvc (im_params D Mk))
    by (unfold ctx_mvc, im_params; apply List.Forall_app; split; [ exact (proj1 (decl_mvc_members _ Hmv _ _ Hk)) | exact (decl_mvc_uparams _ Hmv) ]).
  pose proof (wf_vars_tele _ _ _ _ (decl_closed_params_ass _ _ _ Hc Hk) (decl_closed_params _ _ _ Hc Hk) Hmvp HΨ) as Hv.
  assert (Hsp : vars_from (List.length Φ) (List.length (im_params D Mk))
                = ind_uvars D (im_nn Mk) (List.length Φ) ++ vars_from (List.length Φ) (im_nn Mk))
    by (unfold ind_uvars; rewrite length_im_params, vars_from_app; unfold im_np; f_equal; lia).
  rewrite Hsp in Hv; unfold im_params at 2 in Hv.
  setoid_rewrite tele_insts_app in Hv; [| exact (decl_typed_ass _ _ _ HD) | rewrite length_ind_uvars; reflexivity ].
  assert (Hl1 : List.length (tele_insts (ind_uparams D) Id (ind_uvars D (im_nn Mk) (List.length Φ))) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_typed_ass _ _ _ HD); rewrite length_ind_uvars; unfold ind_nu; lia).
  split.
  - intros i U T HU HT; apply (Hv i).
    + rewrite List.nth_error_app1; [ exact HU | apply List.nth_error_Some; rewrite HU; discriminate ].
    + rewrite List.nth_error_app1; [ exact HT | apply List.nth_error_Some; rewrite HT; discriminate ].
  - intros i N T HN HT; apply (Hv (ind_nu D + i)).
    + rewrite List.nth_error_app2 by (rewrite length_ind_uvars; lia); rewrite length_ind_uvars.
      replace (ind_nu D + i - ind_nu D) with i by lia; exact HN.
    + rewrite List.nth_error_app2 by lia; rewrite Hl1; replace (ind_nu D + i - ind_nu D) with i by lia; exact HT.
Qed.

(** The type of a constructor's result is a type. *)
Lemma con_cod_typed : forall Θ Ξ p D k Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    exists j, Θ ⍮ Ξ ⍮ cargs_ctx p D Mk gs ++ im_params D Mk
      ⊢ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) : Typeω@j.
Proof.
  intros * Hg HDs Hl Hk Hcon.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ & _ & _).
  destruct (wf_vars_params _ _ _ _ _ _ HD Hc Hk HΨ) as [HU HN]; rewrite length_cargs_ctx in HU, HN.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D)
    by (rewrite <- List.app_assoc; exact HΨ).
  assert (HlE : List.length (cargs_ctx p D Mk gs ++ im_nparams Mk) = List.length gs + im_nn Mk)
    by (rewrite List.length_app, length_cargs_ctx; reflexivity).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, HlE in Hn; rewrite HlE in HSu.
  eapply sort_large; [ exact HSu | exact Hn |].
  rewrite <- (sort_at_vars D _ Hc (decl_typed_mvc _ _ _ HD)); fold (ind_uvars D (im_nn Mk) (List.length gs)).
  eapply ind_mty_typed; [ exact Hg | exact HDs | exact Hl | exact Hk | exact HΨ | apply length_ind_uvars | exact HU
                        | apply length_vars_from | exact HN ].
Qed.

Lemma con_ty_typed0 : forall Θ Ξ p D k Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D k Mk gs : Typeω@j.
Proof.
  intros * Hg HDs Hl Hk Hcon.
  destruct (con_cod_typed _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j Hj].
  destruct (ctx_pi_wf0 _ _ _ _ _ Hj) as [j' Hj']; exists j'.
  unfold con_ty; rewrite <- ctx_pi_app; exact Hj'.
Qed.

Lemma con_ty_typed : forall Θ Ξ Γ p D k Mk c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ Γ -> exists j, Θ ⍮ Ξ ⍮ Γ ⊢ con_ty p D k Mk gs : Typeω@j.
Proof.
  intros * Hg HDs Hl Hk Hcon HΓ; destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j Hj]; exists j.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  eapply closed_weaken_exp; [ exact HΓ | exact Hj | eapply decl_closed_con_ty; [ exact Hc | exact Hk | apply cons_lookup_in; exact Hcon ] | exact I ].
Qed.

(** The motive's instance at the non-uniform parameters and the scrutinee
    is a substitution into the motive's context. *)
Lemma wf_elim_inst_sub : forall Θ Ξ Γ p D m Mm Ps M,
    decl_closed D -> ind_member D m = Some Mm -> List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) : elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hc Hm HPl HPs HM HΨ.
  pose proof (decl_closed_ass _ Hc) as Hass.
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (Hrass : tele_ass (tele_sub (im_nparams Mm) (sb_of_list Id (List.firstn (ind_nu D) Ps))))
    by (apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption).
  apply wf_sub_of_list_id; [| exact HΨ | rewrite length_elim_mctx, List.length_app, HNl; cbn; lia |].
  - unfold elim_mctx; constructor; [ eauto | exact Hrass ].
  - intros k N T HN HT.
    unfold elim_mctx in HT.
    change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub; exact HNl).
    assert (Hl2 : List.length (tele_insts (tele_sub (im_nparams Mm) (sb_of_list Id (List.firstn (ind_nu D) Ps))) Id
                                (List.skipn (ind_nu D) Ps)) = im_nn Mm)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, HNl; unfold im_nn; lia).
    destruct (Nat.lt_ge_cases k (im_nn Mm)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (List.firstn (ind_nu D) Ps))) in HT
        by apply sb_compose_id_right.
      apply (HPs (ind_nu D + k)).
      * rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN.
      * rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; rewrite tele_insts_app;
          [| exact Hass | rewrite HUl; reflexivity ].
        rewrite List.nth_error_app2 by (rewrite length_tele_insts by exact Hass; rewrite HUl; unfold ind_nu; lia).
        rewrite length_tele_insts by exact Hass; rewrite HUl.
        unfold ind_nu at 2; rewrite Nat.min_id; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
    + rewrite List.nth_error_app2 in HN, HT by lia; rewrite HNl in HN; rewrite Hl2 in HT.
      destruct (k - im_nn Mm) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite ind_mty_sub by (try exact Hc; rewrite List.length_map; exact HUl).
      rewrite List.map_map, <- HNl, map_shift_sb_of_list, vars_from_sb_of_list.
      rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id; exact HM.
Qed.

(** ** The View Equations of a Filed Group

    The rest of what [views_self_typed] gives, sent by [grp_sb] to the
    uniform parameters (see [decl_typed_view_is]). *)

Lemma tele_insts_closed_sub : forall Δ Ms τ j T,
    tele_ass Δ -> ctx_scoped 0 Δ -> nth_error (tele_insts Δ Id Ms) j = Some T ->
    nth_error (tele_insts Δ Id (List.map (fun M => M[τ]) Ms)) j = Some T[τ].
Proof.
  intros * Hass Hs HT.
  rewrite <- (tele_insts_sub Δ 0 Id Id τ Ms Hass Hs ltac:(intros; lia)), List.nth_error_map, HT; reflexivity.
Qed.

Lemma length_scargs_ctx_aux : forall D IsS nn pat gs, List.length (scargs_ctx_aux D IsS nn pat gs) = List.length gs.
Proof. intros D IsS nn pat gs; revert pat; induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_scargs_ctx : forall D IsS M gs, List.length (scargs_ctx D IsS M gs) = List.length gs.
Proof. intros; apply length_scargs_ctx_aux. Qed.

Lemma scargs_ctx_aux_ass : forall D IsS nn pat gs, tele_ass (scargs_ctx_aux D IsS nn pat gs).
Proof.
  intros D IsS nn pat gs; revert pat; induction gs as [| [] gs IH]; intros; cbn; [ constructor | |];
    apply List.Forall_app; split; [ apply IH | | apply IH |]; repeat constructor; eexists; reflexivity.
Qed.

Lemma sh_ctx_ass : forall Bs pat, tele_ass (sh_ctx pat Bs).
Proof.
  induction Bs as [| B Bs IH]; intros; cbn; [ constructor |].
  apply List.Forall_app; split; [ apply IH | repeat constructor; eexists; reflexivity ].
Qed.

Lemma ptyp_scoped_dom : forall t n d, ptyp_scoped n t -> exp_scoped (d + n) (List.nth d (ptyp_doms t) a_True).
Proof.
  induction t as [j Ps | B t IH]; intros * Ht; cbn in Ht |- *; [ destruct d; exact I |].
  destruct Ht as [HB Ht]; destruct d as [| d]; [ exact HB |].
  replace (S d + n) with (d + S n) by lia; apply IH; exact Ht.
Qed.

Lemma ptyp_scoped_ps : forall t n, ptyp_scoped n t -> List.Forall (exp_scoped (ptyp_depth t + n)) (ptyp_ps t).
Proof.
  induction t as [j Ps | B t IH]; intros * Ht; cbn in Ht.
  - exact Ht.
  - destruct Ht as [_ Ht]; specialize (IH _ Ht); unfold ptyp_depth in *; cbn [ptyp_doms ptyp_ps List.length].
    replace (S (List.length (ptyp_doms t)) + n) with (List.length (ptyp_doms t) + S n) by lia; exact IH.
Qed.

(** A domain of a recursive argument's shape, and the non-uniform
    parameters it ends at, in the context of the arguments before it. *)
Lemma ptyp_dom_at_scoped : forall D k Mi c gs gs1 t gs2 d,
    decl_closed D -> ind_member D k = Some Mi -> In (c, gs) (im_cons Mi) -> gs = gs1 ++ ca_rec t :: gs2 ->
    exp_scoped (d + List.length gs1 + im_np D Mi) (ptyp_dom_at (cargs_pat gs1) d t).
Proof.
  intros * Hc Hk Hin Hgs; unfold ptyp_dom_at.
  pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ Hk) _ _ _ _ _ Hin Hgs) as Ht.
  eapply exp_scoped_wk; [ exact (ptyp_scoped_dom _ _ d Ht) |]; intros x Hx.
  replace (d + List.length gs1 + im_np D Mi) with (List.length (List.repeat false d ++ cargs_pat gs1) + im_np D Mi)
    by (rewrite length_app, List.repeat_length, length_cargs_pat; lia).
  apply wk_pat_bound; rewrite pat_nargs_falses, pat_nargs_cargs_pat; lia.
Qed.

Lemma ptyp_ps_at_scoped : forall D k Mi c gs gs1 t gs2,
    decl_closed D -> ind_member D k = Some Mi -> In (c, gs) (im_cons Mi) -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.Forall (exp_scoped (ptyp_depth t + List.length gs1 + im_np D Mi)) (ptyp_ps_at (cargs_pat gs1) t).
Proof.
  intros * Hc Hk Hin Hgs; unfold ptyp_ps_at.
  pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ Hk) _ _ _ _ _ Hin Hgs) as Ht.
  apply List.Forall_map; eapply List.Forall_impl; [| exact (ptyp_scoped_ps _ _ Ht) ]; intros P HP.
  eapply exp_scoped_wk; [ exact HP |]; intros x Hx.
  replace (ptyp_depth t + List.length gs1 + im_np D Mi)
    with (List.length (List.repeat false (ptyp_depth t) ++ cargs_pat gs1) + im_np D Mi)
    by (rewrite length_app, List.repeat_length, length_cargs_pat; lia).
  apply wk_pat_bound; rewrite pat_nargs_falses, pat_nargs_cargs_pat; lia.
Qed.

(** Arguments recursive in both a container's constructor and its view's
    are through as many domains. *)
Lemma cargs_corr_rec_depth : forall vm gs1' t' gs2' gs1 t gs2,
    cargs_corr vm (gs1' ++ ca_rec t' :: gs2') (gs1 ++ ca_rec t :: gs2) -> List.length gs1' = List.length gs1 ->
    ptyp_depth t' = ptyp_depth t.
Proof.
  intros vm gs1'; induction gs1' as [| g' gs1' IH]; intros * Hc Hl; destruct gs1 as [| g gs1]; cbn in Hl; try lia.
  - cbn in Hc; tauto.
  - cbn [List.app] in Hc; destruct g', g; cbn in Hc; try contradiction; try (destruct Hc as (_ & _ & Hc));
      exact (IH _ _ _ _ _ Hc ltac:(lia)).
Qed.

(** What a view and its container's member share: the non-uniform
    parameters' number, the view's arguments' number, and the container's
    closedness. *)
Lemma view_shared : forall Θ Ξ p D IsS, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D -> grp_link p D IsS ->
    forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv ->
      decl_closed D' /\ List.length (IsS k) = ind_nu D' /\ im_nn Mv = im_nn Mi'.
Proof.
  intros * Hg HD Hl Hlk * Hk Hh Hl' Hi' Hv HMv.
  split; [ exact (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') |].
  destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
  rewrite Hl' in Hl2; injection Hl2 as <-.
  split; [ rewrite (Hlk _ _ _ _ _ _ Hk Hh), List.length_map in HIl; exact HIl |].
  destruct (decl_typed_vwrap _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D2 & Hl2 & Hw).
  rewrite Hl' in Hl2; injection Hl2 as <-.
  destruct (vwrap_ok_members _ _ _ Hw _ _ _ Hi' Hv) as (Mv' & HMv' & Hnn & _).
  rewrite HMv in HMv'; injection HMv' as <-; exact Hnn.
Qed.

(** The members as variables under the view equations' binders, sent to
    the uniform parameters. *)
Lemma grp_sb_nparams : forall p D (Mv : imember), tele_sub (tele_wk (im_nparams Mv) (self_wk D 0)) (grp_sb p D) = im_nparams Mv.
Proof. intros; exact (tele_self_wk_grp_sb p D 0 (im_nparams Mv)). Qed.

Lemma decl_typed_view_view_is : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
      ind_lookup Θ Ξ q'' = Some D'' ->
      nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
      nth_error X j' = Some C ->
      nth_error (List.map (fun I => I[sb_of_list Id Is]) Is'') j' = Some C' ->
      nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
      Θ ⍮ Ξ ⍮ ind_uparams D ⊢ C ≈ C' : T[sb_of_list Id Is].
Proof.
  intros * Hg HD Hl * Hk Hh Hl' Hi' Hh' Hl'' Hv HMv HhMv HC HC' HT; views_filed Hg HD Hl.
  destruct (view_shared _ _ _ _ _ Hg HD Hl Hlk _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv) as (Hc' & HIl & _).
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl'') as Hc''.
  pose proof (decl_closed_head_scoped _ Hc' _ _ _ _ _ _ Hi' Hh') as HsIs''.
  rewrite (Hlk _ _ _ _ _ _ HMv HhMv) in HC; apply nth_error_map_inv in HC as (C0 & HC0 & ->).
  apply nth_error_map_inv in HC' as (I'' & HI'' & ->).
  assert (HC0' : nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some I''[sb_of_list Id (IsS k)])
    by (rewrite List.nth_error_map, HI''; reflexivity).
  pose proof (views_self_typed_view_is _ _ _ _ Hs k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' _ _ T
                Hk Hh Hl' Hi' Hh' Hl'' Hv HMv HhMv HC0 HC0' HT) as H.
  pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H (grp_sb_typed _ _ _ _ HD Hc Hl (presup_exp_eq_ctx H))) as H'.
  assert (HsI : exp_scoped (List.length (IsS k)) I'')
    by (rewrite HIl; rewrite List.Forall_forall in HsIs''; exact (HsIs'' _ (List.nth_error_In _ _ HI''))).
  rewrite (exp_list_grp_sb0 _ _ I'') in H' by exact HsI.
  assert (HTT : T[sb_of_list Id (IsS k)][grp_sb p D] = T[sb_of_list Id (List.map (fun I => I[grp_sb p D]) (IsS k))]).
  { pose proof (tele_insts_closed_sub _ _ (sb_of_list Id (IsS k)) _ _ (decl_closed_ass _ Hc'') (decl_closed_uparams _ Hc'') HT) as H1.
    pose proof (tele_insts_closed_sub _ _ (grp_sb p D) _ _ (decl_closed_ass _ Hc'') (decl_closed_uparams _ Hc'') H1) as H2.
    pose proof (tele_insts_closed_sub _ _ (sb_of_list Id (List.map (fun I => I[grp_sb p D]) (IsS k))) _ _
                  (decl_closed_ass _ Hc'') (decl_closed_uparams _ Hc'') HT) as H3.
    rewrite List.map_map in H2.
    rewrite (List.map_ext_in _ (fun I => I[sb_of_list Id (List.map (fun I => I[grp_sb p D]) (IsS k))])) in H2.
    - rewrite H2 in H3; injection H3 as E; exact E.
    - intros I HI; apply exp_list_grp_sb0; rewrite HIl.
      rewrite List.Forall_forall in HsIs''; exact (HsIs'' _ HI). }
  rewrite HTT, <- (Hlk _ _ _ _ _ _ Hk Hh) in H'; exact H'.
Qed.

(** The arguments of a view's constructor are its container's at the
    view's instance. *)
Lemma decl_typed_view_args : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      Θ ⍮ Ξ ⍮ im_params D Mv
        ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is)) ≈ cargs_ctx p D Mv gs.
Proof.
  intros * Hg HD Hl * Hk Hh Hl' Hi' Hv HMv Hc1 Hc2; views_filed Hg HD Hl.
  destruct (view_shared _ _ _ _ _ Hg HD Hl Hlk _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv) as (Hc' & HIl & Hnn).
  pose proof (views_self_typed_args _ _ _ _ Hs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv Hc1 Hc2) as H.
  assert (Hass : tele_ass (tele_wk (im_nparams Mv) (self_wk D 0)))
    by exact (tele_ass_wk _ _ (decl_typed_nparams_ass _ _ _ HD _ _ HMv)).
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ H (grp_sb_ext _ _ _ _ _ HD Hc Hl Hass (presup_ext_eq_ctx H))) as H'.
  rewrite length_tele_wk, grp_sb_nparams in H'; fold (im_nn Mv) in H'.
  rewrite tele_list_grp_sb, scargs_ctx_grp_sb in H' by
    (try exact Hc; try exact (decl_typed_mvc _ _ _ HD); try exact (decl_typed_order _ _ _ HD); try exact Hlk;
     rewrite Hnn, HIl; exact (decl_closed_cargs_scoped _ Hc' _ _ _ _ _ Hi' (cons_lookup_in _ _ _ Hc1))).
  rewrite <- (Hlk _ _ _ _ _ _ Hk Hh) in H'; exact H'.
Qed.

(** Each domain of a recursive argument's shape, and each non-uniform
    parameter it ends at, is its container's at the view's instance. *)
Lemma decl_typed_view_doms : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      d < ptyp_depth t ->
      exists i, Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
        ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id Is)]
        ≈ ptyp_dom_at (cargs_pat gs1) d t : Typeω@i.
Proof.
  intros * Hg HD Hl * Hk Hh Hl' Hi' Hv HMv Hc1 Hc2 Hgs' Hgs Hlen Hd; views_filed Hg HD Hl.
  destruct (view_shared _ _ _ _ _ Hg HD Hl Hlk _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv) as (Hc' & HIl & Hnn).
  destruct (views_self_typed_doms _ _ _ _ Hs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv Hc1 Hc2 Hgs' Hgs Hlen Hd)
    as [i H]; exists i.
  assert (Hassoc : forall A B C G : ctx, A ++ B ++ C ++ G = (A ++ B ++ C) ++ G)
    by (intros; rewrite <- !List.app_assoc; reflexivity).
  rewrite Hassoc in H.
  set (Ψ := tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
              ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0)) in *.
  assert (HΨl : List.length Ψ = d + List.length gs1 + im_nn Mv).
  { subst Ψ; rewrite !length_app, !length_tele_wk, length_sh_ctx, length_scargs_ctx, List.length_firstn.
    unfold ptyp_depth in Hd; unfold im_nn; lia. }
  assert (Hass : tele_ass Ψ).
  { subst Ψ; apply List.Forall_app; split; [ apply tele_ass_wk, sh_ctx_ass |].
    apply List.Forall_app; split; [ apply scargs_ctx_aux_ass | exact (tele_ass_wk _ _ (decl_typed_nparams_ass _ _ _ HD _ _ HMv)) ]. }
  pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H
                (grp_sb_ext _ _ _ _ _ HD Hc Hl Hass (presup_exp_eq_ctx H))) as H'.
  rewrite HΨl in H'; cbn [exp_sub] in H'.
  rewrite exp_self_wk_grp_sb in H'.
  rewrite exp_list_grp_sb in H'.
  - rewrite <- (Hlk _ _ _ _ _ _ Hk Hh) in H'.
    replace (tele_sub Ψ (grp_sb p D) ++ ind_uparams D)
      with (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv) in H'; [ exact H' |].
    subst Ψ; rewrite !tele_sub_app, !length_app, !length_tele_wk, length_scargs_ctx.
    fold (im_nn Mv); rewrite (tele_self_wk_grp_sb p D (List.length gs1 + im_nn Mv)).
    rewrite scargs_ctx_grp_sb, grp_sb_nparams by (first [ exact Hc | exact (decl_typed_mvc _ _ _ HD) | exact (decl_typed_order _ _ _ HD) | exact Hlk ]).
    unfold im_params; rewrite !List.app_assoc; reflexivity.
  - rewrite HIl, Hnn, <- Hlen.
    replace (d + List.length gs1' + im_nn Mi' + ind_nu D') with (d + List.length gs1' + im_np D' Mi') by (unfold im_np; lia).
    exact (ptyp_dom_at_scoped _ _ _ _ _ _ _ _ d Hc' Hi' (cons_lookup_in _ _ _ Hc1) Hgs').
Qed.

Lemma decl_typed_view_ps : forall Θ Ξ p D, ⊢ᵍ Θ ⍮ Ξ -> decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D ->
    forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      ind_member D (ptyp_mem t) = Some Mj ->
      nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
      nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                   (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
      Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
        ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id Is)] : T /\
      Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
        ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id Is)] ≈ P : T.
Proof.
  intros * Hg HD Hl * Hk Hh Hl' Hi' Hv HMv Hc1 Hc2 Hgs' Hgs Hlen HMj HP' HP HT; views_filed Hg HD Hl.
  destruct (view_shared _ _ _ _ _ Hg HD Hl Hlk _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hl' Hi' Hv HMv) as (Hc' & HIl & Hnn).
  destruct (views_self_typed_ps _ _ _ _ Hs k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T
              Hk Hh Hl' Hi' Hv HMv Hc1 Hc2 Hgs' Hgs Hlen HMj HP' HP HT) as [H1 H2].
  assert (Hassoc : forall A B C G : ctx, A ++ B ++ C ++ G = (A ++ B ++ C) ++ G)
    by (intros; rewrite <- !List.app_assoc; reflexivity).
  rewrite Hassoc in H1, H2.
  set (Ψ := tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
              ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0)) in *.
  assert (HΨl : List.length Ψ = ptyp_depth t + List.length gs1 + im_nn Mv).
  { subst Ψ; rewrite !length_app, !length_tele_wk, length_sh_ctx, length_scargs_ctx.
    unfold ptyp_depth, im_nn; lia. }
  assert (Hass : tele_ass Ψ).
  { subst Ψ; apply List.Forall_app; split; [ apply tele_ass_wk, sh_ctx_ass |].
    apply List.Forall_app; split; [ apply scargs_ctx_aux_ass | exact (tele_ass_wk _ _ (decl_typed_nparams_ass _ _ _ HD _ _ HMv)) ]. }
  pose proof (grp_sb_ext _ _ _ _ _ HD Hc Hl Hass (presup_exp_ctx H1)) as Hσ.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ H1 Hσ) as H1'.
  pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H2 Hσ) as H2'.
  rewrite HΨl in H1', H2'; rewrite exp_self_wk_grp_sb in H1'; rewrite !exp_self_wk_grp_sb in H2'.
  assert (HsP' : exp_scoped (ptyp_depth t + List.length gs1 + im_nn Mv + List.length (IsS k)) P').
  { rewrite HIl, Hnn, <- Hlen.
    pose proof (ptyp_ps_at_scoped _ _ _ _ _ _ _ _ Hc' Hi' (cons_lookup_in _ _ _ Hc1) Hgs') as HPs.
    rewrite List.Forall_forall in HPs; pose proof (HPs _ (List.nth_error_In _ _ HP')) as HsP.
    destruct (decl_typed_vwrap _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D2 & Hl2 & Hw).
    rewrite Hl' in Hl2; injection Hl2 as <-.
    destruct (vwrap_ok_members _ _ _ Hw _ _ _ Hi' Hv) as (Mv' & HMv' & _ & _ & Hcorr).
    rewrite HMv in HMv'; injection HMv' as <-.
    pose proof (Hcorr _ _ _ (cons_lookup_in _ _ _ Hc1) Hc2) as Hco; rewrite Hgs', Hgs in Hco.
    rewrite <- (cargs_corr_rec_depth _ _ _ _ _ _ _ Hco Hlen).
    replace (ptyp_depth t' + List.length gs1' + im_nn Mi' + ind_nu D') with (ptyp_depth t' + List.length gs1' + im_np D' Mi')
      by (unfold im_np; lia); exact HsP. }
  rewrite exp_list_grp_sb in H1', H2' by exact HsP'.
  rewrite <- (Hlk _ _ _ _ _ _ Hk Hh) in H1', H2'.
  replace (tele_sub Ψ (grp_sb p D) ++ ind_uparams D)
    with (sh_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv) in H1', H2';
    [ split; assumption |].
  subst Ψ; rewrite !tele_sub_app, !length_app, !length_tele_wk, length_scargs_ctx.
  fold (im_nn Mv); rewrite (tele_self_wk_grp_sb p D (List.length gs1 + im_nn Mv)).
  rewrite scargs_ctx_grp_sb, grp_sb_nparams by (first [ exact Hc | exact (decl_typed_mvc _ _ _ HD) | exact (decl_typed_order _ _ _ HD) | exact Hlk ]).
  unfold im_params; rewrite !List.app_assoc; reflexivity.
Qed.

(** A typed record declaration: what [wf_gentry_record] checks of it. *)
Record record_typed (Θ : gdeps) (Ξ : gstack) (R : record_decl) : Prop := mk_record_typed
  { (** The parameters are assumptions *)
    typed_params_ass : tele_ass (record_params R)
    (** No type of the declaration has a free module variable *)
  ; typed_mvc : record_mvc R
    (** The sort is a universe over the parameters *)
  ; typed_sort : Θ ⍮ Ξ ⍮ record_params R ⊢ᵤ record_sort R
    (** The field names are distinct *)
  ; typed_nodup : List.NoDup (List.map fst (record_fields R))
    (** Each field is a type in the sort, over the fields before it and
        the parameters *)
  ; typed_fields : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : (record_sort R)[wk_shiftn k]ʷ }.

(** A typed record stays typed along an embedding. *)
Lemma record_typed_emb : forall Θ Ξ Θ2 Ξ2 R, Emb Θ Ξ Θ2 Ξ2 -> record_typed Θ Ξ R -> record_typed Θ2 Ξ2 R.
Proof.
  intros * He [Ha Hmv Hs Hnd Hf].
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _ & _ & _ & _ & _).
  constructor; [ exact Ha | exact Hmv | | exact Hnd | intros; apply Ht; eapply Hf; eassumption ].
  (* the sort: a universe moves along the embedding *)
  inversion Hs; subst; [ constructor; apply Hc; assumption | econstructor; apply Ht; eassumption ].
Qed.

(** A universe is large, or small at a level. *)
Lemma is_univ_cases : forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
    (exists i, U = Typeω@i) \/ (exists L n, U = Type⟨L⟩ /\ Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n).
Proof. intros * H; inversion H; subst; eauto 6. Qed.

(** The sort of a typed record is a universe. *)
Lemma record_typed_sort_univ : forall Θ Ξ R, record_typed Θ Ξ R -> ind_sort_univ (record_sort R).
Proof.
  intros * Ht; destruct (is_univ_cases _ _ _ _ (typed_sort _ _ _ Ht)) as [(i & ->) | (L & n & -> & _)];
    [ left | right ]; eauto.
Qed.

(** The context of a typed record's first [k] fields over its parameters
    is well formed: each field is a type of the sort, a universe. *)
Lemma record_typed_fctx_wf : forall Θ Ξ R, record_typed Θ Ξ R ->
    forall k, k <= List.length (record_fields R) -> ⊢ Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R.
Proof.
  intros * [Ha Hmv Hs Hnd Hf]; pose proof (presup_is_univ_ctx Hs) as HP.
  induction k as [| k IH]; intros Hk; [ exact HP |].
  assert (Hlt : k < List.length (record_fields R)) by lia.
  destruct (List.nth_error (record_fields R) k) as [[f T] |] eqn:HT;
    [| apply List.nth_error_None in HT; lia ].
  rewrite (record_fctx_succ _ _ _ _ HT); cbn [List.app].
  specialize (IH ltac:(lia)).
  pose proof (Hf _ _ _ HT) as HTt.
  pose proof (wf_wk_shiftn_app _ _ _ _ IH HP) as Hw; rewrite length_record_fctx in Hw by lia.
  destruct (is_univ_cases _ _ _ _ Hs) as [(i & HU) | (L & n & HU & HL)]; rewrite HU in HTt; cbn in HTt.
  - eapply wf_ctx_extend; exact HTt.
  - pose proof (wk_preserves_exp _ _ _ _ _ _ _ HL Hw) as HL'; cbn in HL'.
    eapply wf_ctx_extend; exact (@wf_exp_suniv_large _ _ _ _ _ 0 _ HL' HTt).
Qed.

(** The type of a typed record's type former is a type. *)
Lemma record_typed_ty : forall Θ Ξ R, record_typed Θ Ξ R -> exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ record_ty R : Typeω@i.
Proof.
  intros * [Ha Hmv Hs Hnd Hf]; pose proof (presup_is_univ_ctx Hs) as HP.
  destruct (wf_is_univ_typ Hs) as [i Hi].
  unfold record_ty; apply (ctx_pi_wf _ _ _ nil _ i); rewrite List.app_nil_r; assumption.
Qed.

(** The type former of a typed record found at [p] is typed. *)
Lemma record_typed_former : forall Θ Ξ Γ p R, record_typed Θ Ξ R -> record_lookup Θ Ξ p = Some R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R.
Proof.
  intros * HR Hl HΓ; pose proof HR as [Ha Hmv Hs Hnd Hf].
  destruct (record_typed_ty _ _ _ HR) as [i Hi].
  eapply wf_record; [ exact HΓ | exact Hl | exact Hnd | exact Ha | exact Hi
                    | exact (record_typed_fctx_wf _ _ _ HR _ (le_n _)) | exact Hs | exact Hf ].
Qed.

(** A record entry, and the module of a record type, have a typed
    declaration: it is checked where the module starts
    ([wf_gmod_record_nil]). *)
Lemma wf_record_typed_all :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> forall pv pr R Φ, E = ge_record pv pr R Φ -> record_typed Θ Ξ R) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> forall R, K = fk_record R -> record_typed Θ Ξ R).
Proof.
  apply global_wf_mut_ind; intros; try discriminate.
  - (* the declaration *)
    match goal with Heq : ge_record _ _ _ _ = ge_record _ _ _ _ |- _ => injection Heq as <- <- <- <- end.
    constructor; assumption.
  - (* with the body of its module *)
    match goal with Heq : ge_record _ _ _ _ = ge_record _ _ _ _ |- _ => injection Heq as <- <- <- <- end.
    match goal with IH : forall R, fk_record _ = fk_record R -> _ |- _ => exact (IH _ eq_refl) end.
  - (* the module, before its members *)
    match goal with Heq : fk_record _ = fk_record _ |- _ => injection Heq as <- end.
    match goal with IH : forall pv pr R Φ, ge_record _ _ _ _ = _ -> _ |- _ => exact (IH _ _ _ _ eq_refl) end.
  - (* one more member of the module *)
    match goal with IH : forall R, ?K = fk_record R -> _, Heq : ?K = fk_record _ |- _ => exact (IH _ Heq) end.
Qed.

Lemma wf_gmod_record_typed : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
    forall R, K = fk_record R -> record_typed Θ Ξ R.
Proof. exact (proj2 wf_record_typed_all). Qed.

(** The type of a value of a typed record found at [p] is a type over the
    record's parameters: its module's telescope is well formed where the
    record is found.  The parameters as variables are of the parameters'
    types, and the sort is the sort at them, as the declaration has no
    free module variable. *)
Lemma record_mod_tele_wf : forall Θ Ξ p R, record_typed Θ Ξ R -> record_lookup Θ Ξ p = Some R ->
    ⊢ Θ ⍮ Ξ ⍮ record_mod_tele p R.
Proof.
  intros * HR Hl; pose proof HR as [Ha Hmv Hs Hnd Hf]; pose proof (presup_is_univ_ctx Hs) as HP.
  destruct (wf_is_univ_typ Hs) as [i Hi].
  pose proof (wf_ctx_scoped _ _ _ HP) as HsP.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ Hi) as (_ & HsS & _).
  assert (Hself : Θ ⍮ Ξ ⍮ record_params R ⊢ record_self p R : record_sort R).
  { pose proof (wf_apps_closed_pi _ _ (record_params R) (record_sort R) i (record_params R) (a_record p)
                  (vars_from 0 (List.length (record_params R))) Ha HsP HsS Hi HP
                  (record_typed_former _ _ _ _ _ HR Hl HP) (length_vars_from _ _)
                  (wf_vars_tele _ _ nil _ Ha HsP (params_mvc _ Hmv) HP)) as H.
    rewrite (exp_at_vars _ _ 0 HsS (sort_mvc _ Hmv)), exp_wk_id_ext in H by (intros x; cbn; lia).
    exact H. }
  unfold record_mod_tele.
  destruct (is_univ_cases _ _ _ _ Hs) as [(j & HU) | (L & n & HU & HL)]; rewrite HU in Hself.
  - eapply wf_ctx_extend; exact Hself.
  - eapply wf_ctx_extend; exact (@wf_exp_suniv_large _ _ _ _ _ 0 _ HL Hself).
Qed.

(** The telescope of the frames' parameters is a well-formed context: the
    innermost frame's module was checked over it, one frame out, and pushing
    the frame is an embedding; a record's module ends with a value of the
    record, typed in the record's own frame, where the record is found. *)
Lemma wf_gs_tele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ.
Proof.
  intros Θ [| [[mp K] U] Ξ] Hg; [ constructor; exact Hg |].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg) as (Hs0 & HU & Hff).
  pose proof (wf_gunit_mod _ _ _ _ _ HU) as HΦ.
  assert (HP : ⊢ Θ ⍮ Ξ ⍮ frame_params K (gu_params U) ++ gs_tele Ξ) by exact (wf_gmod_ctx _ _ _ _ _ _ HΦ).
  assert (He : Emb Θ Ξ Θ ((mp, K, U) :: Ξ)) by (constructor; [ exact Hg | apply gc_sub_push; exact Hff ]).
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & _).
  destruct K as [| pq k D | R]; cbn [frame_params gs_tele] in HP |- *; [ exact (Hc _ HP) | exact (Hc _ HP) |].
  destruct (wf_gmod_record_params _ _ _ _ _ _ HΦ _ eq_refl) as (Δr & HΔ & HPR & _).
  rewrite HΔ; cbn [List.app]; rewrite <- HPR.
  apply (record_mod_tele_wf _ _ mp R).
  - exact (record_typed_emb _ _ _ _ _ He (wf_gmod_record_typed _ _ _ _ _ _ HΦ _ eq_refl)).
  - unfold record_lookup; rewrite gs_find_record_own; reflexivity.
Qed.

(** A module's whole telescope is well formed in its own frame, pushed: the
    parameters checked one frame out ([wf_gmod_ctx]) and, for a record's
    module, the value. *)
Corollary wf_gmod_ctx_pushed : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> frame_fresh Θ Ξ mp ->
    ⊢ Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ ⍮ Δ ++ gs_tele Ξ.
Proof.
  intros * HΦ Hff.
  exact (wf_gs_tele _ _ (wf_gstack_cons _ _ _ _ _ _ (ctx_wf_gctx _ _ _ (wf_gmod_ctx _ _ _ _ _ _ HΦ)) HΦ Hff)).
Qed.

Section Induction.
  (** [V Θ Ξ E]: the (closed) entry [E] is valid at [Θ ⍮ Ξ]; [VD Θ Ξ D]: so
      is the declaration [D] of an inductive type. *)
  Variable V : gdeps -> gstack -> gentry -> Prop.
  Variable VD : gdeps -> gstack -> ind_decl -> Prop.

  (** A definition with a module part is valid as its term part, the
      transparent definition it is. *)
  Definition dm_def (pv : bool) (A M : exp) : gentry := ge_def true pv A (Some M).

  (** [GV Θ1 Ξ1 Θ2 Ξ2]: everything resolving at [Θ1 ⍮ Ξ1] is valid at
      [Θ2 ⍮ Ξ2]. *)
  Record GV (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop := mk_GV
    { (** Every resolving entry *)
      gv_entries : forall p E, gc_resolve Θ1 Ξ1 p = Some E -> V Θ2 Ξ2 E
      (** Every filed group *)
    ; gv_decls : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> VD Θ2 Ξ2 D
      (** Every definition with a module part, as its term part *)
    ; gv_def_mods : forall p pv A M U, gc_entry Θ1 Ξ1 p = Some (ge_def_mod pv A M U) -> V Θ2 Ξ2 (dm_def pv A M) }.

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
  (** What an entry checked over [T] contributes is valid at [Θ2 ⍮ Ξ2]. *)
  Record entry_good (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop := mk_entry_good
    { (** Every entry inside it *)
      entry_good_entries : forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> V Θ2 Ξ2 E0
      (** The group, if it is a group's first member *)
    ; entry_good_module : forall T' pq D, ge_module T E = Some (mr_body T' (Some (pq, 0, D))) -> VD Θ2 Ξ2 D
      (** Every group whose first member is inside it *)
    ; entry_good_submodule : forall x (ip : list String.string) T' pq D,
        ge_submodule T E x ip = Some (mr_body T' (Some (pq, 0, D))) -> VD Θ2 Ξ2 D
      (** Every definition with a module part it is or has inside it *)
    ; entry_good_def_mods : forall (ip : list String.string) pv A M U, ge_subentry E ip = Some (ge_def_mod pv A M U) ->
        V Θ2 Ξ2 (dm_def pv A M) }.

  (** The group an entry declares, if it is a group's first member, is
      valid at [Θ2 ⍮ Ξ2]. *)
  Definition entry_decl (Θ2 : gdeps) (Ξ2 : gstack) (E : gentry) : Prop :=
    forall pv pq D Φ, E = ge_ind pv pq 0 D Φ -> VD Θ2 Ξ2 D.

  (** What an entry declares is valid wherever the context it is checked in
      embeds, and what it contributes is valid where its contributions are
      found too. *)
  Definition GoodE (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 ->
      entry_decl Θ2 Ξ2 E /\ (Ctb Θ2 Ξ2 (gs_tele Ξ) mp E -> entry_good Θ2 Ξ2 (gs_tele Ξ) E).

  (** What a body checked over [T] contributes is valid at [Θ2 ⍮ Ξ2]. *)
  Record body_good (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (Φ : gmod) : Prop := mk_body_good
    { (** Every entry resolving in it *)
      body_good_entries : forall ip E0, gm_resolve Φ ip = Some E0 -> V Θ2 Ξ2 E0
      (** Every group whose first member is in it *)
    ; body_good_submodule : forall x ip T' pq D, gm_submodule T Φ x ip = Some (mr_body T' (Some (pq, 0, D))) -> VD Θ2 Ξ2 D
      (** Every definition with a module part in it *)
    ; body_good_def_mods : forall ip pv A M U, gm_entry Φ ip = Some (ge_def_mod pv A M U) -> V Θ2 Ξ2 (dm_def pv A M) }.

  (** The group a frame's kind names, if the frame is the module of the
      group's first member, is valid at [Θ2 ⍮ Ξ2]. *)
  Definition kind_decl (Θ2 : gdeps) (Ξ2 : gstack) (K : frame_kind) : Prop :=
    forall pq D, K = fk_ind pq 0 D -> VD Θ2 Ξ2 D.

  (** The group a module's kind names is valid wherever the context the
      module is checked in embeds, and what its body contributes is valid
      wherever its frame embeds too. *)
  Definition GoodM (Θ : gdeps) (Ξ : gstack) (mp : qname) (K : frame_kind) (Δ : ctx) (Φ : gmod) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 ->
      kind_decl Θ2 Ξ2 K /\ (Emb Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 -> body_good Θ2 Ξ2 (Δ ++ gs_tele Ξ) Φ).

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
    (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> GoodM Θ Ξ mp K Δ Φ) /\
    (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> Good Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - (* a definition or an axiom *)
      intros Θ2 Ξ2 He; split; [ intros ? ? ? ? Heq; discriminate Heq |]; intros _.
      constructor; [| discriminate | intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? ? Hx; discriminate ].
      intros [| ? ?] E0 HE; cbn in HE; inversion HE; subst.
      match goal with HM : forall M, ?o = Some M -> _ |- _ =>
        destruct o as [M0 |]; cbn; [ specialize (HM M0 eq_refl) | clear HM ] end; eauto.
    - (* a nested module *)
      intros Θ2 Ξ2 He; split; [ intros ? ? ? ? Heq; discriminate Heq |]; intros Hc.
      destruct (H0 _ _ He) as [_ HM].
      destruct (HM (Emb_nested _ _ _ pv fk_module _ _ _ _ He Hc I)) as [HE HU HA].
      constructor; [ exact HE | intros ? ? Hx; discriminate | exact HU |].
      intros [| z ip] ? ? ? ? Hx; [ discriminate | exact (HA _ _ _ _ _ Hx) ].
    - (* an alias: it contributes no entry and no declaration *)
      intros ? ? _; split; [ intros ? ? ? ? Heq; discriminate Heq |]; intros _.
      constructor; [ intros ip ? Hx; cbn in Hx; discriminate | discriminate | intros ? ? ? ? Hx; discriminate
                   | intros [| ? ?] ? ? ? ? Hx; discriminate ].
    - (* a group, at its first member, with no member in its module *)
      intros Θ2 Ξ2 He.
      assert (HD : VD Θ2 Ξ2 D) by (eapply Hind; [ build_decl_typed | eassumption | exact He ]).
      split; [ intros ? ? ? ? Heq; injection Heq as <- _ <- _; exact HD | intros _ ].
      constructor; [ intros [| ? ?] ? Hx; discriminate | | intros ? ? ? ? ? Hx; discriminate
                   | intros [| ? ?] ? ? ? ? Hx; [ discriminate | cbn in Hx; discriminate ] ].
      intros T pq0 D0 [= _ <- <-]; exact HD.
    - (* a later declared member of a group, with no member in its module:
         it declares no group, the group's is filed *)
      intros Θ2 Ξ2 He; split; [ intros ? ? ? ? Heq; injection Heq as _ _ Hk0 _ _; lia | intros _ ].
      constructor; [ intros [| ? ?] ? Hx; discriminate | | intros ? ? ? ? ? Hx; discriminate
                   | intros [| ? ?] ? ? ? ? Hx; [ discriminate | cbn in Hx; discriminate ] ].
      intros T pq0 D0 Hx; cbn [ge_module] in Hx; injection Hx as _ _ Hk0 _; lia.
    - (* a declared member with the body of its module, checked in the
         member's open frame *)
      match goal with IH : GoodM _ _ _ _ _ _ |- _ => rename IH into IHM end.
      intros Θ2 Ξ2 He; destruct (IHM _ _ He) as [HK HB].
      split; [ intros ? ? ? ? Heq; injection Heq as _ <- -> <- _; exact (HK _ _ eq_refl) | intros Hc ].
      destruct (HB (Emb_nested _ _ _ pv (fk_ind pq k D) _ _ _ _ He Hc ltac:(match goal with Hu : ind_uparams D = _ |- _ => exact Hu end))) as [HΦE HΦU HΦA].
      constructor.
      + intros ip E0 HE; exact (HΦE _ _ HE).
      + intros T pq0 D0 Hx; cbn [ge_module] in Hx; injection Hx as _ <- -> <-; exact (HK _ _ eq_refl).
      + intros z ip T pq0 D0 Hx; cbn [ge_submodule] in Hx.
        match goal with Hu : ind_uparams D = _ |- _ => rewrite Hu in Hx end; exact (HΦU _ _ _ _ _ Hx).
      + intros [| z ip] ? ? ? ? Hx; [ discriminate |]; exact (HΦA _ _ _ _ _ Hx).
    - (* a definition with a module part: valid as its term part *)
      intros Θ2 Ξ2 He; split; [ intros ? ? ? ? Heq; discriminate Heq |]; intros _.
      constructor; [ intros [| ? ?] ? Hx; discriminate | intros ? ? ? Hx; cbn in Hx; discriminate
                   | intros ? ? ? ? ? Hx; cbn in Hx; discriminate |].
      intros [| ? ?] ? ? ? ? Hx; [| discriminate ]; cbn in Hx; injection Hx as <- <- <- <-.
      unfold dm_def; eapply Hdef; [ eassumption | | exact He ].
      match goal with H : Good _ _ |- _ => exact H end.
    - (* a record: it contributes no entry and no declaration *)
      intros ? ? _; split; [ intros ? ? ? ? Heq; discriminate Heq |]; intros _; constructor;
        [ intros [| ? ?] ? Hx; cbn in Hx; discriminate | intros ? ? ? Hx; cbn in Hx; discriminate
        | intros ? ? ? ? ? Hx; cbn in Hx; discriminate | intros [| ? ?] ? ? ? ? Hx; cbn in Hx; discriminate ].
    - (* a record with the body of its module, checked in the record's open
         frame: it declares no group *)
      match goal with IH : GoodM _ _ _ _ _ _ |- _ => rename IH into IHM end.
      match goal with Hu : record_params R = _ |- _ => rename Hu into HRu end.
      intros Θ2 Ξ2 He; destruct (IHM _ _ He) as [_ HB].
      split; [ intros ? ? ? ? Heq; discriminate Heq | intros Hc ].
      destruct (HB (Emb_nested _ _ _ pv (fk_record R) _ _ _ _ He Hc (ex_intro _ _ (conj eq_refl HRu)))) as [HΦE HΦU HΦA].
      constructor.
      + intros ip E0 HE; exact (HΦE _ _ HE).
      + intros T pq0 D0 Hx; cbn [ge_module] in Hx; discriminate.
      + intros z ip T pq0 D0 Hx; cbn [ge_submodule] in Hx; unfold record_mod_tele in Hx; rewrite HRu in Hx.
        exact (HΦU _ _ _ _ _ Hx).
      + intros [| z ip] ? ? ? ? Hx; [ cbn in Hx; discriminate |]; exact (HΦA _ _ _ _ _ Hx).
    - (* the empty module *)
      intros ? ? _; split; [ intros ? ? Heq; discriminate Heq | intros _ ].
      constructor; [ intros [| ? ?] ? Hx; discriminate | intros ? ? ? ? ? Hx; discriminate |].
      intros ? ? ? ? ? Hx; cbn in Hx; discriminate.
    - (* the module of a member, before its members: the member's group *)
      match goal with IH : GoodE _ _ _ _ |- _ => rename IH into IHE end.
      intros Θ2 Ξ2 He; split.
      + intros pq0 D0 Heq; injection Heq as -> -> ->.
        exact (proj1 (IHE _ _ He) _ _ _ _ eq_refl).
      + intros _; constructor; [ intros [| ? ?] ? Hx; discriminate | intros ? ? ? ? ? Hx; discriminate |].
        intros ? ? ? ? ? Hx; cbn in Hx; discriminate.
    - (* the module of a record, before its members: no group *)
      intros Θ2 Ξ2 He; split.
      + intros pq0 D0 Heq; discriminate Heq.
      + intros _; constructor; [ intros [| ? ?] ? Hx; discriminate | intros ? ? ? ? ? Hx; discriminate |].
        intros ? ? ? ? ? Hx; cbn in Hx; discriminate.
    - (* extending a module *)
      match goal with IH : GoodM _ _ _ _ _ _ |- _ => rename IH into IHΦ end.
      match goal with IH : GoodE _ _ _ _ |- _ => rename IH into IHE end.
      intros Θ2 Ξ2 He0; destruct (IHΦ _ _ He0) as [HK HB]; split; [ exact HK | intros He ].
      assert (He' : Emb Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Emb_pre; [ apply gc_sub_grow; eassumption | exact He ]).
      destruct (HB He') as [HΦE HΦU HΦA].
      destruct (proj2 (IHE _ _ He') (Ctb_frame _ _ _ _ _ _ _ _ _ _ (em_res _ _ _ _ He))) as [HEE HEM HEU HEA].
      constructor.
      + intros ip E0 Hr; destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ']; eauto.
      + intros z ip T pq0 D Hr.
        destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(_ & _ & HE) | [(? & ? & _ & _ & HE) | HΦ']]; eauto.
      + intros ip pv0 A0 M0 U0 Hx.
        destruct (gm_entry_ext_inv _ _ _ _ _ Hx) as [(ip' & -> & HE) | HΦ']; eauto.
    - (* nothing filed *)
      intros ? ? _; constructor; [ intros p E Hr; unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr; discriminate
                                 | intros p D Hr; unfold ind_lookup, ind_lookup_u, ind_mlookup_u, gc_module, gc_module_u in Hr; cbn in Hr; discriminate
                                 | intros p ? ? ? ? Hr; unfold gc_entry, gc_entry_u in Hr; cbn in Hr; discriminate ].
    - (* a filed unit: it resolves as its closed frame did *)
      rename H into Hg, H0 into IHU.
      intros Θ2 Ξ2 He.
      destruct (wf_gstack_cons_inv _ _ _ _ _ Hg) as (_ & _ & [Hn _]).
      destruct (IHU _ _ (Emb_pre _ _ _ _ _ _ (gc_sub_file _ _ U Hn) He)) as [HR HI HA].
      constructor; [ intros p E Hr; rewrite gc_resolve_file in Hr; eauto | |].
      + intros p D Hr; rewrite ind_lookup_file in Hr; eauto.
      + intros p ? ? ? ? Hr; rewrite gc_entry_file in Hr; eauto.
    - (* a frame *)
      rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He.
      assert (HeΞ : Emb Θ Ξ Θ2 Ξ2) by (eapply Emb_pre; [ apply gc_sub_push; eassumption | exact He ]).
      destruct (IHU _ _ HeΞ) as [HK HB]; destruct (HB He) as [HUE HUU HUA].
      destruct (IHΞ _ _ HeΞ) as [HR HI HA].
      constructor.
      + intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr']; eauto.
      + intros p D Hr; destruct (ind_lookup_module _ _ _ _ Hr) as (pq0 & [(T & Hm) | Hf]).
        * destruct (gc_module_frame _ _ _ _ _ _ _ Hm) as [(x & ip & -> & Hm') | Hm']; [ eauto |].
          apply (HI p); rewrite (ind_lookup_body _ _ _ _ _ Hm'); reflexivity.
        * cbn [gs_find_ind] in Hf; destruct (qname_strip mp p) as [[| ? ?] |] eqn:Hs; [| discriminate |].
          -- destruct K as [| pq1 k1 D1 | R1]; [ discriminate | | discriminate ]; injection Hf as -> -> ->; exact (HK _ _ eq_refl).
          -- apply (HI p); rewrite ind_lookup_unfold, ind_mlookup_unfold, Hf; reflexivity.
      + intros p ? ? ? ? Hr; destruct (gc_entry_frame _ _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr']; eauto.
  Qed.

  Corollary global_induction : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GV Θ Ξ Θ Ξ.
  Proof.
    intros * Hg; destruct global_induction_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
    exact (H _ _ Hg _ _ (Emb_refl _ _ Hg)).
  Qed.
End Induction.

(** ** Validity of Bodies, by Induction over Insertion

    The induction of [Global/Presup.v] for entries, extended to what a module
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

Lemma Ctbx_frame : forall Θ mp K Δ Φ x E Ξ Θ2 Ξ2,
    gc_subx Θ ((mp, K, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ) Θ2 Ξ2 ->
    Ctbx Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mp x) E.
Proof.
  intros * Hs; split; [ exact (Ctb_frame _ _ _ _ _ _ _ _ _ _ (gc_subx_sub _ _ _ _ Hs)) |].
  intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_subx_body _ _ _ _ _ _ Hs).
  rewrite gc_body_frame_here; cbn [gu_mod gu_params]; apply gm_subbody_ext_here; exact Hr0.
Qed.

Lemma Embx_nested : forall Θ Ξ mp pv K Δ' Φ' Θ2 Ξ2,
    Embx Θ Ξ Θ2 Ξ2 ->
    Ctbx Θ2 Ξ2 (gs_tele Ξ) mp (frame_entry pv mp K Δ' Φ') ->
    kind_tele mp K Δ' (gs_tele Ξ) ->
    Embx Θ ((mp, K, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * He [Hc Hbod] HK; constructor; [ exact (emx_wf _ _ _ _ He) | split ].
  - exact (em_res _ _ _ _ (Emb_nested _ _ _ _ _ _ _ _ _ (Embx_emb _ _ _ _ He) Hc HK)).
  - intros p r Hr; destruct (gc_body_frame _ _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'].
    + apply Hbod; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (frame_entry_reads pv _ _ _ Φ' _ HK)))))); exact Hm.
    + exact (gc_subx_body _ _ _ _ _ _ (emx_res _ _ _ _ He) Hr').
Qed.

Section ModInduction.
  (** The validity of an entry, read from a source context, at a target
      it embeds into. *)
  Variable V : gdeps -> gstack -> gdeps -> gstack -> ctx -> gentry -> Prop.
  Variable F : gdeps -> gstack -> ctx -> Prop.
  (** The validity of the declaration of an inductive type. *)
  Variable VD : gdeps -> gstack -> ind_decl -> Prop.
  (** The validity of the declaration of a record type. *)
  Variable VR : gdeps -> gstack -> record_decl -> Prop.

  (** A body is valid when its definitions and aliases are, and its body
      modules and the modules of its inductive and record types are, over
      their telescopes; the declaration of an inductive or a record type is
      valid too. *)
  Fixpoint gm_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (Φ : gmod) : Prop :=
    match Φ with
    | gm_nil => True
    | gm_open Φ0 _ _ => gm_valid Θs Ξs Θ2 Ξ2 T Φ0
    | gm_ext Φ0 _ (ge_mod _ (gu_mk Δ (md_body sm Φ'))) =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θs Ξs Θ2 Ξ2 (Δ ++ T) Φ'
    | gm_ext Φ0 _ (ge_ind _ _ k D Φ') =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ (k = 0 -> VD Θ2 Ξ2 D) /\ F Θ2 Ξ2 (ind_uparams D) /\
        gm_valid Θs Ξs Θ2 Ξ2 (ind_uparams D) Φ'
    | gm_ext Φ0 _ (ge_def_mod pv A M U) =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ V Θs Ξs Θ2 Ξ2 T (ge_mod pv U) /\ V Θs Ξs Θ2 Ξ2 T (ge_def true pv A (Some M))
    | gm_ext Φ0 _ (ge_record pv pr R Φ') =>
        gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ VR Θ2 Ξ2 R /\ F Θ2 Ξ2 (record_mod_tele pr R) /\
        gm_valid Θs Ξs Θ2 Ξ2 (record_mod_tele pr R) Φ'
    | gm_ext Φ0 _ E => gm_valid Θs Ξs Θ2 Ξ2 T Φ0 /\ V Θs Ξs Θ2 Ξ2 T E
    end.

  (** What the entry [E], filed over [T], contributes is valid: as
      [gm_valid] does for one entry of a body. *)
  Definition ge_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
    match E with
    | ge_mod _ (gu_mk Δ (md_body sm Φ')) => F Θ2 Ξ2 (Δ ++ T) /\ gm_valid Θs Ξs Θ2 Ξ2 (Δ ++ T) Φ'
    (** The group is valid at its first member. *)
    | ge_ind _ _ k D Φ' => (k = 0 -> VD Θ2 Ξ2 D) /\ F Θ2 Ξ2 (ind_uparams D) /\ gm_valid Θs Ξs Θ2 Ξ2 (ind_uparams D) Φ'
    (** A definition with a module part is valid as its two views: its
        module part, a module alias, and its term part, a transparent
        definition. *)
    | ge_def_mod pv A M U => V Θs Ξs Θ2 Ξ2 T (ge_mod pv U) /\ V Θs Ξs Θ2 Ξ2 T (ge_def true pv A (Some M))
    (** A record is valid as its declaration, and its module as a body over
        its parameters and a value. *)
    | ge_record pv pr R Φ' =>
        VR Θ2 Ξ2 R /\ F Θ2 Ξ2 (record_mod_tele pr R) /\ gm_valid Θs Ξs Θ2 Ξ2 (record_mod_tele pr R) Φ'
    | _ => V Θs Ξs Θ2 Ξ2 T E
    end.

  Lemma gm_valid_ext : forall Θs Ξs Θ2 Ξ2 T Φ x E,
      gm_valid Θs Ξs Θ2 Ξ2 T (Φ ⊳ x ↦ E) <-> gm_valid Θs Ξs Θ2 Ξ2 T Φ /\ ge_valid Θs Ξs Θ2 Ξ2 T E.
  Proof. intros; destruct E as [? ? ? ? | ? [Δ [? Φ' | E']] | ? ? ? ? ? | ? Aa Ma Ua | ? pr Rr ΦR]; cbn; tauto. Qed.

  (** The group a frame's kind names, if the frame is the module of the
      group's first member, is valid at [Θ2 ⍮ Ξ2]; so is the record type
      whose module the frame is. *)
  Definition kind_valid (Θ2 : gdeps) (Ξ2 : gstack) (K : frame_kind) : Prop :=
    (forall pq D, K = fk_ind pq 0 D -> VD Θ2 Ξ2 D) /\ (forall R, K = fk_record R -> VR Θ2 Ξ2 R).

  Fixpoint gs_valid (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Ξ : gstack) : Prop :=
    match Ξ with
    | nil => True
    | (_, K, U) :: Ξ' =>
        F Θ2 Ξ2 (gu_params U ++ gs_tele Ξ') /\ gm_valid Θs Ξs Θ2 Ξ2 (gu_params U ++ gs_tele Ξ') (gu_mod U) /\
        kind_valid Θ2 Ξ2 K /\ gs_valid Θs Ξs Θ2 Ξ2 Ξ'
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
  Hypothesis Hnil : forall Θ Ξ Δ Θ2 Ξ2,
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
  (** A declaration, and the telescope of its uniform parameters, which its
      module's members are checked in. *)
  Hypothesis Hind : forall Θ Ξ D Θ2 Ξ2,
      decl_typed Θ Ξ D -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D).
  (** A record's declaration, at any target its context embeds into. *)
  Hypothesis Hrecord : forall Θ Ξ R Θ2 Ξ2,
      record_typed Θ Ξ R -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> VR Θ2 Ξ2 R.
  (** A record's module telescope, at any target its context embeds into
      where the record is found: its parameters, then a value of it, which
      is typed only there. *)
  Hypothesis Hrecord_tele : forall Θ Ξ p R Θ2 Ξ2,
      record_typed Θ Ξ R -> GoodV Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> record_lookup Θ2 Ξ2 p = Some R ->
      F Θ2 Ξ2 (record_params R) -> F Θ2 Ξ2 (record_mod_tele p R).

  (** An entry, and the context it is checked in: valid read from any
      context that has it and what the context it is checked in has. *)
  Definition GoodEV (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    GoodV Θ Ξ /\
    (forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> forall pv pq D Φ, E = ge_ind pv pq 0 D Φ -> VD Θ2 Ξ2 D) /\
    forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> Ctbx Θ2 Ξ2 (gs_tele Ξ) mp E ->
      forall Θs Ξs, gc_sub Θ Ξ Θs Ξs -> Ctb Θs Ξs (gs_tele Ξ) mp E -> ge_valid Θs Ξs Θ2 Ξ2 (gs_tele Ξ) E.

  (** A module, and the context it is checked in: the group its kind names
      is valid wherever the context embeds, and its body is valid read from
      any context that has its frame. *)
  Definition GoodMV (Θ : gdeps) (Ξ : gstack) (mp : qname) (K : frame_kind) (Δ : ctx) (Φ : gmod) : Prop :=
    GoodV Θ Ξ /\
    (forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> kind_valid Θ2 Ξ2 K) /\
    forall Θ2 Ξ2, Embx Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 -> Embx Θ Ξ Θ2 Ξ2 ->
      F Θ2 Ξ2 (Δ ++ gs_tele Ξ) /\
      forall Θs Ξs, gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θs Ξs -> gm_valid Θs Ξs Θ2 Ξ2 (Δ ++ gs_tele Ξ) Φ.

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
    (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> GoodMV Θ Ξ mp K Δ Φ) /\
    (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GoodV Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - (* a definition or an axiom *)
      split; [ assumption |]; split; [ intros ? ? _ ? ? ? ? Heq; discriminate Heq |].
      intros Θ2 Ξ2 He _ Θs Ξs Hs _; cbn.
      match goal with
      | HM : forall M, ?o = Some M -> _ ⍮ _ ⍮ _ ⊢ M : _, IHM : forall M, ?o = Some M -> GoodV _ _ |- _ =>
          destruct o as [M0 |]; cbn;
          [ destruct (IHM M0 eq_refl _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ];
            eapply Hdef; [ exact (HM M0 eq_refl) | exact (IHM M0 eq_refl) | exact (Embx_emb _ _ _ _ He) | exact HΘ | exact HΞ ]
          | eapply Hax; eassumption ]
      end.
    - (* a body module: valid as its frame, pushed, is *)
      destruct H0 as [HG [_ HM]]; split; [ exact HG |]; split; [ intros ? ? _ ? ? ? ? Heq; discriminate Heq |].
      intros Θ2 Ξ2 He Hc Θs Ξs Hs Hcs; cbn.
      destruct (HM _ _ (Embx_nested _ _ _ pv fk_module _ _ _ _ He Hc I) He) as [HF HΦ].
      split; [ exact HF | apply HΦ; exact (gc_sub_nested _ _ _ pv fk_module _ _ _ _ Hs Hcs I) ].
    - split; [ assumption |]; split; [ intros ? ? _ ? ? ? ? Heq; discriminate Heq |].
      intros Θ2 Ξ2 He _ Θs Ξs Hs _; cbn; eapply Halias; eassumption.
    - (* a group, at its first member, with no member in its module *)
      split; [ assumption |].
      assert (HDF : forall Θ2 Ξ2, Embx Θ Ξ Θ2 Ξ2 -> VD Θ2 Ξ2 D /\ F Θ2 Ξ2 (ind_uparams D))
        by (intros Θ2 Ξ2 He; eapply Hind; [ build_decl_typed | eassumption | exact He ]).
      split; [ intros Θ2 Ξ2 He ? ? ? ? Heq; injection Heq as _ _ <- _; exact (proj1 (HDF _ _ He)) |].
      intros Θ2 Ξ2 He _ Θs Ξs _ _; cbn.
      destruct (HDF _ _ He) as [HD HF].
      repeat split; [ intros _; exact HD | exact HF ].
    - (* a later declared member of a group, before the members of its
         module: over the group's uniform parameters *)
      split; [ assumption |]; split; [ intros ? ? _ ? ? ? ? Heq; injection Heq as _ _ Hk0 _ _; lia |].
      intros Θ2 Ξ2 He _ Θs Ξs _ _; cbn.
      split; [ intros; lia | split; [| exact I ] ].
      match goal with
      | HU : ind_uparams ?D = ?Δu ++ gs_tele ?Ξ', Ha : tele_ass (ind_uparams ?D), HC : ⊢ _ ⍮ _ ⍮ ind_uparams ?D,
        HG : GoodV _ _ |- F _ _ (ind_uparams ?D) =>
          rewrite HU in Ha, HC |- *; eapply Hnil; [ exact (proj1 (proj1 (List.Forall_app _ _ _) Ha)) | exact HC | exact HG | exact He ]
      end.
    - (* a declared member with the body of its module, checked in the
         member's open frame *)
      match goal with IH : GoodMV _ _ _ _ _ _ |- _ => rename IH into IHM end.
      match goal with Hu : ind_uparams D = _ |- _ => rename Hu into HU end.
      destruct IHM as [HG [HK IHM]]; split; [ exact HG |].
      split; [ intros Θ2 Ξ2 He ? ? ? ? Heq; injection Heq as _ <- -> <- _; exact (proj1 (HK _ _ He) _ _ eq_refl) |].
      intros Θ2 Ξ2 He Hc Θs Ξs Hs Hcs; cbn.
      destruct (IHM _ _ (Embx_nested _ _ _ pv (fk_ind pq k D) _ _ _ _ He Hc HU) He) as [HF HΦ].
      rewrite HU; split; [ intros ->; exact (proj1 (HK _ _ He) _ _ eq_refl) | split; [ exact HF |] ].
      apply HΦ; exact (gc_sub_nested _ _ _ pv (fk_ind pq k D) _ _ _ _ Hs Hcs HU).
    - (* a definition with a module part: valid as its module part, an
         alias, and as its term part, a transparent definition *)
      split; [ assumption |]; split; [ intros ? ? _ ? ? ? ? Heq; discriminate Heq |].
      intros Θ2 Ξ2 He _ Θs Ξs Hs _; cbn; split; [ eapply Halias; eassumption |].
      match goal with HG : GoodV _ _ |- _ => destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ] end.
      eapply Hdef; [ eassumption | eassumption | exact (Embx_emb _ _ _ _ He) | exact HΘ | exact HΞ ].
    - (* a record, before the members of its module: valid as its
         declaration, over its parameters and a value *)
      split; [ assumption |]; split; [ intros ? ? _ ? ? ? ? Heq; discriminate Heq |].
      intros Θ2 Ξ2 He [Hct _] Θs Ξs Hs _; cbn.
      split; [ eapply Hrecord; [ constructor; eassumption | eassumption | exact He ] | split; [| exact I ] ].
      eapply Hrecord_tele; [ constructor; eassumption | eassumption | exact He | exact (Ctb_record_lookup _ _ _ _ _ _ _ _ Hct) |].
      match goal with
      | HU : record_params ?R = ?Δu ++ gs_tele ?Ξ', Ha : tele_ass (record_params ?R),
        HS : _ ⍮ _ ⍮ record_params ?R ⊢ᵤ _, HG : GoodV _ _ |- F _ _ (record_params ?R) =>
          pose proof (presup_is_univ_ctx HS) as HC;
          rewrite HU in Ha, HC |- *; eapply Hnil; [ exact (proj1 (proj1 (List.Forall_app _ _ _) Ha)) | exact HC | exact HG | exact He ]
      end.
    - (* a record with the body of its module, checked in the record's open
         frame *)
      match goal with IH : GoodMV _ _ _ _ _ _ |- _ => rename IH into IHM end.
      match goal with Hu : record_params R = _ |- _ => rename Hu into HU end.
      match goal with Hm : _ ⍮ _ ⍮ _ ⍮ fk_record R ⍮ _ ⊢ᵍᵐ _ |- _ => pose proof (wf_gmod_record_typed _ _ _ _ _ _ Hm _ eq_refl) as HRt end.
      destruct IHM as [HG [HK IHM]]; split; [ exact HG |].
      split; [ intros Θ2 Ξ2 He ? ? ? ? Heq; discriminate Heq |].
      intros Θ2 Ξ2 He Hc Θs Ξs Hs Hcs; cbn.
      assert (HKt : kind_tele mp (fk_record R) (ce_ass (record_self mp R) :: Δ) (gs_tele Ξ))
        by (exists Δ; split; [ reflexivity | exact HU ]).
      destruct (IHM _ _ (Embx_nested _ _ _ pv (fk_record R) _ _ _ _ He Hc HKt) He) as [HF HΦ].
      split; [ exact (proj2 (HK _ _ He) _ eq_refl) |].
      unfold record_mod_tele; rewrite HU; split; [ exact HF |].
      apply HΦ; exact (gc_sub_nested _ _ _ pv (fk_record R) _ _ _ _ Hs Hcs HKt).
    - split; [ assumption |]; split; [ intros ? ? _; split; [ intros ? ? Heq | intros ? Heq ]; discriminate Heq |].
      intros Θ2 Ξ2 _ He; split; [ eapply Hnil; eassumption | intros; exact I ].
    - (* the module of a member, before its members: the member's group *)
      match goal with IH : GoodEV _ _ _ _ |- _ => rename IH into IHE end.
      split; [ exact (proj1 IHE) |]; split.
      + intros Θ2 Ξ2 He; split; [| intros ? Heq; discriminate Heq ].
        intros pq0 D0 Heq; injection Heq as -> -> ->; exact (proj1 (proj2 IHE) _ _ He _ _ _ _ eq_refl).
      + intros Θ2 Ξ2 _ He; split; [ eapply Hnil; eassumption | intros; exact I ].
    - (* the module of a record, before its members: the record's
         declaration *)
      match goal with IH : GoodEV _ _ _ _ |- _ => rename IH into IHE end.
      split; [ exact (proj1 IHE) |]; split.
      + intros Θ2 Ξ2 He; split; [ intros ? ? Heq; discriminate Heq |].
        intros R0 Heq; injection Heq as <-.
        match goal with HE : _ ⍮ _ ⍮ _ ⊢ᵉ ge_record _ _ _ _ |- _ =>
          exact (Hrecord _ _ _ _ _ (proj1 wf_record_typed_all _ _ _ _ HE _ _ _ _ eq_refl) (proj1 IHE) He) end.
      + (* its telescope: the parameters, valid one frame out, and the
           value, where the record's frame is *)
        intros Θ2 Ξ2 Hp He; split; [| intros; exact I ].
        match goal with HE : _ ⍮ _ ⍮ _ ⊢ᵉ ge_record _ _ _ _, HU : record_params _ = _ ++ _ |- _ =>
          pose proof (proj1 wf_record_typed_all _ _ _ _ HE _ _ _ _ eq_refl) as HRt; cbn [List.app]; rewrite <- HU end.
        eapply Hrecord_tele; [ exact HRt | exact (proj1 IHE) | exact He | |].
        * apply (gc_sub_frame_record _ _ _ _ _ _ (gc_subx_sub _ _ _ _ (emx_res _ _ _ _ Hp))).
          rewrite gs_find_record_own; reflexivity.
        * match goal with HU : record_params _ = _ ++ _ |- _ => rewrite HU end.
          match goal with Ha : tele_ass ?Δ, HC : ⊢ _ ⍮ _ ⍮ ?Δ ++ _ |- _ => exact (Hnil _ _ _ _ _ Ha HC (proj1 IHE) He) end.
    - match goal with IH : GoodMV _ _ _ _ _ _ |- _ => rename IH into IHΦ end.
      match goal with IH : GoodEV _ _ _ _ |- _ => rename IH into IHE end.
      destruct IHΦ as [HG [HK IHΦ]]; split; [ exact HG |]; split; [ exact HK |].
      intros Θ2 Ξ2 He Hout.
      assert (He' : Embx Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Embx_pre; [ apply gc_subx_grow; eassumption | exact He ]).
      destruct (IHΦ _ _ He' Hout) as [HF HΦ].
      split; [ exact HF |]; intros Θs Ξs Hs.
      apply gm_valid_ext; split; [ apply HΦ; eapply gc_sub_trans; [ apply gc_sub_grow; eassumption | exact Hs ] |].
      apply (proj2 (proj2 IHE) _ _ He' (Ctbx_frame _ _ _ _ _ _ _ _ _ _ (emx_res _ _ _ _ He))).
      + eapply gc_sub_trans; [ apply gc_sub_grow; eassumption | exact Hs ].
      + exact (Ctb_frame _ _ _ _ _ _ _ _ _ _ Hs).
    - intros Θ2 Ξ2 _ Θs Ξs _; split; [ intros fp U Hl; discriminate | exact I ].
    - (* a filed unit: valid as its closed frame was *)
      rename H into Hg, H0 into IHU.
      match goal with |- GoodV ((?f, _) :: _) nil => rename f into fp0 end.
      intros Θ2 Ξ2 He Θs Ξs Hs; split; [| exact I ].
      destruct (wf_gstack_cons_inv _ _ _ _ _ Hg) as (_ & _ & [Hn _]).
      destruct (IHU Θ2 Ξ2 ltac:(eapply Embx_pre; [ apply gc_subx_file; exact Hn | exact He ])
                  Θs Ξs ltac:(eapply gc_sub_trans; [ apply gc_sub_file; exact Hn | exact Hs ])) as [HΘ HΞ].
      intros fq W Hl; cbn in Hl; destruct (path_beq fq fp0);
        [ injection Hl as <-; cbn [gs_valid gs_tele] in HΞ; rewrite app_nil_r in HΞ; tauto | exact (HΘ _ _ Hl) ].
    - rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He Θs Ξs Hs.
      assert (He0 : Embx Θ Ξ Θ2 Ξ2) by (eapply Embx_pre; [ apply gc_subx_push; eassumption | exact He ]).
      destruct (IHΞ _ _ He0 Θs Ξs ltac:(eapply gc_sub_trans; [ apply gc_sub_push; eassumption | exact Hs ])) as [HΘ HΞ].
      split; [ exact HΘ |].
      destruct (proj2 (proj2 IHU) _ _ He He0) as [HF HΦ]; cbn [gs_valid].
      split; [ exact HF | split; [ apply HΦ; exact Hs | split; [ exact (proj1 (proj2 IHU) _ _ He0) | exact HΞ ] ] ].
  Qed.

  Corollary global_valid : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GoodV Θ Ξ.
  Proof. intros; apply global_valid_all; assumption. Qed.

  (** *** Reading validity back *)

  Lemma gm_valid_subbody : forall Φ Θs Ξs Θ2 Ξ2 T x ip T' Φ',
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> F Θ2 Ξ2 T' /\ gm_valid Θs Ξs Θ2 Ξ2 T' Φ'.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | ? Aa Ma Ua | ? Rr ΦR]; try discriminate.
    - destruct Hv as (_ & HF & Hv); destruct ip as [| w ip].
      + injection H as <- <-; split; assumption.
      + exact (IH _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & HF & Hv); destruct ip as [| w ip].
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
      [| destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? D Φ0 | ? Aa Ma Ua | ? Rr ΦR]; try discriminate.
    - injection H as <-; exists T; exact (proj2 Hv).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_def : forall Φ Θs Ξs Θ2 Ξ2 T z b pv A B,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> V Θs Ξs Θ2 Ξ2 T (ge_def b pv A B).
  Proof.
    induction Φ as [| Φ IH y E0 | Φ IH c]; intros * Hv H; cbn in Hv, H; [ discriminate | | eauto ].
    destruct (String.eqb z y);
      [| destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; try discriminate.
    injection H; intros; subst; exact (proj2 Hv).
  Qed.

  Lemma gm_valid_alias : forall Φ Θs Ξs Θ2 Ξ2 T x ip U,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_alias U) -> exists T' pv, V Θs Ξs Θ2 Ξ2 T' (ge_mod pv U).
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | pm Aa Ma [Δa [? Φa | Ea]] | pm Rr ΦR]; try discriminate.
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ Hv H).
    - destruct ip; [| discriminate ]; injection H as <-; exists T, pm; exact (proj2 Hv).
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ Hv H).
    - destruct ip; [| discriminate ]; injection H as <-; exists T, pm; exact (proj1 (proj2 Hv)).
    - destruct ip as [| w ip]; [ discriminate |].
      destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  (** A definition with a module part stored in a valid body is valid as
      its two views. *)
  Lemma gm_valid_def_mod : forall Φ Θs Ξs Θ2 Ξ2 T ip pv A M U,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_entry Φ ip = Some (ge_def_mod pv A M U) ->
      exists T', V Θs Ξs Θ2 Ξ2 T' (ge_mod pv U) /\ V Θs Ξs Θ2 Ξ2 T' (ge_def true pv A (Some M)).
  Proof.
    fix IH 1; intros [| Φ y E0 | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y);
      [| destruct E0 as [? ? ? ? | ? [Δ0 [? Φ0 | E1]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ0 [? Φ0 | E1]] | ? ? ? D Φ0 | pm Aa Ma Ua | pm Rr ΦR]; cbn in H; try discriminate.
    - injection H as <- <- <- <-; exists T; exact (proj2 Hv).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gm_valid_ind : forall Φ Θs Ξs Θ2 Ξ2 T x ip T' pq D,
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_submodule T Φ x ip = Some (mr_body T' (Some (pq, 0, D))) -> VD Θ2 Ξ2 D.
  Proof.
    fix IH 1; intros [| Φ y E | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct (String.eqb x y);
      [| destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? ? ? | ? Aa Ma Ua | ? Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct E as [? ? ? ? | pm [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | pm Aa Ma [Δa [? Φa | Ea]] | pm Rr ΦR]; try discriminate;
      destruct ip as [| w ip]; try discriminate.
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - injection H; intros; subst; exact (proj1 (proj2 Hv) eq_refl).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  (** A record entry of a valid body is valid as its declaration. *)
  Lemma gm_valid_record : forall Φ Θs Ξs Θ2 Ξ2 T ip pv pr R Φ',
      gm_valid Θs Ξs Θ2 Ξ2 T Φ -> gm_entry Φ ip = Some (ge_record pv pr R Φ') -> VR Θ2 Ξ2 R.
  Proof.
    fix IH 1; intros [| Φ y E0 | Φ c] * Hv H; cbn in Hv, H; [ discriminate | | exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H) ].
    destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y);
      [| destruct E0 as [? ? ? ? | ? [Δ [? Φ0 | E1]] | ? ? ? ? ? | ? Aa Ma Ua | ? pr0 Rr ΦR]; (eapply IH; [ exact (proj1 Hv) | exact H ]) ].
    destruct ip as [| w ip], E0 as [? ? ? ? | ? [Δ0 [? Φ0 | E1]] | ? ? ? D Φ0 | pm Aa Ma Ua | pm pr0 Rr ΦR]; cbn in H; try discriminate.
    - injection H as <- <- <- <-; exact (proj1 (proj2 Hv)).
    - destruct Hv as (_ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct Hv as (_ & _ & _ & Hv); exact (IH _ _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma gs_valid_find : forall Θs Ξs Θ2 Ξ2 Ξ p U ip T,
      gs_valid Θs Ξs Θ2 Ξ2 Ξ -> gs_find_tele Ξ p = Some (U, ip, T) ->
      F Θ2 Ξ2 (gu_params U ++ T) /\ gm_valid Θs Ξs Θ2 Ξ2 (gu_params U ++ T) (gu_mod U).
  Proof.
    induction Ξ as [| [[mp K0] U0] Ξ IH]; intros * Hv H; cbn in Hv, H; [ discriminate |].
    destruct (qname_strip mp p); [ injection H as <- <- <-; split; apply Hv | exact (IH _ _ _ _ (proj2 (proj2 (proj2 Hv))) H) ].
  Qed.

  (** The group an open frame's kind names, at its first member, is valid. *)
  Lemma gs_valid_kind : forall Θs Ξs Θ2 Ξ2 Ξ p pq D,
      gs_valid Θs Ξs Θ2 Ξ2 Ξ -> gs_find_ind Ξ p = Some (pq, 0, D) -> VD Θ2 Ξ2 D.
  Proof.
    induction Ξ as [| [[mp K0] U0] Ξ IH]; intros * Hv H; cbn in Hv, H; [ discriminate |].
    destruct (qname_strip mp p) as [[| ? ?] |]; [| discriminate | exact (IH _ _ _ (proj2 (proj2 (proj2 Hv))) H) ].
    destruct K0 as [| pq' k' D' | R']; [ discriminate | | discriminate ]; injection H as -> -> ->.
    exact (proj1 (proj1 (proj2 (proj2 Hv))) _ _ eq_refl).
  Qed.

  (** The record type whose module an open frame is, is valid. *)
  Lemma gs_valid_record_kind : forall Θs Ξs Θ2 Ξ2 Ξ p R,
      gs_valid Θs Ξs Θ2 Ξ2 Ξ -> gs_find_record Ξ p = Some R -> VR Θ2 Ξ2 R.
  Proof.
    induction Ξ as [| [[mp K0] U0] Ξ IH]; intros * Hv H; cbn in Hv, H; [ discriminate |].
    destruct (qname_strip mp p) as [[| ? ?] |]; [| discriminate | exact (IH _ _ (proj2 (proj2 (proj2 Hv))) H) ].
    destruct K0 as [| pq' k' D' | R']; try discriminate; injection H as ->.
    exact (proj2 (proj1 (proj2 (proj2 Hv))) _ eq_refl).
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

  (** A filed record entry is valid as its declaration. *)
  Lemma good_record_entry : forall Θ Ξ Θs Ξs Θ2 Ξ2 p pv pr R Φ', gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      gc_entry Θ Ξ p = Some (ge_record pv pr R Φ') -> VR Θ2 Ξ2 R.
  Proof.
    intros * HΘ HΞ H; unfold gc_entry, gc_entry_u in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ p) as [[[U ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_record _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_record _ _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  (** A record type a path names, filed or with its module's frame open,
      is valid. *)
  Lemma good_record : forall Θ Ξ Θs Ξs Θ2 Ξ2 p R, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      record_lookup Θ Ξ p = Some R -> VR Θ2 Ξ2 R.
  Proof.
    intros * HΘ HΞ H; unfold record_lookup in H.
    destruct (gs_find_record Ξ p) as [R' |] eqn:Hf; [ injection H as <-; exact (gs_valid_record_kind _ _ _ _ _ _ _ HΞ Hf) |].
    destruct (gc_entry Θ Ξ p) as [[| | | | pv pr R' Φ'] |] eqn:He; try discriminate; injection H as <-.
    exact (good_record_entry _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ He).
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

  (** A stored definition with a module part is valid as its two views. *)
  Lemma good_def_mod : forall Θ Ξ Θs Ξs Θ2 Ξ2 p pv A M U, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) ->
      exists T, V Θs Ξs Θ2 Ξ2 T (ge_mod pv U) /\ V Θs Ξs Θ2 Ξ2 T (ge_def true pv A (Some M)).
  Proof.
    intros * HΘ HΞ H; unfold gc_entry, gc_entry_u in H.
    rewrite gs_find_tele_find in H.
    destruct (gs_find_tele Ξ p) as [[[Uf ip] T0] |] eqn:Hf; cbn in H.
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_def_mod _ _ _ _ _ _ _ _ _ _ _ Hv H).
    - destruct (gds_lookup Θ (q_unit p)) as [Uf |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv]; exact (gm_valid_def_mod _ _ _ _ _ _ _ _ _ _ _ Hv H).
  Qed.

  Lemma good_ind : forall Θ Ξ Θs Ξs Θ2 Ξ2 p D, gds_valid Θs Ξs Θ2 Ξ2 Θ -> gs_valid Θs Ξs Θ2 Ξ2 Ξ ->
      ind_lookup Θ Ξ p = Some D -> VD Θ2 Ξ2 D.
  Proof.
    intros * HΘ HΞ H.
    destruct (ind_lookup_module _ _ _ _ H) as (pq & [(T & H') | Hf]); [| exact (gs_valid_kind _ _ _ _ _ _ _ _ HΞ Hf) ].
    unfold gc_module, gc_module_u in H'.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
    - destruct (gs_valid_find _ _ _ _ _ _ _ _ _ HΞ Hf) as [_ Hv]; exact (gm_valid_ind _ _ _ _ _ _ _ _ _ _ _ Hv H').
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      destruct (HΘ _ _ Hl) as [_ Hv].
      destruct (q_chain p) as [| x ip]; [ discriminate |]; exact (gm_valid_ind _ _ _ _ _ _ _ _ _ _ _ Hv H').
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

Definition syn_VR : gdeps -> gstack -> record_decl -> Prop := record_typed.

(** The syntactic validity of a stored entry, filed over [T]: a definition
    is closed over [T] from a typed body under it; a module alias's target
    is well formed and denotes typed module descriptions.  A definition with
    a module part is valid as these two views ([ge_valid]). *)
Definition syn_V (Θ : gdeps) (Ξ : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A oM =>
      exists A0, A = ctx_pi T A0 /\ (exists i, Θ ⍮ Ξ ⍮ T ⊢ A0 : Typeω@i) /\
        (forall M, oM = Some M -> exists M0, M = ctx_fn T M0 /\ Θ ⍮ Ξ ⍮ T ⊢ M0 : A0)
  | ge_mod _ (gu_mk Δa (md_alias E')) =>
      Θ ⍮ Ξ ⍮ Δa ⊢ᵐ E' ≈ E' /\ ⊢ Θ ⍮ Ξ ⍮ Δa /\
      forall Γ, ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ ->
        (exists R, mdenote Θ Ξ (Δa ++ Γ) E' R) /\
        forall R, mdenote Θ Ξ (Δa ++ Γ) E' R -> desc_ok Θ Ξ (Δa ++ Γ) R /\ exists Rm, ds_mod R = Some Rm
  | ge_record _ _ R _ => record_typed Θ Ξ R
  | _ => True
  end.

(** Syntactic validity does not depend on where it is read from. *)
Abbreviation syn_Vs := (fun (_ : gdeps) (_ : gstack) => syn_V).

(** Everything stored at [Θ ⍮ Ξ] is valid there. *)
Definition valid_syn (Θ : gdeps) (Ξ : gstack) : Prop :=
  gds_valid syn_Vs syn_F syn_VD syn_VR Θ Ξ Θ Ξ Θ /\ gs_valid syn_Vs syn_F syn_VD syn_VR Θ Ξ Θ Ξ Ξ.

Lemma gm_valid_prefix : forall V F VD VR Θs Ξs Θ2 Ξ2 T Φ y Φ0 E,
    gm_valid V F VD VR Θs Ξs Θ2 Ξ2 T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> ge_valid V F VD VR Θs Ξs Θ2 Ξ2 T E.
Proof.
  intros V F VD VR Θs Ξs Θ2 Ξ2 T; induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hv Hp; cbn in Hp; [ discriminate | |].
  - apply gm_valid_ext in Hv as [Hv HE].
    destruct (String.eqb y x); [ injection Hp as -> -> ->; exact HE | eauto ].
  - destruct (existsb _ _); [ discriminate | cbn in Hv; eauto ].
Qed.

Lemma loc_valid : forall Θ Ξ p T Φ, valid_syn Θ Ξ -> loc Θ Ξ p T Φ ->
    syn_F Θ Ξ T /\ gm_valid syn_Vs syn_F syn_VD syn_VR Θ Ξ Θ Ξ T Φ.
Proof.
  intros * [HΘ HΞ] [Hl | Hl].
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hl as <- <-; exact (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef).
  - exact (good_body _ _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl).
Qed.

(** The record type an open frame is the module of is typed: it was
    checked where the module started. *)
Lemma record_frame_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p R, gs_find_record Ξ p = Some R -> record_typed Θ Ξ R.
Proof.
  intros * Hg * Hf.
  destruct (gs_find_record_split _ _ _ Hf) as (Ξ1 & U & Ξ0 & HΞ & _); subst Ξ.
  destruct (wf_gstack_app_inv _ _ _ Hg) as [Hg0 Hsub].
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & [Δ Φ0 -> HΦ] & Hff).
  eapply record_typed_emb; [| exact (wf_gmod_record_typed _ _ _ _ _ _ HΦ _ eq_refl) ].
  constructor; [ exact Hg | eapply gc_sub_trans; [ apply gc_sub_push; exact Hff | exact Hsub ] ].
Qed.

(** Over valid storage, every record type found is typed. *)
Lemma record_lookup_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall p R,
    record_lookup Θ Ξ p = Some R -> record_typed Θ Ξ R.
Proof.
  intros * Hg [HΘ HΞ] * Hl; unfold record_lookup in Hl.
  destruct (gs_find_record Ξ p) as [R0 |] eqn:Hf; [ injection Hl as <-; exact (record_frame_typed _ _ Hg _ _ Hf) |].
  destruct (gc_entry Θ Ξ p) as [[| | | | pv pr R0 Φ] |] eqn:He; try discriminate; injection Hl as <-.
  exact (good_record_entry syn_Vs syn_F syn_VD syn_VR _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ He).
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
  destruct (filed_denote _ _ Hg _ _ _ Γ nil (gc_loc_of_loc _ _ Hg _ _ _ Hl)) as (R1 & Hm & Hmd); cbn [me_apps] in Hm.
  eapply wf_mem; [ exact (loc_modexp_wf _ _ _ HΓ _ _ _ Hl) | | | exact HA | ].
  - eapply mdenote_mem; [ exact Hm | exact Hmd | cbn; rewrite Hp; reflexivity | constructor | reflexivity ].
  - destruct b, oM; reflexivity.
  - intros M Hr0; rewrite ds_named_nil in Hr0; cbn in Hr0; rewrite Hn in Hr0; discriminate.
Qed.

Lemma ds_ats_some_red : forall Ns A M R, ds_ats (ds_term A (Some M)) Ns = Some R -> exists A' M', R = ds_term A' (Some M').
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [| discriminate ].
  destruct (fn_view M) as [M' |]; [ exact (IH _ _ _ Ha) | discriminate ].
Qed.

(** The type former at typed arguments for its first uniform parameters. *)
Lemma wf_ind_args : forall Θ Ξ Γ p D k Mk Ns,
    decl_typed Θ Ξ D -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> k < ind_ndecl D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    args_ok Θ Ξ Γ (ind_uparams D) Ns ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty_at D Mk Ns : Typeω@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_ind p k) Ns : ind_ty_at D Mk Ns.
Proof.
  intros * HD Hl Hk Hlt HΓ [T1 T2 HT Hlen Ha Hs HT2 HN].
  destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([i Hi] & _).
  pose proof (member_params_wf _ _ _ _ _ HD Hk) as HP.
  assert (Hp : im_params D Mk = (im_nparams Mk ++ T1) ++ T2) by (unfold im_params; rewrite HT, List.app_assoc; reflexivity).
  rewrite Hp in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : ind_ty_at D Mk Ns = (ctx_pi (im_nparams Mk ++ T1) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[sb_of_list Id Ns]).
  { unfold ind_ty_at; rewrite <- length_im_params, Hp.
    replace (length ((im_nparams Mk ++ T1) ++ T2) - length Ns) with (length (im_nparams Mk ++ T1))
      by (rewrite !List.length_app in *; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ a_ind p k : ctx_pi T2 (ctx_pi (im_nparams Mk ++ T1) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)).
  { rewrite <- ctx_pi_app, <- Hp; eapply wf_ind; eassumption. }
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha HT2 (eq_sym Hlen) HN) as Hσ.
  rewrite Hat; split.
  - exists j; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' Hσ) as H; cbn in H; exact H.
  - eapply wf_apps_ctx_pi; [ exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

(** The type former of a typed record at arguments for its outermost
    parameters is of the type its declaration gives there. *)
Lemma wf_record_args : forall Θ Ξ Γ p R Ns,
    record_typed Θ Ξ R -> record_lookup Θ Ξ p = Some R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    args_ok Θ Ξ Γ (record_params R) Ns ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ record_ty_at R Ns : Typeω@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_record p) Ns : record_ty_at R Ns.
Proof.
  intros * HR Hl HΓ [T1 T2 HT Hlen Ha Hs HT2 HN].
  pose proof HR as [_ _ HSu _ _].
  destruct (wf_is_univ_typ HSu) as [i Hi].
  pose proof (presup_is_univ_ctx HSu) as HP.
  rewrite HT in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : record_ty_at R Ns = (ctx_pi T1 (record_sort R))[sb_of_list Id Ns]).
  { unfold record_ty_at; rewrite HT.
    replace (length (T1 ++ T2) - length Ns) with (length T1) by (rewrite List.length_app; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : ctx_pi T2 (ctx_pi T1 (record_sort R))).
  { rewrite <- ctx_pi_app, <- HT; exact (record_typed_former _ _ _ _ _ HR Hl HΓ). }
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha HT2 (eq_sym Hlen) HN) as Hσ.
  rewrite Hat; split.
  - exists j; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' Hσ) as H; cbn in H; exact H.
  - eapply wf_apps_ctx_pi; [ exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

(** No argument is an argument list for any telescope. *)
Lemma args_ok_nil : forall Θ Ξ Γ T, ⊢ Θ ⍮ Ξ ⍮ Γ -> args_ok Θ Ξ Γ T nil.
Proof.
  intros * HΓ; exists T nil; [ rewrite List.app_nil_r; reflexivity | reflexivity | constructor | exact I | exact HΓ |].
  intros k ? ? Hk; rewrite List.nth_error_nil in Hk; discriminate.
Qed.

(** The type former of a member of a typed group, at arguments for its
    outermost uniform parameters, with its module there: typed. *)
Lemma desc_ok_ind_former_at : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ pq k D Mk Ns pm Tm Φm,
    ind_lookup Θ Ξ pq = Some D -> ind_member D k = Some Mk -> k < ind_ndecl D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    args_ok Θ Ξ Γ (ind_uparams D) Ns -> desc_ok Θ Ξ Γ (ds_closed nil pm Tm Φm Ns) ->
    exists R', ds_ats_read (ind_former_desc pq k D Mk (ds_closed nil pm Tm Φm nil)) Ns = Some R' /\ desc_ok Θ Ξ Γ R'.
Proof.
  intros * Hg Hv * Hl HMk Hlt HΓ Hargs Hok.
  pose proof Hv as [HΘv HΞv].
  pose proof (good_ind _ _ _ _ _ _ _ _ _ _ _ _ HΘv HΞv Hl) as HD.
  pose proof (decl_closed_ass _ (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl)) as HaU.
  unfold ind_former_desc; cbn [ds_ats_read].
  rewrite (ds_ats_tm_ind _ _ _ _ _ HaU (args_ok_length _ _ _ _ _ Hargs)), ds_ats_closed_nil; cbn [List.app].
  eexists; split; [ reflexivity |].
  destruct (wf_ind_args _ _ _ _ _ _ _ _ HD Hl HMk Hlt HΓ Hargs) as [[i Hi] HM].
  rewrite <- (ds_up_nil (ds_closed nil pm Tm Φm Ns)).
  constructor; [ exact HΓ | constructor | exists i; exact Hi | exact HM | exact Hok ].
Qed.

(** The type former of a typed record type at arguments for its outermost
    parameters, with its module there: typed. *)
Lemma desc_ok_record_former_at : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ p R Ns pm Tm Φm,
    record_lookup Θ Ξ p = Some R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    args_ok Θ Ξ Γ (record_params R) Ns -> desc_ok Θ Ξ Γ (ds_closed nil pm Tm Φm Ns) ->
    exists R', ds_ats_read (record_former_desc p R (ds_closed nil pm Tm Φm nil)) Ns = Some R' /\ desc_ok Θ Ξ Γ R'.
Proof.
  intros * Hg Hv * Hl HΓ Hargs Hok.
  pose proof (record_lookup_typed _ _ Hg Hv _ _ Hl) as HRt.
  unfold record_former_desc; cbn [ds_ats_read].
  rewrite (ds_ats_tm_record _ _ _ (typed_params_ass _ _ _ HRt) (args_ok_length _ _ _ _ _ Hargs)), ds_ats_closed_nil;
    cbn [List.app].
  eexists; split; [ reflexivity |].
  destruct (wf_record_args _ _ _ _ _ _ HRt Hl HΓ Hargs) as [[i Hi] HM].
  rewrite <- (ds_up_nil (ds_closed nil pm Tm Φm Ns)).
  constructor; [ exact HΓ | constructor | exists i; exact Hi | exact HM | exact Hok ].
Qed.

(** An entry of a typed closed description, read with the arguments recorded
    and abstracted over the outside parameters, is typed. *)
Lemma desc_ok_entry_closed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ ->
    forall Γ Θ' p T Φ Ns y Γy E rd R R',
    desc_ok Θ Ξ Γ (ds_closed Θ' p T Φ Ns) -> ds_entry (ds_closed Θ' p T Φ Ns) y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (Some (qname_in p y)) E R -> ds_read rd R = Some R' -> desc_ok Θ Ξ Γ R'.
Proof.
  intros Θ Ξ Hg Hv * HR He Hed Hr.
  inversion HR as [| | Γ0 Θa T0 Φ1 Ns0 Θ0 Ξ0 p0 Hg0 Hsub Hloc Ha HsT HT HΘ' Hargs HaΘ' |]; subst.
  cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 x E0 | ? ? ?] |] eqn:Hp; try discriminate.
  injection He as <- <- <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
  cbn [ds_read] in Hr; destruct (ds_ats_read R Ns) as [R0 |] eqn:Hats; [| discriminate ]; injection Hr as <-.
  (* the entry as it is stored now, grown, is valid *)
  assert (Hloc' : exists Φ', loc Θ Ξ p T Φ').
  { destruct Hloc as [Hf | Hb].
    - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φ' & [[Hf' _] | [Hb' _]]); exists Φ'; [ left | right ]; assumption.
    - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φ' & Hb' & _); exists Φ'; right; exact Hb'. }
  destruct Hloc' as (Φ' & Hloc').
  pose proof (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent) as HeΘ0.
  destruct (gc_sub_entry _ _ _ _ _ _ Hsub HeΘ0) as (E1 & HeΘ & Hgr).
  pose proof (proj1 (loc_entry _ _ Hg _ _ _ Hloc' _ _) HeΘ) as Hent1.
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hloc'))) Hent1) as (Φ0' & Hp1).
  destruct (loc_valid _ _ _ _ _ Hv Hloc') as [_ HvΦ].
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp1) as HE0.
  pose proof (gm_coh_prefix _ _ _ _ _ (loc_coh _ _ Hg0 _ _ _ Hloc) Hp) as HcE0.
  pose proof (loc_closed _ _ Hg0 _ _ _ Hloc) as [_ HcΦ].
  pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
  pose proof (closed_tele_wf _ _ _ _ HsT HT HΘ') as HTΘ.
  apply desc_ok_up; [| exact HΘ' | exact HaΘ' ].
  destruct E0 as [b pv A oM | pv [Δ [sm Φy | E'] ] | pv pq k D ΦD | pv Adm Mdm Udm | pv pr Rr ΦR ].
  - (* a definition: its body, applied *)
    cbn in Hgr; subst E1.
    cbn in HE0; destruct HE0 as (A0 & -> & [i HA0] & HM0).
    inversion Hed; subst; cbn [ds_ats_read] in Hats.
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
    destruct E1 as [| pv1 [Δ1 [sm1 Φy1 | ?]] | | | ]; cbn in Hgr; try discriminate; destruct Hgr as (<- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hx : body_xp _ _ _ Φy ?Φx |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ (body_xp_noopen Θ Ξ _ _ (body_closed_noopen _ _ HcΦy))) as <- end.
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    cbn [ds_ats_read] in Hats; rewrite ds_ats_closed_nil in Hats; injection Hats as <-; cbn [List.app].
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
    match goal with Hm : mdenote _ _ _ E' ?R1, Hmd : ds_mod ?R1 = Some ?R1m |- _ =>
      destruct (proj2 (Hcl _ HΔΓ) _ Hm) as [Hok1 _];
      pose proof (desc_ok_mod _ _ Hg _ _ _ Hok1 Hmd) as Hok1m;
      pose proof (proj1 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ Hm _
                    (slots_ok_app _ 0 _ ltac:(intros ? ? ?; lia) ltac:(exact HsΔ)) ltac:(rewrite Nat.add_0_r; exact HsE)) as HsR1;
      rewrite Nat.add_0_r in HsR1;
      pose proof (ds_mod_scoped _ _ _ HsR1 Hmd) as HsR1m end.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HTΘ)) as HΔΘ.
    pose proof (desc_ok_tele_weaken _ _ Hg _ Θ' _ _ HsΔ HΔΓ HΔΘ HsR1m Hok1m) as Hok2.
    assert (HaΔ : tele_ass (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
    pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) (Δ0 ++ T) _ HΔΘ HaΔ (args_ok_length _ _ _ _ _ Hargs') (args_ok_insts _ _ _ _ _ Hargs') Hok2) as (R2 & HR2 & Hok3).
    rewrite ds_ats_read_mod in Hats by (apply ds_is_mod_up; eapply ds_mod_is_mod; eassumption).
    rewrite Hats in HR2; injection HR2 as <-.
    rewrite ds_named_fix; [ exact Hok3 |]; apply ds_self_mod.
    eapply ds_ats_is_mod; [| exact Hats ]; apply ds_is_mod_up; eapply ds_mod_is_mod; eassumption.
  - (* an inductive type, stored at its own path: its type former at the
       arguments, with its module there *)
    destruct E1 as [| | pv1 pq1 k1 D1 ΦD1 | |]; cbn in Hgr; try discriminate; destruct Hgr as (<- & <- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed as [| | ? ? ? ? ? ? ? Mk pm Tm Φm HMk Hpm Hlm | |]; subst.
    destruct HE0 as (_ & [HaU HU] & _).
    destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
    destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeΘ) as [_ Hml].
    destruct (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hml) as [Hmp _ Hlt].
    pose proof (ind_mlookup_group _ _ Hg _ _ _ _ Hml) as Hl.
    pose proof (decl_closed_uparams _ (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl)) as HsU.
    (* the module, stored at the type's path over the uniform parameters *)
    pose proof (loc_child_ind _ _ Hg _ _ _ _ _ _ _ _ _ Hloc' Hent1) as Hbm.
    rewrite Hmp in Hpm; injection Hpm as <-.
    rewrite (gc_loc_of_loc _ _ Hg _ _ _ (or_intror Hbm)) in Hlm; injection Hlm as <- <-.
    assert (HargsU : args_ok Θ Ξ (Θ' ++ Γ) (ind_uparams D) Ns) by (rewrite HΔ0; apply args_ok_ext; exact Hargs).
    destruct (desc_ok_ind_former_at _ _ Hg Hv _ _ _ _ _ _ (qname_in p y) (ind_uparams D) ΦD1 Hl HMk Hlt HΘ' HargsU)
      as (R1 & HR1 & Hok1).
    { econstructor; [ exact Hg | apply gc_sub_refl | right; exact Hbm | exact HaU | exact HsU | exact HU | exact HΘ'
                    | exact HargsU | constructor ]. }
    rewrite Hats in HR1; injection HR1 as <-.
    unfold ind_former_desc in Hats; cbn [ds_ats_read] in Hats; ds_dm_read_shape Hats.
    rewrite ds_named_fix by reflexivity; exact Hok1.
  - (* a definition with a module part: its term part at the arguments,
       as a transparent definition's, and its module part at them *)
    cbn in Hgr; subst E1.
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    cbn [List.app] in *.
    cbn [ge_valid syn_V] in HE0; destruct HE0 as [[_ [HΔ Hcl]] (A0 & -> & [i HA0] & HM0)].
    destruct (HM0 _ eq_refl) as (M0 & -> & HM0').
    destruct HcE0 as (_ & Δ0 & E0' & HΔ0 & HaΔ0); injection HΔ0 as HΔ0 HE0'; subst.
    destruct HcE as (HsA & HsM & HsU).
    rewrite gunit_scoped_mk in HsU; destruct HsU as [HsΔ HsE]; cbn [moddef_scoped] in HsE; rewrite Nat.add_0_r in HsE.
    (* the module part, as an alias's *)
    pose proof (ctx_app_wf_tail _ _ _ _ HΘ') as HΓ.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ HΓ) as HΔΓ.
    match goal with Hm : mdenote _ _ _ ?E' ?R1, Hmd : ds_mod ?R1 = Some ?R1m |- _ =>
      destruct (proj2 (Hcl _ HΔΓ) _ Hm) as [Hok1 _];
      pose proof (desc_ok_mod _ _ Hg _ _ _ Hok1 Hmd) as Hok1m;
      pose proof (proj1 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ Hm _
                    (slots_ok_app _ 0 _ ltac:(intros ? ? ?; lia) ltac:(exact HsΔ)) ltac:(rewrite Nat.add_0_r; exact HsE)) as HsR1;
      rewrite Nat.add_0_r in HsR1;
      pose proof (ds_mod_scoped _ _ _ HsR1 Hmd) as HsR1m end.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HTΘ)) as HΔΘ.
    pose proof (desc_ok_tele_weaken _ _ Hg _ Θ' _ _ HsΔ HΔΓ HΔΘ HsR1m Hok1m) as Hok2.
    assert (HaΔ : tele_ass (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
    pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) (Δ0 ++ T) _ HΔΘ HaΔ (args_ok_length _ _ _ _ _ Hargs') (args_ok_insts _ _ _ _ _ Hargs') Hok2) as (R2 & HR2 & Hok3).
    (* the term part: as a transparent definition, at the arguments *)
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) T (ds_term A0 (Some M0)) HTΘ Ha (args_ok_length _ _ _ _ _ Hargs)
                (args_ok_insts _ _ _ _ _ Hargs)) as (R3 & HR3 & Hok4).
    { constructor; [ exists i; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΘ)
                   | intros M1 [= <-]; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT HM0' HTΘ) ]. }
    cbn [ds_up option_map] in HR3.
    destruct (ds_ats_some_red _ _ _ _ HR3) as (B & M' & ->).
    cbn [ds_ats_read] in Hats; rewrite (ds_ats_tm_of_ats _ _ _ HR3), HR2 in Hats; cbv beta iota in Hats; injection Hats as <-.
    rewrite ds_named_fix by reflexivity.
    inversion Hok4 as [? ? ? HBt HMB | | |]; subst.
    rewrite <- (ds_up_nil R2).
    econstructor; [ exact HΘ' | constructor | exact HBt | exact (HMB _ eq_refl) | exact Hok3 ].
  - (* a record type, stored at its own path: its type former at the
       arguments, with its module there *)
    destruct E1 as [| ? [? [? ?| ?]] | | | pv1 pr1 Rr1 ΦR1]; cbn in Hgr; try discriminate; try contradiction.
    destruct Hgr as (<- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed as [| | | | ? ? ? ? ? ? Tm Φm Hlm]; subst.
    pose proof (gc_entry_record_selfpath _ _ Hg _ _ _ _ _ HeΘ) as ->.
    destruct HE0 as (_ & [HaU HU] & _).
    destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
    destruct HcE as ((HF & _) & _).
    assert (Hrl : record_lookup Θ Ξ (qname_in p y) = Some Rr)
      by (unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ HeΘ), HeΘ; reflexivity).
    (* the module, stored at the type's path over its module telescope *)
    pose proof (loc_child_record _ _ Hg _ _ _ _ _ _ _ _ Hloc' Hent1) as Hbm.
    rewrite (gc_loc_of_loc _ _ Hg _ _ _ (or_intror Hbm)) in Hlm; injection Hlm as <- <-.
    assert (HargsP : args_ok Θ Ξ (Θ' ++ Γ) (record_params Rr) Ns) by (rewrite HΔ0; apply args_ok_ext; exact Hargs).
    destruct (desc_ok_record_former_at _ _ Hg Hv _ _ _ _ (qname_in p y) (record_mod_tele (qname_in p y) Rr) ΦR1 Hrl HΘ' HargsP)
      as (R1 & HR1 & Hok1).
    { econstructor; [ exact Hg | apply gc_sub_refl | right; exact Hbm | exact HaU
                    | exact (record_mod_tele_scoped _ _ (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)))
                    | exact HU | exact HΘ' | | constructor ].
      unfold record_mod_tele; rewrite HΔ0.
      exact (args_ok_ext _ _ _ _ _ (ce_ass (record_self (qname_in p y) Rr) :: Δ0) Hargs). }
    rewrite Hats in HR1; injection HR1 as <-.
    unfold record_former_desc in Hats; cbn [ds_ats_read] in Hats; ds_dm_read_shape Hats.
    rewrite ds_named_fix by reflexivity; exact Hok1.
Qed.

(** ** Well-formed Module Expressions Denote Typed Descriptions *)


(** The unit of each slot of [Γ] (of a module or of a definition with a
    module part) denotes, where it stands, only typed descriptions. *)
Definition slots_typed (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  forall Γ1 e U Γ0, Γ = Γ1 ++ e :: Γ0 -> centry_unit e = Some U ->
    forall R, udenote Θ Ξ Γ0 None U R -> desc_ok Θ Ξ Γ0 R.

Lemma slots_typed_nil : forall Θ Ξ, slots_typed Θ Ξ nil.
Proof. intros * Γ1 e U Γ0 Heq; destruct Γ1; discriminate. Qed.

Lemma slots_typed_cons : forall Θ Ξ Γ e, slots_typed Θ Ξ Γ ->
    (forall U, centry_unit e = Some U -> forall R, udenote Θ Ξ Γ None U R -> desc_ok Θ Ξ Γ R) -> slots_typed Θ Ξ (e :: Γ).
Proof.
  intros * HΓ He Γ1 e0 U Γ0 Heq Hu R HR.
  destruct Γ1 as [| e' Γ1]; cbn in Heq; injection Heq as Heq1 Heq2; subst.
  - exact (He _ Hu _ HR).
  - exact (HΓ _ _ _ _ eq_refl Hu _ HR).
Qed.

Lemma slots_typed_app : forall Θ Ξ Ψ Γ, slots_typed Θ Ξ (Ψ ++ Γ) -> slots_typed Θ Ξ Γ.
Proof.
  intros * HΓ Γ1 e U Γ0 -> Hu R HR; apply (HΓ (Ψ ++ Γ1) e U Γ0); [ rewrite <- List.app_assoc; reflexivity | exact Hu | exact HR ].
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
  intros Θ Ξ Hg; induction 1 as [U Γ | U A M Γ | Γ n U e Hl IH]; intros HΓ Hs.
  - destruct (ctx_decomp_mod HΓ) as [HΓ0 HU].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R0 HR0] & _).
    destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (_ & HUs & _).
    eapply desc_ok_shift; [ exact Hg | exact HΓ | exact HUs | exact HR0 | exact (Hs nil _ U Γ eq_refl eq_refl _ HR0) ].
  - destruct (ctx_decomp_dm HΓ) as (HΓ0 & _ & _ & HU).
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R0 HR0] & _).
    destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (_ & HUs & _).
    eapply desc_ok_shift; [ exact Hg | exact HΓ | exact HUs | exact HR0 | exact (Hs nil _ U Γ eq_refl eq_refl _ HR0) ].
  - pose proof (ctx_decomp_tail HΓ) as HΓ0.
    destruct (proj1 denote_exists _ _ _ HΓ0 _ _ Hl) as [R0 HR0].
    pose proof (ctx_scoped_lookup_mod _ _ _ 0 (wf_ctx_scoped _ _ _ HΓ0) Hl) as HUs; rewrite Nat.add_0_r in HUs.
    eapply desc_ok_shift; [ exact Hg | exact HΓ | exact HUs | exact HR0 |].
    exact (IH HΓ0 (slots_typed_app _ _ (e :: nil) _ Hs) _ HR0).
Qed.

(** A stored location, at no argument. *)
Lemma desc_ok_loc : forall Θ Ξ Γ p T Φ, ⊢ Θ ⍮ Ξ ⍮ Γ -> valid_syn Θ Ξ -> loc Θ Ξ p T Φ ->
    desc_ok Θ Ξ Γ (ds_closed nil p T Φ nil).
Proof.
  intros * HΓ Hv Hl.
  destruct (loc_valid _ _ _ _ _ Hv Hl) as [[Ha HT] _].
  econstructor; [ exact (ctx_wf_gctx _ _ _ HΓ) | apply gc_sub_refl | exact Hl | exact Ha | exact (wf_ctx_scoped _ _ _ HT) | exact HT | exact HΓ | | constructor ].
  exists T nil; [ rewrite List.app_nil_r; reflexivity | reflexivity | constructor | constructor | exact HΓ |].
  intros k ? ? Hk; rewrite List.nth_error_nil in Hk; discriminate.
Qed.

(** A loaded unit or an open frame, at no argument. *)
Lemma desc_ok_unit : forall Θ Ξ Γ H p T Φ, ⊢ Θ ⍮ Ξ ⍮ Γ -> valid_syn Θ Ξ -> mod_qname H = Some p ->
    gc_unit Θ Ξ H = Some (T, Φ) -> desc_ok Θ Ξ Γ (ds_closed nil p T Φ nil).
Proof.
  intros * HΓ Hv Hq Hu.
  destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq' & Hl); rewrite Hq in Hq'; injection Hq' as <-.
  exact (desc_ok_loc _ _ _ _ _ _ HΓ Hv Hl).
Qed.

(** A member of a module of typed descriptions. *)
Lemma desc_ok_mem : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ H y R,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> (forall R0, mdenote Θ Ξ Γ H R0 -> desc_ok Θ Ξ Γ R0) ->
    mdenote Θ Ξ Γ (me_mem H y) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * Hg Hv * HΓ HH Hm; inversion Hm; subst.
  - eapply desc_ok_unit; eassumption.
  - (* the open frame of a member's module: the member's type former, with
       its module *)
    match goal with Hk0 : gs_find_ind _ _ = Some _ |- _ => rename Hk0 into Hk end.
    match goal with Hm0 : ind_member _ _ = Some _ |- _ => rename Hm0 into HMk end.
    match goal with Hl0 : gc_loc _ _ _ = Some _ |- _ => rename Hl0 into Hlm end.
    destruct (frame_ind_selfpath _ _ Hg _ _ _ _ Hk) as [_ _ Hlt].
    pose proof (frame_ind_lookup _ _ Hg _ _ _ _ Hk) as Hl.
    destruct (desc_ok_ind_former_at _ _ Hg Hv Γ _ _ _ _ nil _ _ _ Hl HMk Hlt HΓ (args_ok_nil _ _ _ _ HΓ)
                (desc_ok_loc _ _ _ _ _ _ HΓ Hv (gc_loc_loc _ _ _ _ _ Hlm))) as (R1 & HR1 & Hok1).
    rewrite ds_ats_read_nil in HR1; injection HR1 as <-; exact Hok1.
  - match goal with Hm0 : mdenote _ _ _ H ?R0, Hd : ds_mod ?R0 = Some ?Rm, He : ds_entry ?Rm _ = Some _ |- _ =>
      pose proof (desc_ok_mod _ _ Hg _ _ _ (HH _ Hm0) Hd) as Hok;
      destruct Rm; cbn in He; try discriminate
    end.
    + eapply desc_ok_entry_open; eassumption.
    + eapply desc_ok_entry_closed; eassumption.
  - (* the open frame of a record's module: the record's type former, with
       its module *)
    match goal with Hk0 : gs_find_record _ _ = Some _ |- _ => rename Hk0 into Hk end.
    match goal with Hl0 : gc_loc _ _ _ = Some _ |- _ => rename Hl0 into Hlm end.
    assert (Hrl : record_lookup Θ Ξ p = Some R0) by (unfold record_lookup; rewrite Hk; reflexivity).
    destruct (desc_ok_record_former_at _ _ Hg Hv Γ _ _ nil _ _ _ Hrl HΓ (args_ok_nil _ _ _ _ HΓ)
                (desc_ok_loc _ _ _ _ _ _ HΓ Hv (gc_loc_loc _ _ _ _ _ Hlm))) as (R1 & HR1 & Hok1).
    rewrite ds_ats_read_nil in HR1; injection HR1 as <-; exact Hok1.
Qed.

(** What a path denotes is typed. *)
Lemma desc_ok_qname : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ ->
    forall p R, mdenote Θ Ξ Γ (qname_mod p) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * Hg Hv * HΓ [u ch]; induction ch as [| y ch IH] using List.rev_ind; intros R HR.
  - (* a loaded unit or an open frame; a unit is the module of no member *)
    unfold qname_mod in HR; cbn in HR.
    inversion HR; subst; try (eapply desc_ok_unit; eassumption); exfalso;
      first [ match goal with Hk : gs_find_ind _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
                cbn in Hq; injection Hq as <-; destruct (frame_ind_parent _ _ Hg _ _ Hk) as ([? cq] & ? & Hp) end
            | match goal with Hk : gs_find_record _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
                cbn in Hq; injection Hq as <-; destruct (frame_record_parent _ _ Hg _ _ Hk) as ([? cq] & ? & Hp) end ];
      unfold qname_in in Hp; cbn in Hp; injection Hp as _ Hc; destruct cq; discriminate.
  - change {| q_unit := u; q_chain := ch ++ y :: nil |} with (qname_in {| q_unit := u; q_chain := ch |} y) in HR.
    rewrite qname_mod_in in HR.
    exact (desc_ok_mem _ _ Hg Hv _ _ _ _ HΓ IH HR).
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
    destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in HE |- *; try contradiction; destruct_all; auto.
  - destruct Hs as [Hs _]; split; [ exact (IH _ Hs) | reflexivity ].
Qed.

Lemma body_shape_r : forall Φ Φ', body_shape Φ Φ' -> body_shape Φ' Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros [| Φ' x' E' | Φ' H' its'] Hs; cbn in Hs |- *; try contradiction; [ exact I | |].
  - destruct Hs as (Hs & _ & HE); split; [ exact (IH _ Hs) | split; [ reflexivity |] ].
    destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in HE |- *; try contradiction; destruct_all; auto.
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
  - intros y Φ0 E U Hp HE R0 HR0.
    destruct (gm_prefix_body_ctx _ _ _ (body_xp_result_noopen _ _ _ _ _ Hx) Hp) as (Ψ & HΨ).
    destruct E; cbn in HE; try discriminate; injection HE as ->;
      [ apply (Hs Ψ (ce_mod U) U (body_ctx Φ0 ++ Δ ++ Γ)) | eapply (Hs Ψ (ce_dm _ _ U) U (body_ctx Φ0 ++ Δ ++ Γ)) ];
      first [ rewrite HΨ; cbn [body_ctx]; rewrite <- !List.app_assoc; reflexivity | reflexivity | exact HR0 ].
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
    exists T1, ds_mtele (ds_up (ce_ass X :: nil) R2) = Some (T1 ++ ce_ass X :: nil).
Proof.
  intros * Hm Hok; destruct R2 as [| Δ Φ | Θ' p T Φ Ns |]; cbn in Hm; try contradiction.
  - exists Δ; reflexivity.
  - inversion Hok as [| | Γ0 Θa T0 Φ1 Ns0 Θ0 Ξ0 p0 Hg0 Hsub Hloc Ha HsT HT HΘ' Hargs |]; subst.
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
  { intros R HR; inversion HR; subst; try (unfold gc_unit in *; cbn in *; discriminate).
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
    module part itself, or the type former it is the module of. *)
Lemma ds_unit_desc_ok : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ -> forall Γ Rm, desc_ok Θ Ξ Γ Rm -> ds_canon Θ Ξ Rm -> ds_is_mod Rm ->
    ds_xp Θ Ξ Γ Rm -> forall R, mdenote Θ Ξ Γ (ds_unit Rm) R -> desc_ok Θ Ξ Γ R.
Proof.
  intros Θ Ξ Hg Hv * Hok Hc Hm Hxp R HR.
  pose proof (proj1 (mdenote_functional_all _ _ Hg)) as Hf.
  destruct Rm as [A om | Δ Φw Φ | [| e Θ'] p T Φ Ns | ]; cbn in Hm, Hc, Hxp, HR; try contradiction.
  - inversion HR; subst; try (cbn in *; discriminate); match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hx : body_xp _ _ _ Φw ?Φx, Hb : ds_body _ _ _ _ _ = Some _ |- _ =>
      rewrite <- (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hxp _ Hx) in Hb; cbn in Hb; injection Hb as <- end.
    exact Hok.
  - destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hc) as (R1 & Hm1 & [-> | (A & M & ->)]).
    + pose proof (mdenote_apps _ _ _ _ _ _ _ Hm1 (ds_ats_closed_nil Ns p T Φ nil)) as Hm2.
      rewrite (Hf _ _ _ HR _ Hm2); exact Hok.
    + (* the module of a type former: at no argument the type former, at
         some only the module part *)
      destruct Ns as [| N Ns].
      * assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (inversion Hok; subst; assumption).
        exact (desc_ok_qname _ _ Hg Hv _ HΓ _ _ HR).
      * pose proof (mdenote_apps _ _ _ _ _ _ _ Hm1
                      (eq_trans (ds_ats_dm_nil (N :: Ns) A M _ ltac:(discriminate)) (ds_ats_closed_nil (N :: Ns) p T Φ nil))) as Hm2.
        rewrite (Hf _ _ _ HR _ Hm2); exact Hok.
  - inversion HR; subst; try (cbn in *; discriminate); match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    destruct (filed_denote _ _ Hg _ _ _ ((e :: Θ') ++ Γ) Ns (gc_loc_of_loc _ _ Hg _ _ _ Hc)) as (R2 & HR2 & HR2m).
    match goal with Hm0 : mdenote _ _ _ _ ?R0, Hd : ds_mod ?R0 = Some _ |- _ =>
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
        intros R1 HR1; inversion HR1; subst; try (unfold gc_unit in *; cbn in *; discriminate); auto
      | pose proof (udenote_abs _ _ _ _ _ _ HR0) as Habs; cbn [gunit_abs] in Habs;
        rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HR _ Habs);
        apply desc_ok_up; [ exact (IH _ HR0) | exact HΔ | exact Ha ] ]
    end.
  - (* a loaded unit or an open frame; a unit is the module of no member *)
    split; intros R0 HR0; inversion HR0; subst;
      [ eapply desc_ok_unit; eassumption | exfalso | exfalso | eapply desc_ok_unit; eassumption | exfalso | exfalso ];
      first [ match goal with Hk : gs_find_ind _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
                cbn in Hq; injection Hq as <-; destruct (frame_ind_parent _ _ Hg _ _ Hk) as ([? cq] & ? & Hp) end
            | match goal with Hk : gs_find_record _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
                cbn in Hq; injection Hq as <-; destruct (frame_record_parent _ _ Hg _ _ Hk) as ([? cq] & ? & Hp) end ];
      unfold qname_in in Hp; cbn in Hp; injection Hp as _ Hc; destruct cq; discriminate.
  - (* a slot *)
    split; intros R HR; inversion HR; subst; try (cbn in *; discriminate); first [ eapply desc_ok_unit; eassumption |
      match goal with Hl : ctx_lookup_mod _ ?U0 _, HU : udenote _ _ _ _ ?U0 _ |- _ =>
        exact (slots_typed_lookup _ _ Hg _ _ _ Hl H H0 _ HU) end ].
  - (* a literal *)
    pose proof (presup_unit_eq_ctx H).
    split; intros R HR; inversion HR; subst; try (cbn in *; discriminate); first [ eapply desc_ok_unit; eassumption | auto ].
  - (* a member *)
    pose proof (presup_modexp_eq_ctx H0).
    split; intros R0 HR0; [ exact (desc_ok_mem _ _ Hg H6 _ _ _ _ H9 H7 HR0) | exact (desc_ok_mem _ _ Hg H6 _ _ _ _ H9 H8 HR0) ].
  - (* an application *)
    pose proof (presup_modexp_eq_ctx H0).
    split; intros R0 HR0; inversion HR0; subst;
      [ eapply desc_ok_unit; eassumption | cbn in *; discriminate | | cbn in *; discriminate
      | eapply desc_ok_unit; eassumption | cbn in *; discriminate | | cbn in *; discriminate ].
    + match goal with Hm : mdenote _ _ _ H ?R1, Ha : ds_at ?R1 _ = Some _ |- _ =>
        rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ H2) in Ha;
        exact (desc_ok_at _ _ Hg _ _ _ _ _ _ _ (H19 _ H2) H3 H4 H7 Ha) end.
    + match goal with Hm : mdenote _ _ _ H' ?R1, Ha : ds_at ?R1 _ = Some _ |- _ =>
        rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ H11) in Ha;
        exact (desc_ok_at _ _ Hg _ _ _ _ _ _ _ (H20 _ H11) H12 H13 H16 Ha) end.
  - (* a slot is its unit *)
    split; intros R HR; inversion HR; subst; try (cbn in *; discriminate); first [ eapply desc_ok_unit; eassumption |
      match goal with Hl : ctx_lookup_mod _ ?U0 _, HU : udenote _ _ _ _ ?U0 _ |- _ =>
        exact (slots_typed_lookup _ _ Hg _ _ _ Hl H H0 _ HU) end
      | match goal with HU : udenote _ _ _ _ _ _, Hl : ctx_lookup_mod _ _ _ |- _ =>
        exact (slots_typed_lookup _ _ Hg _ _ _ Hl H H0 _ HU) end ].
  - (* a selection is the unit its module part stands for *)
    split; [ assumption |].
    match goal with Hm : mdenote _ _ _ (me_mem _ _) ?R, Hd : ds_mod ?R = Some _,
      IH : forall R, mdenote _ _ _ (me_mem _ _) R -> desc_ok _ _ _ R,
      HH : wf_modexp_eq _ _ _ (me_mem _ _) (me_mem _ _) |- _ =>
      intros R' HR'; eapply ds_unit_desc_ok; [ exact Hg | assumption | exact (desc_ok_mod _ _ Hg _ _ _ (IH _ Hm) Hd)
        | exact (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hd) | exact (ds_mod_is_mod _ _ Hd)
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

(** The term part of a typed description is of a type, and its δ-reduct of
    that type. *)
Lemma desc_ok_ty : forall Θ Ξ, valid_syn Θ Ξ -> forall Γ R A, desc_ok Θ Ξ Γ R -> ds_ty R = Some A ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) /\ (forall M, ds_red R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A).
Proof.
  intros * Hv * HR HA.
  destruct HR as [Γ A0 om HA0 HM | | | Γ Θd A0 M0 Rm HΘd HaΘd [i HBt] HMt _];
    cbn in HA |- *; try discriminate.
  - injection HA as <-; split; [ exact HA0 | exact HM ].
  - (* a definition with a module part, or a type former: its term part *)
    injection HA as <-.
    split; [ exact (ctx_pi_wf _ _ _ _ _ _ HΘd HBt) | intros M [= <-]; exact (ctx_fn_wf _ _ _ _ _ _ _ HΘd HBt HMt) ].
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
  intros * Hok; inversion Hok; subst;
    first [ match goal with HA : exists i, _ |- _ => destruct HA as [i HA]; exact (presup_exp_ctx HA) end
          | eapply ctx_app_wf_tail; eassumption
          | eapply ctx_app_wf_tail; eapply ctx_app_wf_tail; eassumption ].
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




(** ** A Filed Member at Arguments is Typed *)

Lemma ds_ty_up : forall Δ R A, ds_ty R = Some A -> ds_ty (ds_up Δ R) = Some (ctx_pi Δ A).
Proof.
  intros * Ht; destruct R as [A0 om | | | Θd A0 M0 Rm]; cbn in *; try discriminate.
  - injection Ht as <-; reflexivity.
  - injection Ht as <-; rewrite ctx_pi_app; reflexivity.
Qed.

(** A term of the type a description abstracted over [Δa] has, applied to
    arguments for the outermost parameters of [Δa], is of the type the
    description at the arguments has. *)
Lemma ats_up_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa R A0 M,
    ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> tele_ass Δa -> length Ns <= length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    ds_ty R = Some A0 -> (exists i, Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ A0 : Typeω@i) -> Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δa A0 ->
    exists R' A', ds_ats (ds_up Δa R) Ns = Some R' /\ ds_ty R' = Some A' /\ Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns : A'.
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
    + apply ds_ty_sub; exact Ht.
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
Lemma wf_ind_args_gen : forall Θ Ξ Γ D k Mk Ns M,
    decl_typed Θ Ξ D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ -> args_ok Θ Ξ Γ (ind_uparams D) Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_ty_at D Mk nil -> Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns : ind_ty_at D Mk Ns.
Proof.
  intros * HD Hk HΓ [T1 T2 HT Hlen Ha Hs HT2 HN] HM0.
  destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([i Hi] & _).
  pose proof (member_params_wf _ _ _ _ _ HD Hk) as HP.
  assert (Hp : im_params D Mk = (im_nparams Mk ++ T1) ++ T2) by (unfold im_params; rewrite HT, List.app_assoc; reflexivity).
  rewrite Hp in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : ind_ty_at D Mk Ns = (ctx_pi (im_nparams Mk ++ T1) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[sb_of_list Id Ns]).
  { unfold ind_ty_at; rewrite <- length_im_params, Hp.
    replace (length ((im_nparams Mk ++ T1) ++ T2) - length Ns) with (length (im_nparams Mk ++ T1))
      by (rewrite !List.length_app in *; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi T2 (ctx_pi (im_nparams Mk ++ T1) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)).
  { rewrite <- ctx_pi_app, <- Hp.
    unfold ind_ty_at in HM0; rewrite <- length_im_params, Nat.sub_0_r, List.firstn_all in HM0; cbn [sb_of_list List.length] in HM0.
    rewrite exp_sub_id in HM0; exact HM0. }
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha HT2 (eq_sym Hlen) HN) as Hσ.
  rewrite Hat; eapply wf_apps_ctx_pi; [ exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

Lemma ds_ats_term_none : forall Ns A om R1, ds_ats (ds_term A om) Ns = Some R1 ->
    exists R1', ds_ats (ds_term A None) Ns = Some R1' /\ ds_ty R1' = ds_ty R1.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha |- *; [ injection Ha as <-; eexists; split; reflexivity |].
  destruct (pi_view A) as [[X C] |]; [| discriminate ].
  destruct om as [M |]; [ destruct (fn_view M) as [M' |]; [| discriminate ] |]; exact (IH _ _ _ Ha).
Qed.




(** ** Typed Descriptions Grow with the Global Context *)

Lemma args_ok_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ T Ns, Emb Θ1 Ξ1 Θ2 Ξ2 -> args_ok Θ1 Ξ1 Γ T Ns -> args_ok Θ2 Ξ2 Γ T Ns.
Proof.
  intros * He [T1 T2 HT Hl Ha Hs HT2 HN].
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _).
  exists T1 T2; [ exact HT | exact Hl | exact Ha | exact Hs | exact (Hc _ HT2) | intros; apply Ht; eauto ].
Qed.

(** What a description grows into, read at a bigger global context, is
    typed there. *)
Lemma desc_ok_grow : forall Θ1 Ξ1 Θ2 Ξ2, ⊢ᵍ Θ1 ⍮ Ξ1 -> Emb Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ R1, desc_ok Θ1 Ξ1 Γ R1 -> forall R2, dsg Θ1 Ξ1 Θ2 Ξ2 R1 R2 -> desc_ok Θ2 Ξ2 Γ R2.
Proof.
  intros * Hg1 He; pose proof (em_wf _ _ _ _ He) as Hg2; pose proof (em_res _ _ _ _ He) as Hs.
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _ & _ & _ & Hu & _).
  induction 1 as [Γ A om HA HM
                 | Γ Δ Φw Φ HΦ Hn Hent IH HaΔ Hsh Hnd HUw
                 | Γ Θ' T Φ Ns Θ0 Ξ0 p Hg0 Hs0 Hloc Ha Hsc HT HΘ' Hargs HaΘ
                 | Γ Θd A M Rm HΘd HaΘd [i HBt] HMt HRm IH];
    intros R2 Hd.
  4: { (* a definition with a module part, or a type former: its module
          part grows *)
       inversion Hd as [? Hcb | | ? ? ? R1' R2' Hd']; subst.
       - (* reading no closed body *)
         econstructor; [ apply Hc, HΘd | exact HaΘd | exists i; apply Ht, HBt | apply Ht, HMt |].
         apply IH, dsg_same; cbn in Hcb; rewrite ds_closedb_up in Hcb; exact Hcb.
       - destruct (dsg_up_inv _ _ _ _ _ _ _ Hd') as (Rm' & -> & HRm').
         econstructor; [ apply Hc, HΘd | exact HaΘd | exists i; apply Ht, HBt | apply Ht, HMt | exact (IH _ HRm') ]. }
  all: inversion Hd as [? Hcb | Θ'' T' Φ1 Φ2 Ns' p' Hl1 Hl2 |]; subst; try (cbn in Hcb; discriminate).
  - constructor; [ destruct HA as [i HA]; exists i; apply Ht, HA | intros M HM0; apply Ht, HM, HM0 ].
  - constructor; [ apply Hc, HΦ | exact Hn | | exact HaΔ | exact Hsh | exact Hnd | apply Hu, HUw ].
    intros y Φ0 E U Hp HE R HR.
    destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
    rewrite HΨ in HΦ.
    pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ; exact HΦ)) as HΦ0.
    destruct (body_ext_unit_wf _ _ _ _ _ _ _ HΦ0 HE) as [_ HU].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R1 HR1] & _).
    destruct (proj1 (proj2 (mdenote_grow_all _ _ _ _ Hg1 Hg2 Hs)) _ _ _ _ HR1 (or_introl eq_refl)) as (R1' & HR1' & Hd1).
    rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg2)) _ _ _ _ HR _ HR1').
    exact (IH _ _ _ _ Hp HE _ HR1 _ Hd1).
  - econstructor; [ exact Hg2 | apply gc_sub_refl | exact Hl2 | exact Ha | exact Hsc
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
    | Hm : mdenote _ _ _ (me_mem ?H0 _) ?R, Ht : ds_ty ?R = Some _, HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H0 ≈ _ |- _ =>
        exact (proj1 (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht))
    end.
  (* inductive types: the declaration's types are types, and the motive at
     the scrutinee *)
  all: try match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, HΓ : ⊢ _ ⍮ _ ⍮ ?Γ |- _ =>
        pose proof (good_ind _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hv) (proj2 Hv) Hl) as HDt; cbn [syn_VD] in HDt;
        pose proof (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HΓ) Hl) as HDc
    end.
  all: try solve [ eapply ind_ty_typed; eassumption ].
  (* a constructor: its type is a closed type *)
  all: try solve [
    match goal with
    | HM : ind_member ?D ?k = Some ?M, Hcon : ind_con ?M _ = Some _, Hty : _ ⍮ _ ⍮ ⋅ ⊢ con_ty _ ?D ?k ?M _ : _ |- _ =>
        eexists; eapply closed_weaken_exp;
          [ eassumption | exact Hty | eapply decl_closed_con_ty; [ eassumption | exact HM | apply cons_lookup_in; exact Hcon ]
          | exact I ]
    end ].
  (* an elimination: the motive of the member at the scrutinee *)
  all: try solve [
    match goal with
    | Hm : ind_member ?D ?m = Some ?Mm, Hb : nth_error ?Bks ?m = Some ?bm,
      HA : forall k Mk b, ind_member ?D k = Some Mk -> nth_error ?Bks k = Some b -> _ ⍮ _ ⍮ _ ⊢ eb_motive b : _,
      Hx : forall k Mk, ind_member ?D k = Some Mk -> _ ⍮ _ ⍮ _ ⊢ˣ _ ≈ _
      |- exists _, _ ⍮ _ ⍮ _ ⊢ (eb_motive ?bm)[_] : _ =>
        eexists; eapply (sub_preserves_exp _ _ _ _ _ _ _ (HA _ _ _ Hm Hb)); eapply wf_elim_inst_sub;
          [ eassumption | exact Hm | assumption | assumption | assumption | eapply ext_eq_ctx_left; exact (Hx _ _ Hm) ]
    end ].
  (* a record's type former: its type is a closed type *)
  all: try solve [
    match goal with
    | Hl : record_lookup _ _ _ = Some ?R, Hty : _ ⍮ _ ⍮ ⋅ ⊢ record_ty ?R : _, HΓ : ⊢ _ ⍮ _ ⍮ ?Γ |- _ =>
        eexists; eapply closed_weaken_exp;
          [ exact HΓ | exact Hty | apply record_ty_scoped; eapply wf_record_closed; eassumption | exact I ]
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

Lemma syn_valid_here : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> valid_syn Θ Ξ.
Proof. intros * Hg HG; exact (HG _ _ (Embx_refl _ _ Hg) _ _ (gc_sub_refl _ _)). Qed.

Lemma syn_tele_ass : forall Θ Ξ Θ2 Ξ2, GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof.
  intros * HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [_ HΞ].
  destruct Ξ as [| [[mp K] U] Ξ]; [ constructor | exact (proj1 (proj1 HΞ)) ].
Qed.

Lemma syn_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid syn_Vs syn_F syn_VD syn_VR Θ Ξ Θ2 Ξ2 Θ -> gs_valid syn_Vs syn_F syn_VD syn_VR Θ Ξ Θ2 Ξ2 Ξ ->
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
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    syn_V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA _ He _; destruct (emb_preserves_wf _ _ _ _ (Embx_emb _ _ _ _ He)) as (_ & Ht & _).
  exists A; split; [ reflexivity |]; split; [ exists i; apply Ht, HA | discriminate ].
Qed.

(** An alias: what its target denotes, wherever it is read, is typed. *)
Lemma syn_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 (Θs : gdeps) (Ξs : gstack),
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
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
  destruct (dsg_mod _ _ _ _ _ _ _ Hd HR1m) as (R2m & HR2m & _).
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

Lemma syn_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    syn_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HG He.
  split; [ apply List.Forall_app; split; [ exact HΔ | exact (syn_tele_ass _ _ _ _ HG He) ] |].
  exact (proj1 (emb_preserves_wf _ _ _ _ (Embx_emb _ _ _ _ He)) _ HC).
Qed.

Lemma syn_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    syn_VD Θ2 Ξ2 D /\ syn_F Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * HD _ He.
  pose proof (decl_typed_emb _ _ _ _ _ (Embx_emb _ _ _ _ He) HD) as HD2.
  destruct (decl_typed_uparams _ _ _ HD2) as [HU HaU].
  split; [ exact HD2 | split; assumption ].
Qed.

(** A record: its declaration, typed where it is checked, moved along. *)
Lemma syn_record : forall Θ Ξ R Θ2 Ξ2,
    record_typed Θ Ξ R -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> syn_VR Θ2 Ξ2 R.
Proof. intros * HR _ He; exact (record_typed_emb _ _ _ _ _ (Embx_emb _ _ _ _ He) HR). Qed.

(** A record's module telescope, where the record is found: the value's
    type is typed there. *)
Lemma syn_record_tele : forall Θ Ξ p R Θ2 Ξ2,
    record_typed Θ Ξ R -> GoodV syn_Vs syn_F syn_VD syn_VR Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> record_lookup Θ2 Ξ2 p = Some R ->
    syn_F Θ2 Ξ2 (record_params R) -> syn_F Θ2 Ξ2 (record_mod_tele p R).
Proof.
  intros * HR _ He Hl [Ha _]; split; [ constructor; [ eexists; reflexivity | exact Ha ] |].
  exact (record_mod_tele_wf _ _ _ _ (record_typed_emb _ _ _ _ _ (Embx_emb _ _ _ _ He) HR) Hl).
Qed.

(** Everything stored in a well-formed global context is valid there. *)
Theorem gctx_valid_syn : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ.
Proof.
  intros * Hg; apply (syn_valid_here _ _ Hg).
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
           (global_valid_all syn_Vs syn_F syn_VD syn_VR syn_def syn_ax syn_alias syn_nil syn_ind syn_record
              syn_record_tele)))))))))) _ _ Hg).
Qed.

(** A term a well-formed module expression looks up is typed at the type
    the lookup reads: the premises of [wf_mem] on the type and on the
    δ-reduct hold of every description looked up ([mem_desc_ok]).  The
    checker supplies them so, without reading a body again. *)
Corollary wf_mem_desc : forall Θ Ξ Γ H x R A,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty R = Some A ->
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

(** A resolved entry is typed: a definition's type is a closed type, and
    its body, if any, of that type; other entries ask nothing. *)
Definition entry_typed (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Typeω@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod _ _ | ge_ind _ _ _ _ _ | ge_def_mod _ _ _ _ | ge_record _ _ _ _ => True
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
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> GoodM entry_typed decl_typed Θ Ξ mp K Δ Φ) /\
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
  intros * HΓ Hl; destruct (gv_entries _ _ _ _ _ _ (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl) as [[i HA] _].
  exists i; eapply closed_weaken_exp;
    [ assumption | exact HA | eapply wf_gc_resolve_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A (Some M)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hl; destruct (gv_entries _ _ _ _ _ _ (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl) as [_ HM].
  eapply closed_weaken_exp;
    [ assumption | apply HM; reflexivity
    | eapply wf_gc_resolve_body_closed; eassumption
    | eapply wf_gc_resolve_type_closed; eassumption ].
Qed.

(** What a use of a definition with a module part as a term needs: its
    type is a type and its body of that type, in any well-formed
    context. *)
Corollary wf_def_mod_typ : forall Θ Ξ Γ p pv A M U,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ He.
  destruct (gv_def_mods _ _ _ _ _ _ (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ _ _ _ He) as [[i HA] HM].
  destruct (wf_def_mod_closed _ _ _ _ _ _ _ _ HΓ He) as [HsA HsM].
  split.
  - exists i; eapply closed_weaken_exp; [ assumption | exact HA | exact HsA | exact I ].
  - eapply closed_weaken_exp; [ assumption | apply HM; reflexivity | exact HsM | exact HsA ].
Qed.
