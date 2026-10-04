(** * Well-Formed Parts of Modules

    The parts a well-formed module expression, unit or context is made of are
    well-formed: the unit of a slot, the parts of an equivalence of module
    expressions, an extension read off a context, and the telescopes and alias
    units of a valid global context. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export GlobalModules.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Unit of a Slot *)

Lemma ctx_lookup_mod_wf : forall Θ Ξ Γ x U,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #x ⇒ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * HΓ Hx; induction Hx.
  - destruct (ctx_decomp_mod HΓ) as [HΓ' HU].
    eapply wk_preserves_unit; [ exact HU | apply wf_wk_shift; exact HΓ ].
  - match goal with HΓ : ⊢ _ ⍮ _ ⍮ ?e :: ?G |- _ =>
      assert (⊢ Θ ⍮ Ξ ⍮ G) as HΓ' by (eapply (ctx_app_wf_tail _ _ (e :: nil)); exact HΓ) end.
    eapply wk_preserves_unit; [ eauto | apply wf_wk_shift; exact HΓ ].
Qed.

(** ** An Extension Read off a Context *)

Lemma ext_of_ctx : forall Θ Ξ X Γ, ⊢ Θ ⍮ Ξ ⍮ X ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ X ≈ X.
Proof.
  induction X as [| [A | A M | U] X IH]; intros * H; cbn in H.
  - constructor; exact H.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Type@?i |- _ =>
      eapply wf_ext_eq_ass; [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HA ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Type@?i, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A |- _ =>
      eapply wf_ext_eq_def;
        [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HM
        | eapply wf_exp_eq_refl; exact HM | exact HA | exact HM ] end.
  - inversion H; subst.
    match goal with HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_mod; [ apply IH; eauto using presup_unit_eq_ctx | exact HU | exact HU ] end.
Qed.

(** ** The Parts of an Equivalence of Module Expressions *)

Definition modexp_parts (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) : Prop :=
  match H with
  | me_unit fp => exists T, member_type Θ Ξ Γ (me_unit fp) nil (mr_mod T)
  | me_var x => exists U, Γ ∋ #x ⇒ₘ U
  | me_lit U => Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U
  (** A chain from a unit may be a module whose prefix is an open frame. *)
  | me_mem H y =>
      (Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H /\ exists T, member_type Θ Ξ Γ H (y :: nil) (mr_mod T)) \/
      (mod_qname (me_mem H y) <> None /\ exists T, member_type Θ Ξ Γ (me_mem H y) nil (mr_mod T))
  | me_app H N =>
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H /\
      exists T B T1 i, member_type Θ Ξ Γ H nil (mr_mod T) /\ tele_view T = Some (B, T1) /\
        Θ ⍮ Ξ ⍮ Γ ⊢ B : Type@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : B
  end.

Lemma modexp_eq_parts : forall Θ Ξ Γ H H',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> modexp_parts Θ Ξ Γ H /\ modexp_parts Θ Ξ Γ H'.
Proof.
  induction 1; cbn; try solve [ intuition eauto ].
  - destruct H; cbn in *; try discriminate; [ split; eauto |].
    split; right; split; [ congruence | eauto | congruence | eauto ].
  - split; eauto using wf_unit_eq_refl_left, wf_unit_eq_refl_right.
  - split; left; split; eauto using wf_modexp_eq_refl_left, wf_modexp_eq_refl_right.
  - split; (split; [ eauto using wf_modexp_eq_refl_left, wf_modexp_eq_refl_right |]); do 4 eexists; repeat split; eassumption.
Qed.

Corollary modexp_parts_of_wf : forall Θ Ξ Γ H, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> modexp_parts Θ Ξ Γ H.
Proof. intros * HH; exact (proj1 (modexp_eq_parts _ _ _ _ _ HH)). Qed.

(** ** Telescopes and Alias Units of a Valid Global Context *)

Definition syn_V (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ _ => True
  | ge_mod U => Θ2 ⍮ Ξ2 ⍮ ⋅ ⊢ᵘ U ≈ U
  end.

Definition syn_F (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop :=
  ⊢ Θ2 ⍮ Ξ2 ⍮ T /\ tele_ass T.

Lemma syn_tele : forall Θ Ξ Θ2 Ξ2, GoodV syn_V syn_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof.
  intros * HG He; destruct (HG _ _ He) as [_ HΞ].
  destruct Ξ as [| [mp U] Ξ]; [ constructor | exact (proj2 (proj1 HΞ)) ].
Qed.

Lemma syn_V_alias : forall Θ Ξ Δ E Θ2 Ξ2,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV syn_V syn_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    syn_V Θ2 Ξ2 (gs_tele Ξ) (ge_mod (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * HΔ Hx HE HG He; cbn.
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & _ & _ & _ & Hxe & Hue & Hme).
  pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as HC.
  assert (Ht : tele_ass (Δ ++ gs_tele Ξ)) by (apply Forall_app; split; [ exact HΔ | exact (syn_tele _ _ _ _ HG He) ]).
  apply Hue.
  eapply wf_unit_eq_alias; [ | exact Ht | exact Ht | rewrite app_nil_r; exact HE | rewrite app_nil_r; exact HE ].
  apply ext_of_ctx; rewrite app_nil_r; exact HC.
Qed.

Lemma syn_F_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV syn_V syn_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    syn_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HG He.
  split; [ exact (proj1 (emb_preserves_wf _ _ _ _ He) _ HC) |].
  apply Forall_app; split; [ exact HΔ | exact (syn_tele _ _ _ _ HG He) ].
Qed.

Lemma syn_good : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> GoodV syn_V syn_F Θ Ξ.
Proof.
  apply global_valid; [ intros; exact I | intros; exact I | exact syn_V_alias | exact syn_F_nil ].
Qed.

Theorem gc_body_tele_wf : forall Θ Ξ, ⊢g Θ ⍮ Ξ ->
    forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> ⊢ Θ ⍮ Ξ ⍮ T /\ tele_ass T.
Proof.
  intros * Hg * Hb.
  exact (proj1 (good_body _ _ _ _ _ _ _ _ _ (syn_good _ _ Hg) (Emb_refl _ _ Hg) Hb)).
Qed.

Theorem gc_alias_unit_wf : forall Θ Ξ, ⊢g Θ ⍮ Ξ ->
    forall p U r, gc_module Θ Ξ p = Some (mr_alias U r) -> Θ ⍮ Ξ ⍮ ⋅ ⊢ᵘ U ≈ U.
Proof.
  intros * Hg * Hm.
  destruct (good_alias _ _ _ _ _ _ _ _ _ (syn_good _ _ Hg) (Emb_refl _ _ Hg) Hm) as [T HV]; exact HV.
Qed.

(** ** The Parts of a Well-Formed Unit *)

Lemma body_shape_refl : forall Φ Φ', body_shape Φ Φ' ->
    body_shape Φ Φ /\ body_shape Φ' Φ' /\ gm_names Φ = gm_names Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] H; cbn in H |- *; try contradiction.
  - auto.
  - destruct H as (HΦ & <- & HE); destruct (IH _ HΦ) as (H1 & H2 & H3).
    destruct E as [b pv A [M |] | U], E' as [b' pv' A' [M' |] | U']; cbn in HE |- *; try contradiction;
      intuition congruence.
  - destruct H as (HΦ & Hc); destruct (IH _ HΦ) as (H1 & H2 & H3).
    destruct c as [E ns], c' as [E' ns']; cbn in Hc |- *; intuition congruence.
Qed.

Definition unit_parts (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ (md_body Φ) => ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ /\ tele_ass Δ /\ body_shape Φ Φ
  | gu_mk Δ (md_alias E) => ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ /\ tele_ass Δ /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
  end.

Lemma unit_eq_parts : forall Θ Ξ Γ U U',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> unit_parts Θ Ξ Γ U /\ unit_parts Θ Ξ Γ U'.
Proof.
  induction 1; cbn; try solve [ intuition eauto ].
  - match goal with Hs : body_shape _ _ |- _ => destruct (body_shape_refl _ _ Hs) as (Hs1 & Hs2 & _) end.
    pose proof (ext_eq_ctx_left _ _ _ _ _ H) as Hl; pose proof (ext_eq_ctx_right _ _ _ _ _ H) as Hr.
    rewrite <- app_assoc in Hl, Hr; intuition.
  - pose proof (ext_eq_ctx_left _ _ _ _ _ H) as Hl; pose proof (ext_eq_ctx_right _ _ _ _ _ H) as Hr.
    intuition eauto using wf_modexp_eq_refl_left.
Qed.

Corollary unit_parts_of_wf : forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U -> unit_parts Θ Ξ Γ U.
Proof. intros * HU; exact (proj1 (unit_eq_parts _ _ _ _ _ HU)). Qed.

(** A filed definition of a well-formed body has a body. *)
Lemma body_shape_prefix_def : forall Φ x Φ' b pv A B, body_shape Φ Φ ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) -> exists M, B = Some M.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * Hs Hx; cbn in Hx; try discriminate.
  - destruct (String.eqb x y); [ injection Hx; intros; subst; cbn in Hs |].
    + destruct B as [M |]; [ eauto | destruct Hs as (_ & _ & []) ].
    + exact (IH _ _ _ _ _ _ (proj1 Hs) Hx).
  - exact (IH _ _ _ _ _ _ (proj1 Hs) Hx).
Qed.

(** ** Prefixes of Global Paths

    Resolution goes through body modules only, and the module at a path is
    reached through the modules at its prefixes: body modules up to the first
    alias, which takes the rest of the chain. *)

Lemma gm_submodule_prefix : forall Φ T x ip1 ip2 r,
    gm_submodule T Φ x (ip1 ++ ip2) = Some r ->
    (exists T1, gm_submodule T Φ x ip1 = Some (mr_body T1)) \/
    (exists U r1, gm_submodule T Φ x ip1 = Some (mr_alias U r1) /\ r = mr_alias U (r1 ++ ip2)).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | [Δ [Φ' | E']]]; [ discriminate | |].
  - destruct ip1 as [| z ip1]; [ eauto |].
    exact (IH _ _ _ _ _ _ H).
  - injection H as <-; eauto.
Qed.

Lemma gm_resolve_prefix : forall Φ T x ip1 ip2 E,
    gm_resolve Φ (x :: ip1 ++ ip2) = Some E -> ip2 <> nil ->
    exists T1, gm_submodule T Φ x ip1 = Some (mr_body T1).
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] * H Hne; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H Hne) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H Hne) ].
  destruct (ip1 ++ ip2) as [| w ip] eqn:E12; [ destruct ip1, ip2; try discriminate; contradiction |].
  destruct E0 as [? ? ? ? | [Δ [Φ' | E']]]; try discriminate.
  destruct ip1 as [| z ip1]; [ eauto |].
  cbn in E12; injection E12 as -> E12; rewrite <- E12 in H.
  exact (IH _ _ _ _ _ _ H Hne).
Qed.

Lemma gm_module_prefix : forall T Φ ch1 ch2 r,
    gm_module T Φ (ch1 ++ ch2) = Some r ->
    (exists T1, gm_module T Φ ch1 = Some (mr_body T1)) \/
    (exists U r1, gm_module T Φ ch1 = Some (mr_alias U r1) /\ r = mr_alias U (r1 ++ ch2)).
Proof.
  intros * H; destruct ch1 as [| x ip1]; cbn in H |- *; [ eauto |].
  exact (gm_submodule_prefix _ _ _ _ _ _ H).
Qed.

Lemma gm_resolve_module_prefix : forall T Φ ch1 ch2 E,
    gm_resolve Φ (ch1 ++ ch2) = Some E -> ch2 <> nil ->
    exists T1, gm_module T Φ ch1 = Some (mr_body T1).
Proof.
  intros * H Hne; destruct ch1 as [| x ip1]; cbn in H |- *; [ eauto |].
  exact (gm_resolve_prefix _ _ _ _ _ _ H Hne).
Qed.

(** ** Members Reached by Selection *)

Lemma member_ref_cons : forall H y ch, ch <> nil -> member_ref H (y :: ch) = member_ref (me_mem H y) ch.
Proof. intros * Hne; destruct ch; [ contradiction | reflexivity ]. Qed.

Lemma path_prefix_resolve : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall qp r0 ch1 ch2 E,
    gc_module Θ Ξ qp = Some r0 -> gc_resolve Θ Ξ (qname_app qp (ch1 ++ ch2)) = Some E -> ch2 <> nil ->
    exists T1, gc_module Θ Ξ (qname_app qp ch1) = Some (mr_body T1).
Proof.
  intros * Hg * Hq Hr Hne.
  assert (Hne' : ch1 ++ ch2 <> nil) by (destruct ch1, ch2; cbn; congruence).
  destruct r0 as [T | U r0].
  - destruct (gc_module_body _ _ _ _ Hq) as [Φ HΦ].
    destruct (closed_read _ _ Hg _ _ _ HΦ (ch1 ++ ch2)) as (_ & _ & H3).
    rewrite (H3 Hne') in Hr.
    destruct (gm_resolve_module_prefix T _ _ _ _ Hr Hne) as [T1 HT1].
    exists T1; rewrite (proj1 (closed_read _ _ Hg _ _ _ HΦ ch1)); exact HT1.
  - rewrite (proj2 (gc_module_alias_app _ _ Hg _ _ _ Hq _) Hne') in Hr; discriminate.
Qed.

Lemma path_prefix_module : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall qp r0 ch1 ch2 r,
    gc_module Θ Ξ qp = Some r0 -> gc_module Θ Ξ (qname_app qp (ch1 ++ ch2)) = Some r ->
    (exists T1, gc_module Θ Ξ (qname_app qp ch1) = Some (mr_body T1)) \/
    (exists U r1, gc_module Θ Ξ (qname_app qp ch1) = Some (mr_alias U r1) /\ r = mr_alias U (r1 ++ ch2)).
Proof.
  intros * Hg * Hq Hr.
  destruct r0 as [T | U r0].
  - destruct (gc_module_body _ _ _ _ Hq) as [Φ HΦ].
    rewrite (proj1 (closed_read _ _ Hg _ _ _ HΦ (ch1 ++ ch2))) in Hr.
    rewrite (proj1 (closed_read _ _ Hg _ _ _ HΦ ch1)).
    exact (gm_module_prefix _ _ _ _ _ Hr).
  - rewrite (proj1 (gc_module_alias_app _ _ Hg _ _ _ Hq _)) in Hr; injection Hr as <-.
    right; exists U, (r0 ++ ch1); split; [ exact (proj1 (gc_module_alias_app _ _ Hg _ _ _ Hq _)) | rewrite app_assoc; reflexivity ].
Qed.

(** The body before a member of a well-formed body unit, the member
    included, extends a well-formed context. *)
Lemma body_prefix_wf : forall Θ Ξ Γ Δ Φ x Φx,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ -> gm_prefix_upto Φ x = Some Φx ->
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ.
Proof.
  intros * HC Hx.
  destruct (gm_prefix_upto_body_ctx _ _ _ Hx) as [Ψ HΨ]; rewrite HΨ, <- app_assoc in HC.
  exact (ctx_app_wf_right _ _ _ _ HC).
Qed.

Lemma body_prefix_mod_wf : forall Θ Ξ Γ Δ Φ y Φ' Uy,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ -> gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    Θ ⍮ Ξ ⍮ body_ctx Φ' ++ Δ ++ Γ ⊢ᵘ Uy ≈ Uy.
Proof.
  intros * HC Hx; pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hx) as H; cbn in H.
  exact (proj2 (ctx_decomp_mod H)).
Qed.

Lemma member_ref_mems : forall pre H x, member_ref H (pre ++ x :: nil) = a_mem (me_mems H pre) x.
Proof.
  induction pre as [| y pre IH]; intros; [ reflexivity |].
  cbn [app me_mems]; rewrite member_ref_cons by (destruct pre; discriminate); apply IH.
Qed.

Lemma qname_term_snoc : forall mp x, qname_term (qname_app mp (x :: nil)) = a_mem (qname_mod mp) x.
Proof. intros [fp ms] x; unfold qname_term, qname_mod; cbn; apply member_ref_mems. Qed.

Lemma me_mems_noargs : forall pre H, me_noargs H -> me_noargs (me_mems H pre).
Proof. induction pre; intros; cbn; auto. Qed.

Lemma me_mems_spine : forall pre H R args p0, modexp_spine H = (R, args, p0) ->
    modexp_spine (me_mems H pre) = (R, args, p0 ++ pre).
Proof.
  induction pre as [| y pre IH]; intros * Hs; cbn [me_mems]; [ rewrite app_nil_r; exact Hs |].
  rewrite (IH _ R args (p0 ++ y :: nil)); [ rewrite <- app_assoc; reflexivity |].
  cbn; rewrite Hs; reflexivity.
Qed.

Lemma me_mems_unfold : forall Θ Ξ Γ pre H ch,
    member_unfold_ch Θ Ξ Γ (me_mems H pre) ch = member_unfold_ch Θ Ξ Γ H (pre ++ ch).
Proof. induction pre as [| y pre IH]; intros; cbn [me_mems app]; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma me_mems_member_type_inv : forall Θ Ξ Γ pre H ch R,
    member_type Θ Ξ Γ (me_mems H pre) ch R -> member_type Θ Ξ Γ H (pre ++ ch) R.
Proof.
  induction pre as [| y pre IH]; intros * Hm; cbn [me_mems app] in *; [ exact Hm |].
  apply IH in Hm; inversion Hm; subst; assumption.
Qed.

Corollary mt_path_inv : forall Θ Ξ Γ p ch R,
    member_type Θ Ξ Γ (qname_mod p) ch R -> member_type Θ Ξ Γ (me_unit (q_unit p)) (q_chain p ++ ch) R.
Proof. intros *; apply me_mems_member_type_inv. Qed.

(** A term member of a chain from a unit that resolves to a global has the
    global's type. *)
Lemma mt_glob_type : forall Θ Ξ Γ H mp x A b pv A' B,
    mod_qname H = Some mp -> member_type Θ Ξ Γ H (x :: nil) (mr_term A) ->
    gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def b pv A' B) -> A = A'.
Proof.
  intros * Hp Hm Hr.
  rewrite (mod_qname_inv _ _ Hp) in Hm; apply mt_path_inv in Hm.
  change (qname_app mp (x :: nil)) with (q_abs (q_unit mp) (q_chain mp ++ x :: nil)) in Hr.
  inversion Hm; subst; [ congruence |].
  match goal with Hx : gc_module _ _ _ = Some _ |- _ => rewrite (gc_module_resolve _ _ _ _ Hx) in Hr; discriminate end.
Qed.

Lemma me_mems_member_type : forall Θ Ξ Γ pre H ch R,
    member_type Θ Ξ Γ H (pre ++ ch) R -> (mres_kind R = mk_term -> ch <> nil) ->
    member_type Θ Ξ Γ (me_mems H pre) ch R.
Proof.
  induction pre as [| y pre IH]; intros * Hm Hch; cbn [me_mems app] in *; [ exact Hm |].
  apply IH; [| exact Hch ].
  eapply mt_mem; [ intros Hk; specialize (Hch Hk); destruct pre, ch; cbn; congruence | exact Hm ].
Qed.

Lemma apps_snoc : forall args M N, apps M (args ++ N :: nil) = a_app (apps M args) N.
Proof. induction args; intros; cbn; auto. Qed.
