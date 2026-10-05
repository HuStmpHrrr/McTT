(** * Well-Formed Parts of Modules

    The parts a well-formed module expression, unit or context is made of are
    well-formed: the unit of a slot, the parts of an equivalence of module
    expressions, an extension read off a context, and the entries of a body,
    each in its self context. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Lemmas.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Unit of a Slot *)

Lemma ctx_lookup_mod_wf : forall Θ Γ x U,
    ⊢ Θ ⍮ Γ -> Γ ∋ #x ⇒ₘ U -> Θ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * HΓ Hx; induction Hx.
  - destruct (ctx_decomp_mod HΓ) as [HΓ' HU].
    eapply wk_preserves_unit; [ exact HU | apply wf_wk_shift; exact HΓ ].
  - match goal with HΓ : ⊢ _ ⍮ ?e :: ?G |- _ =>
      assert (⊢ Θ ⍮ G) as HΓ' by (eapply (ctx_app_wf_tail _ (e :: nil)); exact HΓ) end.
    eapply wk_preserves_unit; [ eauto | apply wf_wk_shift; exact HΓ ].
Qed.

(** ** An Extension Read off a Context *)

Lemma ext_of_ctx : forall Θ X Γ, ⊢ Θ ⍮ X ++ Γ -> Θ ⍮ Γ ⊢ˣ X ≈ X.
Proof.
  induction X as [| [A | A M | U] X IH]; intros * H; cbn in H.
  - constructor; exact H.
  - inversion H; subst.
    match goal with HA : _ ⍮ X ++ Γ ⊢ A : Type@?i |- _ =>
      eapply wf_ext_eq_ass; [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HA ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ X ++ Γ ⊢ A : Type@?i, HM : _ ⍮ X ++ Γ ⊢ M : A |- _ =>
      eapply wf_ext_eq_def;
        [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HM
        | eapply wf_exp_eq_refl; exact HM | exact HA | exact HM ] end.
  - inversion H; subst.
    match goal with HU : _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_mod; [ apply IH; eauto using presup_unit_eq_ctx | exact HU | exact HU ] end.
Qed.

(** ** The Parts of an Equivalence of Module Expressions *)

Definition modexp_parts (Θ : gctx) (Γ : ctx) (H : modexp) : Prop :=
  match H with
  | me_unit fp => exists U, gc_unit Θ fp = Some U
  | me_var x => exists U, Γ ∋ #x ⇒ₘ U
  | me_lit U => Θ ⍮ Γ ⊢ᵘ U ≈ U
  | me_mem H y => Θ ⍮ Γ ⊢ᵐ H ≈ H /\ exists T, member_type Θ Γ H (y :: nil) (mr_mod T)
  | me_app H N =>
      Θ ⍮ Γ ⊢ᵐ H ≈ H /\
      exists T B T1 i, member_type Θ Γ H nil (mr_mod T) /\ tele_view T = Some (B, T1) /\
        Θ ⍮ Γ ⊢ B : Type@i /\ Θ ⍮ Γ ⊢ N : B
  end.

Lemma modexp_eq_parts : forall Θ Γ H H',
    Θ ⍮ Γ ⊢ᵐ H ≈ H' -> modexp_parts Θ Γ H /\ modexp_parts Θ Γ H'.
Proof.
  induction 1; cbn; try solve [ intuition eauto ].
  - split; eauto using wf_unit_eq_refl_left, wf_unit_eq_refl_right.
  - split; split; eauto using wf_modexp_eq_refl_left, wf_modexp_eq_refl_right.
  - split; (split; [ eauto using wf_modexp_eq_refl_left, wf_modexp_eq_refl_right |]); do 4 eexists; repeat split; eassumption.
Qed.

Corollary modexp_parts_of_wf : forall Θ Γ H, Θ ⍮ Γ ⊢ᵐ H ≈ H -> modexp_parts Θ Γ H.
Proof. intros * HH; exact (proj1 (modexp_eq_parts _ _ _ _ HH)). Qed.

(** ** The Parts of a Well-Formed Unit

    The entries of a body, each well-formed in its self context: the self
    slot holding the body before it, over the context [Γ0] of the body,
    which is the parameters over the context of the unit.  No local open is
    left in a typed body. *)

Definition entry_ok (Θ : gctx) (Γ : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ A (Some M) => (exists i, Θ ⍮ Γ ⊢ A : Type@i) /\ Θ ⍮ Γ ⊢ M : A
  | ge_def _ _ None => False
  | ge_mod _ U => Θ ⍮ Γ ⊢ᵘ U ≈ U
  end.

Fixpoint body_ok (Θ : gctx) (Γ0 : ctx) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ x E => body_ok Θ Γ0 Φ /\ gm_fresh x Φ /\ entry_ok Θ (self_ent Φ :: Γ0) E
  | gm_open _ _ _ _ => False
  end.

Definition unit_parts (Θ : gctx) (Γ : ctx) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ (md_body Φ) => ⊢ Θ ⍮ Δ ++ Γ /\ tele_ass Δ /\ body_ok Θ (Δ ++ Γ) Φ
  | gu_mk Δ (md_alias E) => ⊢ Θ ⍮ Δ ++ Γ /\ tele_ass Δ /\ Θ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
  end.

(** The units an extension holds, each with its parts at its position. *)
Fixpoint ext_parts (Θ : gctx) (Γ : ctx) (Ψ : ctx) : Prop :=
  match Ψ with
  | nil => True
  | ce_mod U :: Ψ' => ext_parts Θ Γ Ψ' /\ unit_parts Θ (Ψ' ++ Γ) U
  | _ :: Ψ' => ext_parts Θ Γ Ψ'
  end.

Lemma unit_eq_parts_all :
    (forall Θ Γ Ψ Ψ', Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ext_parts Θ Γ Ψ /\ ext_parts Θ Γ Ψ') /\
    (forall Θ Γ U U', Θ ⍮ Γ ⊢ᵘ U ≈ U' -> unit_parts Θ Γ U /\ unit_parts Θ Γ U') /\
    (forall Θ Γ H H', Θ ⍮ Γ ⊢ᵐ H ≈ H' -> True).
Proof.
  apply module_wf_mut_ind; intros; cbn in *; destruct_all; auto.
  - (* parameters only *)
    pose proof (ext_eq_ctx_left _ _ _ _ H) as Hl; pose proof (ext_eq_ctx_right _ _ _ _ H) as Hr.
    repeat split; auto.
  - (* a definition, under the self slot *)
    repeat split; eauto.
  - (* a submodule, under the self slot *)
    repeat split; eauto using wf_unit_eq_refl_left.
  - (* an alias *)
    pose proof (ext_eq_ctx_left _ _ _ _ H) as Hl; pose proof (ext_eq_ctx_right _ _ _ _ H) as Hr.
    repeat split; eauto using wf_modexp_eq_refl_left.
Qed.

Lemma unit_eq_parts : forall Θ Γ U U',
    Θ ⍮ Γ ⊢ᵘ U ≈ U' -> unit_parts Θ Γ U /\ unit_parts Θ Γ U'.
Proof. exact (proj1 (proj2 unit_eq_parts_all)). Qed.

Corollary unit_parts_of_wf : forall Θ Γ U, Θ ⍮ Γ ⊢ᵘ U ≈ U -> unit_parts Θ Γ U.
Proof. intros * HU; exact (proj1 (unit_eq_parts _ _ _ _ HU)). Qed.

(** A body with well-formed parts is well formed, under any well-formed
    parameters; in particular with none, in the context extended by the
    parameters. *)
Lemma unit_of_body_ok : forall Θ Φ Γ Δ,
    Θ ⍮ Γ ⊢ˣ Δ ≈ Δ -> tele_ass Δ -> body_ok Θ (Δ ++ Γ) Φ -> Θ ⍮ Γ ⊢ᵘ gu_body Δ Φ ≈ gu_body Δ Φ.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H oz its]; intros * HΔ Ht HΦ; cbn in HΦ; destruct_all; [ constructor; assumption | | contradiction ].
  assert (HΦ0 : Θ ⍮ Δ ++ Γ ⊢ᵘ gu_body nil Φ ≈ gu_body nil Φ).
  { apply IH; [ constructor; exact (ext_eq_ctx_left _ _ _ _ HΔ) | constructor | rewrite app_nil_l; assumption ]. }
  assert (Hx : Θ ⍮ Γ ⊢ˣ self_ent Φ :: Δ ≈ self_ent Φ :: Δ) by (eapply wf_ext_eq_mod; eassumption).
  destruct E as [pv A [M |] | pv U]; cbn in *; destruct_all; [| contradiction |].
  - eapply wf_unit_eq_def; try eassumption; eauto using wf_exp_eq_refl.
  - eapply wf_unit_eq_mod; eassumption.
Qed.

Corollary self_ctx_wf : forall Θ Γ0 Φ, ⊢ Θ ⍮ Γ0 -> body_ok Θ Γ0 Φ -> ⊢ Θ ⍮ self_ent Φ :: Γ0.
Proof.
  intros * HΓ HΦ; constructor; apply unit_of_body_ok; [ constructor; exact HΓ | constructor | exact HΦ ].
Qed.

(** The body before an entry, and the entry, of a well-formed body. *)
Lemma body_ok_prefix : forall Θ Γ0 Φ x Φ' E,
    body_ok Θ Γ0 Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    body_ok Θ Γ0 Φ' /\ entry_ok Θ (self_ent Φ' :: Γ0) E.
Proof.
  induction Φ as [| Φ IH y E0 | Φ IH H oz its]; intros * HΦ Hp; cbn in *; try discriminate; [| contradiction ].
  destruct_all; destruct (String.eqb x y); [ injection Hp as -> -> ->; auto | eauto ].
Qed.

(** ** Chains of Selections *)

Lemma member_ref_cons : forall H y ch, ch <> nil -> member_ref H (y :: ch) = member_ref (me_mem H y) ch.
Proof. intros * Hne; destruct ch; [ contradiction | reflexivity ]. Qed.

Lemma member_ref_mems : forall pre H x, member_ref H (pre ++ x :: nil) = a_mem (me_mems H pre) x.
Proof.
  induction pre as [| y pre IH]; intros; [ reflexivity |].
  cbn [app me_mems]; rewrite member_ref_cons by (destruct pre; discriminate); apply IH.
Qed.

Lemma me_mems_noargs : forall pre H, me_noargs H -> me_noargs (me_mems H pre).
Proof. induction pre; intros; cbn; auto. Qed.

Lemma me_mems_spine : forall pre H R args p0, modexp_spine H = (R, args, p0) ->
    modexp_spine (me_mems H pre) = (R, args, p0 ++ pre).
Proof.
  induction pre as [| y pre IH]; intros * Hs; cbn [me_mems]; [ rewrite app_nil_r; exact Hs |].
  rewrite (IH _ R args (p0 ++ y :: nil)); [ rewrite <- app_assoc; reflexivity |].
  cbn; rewrite Hs; reflexivity.
Qed.

Lemma me_mems_unfold : forall Θ Γ pre H ch,
    member_unfold_ch Θ Γ (me_mems H pre) ch = member_unfold_ch Θ Γ H (pre ++ ch).
Proof. induction pre as [| y pre IH]; intros; cbn [me_mems app]; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma me_mems_member_type_inv : forall Θ Γ pre H ch R,
    member_type Θ Γ (me_mems H pre) ch R -> member_type Θ Γ H (pre ++ ch) R.
Proof.
  induction pre as [| y pre IH]; intros * Hm; cbn [me_mems app] in *; [ exact Hm |].
  apply IH in Hm; inversion Hm; subst; assumption.
Qed.

Lemma me_mems_member_type : forall Θ Γ pre H ch R,
    member_type Θ Γ H (pre ++ ch) R -> (mres_kind R = mk_term -> ch <> nil) ->
    member_type Θ Γ (me_mems H pre) ch R.
Proof.
  induction pre as [| y pre IH]; intros * Hm Hch; cbn [me_mems app] in *; [ exact Hm |].
  apply IH; [| exact Hch ].
  eapply mt_mem; [ intros Hk; specialize (Hch Hk); destruct pre, ch; cbn; congruence | exact Hm ].
Qed.

Lemma apps_snoc : forall args M N, apps M (args ++ N :: nil) = a_app (apps M args) N.
Proof. induction args; intros; cbn; auto. Qed.
