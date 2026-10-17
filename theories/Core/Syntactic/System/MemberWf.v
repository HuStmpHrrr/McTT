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
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
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
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Typeω@?i |- _ =>
      eapply wf_ext_eq_ass; [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HA ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Typeω@?i, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A |- _ =>
      eapply wf_ext_eq_def;
        [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HM
        | eapply wf_exp_eq_refl; exact HM | exact HA | exact HM ] end.
  - inversion H; subst.
    match goal with HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_mod; [ apply IH; eauto using presup_unit_eq_ctx | exact HU | exact HU ] end.
Qed.

(** ** The Parts of a Well-Formed Unit *)



Definition unit_parts (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ (md_body sm Φ) =>
      exists Φx, body_xp Θ Ξ (Δ ++ Γ) Φ Φx /\ ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ /\ tele_ass Δ /\ body_shape Φx Φx
  | gu_mk Δ (md_alias E) => ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ /\ tele_ass Δ /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
  end.

(** The parts of a unit of the context after [Δ] are those of the unit
    abstracted over [Δ]. *)
Lemma unit_parts_abs : forall Θ Ξ Γ Δ U, unit_parts Θ Ξ (Δ ++ Γ) U -> tele_ass Δ -> unit_parts Θ Ξ Γ (gunit_abs Δ U).
Proof.
  intros * HU Ha; destruct U as [Δy [sm Φ | E]]; cbn in HU |- *.
  - destruct HU as (Φx & Hx & HC & Hy & Hs); exists Φx; rewrite <- !app_assoc.
    repeat split; try assumption; apply Forall_app; split; assumption.
  - destruct HU as (HC & Hy & HE); rewrite <- !app_assoc; repeat split; try assumption.
    apply Forall_app; split; assumption.
Qed.

Lemma unit_eq_parts : forall Θ Ξ Γ U U',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> unit_parts Θ Ξ Γ U /\ unit_parts Θ Ξ Γ U'.
Proof.
  induction 1; cbn; try solve [ intuition eauto ].
  - match goal with Hs : body_shape Φx Φx' |- _ => destruct (body_shape_refl _ _ Hs) as (Hs1 & Hs2 & _) end.
    match goal with Hx : _ ⍮ _ ⍮ _ ⊢ˣ body_ctx Φx ++ _ ≈ _, Hx' : _ ⍮ _ ⍮ _ ⊢ˣ body_ctx Φx' ++ _ ≈ _ |- _ =>
      pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as Hl; pose proof (ext_eq_ctx_left _ _ _ _ _ Hx') as Hr end.
    rewrite <- app_assoc in Hl, Hr; split; eexists; repeat split; eassumption.
  - pose proof (ext_eq_ctx_left _ _ _ _ _ H) as Hl; pose proof (ext_eq_ctx_right _ _ _ _ _ H) as Hr.
    intuition eauto using wf_modexp_eq_refl_left.
  - (* an alias of a literal, and the literal over both telescopes *)
    split; [ repeat split; [ exact (ext_eq_ctx_left _ _ _ _ _ H) | assumption | apply wf_me_lit; assumption ] |].
    exact (unit_parts_abs _ _ _ _ _ (proj1 IHwf_unit_eq) H0).
Qed.

Corollary unit_parts_of_wf : forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U -> unit_parts Θ Ξ Γ U.
Proof. intros * HU; exact (proj1 (unit_eq_parts _ _ _ _ _ HU)). Qed.

(** The target of each open of a well-formed body is a module where it
    stands. *)
Definition unit_opens (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (U : gunit) : Prop :=
  forall Δ Φ Φx, U = gu_open Δ Φ -> body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
    forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H.

Lemma unit_eq_opens : forall Θ Ξ Γ U U',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> unit_opens Θ Ξ Γ U /\ unit_opens Θ Ξ Γ U'.
Proof.
  induction 1; try solve [ intuition eauto ].
  2: split; intros ? ? ? Heq; discriminate Heq.
  2: { (* an alias of a literal: the literal's opens, under both telescopes *)
    split; intros Δ0 Φ0 Φx0 Heq; [ discriminate Heq |].
    injection Heq as <- ->; intros Hx0 k Ψ Hk0 Hk.
    rewrite <- app_assoc in Hx0 |- *; exact (proj1 IHwf_unit_eq _ _ _ eq_refl Hx0 _ _ _ Hk). }
  match goal with Hc : _ ⍮ _ ⍮ _ ⊢ˣ _ ≈ _ |- _ => pose proof (ctx_wf_gctx _ _ _ (presup_ext_eq_ctx Hc)) as Hg end.
  split; intros Δ0 Φ0 Φx0 Heq Hx0 k Ψ Hk0 Hk; injection Heq as <- <-.
  - match goal with Hx0 : body_xp _ _ _ ?P Φx0, Hx : body_xp _ _ _ ?P ?Φx1, Ho : forall k Ψ H, nth_error (body_opens ?P ?Φx1) k = _ -> _ |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ Hx0); subst Φx0;
      exact (Ho _ _ _ Hk) end.
  - match goal with Hx0 : body_xp _ _ _ ?P Φx0, Hx : body_xp _ _ _ ?P ?Φx1, Ho : forall k Ψ H, nth_error (body_opens ?P ?Φx1) k = _ -> _ |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ Hx0); subst Φx0;
      exact (Ho _ _ _ Hk) end.
Qed.

Corollary unit_opens_of_wf : forall Θ Ξ Γ Δ Φ Φx, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
    forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H.
Proof. intros * HU Hx; exact (proj1 (unit_eq_opens _ _ _ _ _ HU) _ _ _ eq_refl Hx). Qed.

(** A filed definition of a well-formed body has a body. *)
Lemma body_shape_prefix_def : forall Φ x Φ' b pv A B, body_shape Φ Φ ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) -> exists M, B = Some M.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c its]; intros * Hs Hx; cbn in Hx; try discriminate.
  - destruct (String.eqb x y); [ injection Hx; intros; subst; cbn in Hs |].
    + destruct B as [M |]; [ eauto | destruct Hs as (_ & _ & []) ].
    + exact (IH _ _ _ _ _ _ (proj1 Hs) Hx).
  - destruct (existsb _ _); [ discriminate | exact (IH _ _ _ _ _ _ (proj1 Hs) Hx) ].
Qed.

Lemma member_ref_cons : forall H y ch, ch <> nil -> member_ref H (y :: ch) = member_ref (me_mem H y) ch.
Proof. intros * Hne; destruct ch; [ contradiction | reflexivity ]. Qed.

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

(** ** Applied Modules

    A module applied to arguments splits one way into a module that is no
    application and the arguments. *)

Definition me_noapp (H : modexp) : Prop := match H with me_app _ _ => False | _ => True end.

Lemma me_apps_snoc : forall Ns H N, me_apps H (Ns ++ N :: nil) = me_app (me_apps H Ns) N.
Proof. induction Ns as [| N' Ns IH]; intros; cbn; [ reflexivity | apply IH ]. Qed.

(** The head of an inductive alias splits one way: its path, then the
    arguments for the target's telescope, then the rest. *)
Lemma mod_qname_noapp : forall H p, mod_qname H = Some p -> me_noapp H.
Proof. intros [] ? Hq; cbn in *; auto; discriminate. Qed.

Lemma app_split_length : forall (Ms Ks Ms' Ks' : list exp),
    Ms ++ Ks = Ms' ++ Ks' -> List.length Ms = List.length Ms' -> Ms = Ms' /\ Ks = Ks'.
Proof.
  induction Ms as [| M Ms IH]; intros * HL Hl; destruct Ms' as [| M' Ms']; cbn in *; try discriminate; [ auto |].
  injection HL as -> HL; injection Hl as Hl; destruct (IH _ _ _ HL Hl) as [-> ->]; auto.
Qed.

(** A module split into the module it applies and the arguments. *)
Fixpoint me_unapps (H : modexp) : (modexp * list exp)%type :=
  match H with
  | me_app H' N => let (H0, Ns) := me_unapps H' in (H0, Ns ++ N :: nil)
  | _ => (H, nil)
  end.

Lemma me_unapps_spec : forall H, H = me_apps (fst (me_unapps H)) (snd (me_unapps H)) /\ me_noapp (fst (me_unapps H)).
Proof.
  induction H as [| | | H IH N |]; cbn; try (split; [ reflexivity | exact I ]).
  destruct (me_unapps H) as [H0 Ns]; cbn in *; destruct IH as [-> Hn].
  rewrite me_apps_snoc; split; [ reflexivity | exact Hn ].
Qed.

Lemma me_apps_inj : forall Ns Ns' H H', me_noapp H -> me_noapp H' -> me_apps H Ns = me_apps H' Ns' -> H = H' /\ Ns = Ns'.
Proof.
  induction Ns as [| N Ns IH] using rev_ind; intros Ns' * HH HH' Heq;
    destruct Ns' as [| N' Ns' _] using rev_ind; rewrite ?me_apps_snoc in Heq; cbn in Heq.
  - split; [ exact Heq | reflexivity ].
  - subst H; contradiction.
  - subst H'; contradiction.
  - injection Heq as Heq <-; destruct (IH _ _ _ HH HH' Heq) as [-> ->]; split; reflexivity.
Qed.

Lemma apps_snoc : forall args M N, apps M (args ++ N :: nil) = a_app (apps M args) N.
Proof. induction args; intros; cbn; auto. Qed.

(** ** Telescopes of a Valid Global Context *)

Theorem gc_body_tele_wf : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> ⊢ Θ ⍮ Ξ ⍮ T /\ tele_ass T.
Proof.
  intros * Hg * Hb.
  destruct (loc_valid _ _ _ _ _ (gctx_valid_syn _ _ Hg) (or_intror Hb)) as [[Ha HT] _]; split; assumption.
Qed.
