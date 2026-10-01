(** * Presupposition

    Presupposition is proved for all eleven judgments at once.  A global is used
    at its resolved type without premising that it is a type, and a definition's
    type is not checked separately from its body; that each is a type is what
    presupposition of the *entry's* own derivation gives, and that derivation is
    part of [⊢g], so the induction has to range over the global judgments too.

    What the induction carries for a module is [ins_typed]: each member,
    generalized, well typed in the frame it was inserted into.  That is what
    [Discharge] needs to close a frame, member by member. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Discharge.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Generalizing *)

Lemma ctx_pi_wf : forall Θ Ξ Δ Γ A i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Type@j.
Proof.
  induction Δ as [| B Δ IH]; intros * HΔ HA; cbn in *; [ eauto |].
  inversion HΔ; subst.
  match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Type@?k |- _ =>
    eapply IH; [ eauto using presup_exp_ctx |];
    econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
  end.
Qed.

Lemma ctx_fn_wf : forall Θ Ξ Δ Γ A M i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  induction Δ as [| B Δ IH]; intros * HΔ HA HM; cbn in *; [ assumption |].
  inversion HΔ; subst.
  match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Type@?k |- _ =>
    eapply IH with (i := max k i); [ eauto using presup_exp_ctx | |];
    [ econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
    | econstructor; eassumption ]
  end.
Qed.

Corollary ctx_pi_wf0 : forall Θ Ξ Δ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@j.
Proof.
  intros; eapply ctx_pi_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption ].
Qed.

Corollary ctx_fn_wf0 : forall Θ Ξ Δ A M i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  intros; eapply ctx_fn_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption.. ].
Qed.

(** A closed judgment holds in any context. *)
Lemma closed_weaken_exp : forall Θ Ξ Γ M A cs cs',
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
    exp_scoped 0 cs M -> exp_scoped 0 cs' A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ HM HsM HsA.
  rewrite <- (exp_closed_wk M _ (wk_shiftn (length Γ)) HsM),
    <- (exp_closed_wk A _ (wk_shiftn (length Γ)) HsA).
  eapply wk_preserves_exp; [ exact HM |].
  pose proof (wf_wk_shiftn_app Θ Ξ Γ nil) as Hw; rewrite List.app_nil_r in Hw.
  apply Hw; [ assumption | constructor; eapply ctx_wf_gctx; eassumption ].
Qed.

(** ** Pushing Frames *)


(** ** Parameters *)

Lemma wf_gstack_app : forall Ξa Θ U Ξb, wf_gstack Θ (Ξa ++ U :: Ξb) -> wf_gstack Θ Ξb /\ Θ ⍮ Ξb ⊢u U.
Proof.
  induction Ξa; intros * H; cbn in *; inversion H; subst; eauto.
Qed.

Lemma exp_sub_shift_params : forall (A : exp) L j, A[↑]ʷ[sb_params L (S j)] = A[sb_params L j].
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.

(** A lookup in a telescope is, read as parameters, the type of the parameter it
    finds. *)
Lemma ctx_ptys_lookup : forall L Δ x B,
    Δ ∋ #x : B -> List.nth_error (ctx_ptys L Δ) (length Δ - S x) = Some B[sb_params L (length Δ)].
Proof.
  induction 1; cbn [length].
  - rewrite exp_sub_shift_params, Nat.sub_succ, Nat.sub_0_r; apply ctx_ptys_nth_last.
  - rewrite exp_sub_shift_params, ctx_ptys_nth_old by (apply ctx_lookup_length in H; lia).
    replace (S (length Γ) - S (S n)) with (length Γ - S n) by lia; exact IHctx_lookup.
Qed.

(** A parameter's type is a type wherever the parameter is in scope: a binding
    of its frame's telescope, read as parameters. *)
Lemma wf_param_typ : forall Θ Ξ Γ lp T,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gs_param Ξ lp = Some T ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ T : Type@i.
Proof.
  intros * HΓ Hp; pose proof Hp as Hp0; unfold gs_param in Hp.
  destruct lp as [L j]; cbn [lp_mod lp_param] in Hp.
  destruct (gs_frame Ξ L) as [U |] eqn:Hn; [| discriminate ].
  destruct (gs_frame_split _ _ _ Hn) as (Ξa & Ξb & -> & Hl).
  assert (Hg : ⊢g Θ ⍮ Ξa ++ U :: Ξb) by (eapply ctx_wf_gctx; eassumption).
  destruct (wf_gstack_app _ _ _ _ (wf_gctx_stack _ _ Hg)) as [_ HU].
  inversion HU as [? ? ? HUm Hpt]; subst.
  rewrite Hpt in Hp.
  destruct (ctx_ptys_nth _ _ _ _ Hp) as (Pa & A & Pb & HP & HPb & ->).
  pose proof (wf_gmod_ctx _ _ _ _ HUm) as HPw; rewrite HP in HPw.
  pose proof (ctx_app_wf_right _ _ _ _ HPw) as HAb.
  destruct (ctx_decomp_right HAb) as [i HA].
  assert (Hext : gc_ext Θ Ξb Θ (Ξa ++ U :: Ξb))
    by (pose proof (gc_ext_push Θ (Ξa ++ U :: nil) Ξb) as H; rewrite <- List.app_assoc in H; exact H).
  assert (HbΞ : ⊢ Θ ⍮ Ξa ++ U :: Ξb ⍮ ⋅) by (constructor; assumption).
  destruct (rebase_preserves_wf _ _ _ _ Hext HbΞ) as (_ & He & _).
  pose proof (He _ _ _ HA) as HA'.
  exists i; change (Type@i) with (Type@i[sb_params (length Ξb) j]).
  eapply sub_preserves_exp; [ exact HA' |].
  econstructor; [ assumption | eapply presup_exp_ctx; exact HA' |].
  intros x B Hlk; econstructor; [ assumption |].
  unfold gs_param; cbn [lp_mod lp_param]; rewrite Hn, Hpt, HP.
  destruct (ctx_ptys_app (length Ξb) Pa (A :: Pb)) as [ps ->].
  pose proof (ctx_lookup_length _ _ _ Hlk) as Hx.
  rewrite List.nth_error_app1 by (rewrite ctx_ptys_length; cbn; lia).
  cbn [ctx_ptys]; rewrite List.nth_error_app1 by (rewrite ctx_ptys_length; lia).
  rewrite <- HPb; apply ctx_ptys_lookup; assumption.
Qed.
(** ** Levels *)

Lemma wf_gdep_fresh : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gds_fresh fp Θ.
Proof.
  induction 1; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] |]; eauto.
Qed.

Lemma wf_gdep_lookup : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gd_lookup d fp = Some U.
Proof.
  induction 1 as [| Θ d U fp Hd IH HU Hfr Hfr']; intros fq V Hin; cbn in Hin; [ contradiction |].
  unfold gd_lookup, path_beq in *; cbn.
  destruct Hin as [[= <- <-] | Hin].
  - destruct (path_eq_dec fp fp); [ reflexivity | contradiction ].
  - destruct (path_eq_dec fq fp) as [-> |]; [| eauto ].
    exfalso; apply (Hfr' (List.in_map fst _ _ Hin)).
Qed.

Lemma gd_lookup_app_none : forall d d' fp,
    gd_lookup d fp = None ->
    gd_lookup (d ++ d') fp = gd_lookup d' fp.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; cbn; intros * H; [ reflexivity |].
  destruct (path_beq fp (fst fV)); [ discriminate | auto ].
Qed.

Lemma gds_lookup_level : forall Θ d fp U,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    gds_lookup Θ fp = Some U ->
    gds_lookup (d :: Θ) fp = Some U.
Proof.
  unfold gds_lookup; intros * Hfr Hl; cbn [List.concat].
  destruct (gd_lookup d fp) as [V |] eqn:Hd.
  - apply gd_lookup_in, Hfr, gds_fresh_no_lookup in Hd; unfold gds_lookup in Hd; congruence.
  - rewrite gd_lookup_app_none; assumption.
Qed.

(** ** What Resolution Hands Back is Well Typed *)

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p b pv A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
    (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A).

(** What a module entry carries: a definition is typed where it is checked; a
    nested module is the closing of a module whose members are typed where they
    were inserted. *)
Definition entry_typed (Θ : gdeps) (Ξ : gstack) (x : String.string) (E : gentry) : Prop :=
  match E with
  | ge_def _ pv A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Type@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod Δ Φc =>
      exists Φ, Φc = gm_close (length Ξ) (p_rel (Nat.pred (length Ξ)) (x :: nil)) Δ Φ /\
        Θ ⍮ Ξ ⍮ Δ ⊢m Φ /\ ins_typed Θ Ξ Δ Φ
  end.

(** A member, typed in the frame it was inserted into, is typed in the whole
    module. *)
Lemma ins_typed_full : forall Θ Ξ P Φ ip b pv A B,
    ins_typed Θ Ξ P Φ ->
    ⊢ Θ ⍮ gs_push Ξ P Φ ⍮ ⋅ ->
    Φ ∋ ip ⇒ ge_def b pv A B ->
    (exists i, Θ ⍮ gs_push Ξ P Φ ⍮ ⋅ ⊢ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ gs_push Ξ P Φ ⍮ ⋅ ⊢ M : A).
Proof.
  intros * Hins Hb Hl.
  destruct (gm_lookup_ins _ _ _ Hl) as [Φq Hi].
  destruct (frame_grow _ _ _ _ _ _ (gm_ins_prefix _ _ _ _ Hi) Hb) as (_ & He & _).
  destruct (Hins _ _ _ _ _ _ Hi) as [[i HT] HM].
  split; [ exists i; auto | intros; auto ].
Qed.

Lemma rwf_push : forall Θ U Ξ,
    ⊢g Θ ⍮ U :: Ξ ->
    rwf Θ Ξ ->
    ins_typed Θ Ξ (gu_params U) (gu_mod U) ->
    rwf Θ (U :: Ξ).
Proof.
  intros * Hg HR HU p b pv A B Hlk.
  assert (Hb : ⊢ Θ ⍮ U :: Ξ ⍮ ⋅) by (constructor; assumption).
  destruct (push_preserves_wf _ _ _ Hg) as (_ & Hp & _).
  destruct p as [[fp | m] ip]; [| destruct (Nat.eq_dec m (length Ξ)) as [-> | Hm] ].
  2:{ (* a member of the new frame *)
      apply gc_lookup_top in Hlk.
      inversion Hg as [? ? Hs]; inversion Hs as [| ? ? ? ? HUw]; subst.
      inversion HUw as [? ? ? ? Hpt]; subst.
      destruct U as [P X Φ]; cbn in Hpt, Hlk, HU; subst X.
      eapply ins_typed_full; eassumption. }
  all: apply gc_lookup_pop in Hlk; [| cbn; congruence ].
  all: destruct (HR _ _ _ _ _ Hlk) as [[i HA] HM].
  all: split; [ exists i; auto | intros; auto ].
Qed.

(** A filed unit is the closing of a unit whose members are typed where they
    were inserted. *)
Definition unit_filed (Θ : gdeps) (fp : list String.string) (U : gunit) : Prop :=
  exists Uo, U = gu_close fp Uo /\ Θ ⍮ nil ⊢u Uo /\ ins_typed Θ nil (gu_params Uo) (gu_mod Uo).

(** Filing a level: a unit of the new level was closed as it was filed, and one
    of the levels below is resolved as before. *)
Lemma rwf_level : forall Θ d,
    wf_gdeps Θ ->
    wf_gdep Θ d ->
    rwf Θ nil ->
    (forall fp U, List.In (fp, U) d -> unit_filed Θ fp U) ->
    rwf (d :: Θ) nil.
Proof.
  intros * HΘ Hd HR HU p b pv A B Hlk.
  assert (Hb : ⊢ d :: Θ ⍮ nil ⍮ ⋅)
    by (apply wf_ctx_empty, wf_gctx_intro, wf_gstack_nil, wf_gdeps_cons; assumption).
  pose proof (wf_gdep_fresh _ _ Hd) as Hfr.
  assert (Hgrow : Θ ⊑ d :: Θ)
    by (unfold gds_sub; intros; apply gds_lookup_level; assumption).
  inversion Hlk as [? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? Hf Hm]; subst;
    [ unfold gs_frame in *; cbn in *; destruct n; discriminate |].
  pose proof Hf as Hl; unfold gds_lookup in Hl; cbn [List.concat] in Hl.
  apply gd_lookup_app_inv in Hl as [Hl | Hl].
  - (* filed at the new level: closed as it was filed *)
    apply gd_lookup_in in Hl as Hin.
    destruct (HU _ _ Hin) as ([PU X ΦU] & -> & HUw & HUi).
    inversion HUw as [? ? ? HUm _]; subst; cbn [gu_params gu_mod gu_close] in *.
    destruct (gm_close_lookup_inv _ _ _ _ _ _ Hm _ eq_refl) as (b0 & pv0 & A0 & B0 & Hm0 & Heq).
    injection Heq as -> -> -> ->.
    destruct (gm_lookup_ins _ _ _ Hm0) as [Φq Hi].
    destruct (closable_file Θ (d :: Θ) fp PU ΦU ΦU HUm HUi Hf Hgrow Hb
                (S (gm_count Φq)) Φq _ _ _ _ _ ltac:(lia) Hi (gm_ins_prefix _ _ _ _ Hi)) as [[i HT] HM].
    split; [ eapply ctx_pi_wf0; eassumption |].
    intros M' HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
    eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ].
  - (* filed below *)
    pose proof (gcl_abs Θ nil _ _ _ _ _ _ _ Hl Hm) as Hl0.
    destruct (HR _ _ _ _ _ Hl0) as [[i HA] HM].
    destruct (levels_grow Θ (d :: Θ) nil Hgrow Hb) as (_ & He & _).
    split; [ exists i; apply He, HA | intros; apply He, HM; assumption ].
Qed.

(** Extending a module: [x] itself was checked in the module so far, a member
    of a nested module [x] was closed as it was inserted, and an earlier member
    was typed already. *)
Lemma ins_typed_ext : forall Θ Ξ P Φ x E,
    Θ ⍮ Ξ ⍮ P ⊢m Φ ⊳ x ↦ E ->
    ins_typed Θ Ξ P Φ ->
    entry_typed Θ (gs_push Ξ P Φ) x E ->
    ins_typed Θ Ξ P (Φ ⊳ x ↦ E).
Proof.
  intros * Hw HΦ HE Φq ip b pv A B Hi.
  inversion Hi as [| ? ? ? ? ? ? ? ? ? ? Hi' | ? ? ? ? ? ? Hi']; subst.
  - exact HE.
  - cbn [entry_typed length Nat.pred] in HE; destruct HE as (Φo & -> & HΦo & HEi).
    destruct (gm_close_ins_inv _ _ _ _ _ _ _ Hi' _ eq_refl) as (Φr & b0 & pv0 & A0 & B0 & -> & Heq & Hir).
    injection Heq as -> -> -> ->.
    destruct (closable_pop Θ Ξ P Φ x Δ' Φo Hw HΦo HEi (S (gm_count Φr)) Φr _ _ _ _ _ ltac:(lia) Hir)
      as [[i HT] HM].
    split; [ eapply ctx_pi_wf0; eassumption |].
    intros M' HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
    eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ].
  - eauto.
Qed.

(** ** Presupposition for Typing, relative to Resolution *)

Lemma presup_exp_typ_rwf : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    rwf Θ Ξ ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  induction 1; intros HR;
    repeat match goal with IH : rwf _ _ -> _ |- _ => specialize (IH HR) end;
    assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2; destruct_conjs.
  (* a global: its type is a type at [⋅], and closed *)
  all: try match goal with
    | Hl : _ ⍮ _ ∋ᵍ _ ⇒ ge_def _ _ _ _, HΓ : ⊢ _ ⍮ _ ⍮ _ |- _ =>
        destruct (HR _ _ _ _ _ Hl) as [[i HA] _]; exists i;
        eapply (closed_weaken_exp _ _ _ _ _ _ nil);
        [ assumption | exact HA | eapply wf_gc_lookup_type_closed; eassumption | exact I ]
    end.
  (* a parameter *)
  all: try solve [ eapply wf_param_typ; eassumption ].
  all: mauto 3.
  - eexists; mauto 3.
  - eexists; mauto 3.
Qed.

(** ** The Mutual Theorem *)

Theorem presup_global :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> rwf Θ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> rwf Θ Ξ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> rwf Θ Ξ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> rwf Θ Ξ) /\
  (forall Θ Ξ x E, Θ ⍮ Ξ ⊢e x ↦ E -> entry_typed Θ Ξ x E) /\
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ -> ins_typed Θ Ξ Δ Φ) /\
  (forall Θ Ξ U, Θ ⍮ Ξ ⊢u U -> ins_typed Θ Ξ (gu_params U) (gu_mod U)) /\
  (forall Θ d, wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> unit_filed Θ fp U) /\
  (forall Θ, wf_gdeps Θ -> rwf Θ nil) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> rwf Θ Ξ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ).
Proof.
  apply wf_mut_ind_all; intros; try assumption.
  - (* an axiom *)
    cbn; split; [ eauto | discriminate ].
  - (* a definition: its type is a type by presupposition of its body *)
    cbn; split; [ eapply presup_exp_typ_rwf; eassumption | intros ? [= <-]; assumption ].
  - (* a nested module *)
    cbn; eexists; split; [ reflexivity | split; assumption ].
  - (* the empty module *)
    intros ? * Hi; inversion Hi.
  - apply ins_typed_ext; [ econstructor | |]; eassumption.
  - contradiction.
  - match goal with H : List.In _ (_ :: _) |- _ => destruct H as [[= <- <-] |] end; eauto.
    eexists; split; [ reflexivity | split; assumption ].
  - intros ? * Hlk; inversion Hlk; subst;
      [ unfold gs_frame in *; cbn in *; match goal with Hn : List.nth_error nil ?n = Some _ |- _ => destruct n; discriminate end
      | discriminate ].
  - apply rwf_level; assumption.
  - apply rwf_push; [ constructor; constructor | |]; assumption.
Qed.

Corollary gctx_rwf : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ.
Proof. apply presup_global. Qed.

(** What a use of a global needs: its type and body, in any well-formed
    context. *)
Corollary wf_glob_typ : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ _ _ _ Hl) as [[i HA] _].
  exists i; eapply (closed_weaken_exp _ _ _ _ _ _ nil);
    [ assumption | exact HA | eapply wf_gc_lookup_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A (Some M) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ _ _ _ Hl) as [_ HM].
  eapply closed_weaken_exp;
    [ assumption | apply HM; reflexivity
    | eapply wf_gc_lookup_body_closed; eassumption
    | eapply wf_gc_lookup_type_closed; eassumption ].
Qed.

Theorem presup_exp_typ : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * H; eapply (presup_exp_typ_rwf H), gctx_rwf, ctx_wf_gctx, presup_exp_ctx, H.
Qed.
