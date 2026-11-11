(** * Deep Units

    A unit is deep at a context when its body is glued at the instances of
    the context, not at its renamings only ([glu_unit_deep]).  A deep unit
    is glued at each instance ((a), [glu_unit_deep_inst]), and stays deep
    when moved by a substitution that preserves instances
    ([glu_rel_sub_stable]) and whose module components are built from deep
    literals ([glu_rel_sub_mods_deep]) ((b), [glu_unit_deep_stable]).  Such
    are the renamings, the [β] instance [(Id,,N)] of a term glued at the
    instances ((c), [glu_unit_deep_beta]), and the fill of the entries of a
    deep body before one of them ((d), [glu_rel_sub_stable_fill] and
    [glu_rel_sub_mods_deep_fill]): a submodule selected from a deep body is
    deep ([glu_unit_deep_select_body]).  These are what the right-hand
    sides of [wf_me_beta_body], [wf_me_beta_alias] and [wf_me_delta_sel]
    need to be glued. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas LookupSound Presup Paths DescTyping.
From Mctt.Core.Soundness Require Import LogicalRelation ModuleValues Instances Extensions UnitEqCases.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** (a) A deep unit is glued at each instance of its context. *)
Lemma glu_unit_deep_inst : forall Γ U, glu_unit_deep Γ U ->
    forall Γ' τ, glu_rel_sub_inst Γ' τ Γ -> glu_unit_at Γ' U[τ]ᵘ.
Proof.
  intros Γ [Δ [sm Φ | E]]; cbn [glu_unit_deep]; intros HU Γ' τ Hτ.
  - exact (glu_unit_at_body_inst _ _ _ _ (proj1 HU) _ _ Hτ).
  - destruct HU as [HΔ HE _]; exact (glu_unit_at_alias_inst _ _ _ HΔ HE _ _ Hτ).
Qed.

(** ** Substitutions preserving instances *)

(** A substitution from [Γ] to [Δ] preserving instances: composed with
    any instance of [Γ], it is an instance of [Δ]. *)
Definition glu_rel_sub_stable (Γ : ctx) (σ : sub) (Δ : ctx) : Prop :=
  forall Γ' ζ, glu_rel_sub_inst Γ' ζ Γ -> glu_rel_sub_inst Γ' (σ ⨟ ζ) Δ.

(** An instance is one up to the pointwise equality of substitutions. *)
Lemma glu_rel_sub_inst_sb_eq : forall Γ τ τ' Δ, glu_rel_sub_inst Γ τ Δ -> sb_eq τ τ' -> glu_rel_sub_inst Γ τ' Δ.
Proof.
  intros * [Hτ HΓ Hc Hm] E; econstructor; [ exact (wf_sub_sb_eq _ _ _ _ _ _ Hτ E) | exact HΓ | |].
  - intros x A Hx; rewrite <- !(exp_sub_sb_eq _ _ _ E); exact (Hc _ _ Hx).
  - intros x U Hx; rewrite <- (gunit_sub_sb_eq _ _ _ E); exact (Hm _ _ Hx).
Qed.

(** A substitution preserving instances, out of a context glued with its
    types, is typed: at the identity instance. *)
Lemma glu_rel_sub_stable_typed : forall Γ σ Δ, glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ -> Γ ⊢ˢ σ : Δ.
Proof.
  intros * HΓ Hσ.
  pose proof (glu_rel_sub_inst_typed _ _ _ (Hσ _ _ (glu_rel_ctx_types_id HΓ))) as H.
  exact (wf_sub_sb_eq _ _ _ _ _ _ H (sb_compose_id_right σ)).
Qed.

(** A term glued at the instances of [Δ] is glued at those of [Γ], moved
    by a substitution preserving instances. *)
Lemma glu_rel_exp_under_sub_stable : forall Δ M A Γ σ,
    glu_rel_exp_under_sub Δ M A -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ ->
    glu_rel_exp_under_sub Γ M[σ] A[σ].
Proof.
  intros * HM HΓ Hσ; econstructor; [ exact HΓ |].
  intros Γ' ζ Hζ; rewrite !exp_sub_sub; exact (glu_rel_exp_under_sub_inst _ _ _ HM _ _ (Hσ _ _ Hζ)).
Qed.

(** So is a module expression. *)
Lemma glu_rel_modexp_under_sub_stable : forall Δ H Γ σ,
    glu_rel_modexp_under_sub Δ H -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ ->
    glu_rel_modexp_under_sub Γ H[σ]ᵐ.
Proof.
  intros * HH HΓ Hσ; econstructor; [ exact HΓ |].
  intros Γ' ζ Hζ; rewrite modexp_sub_sub; exact (glu_rel_modexp_under_sub_inst _ _ HH _ _ (Hσ _ _ Hζ)).
Qed.

(** And a unit. *)
Lemma glu_rel_unit_under_sub_stable : forall Δ U Γ σ,
    glu_rel_unit_under_sub Δ U -> glu_rel_sub_stable Γ σ Δ -> glu_rel_unit_under_sub Γ U[σ]ᵘ.
Proof. intros * HU Hσ Γ' ζ Hζ; rewrite gunit_sub_sub; exact (HU _ _ (Hσ _ _ Hζ)). Qed.

(** A substitution preserving instances, lifted over an entry: an instance
    of the extended context is its tail, an instance, extended by its
    head, glued at the head's type. *)
Lemma glu_rel_sub_stable_q_gen : forall Γ σ Δ e,
    glu_rel_sub_stable Γ σ Δ ->
    (centry_sub e σ :: Γ)%list ⊢ˢ q σ : (e :: Δ)%list ->
    (forall A, (e :: Δ)%list ∋ #0 : A -> (centry_sub e σ :: Γ)%list ∋ #0 : A[q σ]) ->
    (forall U, (e :: Δ)%list ∋ #0 ≔ₘ U -> (centry_sub e σ :: Γ)%list ∋ #0 ≔ₘ U[q σ]ᵘ) ->
    glu_rel_sub_stable (centry_sub e σ :: Γ)%list (q σ) (e :: Δ)%list.
Proof.
  intros * Hσ Hq Hl Hlm Γ' ζ Hζ.
  assert (He : ⊢ (centry_sub e σ :: Γ)%list) by (destruct (glu_rel_sub_inst_typed _ _ _ Hζ); assumption).
  pose proof (glu_rel_sub_inst_of_wk_comp Hζ (wf_wk_shift _ _ _ _ He)) as Hζ'.
  assert (Ew : sb_eq ((ι ↑) ⨟ ζ) (Wk ⨟ ζ)) by (intros x; reflexivity).
  pose proof (Hσ _ _ (glu_rel_sub_inst_sb_eq _ _ _ _ Hζ' Ew)) as Hσζ.
  assert (E : sb_eq (sb_extend (σ ⨟ (Wk ⨟ ζ)) (ζ 0)) (q σ ⨟ ζ)).
  { intros x; symmetry.
    transitivity (((q σ) ⨟ (sb_extend (Wk ⨟ ζ) (ζ 0))) x);
      [ unfold sb_compose; apply sentry_sub_sb_eq; exact (sb_expand ζ) | apply sb_q_compose_extend_gen ]. }
  eapply glu_rel_sub_inst_sb_eq; [| exact E ].
  apply (glu_rel_sub_inst_extend_gen Hσζ).
  - exact (wf_sub_sb_eq _ _ _ _ _ _ (wf_sub_compose _ _ _ _ _ _ _ Hq (glu_rel_sub_inst_typed _ _ _ Hζ)) (symmetry E)).
  - intros A Hx.
    rewrite (exp_sub_sb_eq _ _ _ E), <- exp_sub_sub.
    exact (glu_rel_sub_inst_comps _ _ _ Hζ _ _ (Hl _ Hx)).
  - intros U Hx.
    rewrite (gunit_sub_sb_eq _ _ _ E), <- gunit_sub_sub.
    exact (glu_rel_sub_inst_mods _ _ _ Hζ _ _ (Hlm _ Hx)).
Qed.

(** An entry's parts glued at the instances of [Δ] are glued at those of
    [Γ], moved by a substitution preserving instances. *)
Lemma glu_rel_entry_under_sub_stable : forall Δ e Γ σ,
    glu_rel_entry_under_sub Δ e -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ ->
    glu_rel_entry_under_sub Γ (centry_sub e σ).
Proof.
  intros * He HΓ Hσ.
  pose proof (glu_rel_sub_stable_typed _ _ _ HΓ Hσ) as Hσt.
  destruct e as [κ A | A M | U | A M U]; cbn [glu_rel_entry_under_sub centry_sub] in He |- *.
  - destruct He as (S & HS & HA); exists S; split; [ exact HS |].
    pose proof (glu_rel_exp_under_sub_stable _ _ _ _ _ HA HΓ Hσ) as H.
    rewrite (type_sort_sub _ _ (sort_kind_type_sort _ _ HS)) in H; exact H.
  - destruct He as (S & [HS HA HM]); exists S; constructor; [ exact HS | | exact (glu_rel_exp_under_sub_stable _ _ _ _ _ HM HΓ Hσ) ].
    pose proof (glu_rel_exp_under_sub_stable _ _ _ _ _ HA HΓ Hσ) as H.
    rewrite (type_sort_sub _ _ HS) in H; exact H.
  - destruct He as [HU HUg]; split; [ exact (sub_preserves_unit _ _ _ _ _ _ _ HU Hσt) | exact (glu_rel_unit_under_sub_stable _ _ _ _ HUg Hσ) ].
  - destruct He as (i & E & [-> HA HM HU HUg]); exists i, E[σ]ᵐ; constructor.
    + reflexivity.
    + exact (glu_rel_exp_under_sub_stable _ _ _ _ _ HA HΓ Hσ).
    + exact (glu_rel_exp_under_sub_stable _ _ _ _ _ HM HΓ Hσ).
    + exact (sub_preserves_unit _ _ _ _ _ _ _ HU Hσt).
    + exact (glu_rel_unit_under_sub_stable _ _ _ _ HUg Hσ).
Qed.

(** An extension glued at the instances of [Δ], moved by a substitution
    preserving instances, is glued at those of [Γ], and the substitution
    lifted through it preserves instances. *)
Lemma glu_rel_ext_under_sub_stable : forall Ψ Δ Γ σ,
    glu_rel_ext_under_sub Δ Ψ -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ ->
    glu_rel_ext_under_sub Γ (tele_sub Ψ σ) /\ glu_rel_sub_stable (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ) (Ψ ++ Δ).
Proof.
  induction Ψ as [| e Ψ IH]; intros Δ Γ σ HΨe HΓ Hσ; [ split; [ exact HΓ | exact Hσ ] |].
  cbn [glu_rel_ext_under_sub] in HΨe; destruct HΨe as [HΨ He].
  destruct (IH _ _ _ HΨ HΓ Hσ) as [HΨσ Hst].
  pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΨσ) as HΨΓ.
  pose proof (glu_rel_sub_stable_typed _ _ _ HΨΓ Hst) as Hstt.
  pose proof (glu_rel_entry_under_sub_stable _ _ _ _ He HΨΓ Hst) as He'.
  assert (Hext : glu_rel_ext_under_sub Γ (tele_sub (e :: Ψ) σ)) by (cbn [tele_sub glu_rel_ext_under_sub]; split; assumption).
  split; [ exact Hext |].
  cbn [tele_sub List.length sb_qn app].
  pose proof (glu_rel_ext_under_sub_ctx_types _ _ Hext) as HeΓ; cbn [tele_sub app] in HeΓ.
  pose proof (glu_rel_ext_under_sub_ctx_types _ _ (conj HΨ He : glu_rel_ext_under_sub Δ (e :: Ψ))) as HeΔ; cbn [app] in HeΔ.
  assert (Hw1 : ⊢ (centry_sub e (sb_qn (List.length Ψ) σ) :: tele_sub Ψ σ ++ Γ)%list)
    by (destruct (glu_rel_ctx_types_ctx _ HeΓ) as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  assert (Hw2 : ⊢ (e :: Ψ ++ Δ)%list)
    by (destruct (glu_rel_ctx_types_ctx _ HeΔ) as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  apply glu_rel_sub_stable_q_gen; [ exact Hst | exact (wf_sub_q_gen _ _ _ _ _ _ Hstt Hw1 Hw2) | |].
  - intros A Hx; inversion Hx; subst; cbn [centry_sub]; rewrite exp_wk_shift_sub_q; constructor.
  - intros U Hx; inversion Hx; subst; cbn [centry_sub]; rewrite gunit_wk_shift_sub_q; constructor.
Qed.

(** A context glued with its types is well formed. *)
Lemma glu_rel_ctx_types_wf : forall {Γ}, glu_rel_ctx_types Γ -> ⊢ Γ.
Proof. intros * HΓ; destruct (glu_rel_ctx_types_ctx _ HΓ) as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb). Qed.

(** The module components of a substitution from [Γ], at every renaming of
    [Γ], built from deep literals: what a slot moved by it reads. *)
Definition glu_rel_sub_mods_deep (Γ : ctx) (σ : sub) : Prop :=
  forall x Γ' φ, Γ' ⊢ʷ φ : Γ -> glu_rel_ctx_types Γ' -> glu_modexp_parts_deep Γ' (modexp_wk (sentry_modexp (σ x)) φ).

(** So are those of the substitution lifted through an extension: the new
    variables are slots, the others the substitution's, weakened. *)
Lemma glu_rel_sub_mods_deep_qn : forall Ψ Γ σ,
    ⊢ tele_sub Ψ σ ++ Γ -> glu_rel_sub_mods_deep Γ σ -> glu_rel_sub_mods_deep (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ).
Proof.
  intros * Hw Hm x Γ' φ Hφ HΓ'.
  destruct (Nat.lt_ge_cases x (List.length Ψ)) as [Hlt | Hge].
  - rewrite sb_qn_lt by exact Hlt; cbn; exact I.
  - rewrite sb_qn_ge by exact Hge.
    rewrite <- Substitution.sentry_modexp_wk, modexp_wk_wk.
    apply Hm; [| exact HΓ' ].
    eapply wf_wk_compose; [ exact Hφ |].
    rewrite <- (length_tele_sub Ψ σ); exact (wf_wk_shiftn_app' _ _ _ _ Hw).
Qed.

(** An application's argument glued deeply, moved by a substitution
    preserving instances: what the moved function denotes is what the
    function denotes, moved ([wf_sub_mdenote]), whose outermost parameter
    is the parameter moved ([tele_view_sub]). *)
Lemma glu_app_arg_deep_stable : forall Δ E N Γ σ,
    glu_app_arg_deep Δ E N -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ -> glu_app_arg_deep Γ E[σ]ᵐ N[σ].
Proof.
  intros * [HE Harg] HΓ Hσ.
  pose proof (glu_rel_sub_stable_typed _ _ _ HΓ Hσ) as Hσt.
  constructor; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HE Hσt) |].
  intros R' T' B' T1' Hm' HT' Hv'.
  destruct (me_mod_tele_exists HE) as (R & T & HmR & HT).
  pose proof (ctx_wf_gctx _ _ _ (wf_sub_dom _ _ _ _ _ Hσt)) as Hg.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm' _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HE HmR Hσt)) in HT'.
  rewrite (mdesc_mod_tele_sub _ _ σ _ (wf_mdenote_scoped _ _ _ _ _ _ HE HmR) HT) in HT'; injection HT' as <-.
  rewrite tele_view_sub in Hv'; destruct (tele_view T) as [[B T1] |] eqn:Hv; cbn in Hv'; [| discriminate ].
  injection Hv' as <- <-.
  exact (glu_rel_exp_under_sub_stable _ _ _ _ _ (Harg _ _ _ _ HmR HT Hv) HΓ Hσ).
Qed.

(** (b) A deep unit moved by a substitution preserving instances, whose
    module components are deep, is deep: its extensions moved
    ([glu_rel_ext_under_sub_stable]), its module entries' units and its
    target's parts, recursively. *)
Lemma glu_unit_deep_stable : forall U Δ Γ σ,
    glu_unit_deep Δ U -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ -> glu_rel_sub_mods_deep Γ σ ->
    glu_unit_deep Γ U[σ]ᵘ
with glu_gmod_units_deep_stable : forall Φ Δ Γ σ,
    glu_rel_ext_under_sub Δ (body_ctx (gm_expand Φ)) ->
    glu_gmod_units_deep Δ Φ -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ -> glu_rel_sub_mods_deep Γ σ ->
    glu_gmod_units_deep Γ (gmod_sub Φ σ)
with glu_modexp_parts_deep_stable : forall E Δ Γ σ,
    glu_modexp_parts_deep Δ E -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ -> glu_rel_sub_mods_deep Γ σ ->
    glu_modexp_parts_deep Γ E[σ]ᵐ.
Proof.
  - intros [Δu [sm Φ | E]] Δ Γ σ HU HΓ Hσ Hm; rewrite gunit_sub_mk; cbn [moddef_sub glu_unit_deep] in HU |- *.
    + destruct HU as [HΦ HΦu].
      destruct (glu_rel_ext_under_sub_stable _ _ _ _ HΦ HΓ Hσ) as [HΦσ _].
      destruct (glu_rel_ext_under_sub_stable _ _ _ _ (glu_rel_ext_under_sub_app_inv _ HΦ) HΓ Hσ) as [HΔσ HΔst].
      pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΔσ) as HΔΓ.
      split.
      * rewrite body_ctx_expand_sub, <- tele_sub_app; exact HΦσ.
      * exact (glu_gmod_units_deep_stable _ _ _ _ (glu_rel_ext_under_sub_app_split _ _ _ HΦ) HΦu HΔΓ HΔst
                 (glu_rel_sub_mods_deep_qn _ _ _ (glu_rel_ctx_types_wf HΔΓ) Hm)).
    + destruct HU as [HΔ HE Hl].
      destruct (glu_rel_ext_under_sub_stable _ _ _ _ HΔ HΓ Hσ) as [HΔσ HΔst].
      pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΔσ) as HΔΓ.
      constructor; [ exact HΔσ | exact (glu_rel_modexp_under_sub_stable _ _ _ _ HE HΔΓ HΔst) |].
      exact (glu_modexp_parts_deep_stable _ _ _ _ Hl HΔΓ HΔst (glu_rel_sub_mods_deep_qn _ _ _ (glu_rel_ctx_types_wf HΔΓ) Hm)).
  - intros [| Φ x En | Φ H its Φg] Δ Γ σ HΦe HΦ HΓ Hσ Hm; cbn [gmod_sub glu_gmod_units_deep] in HΦ |- *; [ exact I | |].
    + cbn [gm_expand] in HΦe.
      (** The entries before, and the context the entry's unit is read at *)
      assert (HΦe' : glu_rel_ext_under_sub Δ (body_ctx (gm_expand Φ)))
        by (destruct En as [? ? ? ? [] | | | | ]; cbn [body_ctx glu_rel_ext_under_sub] in HΦe; apply HΦe).
      destruct (glu_rel_ext_under_sub_stable _ _ _ _ HΦe' HΓ Hσ) as [HBσ HBst].
      pose proof (glu_rel_ext_under_sub_ctx_types _ _ HBσ) as HBΓ.
      assert (Hat : forall U, glu_unit_deep (body_ctx (gm_expand Φ) ++ Δ) U ->
                glu_unit_deep (body_ctx (gm_expand (gmod_sub Φ σ)) ++ Γ) U[sb_qn (gm_binders Φ) σ]ᵘ).
      { intros U HU; rewrite body_ctx_expand_sub, <- length_body_ctx_expand.
        exact (glu_unit_deep_stable _ _ _ _ HU HBΓ HBst (glu_rel_sub_mods_deep_qn _ _ _ (glu_rel_ctx_types_wf HBΓ) Hm)). }
      destruct En as [b pv κ A oM | pv U | pv pq k D ΦD | pv A M U | pv p R ΦR];
        cbn [gentry_sub glu_gmod_units_deep] in HΦ |- *.
      * exact (glu_gmod_units_deep_stable _ _ _ _ HΦe' HΦ HΓ Hσ Hm).
      * destruct HΦ as [HΦ HU]; split; [ exact (glu_gmod_units_deep_stable _ _ _ _ HΦe' HΦ HΓ Hσ Hm) | exact (Hat _ HU) ].
      * exact (glu_gmod_units_deep_stable _ _ _ _ HΦe' HΦ HΓ Hσ Hm).
      * destruct HΦ as [HΦ HU]; split; [ exact (glu_gmod_units_deep_stable _ _ _ _ HΦe' HΦ HΓ Hσ Hm) | exact (Hat _ HU) ].
      * exact (glu_gmod_units_deep_stable _ _ _ _ HΦe' HΦ HΓ Hσ Hm).
    + cbn [gm_expand] in HΦe; rewrite body_ctx_graft in HΦe by apply gm_noopen_expand.
      destruct HΦ as [HΦ HΦg].
      pose proof (glu_rel_ext_under_sub_app_inv _ HΦe) as HΦe'.
      destruct (glu_rel_ext_under_sub_stable _ _ _ _ HΦe' HΓ Hσ) as [HBσ HBst].
      pose proof (glu_rel_ext_under_sub_ctx_types _ _ HBσ) as HBΓ.
      split; [ exact (glu_gmod_units_deep_stable _ _ _ _ HΦe' HΦ HΓ Hσ Hm) |].
      rewrite body_ctx_expand_sub, <- length_body_ctx_expand.
      exact (glu_gmod_units_deep_stable _ _ _ _ (glu_rel_ext_under_sub_app_split _ _ _ HΦe) HΦg HBΓ HBst
               (glu_rel_sub_mods_deep_qn _ _ _ (glu_rel_ctx_types_wf HBΓ) Hm)).
  - intros [fp | y | E' y | E' N | U] Δ Γ σ HE HΓ Hσ Hm; cbn [modexp_sub glu_modexp_parts_deep] in HE |- *.
    + exact I.
    + (** A slot moved: the substitution's module component *)
      pose proof (Hm y Γ wk_id (wf_wk_id _ _ _ (glu_rel_ctx_types_wf HΓ)) HΓ) as H.
      rewrite modexp_wk_id in H; exact H.
    + exact (glu_modexp_parts_deep_stable _ _ _ _ HE HΓ Hσ Hm).
    + destruct HE as [HE Harg]; split; [ exact (glu_modexp_parts_deep_stable _ _ _ _ HE HΓ Hσ Hm) |].
      exact (glu_app_arg_deep_stable _ _ _ _ _ Harg HΓ Hσ).
    + exact (glu_unit_deep_stable _ _ _ _ HE HΓ Hσ Hm).
Qed.

(** ** Renamings *)

(** A renaming preserves instances ([glu_rel_sub_inst_of_wk_comp]). *)
Lemma glu_rel_sub_stable_wk : forall Γ' φ Γ, Γ' ⊢ʷ φ : Γ -> glu_rel_sub_stable Γ' (ι φ) Γ.
Proof. intros * Hφ Γ'' ζ Hζ; exact (glu_rel_sub_inst_of_wk_comp Hζ Hφ). Qed.

(** Its module components are slots. *)
Lemma glu_rel_sub_mods_deep_wk : forall Γ' φ, glu_rel_sub_mods_deep Γ' (ι φ).
Proof. intros * x Γ'' ψ _ _; cbn; exact I. Qed.

(** A deep unit renamed into a context glued with its types is deep. *)
Lemma glu_unit_deep_wk : forall Γ U Γ' φ, glu_unit_deep Γ U -> glu_rel_ctx_types Γ' -> Γ' ⊢ʷ φ : Γ -> glu_unit_deep Γ' U[ι φ]ᵘ.
Proof. intros * HU HΓ' Hφ; exact (glu_unit_deep_stable _ _ _ _ HU HΓ' (glu_rel_sub_stable_wk _ _ _ Hφ) (glu_rel_sub_mods_deep_wk _ _)). Qed.

(** ** The β instance *)

(** A term glued at the instances extends the identity to a substitution
    preserving instances: composed with an instance, the instance extended
    by the term moved, glued at every renaming. *)
Lemma glu_rel_sub_stable_extend_id : forall Γ κ X S N,
    Γ ⊢ X : S -> sort_kind S κ -> glu_rel_exp_under_sub Γ N X -> glu_rel_sub_stable Γ (Id,,N) (Γ ▹{κ} X).
Proof.
  intros * HX HS HN Γ' ζ Hζ.
  assert (E : sb_eq (ζ,,N[ζ]) ((Id,,N) ⨟ ζ))
    by (symmetry; etransitivity; [ apply sb_extend_compose |]; intros [| n]; [ reflexivity | exact (sb_compose_id_left ζ n) ]).
  eapply glu_rel_sub_inst_sb_eq; [| exact E ].
  exact (glu_rel_sub_inst_extend Hζ HX HS (glu_rel_exp_under_sub_inst_renaming HN Hζ)).
Qed.

(** Its module components are slots, or the empty unit. *)
Lemma glu_rel_sub_mods_deep_extend_id : forall Γ N, glu_rel_sub_mods_deep Γ (Id,,N).
Proof. intros * [|] Γ'' ψ _ _; cbn; exact I. Qed.

(** A deep unit whose parameters end in [e] is deep over [e], with the
    other parameters. *)
Lemma glu_unit_deep_params_split : forall Γ Δ e D,
    glu_unit_deep Γ (gu_mk (Δ ++ e :: nil) D) -> glu_unit_deep (e :: Γ)%list (gu_mk Δ D).
Proof.
  intros * HU; destruct D as [sm Φ | E]; cbn [glu_unit_deep] in HU |- *.
  - destruct HU as [HΦ HΦu]; rewrite app_assoc in HΦ; rewrite <- app_assoc in HΦu.
    split; [ exact (glu_rel_ext_under_sub_app_split _ _ _ HΦ) | exact HΦu ].
  - destruct HU as [HΔ HE Hl]; rewrite <- app_assoc in HE, Hl.
    constructor; [ exact (glu_rel_ext_under_sub_app_split _ _ _ HΔ) | exact HE | exact Hl ].
Qed.

(** (c) The β instance: a deep unit with an outermost parameter, given a
    term glued at its instances at it, is deep instantiated. *)
Lemma glu_unit_deep_beta : forall Γ Δ κ X D S N,
    glu_unit_deep Γ (gu_mk (Δ ++ ce_ass κ X :: nil) D) -> Γ ⊢ X : S -> sort_kind S κ -> glu_rel_exp_under_sub Γ N X ->
    glu_unit_deep Γ (gu_mk (tele_sub Δ (Id,,N)) (moddef_sub D (sb_qn (List.length Δ) (Id,,N)))).
Proof.
  intros * HU HX HS HN.
  rewrite <- gunit_sub_mk.
  exact (glu_unit_deep_stable _ _ _ _ (glu_unit_deep_params_split _ _ _ _ HU) (glu_rel_exp_under_sub_ctx _ _ _ HN)
           (glu_rel_sub_stable_extend_id _ _ _ _ _ HX HS HN) (glu_rel_sub_mods_deep_extend_id _ _)).
Qed.

(** ** The fill of a body's entries *)

(** (d) The fill of the entries of a body without opens before an entry,
    the body over the extension [Δ] of [Γ] glued at the instances,
    preserves instances: composed with an instance of [Δ ++ Γ], it is the
    instance extended entry by entry by each entry's term moved and its
    unit's literal moved, which the entry's gluing glues. *)
Lemma glu_rel_sub_stable_fill : forall Φ Γ Δ σ, gm_noopen Φ ->
    glu_rel_ext_under_sub Γ (body_ctx Φ ++ Δ) -> gm_fill Φ = Some σ ->
    glu_rel_sub_stable (Δ ++ Γ) σ (body_ctx Φ ++ Δ ++ Γ).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg _]; intros Γ Δ σ Hn HΦ Hf; cbn [gm_fill gm_noopen] in Hf, Hn.
  - injection Hf as <-; intros Γ' ζ Hζ; cbn [body_ctx app].
    exact (glu_rel_sub_inst_sb_eq _ _ _ _ Hζ (fun x => eq_sym (sb_compose_id_left ζ x))).
  - destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; [| destruct E as [? ? ? ? [] | | | | ]; discriminate ].
    destruct E as [b pv κ A [M |] | pv U | pv pq k D ΦD | pv A M U | pv p R ΦR]; cbn [option_map] in Hf;
      try discriminate; injection Hf as <-;
      cbn [body_ctx app glu_rel_ext_under_sub] in HΦ; destruct HΦ as [HΦ He]; cbn [glu_rel_entry_under_sub] in He;
      rewrite <- app_assoc in He; pose proof (IH _ _ _ Hn HΦ eq_refl) as Hσ0;
      intros Γ' ζ Hζ; pose proof (Hσ0 _ _ Hζ) as Hσζ;
      pose proof (glu_rel_sub_inst_typed _ _ _ Hσζ) as Hσζt;
      (eapply glu_rel_sub_inst_sb_eq; [| symmetry; apply sb_extend_compose_gen ]); cbn [sentry_sub].
    + destruct He as (S & [HS HA HM]); rewrite exp_sub_sub.
      exact (glu_rel_sub_inst_extend_def Hσζ (glu_rel_exp_under_sub_wf HA) HS HM).
    + destruct He as [HU HUg]; cbn [modexp_sub body_ctx app]; rewrite gunit_sub_sub.
      exact (glu_rel_sub_inst_extend_mod Hσζ HU (sub_preserves_unit _ _ _ _ _ _ _ HU Hσζt) HUg).
    + destruct He as (i & E & [-> HA HM HU HUg]); cbn [modexp_sub body_ctx app]; rewrite exp_sub_sub, gunit_sub_sub.
      exact (glu_rel_sub_inst_extend_dm Hσζ (glu_rel_exp_under_sub_wf HA) HM HU (sub_preserves_unit _ _ _ _ _ _ _ HU Hσζt) HUg).
  - contradiction.
Qed.

(** The fill's module components are the body's units moved by the fill
    of the entries before them, deep there when the body's units are
    deep ((b) at that fill, then renamed). *)
Lemma glu_rel_sub_mods_deep_fill : forall Φ Γ Δ σ, gm_noopen Φ ->
    glu_rel_ext_under_sub Γ (body_ctx Φ ++ Δ) -> glu_gmod_units_deep (Δ ++ Γ) Φ -> gm_fill Φ = Some σ ->
    glu_rel_sub_mods_deep (Δ ++ Γ) σ.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg _]; intros Γ Δ σ Hn HΦ HΦu Hf; cbn [gm_fill gm_noopen] in Hf, Hn.
  - injection Hf as <-; intros y Γ' φ _ _; cbn; exact I.
  - destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; [| destruct E as [? ? ? ? [] | | | | ]; discriminate ].
    assert (HΦ0 : glu_rel_ext_under_sub Γ (body_ctx Φ ++ Δ))
      by (destruct E as [? ? ? ? [] | | | | ]; cbn [body_ctx app glu_rel_ext_under_sub] in HΦ; apply HΦ).
    pose proof (glu_rel_sub_stable_fill _ _ _ _ Hn HΦ0 Hf0) as Hσ0.
    pose proof (glu_rel_ext_under_sub_ctx_types _ _ (glu_rel_ext_under_sub_app_inv _ HΦ0)) as HΔΓ.
    (** A unit of the body, moved by the fill before it and renamed *)
    assert (Hat : forall U, glu_unit_deep (body_ctx (gm_expand Φ) ++ Δ ++ Γ) U ->
              glu_rel_sub_mods_deep (Δ ++ Γ) σ0 ->
              forall Γ' φ, Γ' ⊢ʷ φ : Δ ++ Γ -> glu_rel_ctx_types Γ' -> glu_unit_deep Γ' (gunit_wk U[σ0]ᵘ φ)).
    { intros U HU Hm0 Γ' φ Hφ HΓ'.
      rewrite (gm_expand_noopen _ Hn) in HU.
      rewrite <- gunit_sub_of_wk.
      exact (glu_unit_deep_wk _ _ _ _ (glu_unit_deep_stable _ _ _ _ HU HΔΓ Hσ0 Hm0) HΓ' Hφ). }
    destruct E as [b pv κ A [M |] | pv U | pv pq k D ΦD | pv A M U | pv p R ΦR]; cbn [option_map] in Hf;
      try discriminate; injection Hf as <-; cbn [glu_gmod_units_deep] in HΦu.
    + pose proof (IH _ _ _ Hn HΦ0 HΦu eq_refl) as Hm0.
      intros [| y] Γ' φ Hφ HΓ'; cbn; [ exact I | exact (Hm0 y Γ' φ Hφ HΓ') ].
    + destruct HΦu as [HΦu HU]; pose proof (IH _ _ _ Hn HΦ0 HΦu eq_refl) as Hm0.
      intros [| y] Γ' φ Hφ HΓ'; [ cbn [sb_extend sentry_modexp modexp_wk glu_modexp_parts_deep]; exact (Hat _ HU Hm0 _ _ Hφ HΓ') |].
      exact (Hm0 y Γ' φ Hφ HΓ').
    + destruct HΦu as [HΦu HU]; pose proof (IH _ _ _ Hn HΦ0 HΦu eq_refl) as Hm0.
      intros [| y] Γ' φ Hφ HΓ'; [ cbn [sb_extend sentry_modexp modexp_wk glu_modexp_parts_deep]; exact (Hat _ HU Hm0 _ _ Hφ HΓ') |].
      exact (Hm0 y Γ' φ Hφ HΓ').
  - contradiction.
Qed.

(** ** A submodule selected from a deep body *)

(** The deep module entries of a prefix of a body without opens. *)
Lemma glu_gmod_units_deep_prefix : forall Φ Γ y Φ', gm_noopen Φ -> gm_prefix_upto Φ y = Some Φ' ->
    glu_gmod_units_deep Γ Φ -> glu_gmod_units_deep Γ Φ'.
Proof.
  induction Φ as [| Φ IH x En | Φ IH H its Φg _]; intros * Hn Hp HΦ; cbn [gm_prefix_upto gm_noopen] in Hn, Hp;
    [ discriminate | | contradiction ].
  assert (HΦ0 : glu_gmod_units_deep Γ Φ)
    by (destruct En as [? ? ? ? ? | ? ? | ? ? ? ? ? | ? ? ? ? | ? ? ? ?]; cbn [glu_gmod_units_deep] in HΦ; try apply HΦ; exact HΦ).
  destruct (String.eqb y x); [ injection Hp as <-; exact HΦ | exact (IH _ _ _ Hn Hp HΦ0) ].
Qed.

(** The body submodule [y] of a deep body, its unit filled with the
    entries before it ([gm_fill]) and abstracted over the body's
    parameters, as an open body's entry is read ([reader_open]), is deep:
    (b) at the fill ((d)), then joined with the parameters. *)
Lemma glu_unit_deep_select_body : forall Γ Δ sm Φ Φ' y pv Δy smy Φy σ,
    glu_unit_deep Γ (gu_mk Δ (md_body sm Φ)) ->
    gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y (ge_mod pv (gu_mk Δy (md_body smy Φy)))) ->
    gm_fill Φ' = Some σ ->
    glu_unit_deep Γ (gu_mk (tele_sub Δy σ ++ Δ) (md_body smy (gmod_sub Φy (sb_qn (List.length Δy) σ)))).
Proof.
  intros * HU Hp Hf; cbn [glu_unit_deep] in HU; destruct HU as [HΦ HΦu].
  pose proof (gm_noopen_prefix_upto _ _ _ (gm_noopen_expand Φ) Hp) as Hn'; cbn [gm_noopen] in Hn'.
  destruct (gm_prefix_body_ctx _ _ _ (gm_noopen_expand Φ) Hp) as (Ψ & EΨ).
  rewrite EΨ, <- app_assoc in HΦ.
  pose proof (glu_rel_ext_under_sub_app_inv _ HΦ) as HΦ'; cbn [body_ctx app glu_rel_ext_under_sub] in HΦ'.
  destruct HΦ' as [HΦ' _].
  pose proof (glu_gmod_units_deep_prefix _ _ _ _ (gm_noopen_expand Φ) Hp (glu_gmod_units_deep_expand _ _ HΦu)) as Hy.
  cbn [glu_gmod_units_deep] in Hy; destruct Hy as [HΦ'u HUy].
  rewrite (gm_expand_noopen _ Hn') in HUy.
  pose proof (glu_rel_ext_under_sub_app_inv _ HΦ') as HΔ.
  pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΔ) as HΔΓ.
  pose proof (glu_unit_deep_stable _ _ _ _ HUy HΔΓ (glu_rel_sub_stable_fill _ _ _ _ Hn' HΦ' Hf)
                (glu_rel_sub_mods_deep_fill _ _ _ _ Hn' HΦ' HΦ'u Hf)) as Hσ.
  rewrite gunit_sub_mk in Hσ; cbn [moddef_sub] in Hσ.
  exact (glu_unit_deep_params_join _ _ _ _ HΔ Hσ).
Qed.

(** ** Module slots *)

(** The unit of a module slot of a context whose module parts are deep is
    deep, at every renaming into a context glued with its types: the slot's
    own unit at the context before it ([glu_ctx_deep]), renamed past the
    entries after it. *)
Lemma glu_ctx_deep_lookup_wk : forall Γ x U, Γ ∋ #x ≔ₘ U ->
    forall Γ' φ, Γ' ⊢ʷ φ : Γ -> glu_rel_ctx_types Γ' -> glu_ctx_deep Γ -> glu_unit_deep Γ' (gunit_wk U φ).
Proof.
  induction 1 as [ | | ? ? ? ? Hx IH ]; intros Γ' φ Hφ HΓ' Hd; rewrite gunit_wk_wk;
    match goal with Hφ : _ ⊢ʷ _ : ?Γe |- _ => assert (HwΓ : ⊢ Γe) by (destruct Hφ; assumption) end.
  - rewrite <- gunit_sub_of_wk.
    refine (glu_unit_deep_wk _ _ _ _ (Hd nil _ _ _ eq_refl eq_refl) HΓ' _).
    eapply wf_wk_compose; [ exact Hφ | exact (wf_wk_shift _ _ _ _ HwΓ) ].
  - rewrite <- gunit_sub_of_wk.
    refine (glu_unit_deep_wk _ _ _ _ (Hd nil _ _ _ eq_refl eq_refl) HΓ' _).
    eapply wf_wk_compose; [ exact Hφ | exact (wf_wk_shift _ _ _ _ HwΓ) ].
  - apply IH; [| exact HΓ' | exact (glu_ctx_deep_tail _ _ Hd) ].
    eapply wf_wk_compose; [ exact Hφ | exact (wf_wk_shift _ _ _ _ HwΓ) ].
Qed.

(** So at the context itself. *)
Lemma glu_ctx_deep_lookup : forall Γ x U,
    Γ ∋ #x ≔ₘ U -> glu_rel_ctx_types Γ -> glu_ctx_deep Γ -> glu_unit_deep Γ U.
Proof.
  intros * Hx HΓ Hd.
  rewrite <- (gunit_wk_id U).
  exact (glu_ctx_deep_lookup_wk _ _ _ Hx _ _ (wf_wk_id _ _ _ (glu_rel_ctx_types_wf HΓ)) HΓ Hd).
Qed.

(** The unit of a module slot is glued at the instances of the context:
    the instance's component for the slot is glued at the unit moved
    ([glu_rel_sub_inst_mods]). *)
Lemma glu_rel_unit_under_sub_slot : forall Γ x U, Γ ∋ #x ≔ₘ U -> glu_rel_unit_under_sub Γ U.
Proof.
  intros * Hx Γ' τ Hτ.
  pose proof (glu_rel_sub_inst_ctx _ _ _ Hτ) as HΓ'.
  assert (HwΓ' : ⊢ Γ') by (destruct HΓ' as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  pose proof (glu_rel_sub_inst_mods _ _ _ Hτ _ _ Hx _ _ (wf_wk_id _ _ _ HwΓ') HΓ') as Hg.
  rewrite gunit_wk_id in Hg; exact Hg.
Qed.

End Fixed_GCtx.

(** ** Stored aliases *)

(** A deep alias stored just below a stored module: its literal is glued
    over no context, by (a) at the identity of [⋅] and the construction
    ([glu_unit_modexp_at]). *)
Lemma glu_alias_modexp_of_deep : forall {GC : GCtx}, ⊢ᵍ gc_deps ⍮ gc_stack -> forall p T Φ y U,
    gc_loc gc_deps gc_stack p = Some (T, Φ) -> gc_module gc_deps gc_stack (qname_in p y) = Some (mr_alias U) ->
    glu_unit_deep ⋅ U -> glu_modexp_at ⋅ (me_lit U).
Proof.
  intros GC Hg * Hl Hm HU.
  pose proof (glu_rel_ctx_types_empty Hg) as H0.
  apply glu_unit_modexp_at; [ exact (gc_module_alias_wf _ _ Hg _ _ _ _ _ Hl Hm) | exact (glu_rel_ctx_types_ctx _ H0) |].
  rewrite <- (gunit_sub_id U); exact (glu_unit_deep_inst _ _ HU _ _ (glu_rel_ctx_types_id H0)).
Qed.

(** The shallow form of [glu_gctx_embedding_alias_deep], for an alias
    stored just below a module stored at the target. *)
Lemma glu_gctx_embedding_alias_modexp : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ y U,
    glu_gctx_embedding Θ1 Ξ1 Θ2 Ξ2 -> gc_loc Θ2 Ξ2 p = Some (T, Φ) ->
    gc_module Θ1 Ξ1 (qname_in p y) = Some (mr_alias U) -> gc_module Θ2 Ξ2 (qname_in p y) = Some (mr_alias U) ->
    @glu_modexp_at (gc_mk Θ2 Ξ2) ⋅ (me_lit U).
Proof.
  intros * Hμ Hl Hm1 Hm2.
  pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  exact (@glu_alias_modexp_of_deep (gc_mk Θ2 Ξ2) Hg2 _ _ _ _ _ Hl Hm2 (glu_gctx_embedding_alias_deep _ _ _ _ Hμ _ _ Hm1)).
Qed.
