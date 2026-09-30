(** * Experiment: cheaper routes to soundness with a global context

    See REPORT.md.  Build from [theories/]:
    [rocq c -R . Mctt ../experiments/soundness_alt/Exp.v]. *)

From Stdlib Require Import Lia String PeanoNat Morphisms List.
From Equations Require Import Equations.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Transport Scoping Structural.
From Mctt.Core.Syntactic Require Import CtxSub.
From Mctt.Core.Semantic Require Import Evaluation Readback PER.
From Mctt.Core.Soundness.LogicalRelation Require Import Definitions CoreLemmas.
From Mctt.Core.Soundness.Weakening Require Import Lemmas.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope string_scope.

(** ** 1. Extensions that move no term (grow a frame, add a level)

    [gext G1 G2] is the hypotheses of [rebase_preserves_wf] together with
    the [gc_resolve]/[gs_param] form of the same preservation, which evaluation
    and readback read ([gc_ext_raw] of experiments/extension_invariance). *)

Definition gext (G1 G2 : GCtx) : Prop :=
  (forall r Δ b pv A B,
      @gc_deps G1 ⍮ @gc_stack G1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
      @gc_deps G2 ⍮ @gc_stack G2 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B) /\
  (forall n U, List.nth_error (@gc_stack G1) n = Some U ->
      exists U', List.nth_error (@gc_stack G2) n = Some U' /\ gu_params U' = gu_params U) /\
  (forall p r, gc_resolve (@gc_deps G1) (@gc_stack G1) p = Some r ->
      gc_resolve (@gc_deps G2) (@gc_stack G2) p = Some r) /\
  (forall lp T, gs_param (@gc_stack G1) lp = Some T -> gs_param (@gc_stack G2) lp = Some T) /\
  ⊢ @gc_deps G2 ⍮ @gc_stack G2 ⍮ ⋅.

Section Ext.
  Variables (G1 G2 : GCtx).
  Hypothesis Hext : gext G1 G2.
  #[local] Notation Θ1 := (@gc_deps G1).
  #[local] Notation Ξ1 := (@gc_stack G1).
  #[local] Notation Θ2 := (@gc_deps G2).
  #[local] Notation Ξ2 := (@gc_stack G2).

  Lemma gext_syn :
    (forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A').
  Proof. destruct Hext as (Hr & Hn & _ & _ & Hb); apply rebase_preserves_wf; assumption. Qed.

  Lemma gext_ctx : forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ.
  Proof. apply gext_syn. Qed.
  Lemma gext_exp : forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A.
  Proof. apply gext_syn. Qed.
  Lemma gext_exp_eq : forall Γ A M M', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A.
  Proof. apply gext_syn. Qed.
  Lemma gext_subtyp : forall Γ A A', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A'.
  Proof. apply gext_syn. Qed.

  Lemma gext_gctx : ⊢g Θ2 ⍮ Ξ2.
  Proof. destruct Hext as (_ & _ & _ & _ & Hb); eapply ctx_wf_gctx; exact Hb. Qed.

  Lemma gext_ctx_sub : forall Δ Γ, Θ1 ⍮ Ξ1 ⊢ Δ ⊆ Γ -> Θ2 ⍮ Ξ2 ⊢ Δ ⊆ Γ.
  Proof.
    induction 1; econstructor; eauto using gext_exp, gext_subtyp, gext_gctx.
  Qed.

  (** Kripke weakenings are *covariant* in the global context. *)
  Lemma gext_kripke : forall Δ Γ φ, @wk_kripke G1 Δ Γ φ -> @wk_kripke G2 Δ Γ φ.
  Proof.
    induction 1; [ eapply kwk_id | eapply kwk_shift ]; eauto using gext_ctx_sub.
  Qed.

  (** Evaluation and readback only grow (as in extension_invariance/Ext.v). *)
  Theorem gext_eval :
    (forall M ρ m, eval_exp Θ1 Ξ1 M ρ m -> eval_exp Θ2 Ξ2 M ρ m) /\
    (forall A MZ MS m ρ r, eval_natrec Θ1 Ξ1 A MZ MS m ρ r -> eval_natrec Θ2 Ξ2 A MZ MS m ρ r) /\
    (forall m n r, eval_app Θ1 Ξ1 m n r -> eval_app Θ2 Ξ2 m n r).
  Proof.
    destruct Hext as (_ & _ & Hr & Hp & _).
    apply eval_mut_ind; intros; solve [econstructor; eauto].
  Qed.

  Theorem gext_read :
    (forall s m M, read_nf Θ1 Ξ1 s m M -> read_nf Θ2 Ξ2 s m M) /\
    (forall s m M, read_ne Θ1 Ξ1 s m M -> read_ne Θ2 Ξ2 s m M) /\
    (forall s m M, read_typ Θ1 Ξ1 s m M -> read_typ Θ2 Ξ2 s m M).
  Proof.
    destruct gext_eval as (He & _ & Ha).
    apply read_mut_ind; intros; econstructor; eauto.
  Qed.

  Lemma gext_per_bot : forall m n, @per_bot G1 m n -> @per_bot G2 m n.
  Proof.
    cbn; intros * H s; destruct (H s) as [L [? ?]].
    exists L; split; apply gext_read; assumption.
  Qed.
End Ext.

(** ** 2. The clauses that quantify over nothing are monotone *)

Section FirstOrder.
  Variables (G1 G2 : GCtx).
  Hypothesis Hext : gext G1 G2.

  Lemma nat_glu_typ_pred_mono : forall i Γ A,
      @nat_glu_typ_pred G1 i Γ A -> @nat_glu_typ_pred G2 i Γ A.
  Proof. intros * H; exact (gext_exp_eq _ _ Hext _ _ _ _ H). Qed.

  Lemma univ_glu_typ_pred_mono : forall j i Γ A,
      @univ_glu_typ_pred G1 j i Γ A -> @univ_glu_typ_pred G2 j i Γ A.
  Proof. intros * H; exact (gext_exp_eq _ _ Hext _ _ _ _ H). Qed.
End FirstOrder.

(** ** 3. The Kripke clause of a neutral

    Every neutral clause of the model ([glu_nat_neut], [neut_glu_typ_pred],
    [neut_glu_exp_pred], [glu_elem_bot], and likewise [glu_elem_top],
    [glu_typ_top]) has this shape.  It quantifies *negatively* over the
    Kripke weakenings [Δ ⊢k φ : Γ] of the context it is read in, so at [G2] it
    ranges over [Δ] whose types mention globals [G1] does not have.  Nothing
    at [G1] speaks about such a [Δ]. *)

Definition ne_clause (G : GCtx) Γ A M m : Prop :=
  forall Δ φ (M' : ne), @wk_kripke G Δ Γ φ ->
    read_ne (@gc_deps G) (@gc_stack G) (length Δ) m M' ->
    wf_exp_eq (@gc_deps G) (@gc_stack G) Δ A[φ]ʷ M[φ]ʷ M'.

(** The one extra fact that would transport it: readback commutes with
    [⇑^n].  It is true of well-scoped neutrals but it is *not* a lemma of the
    development — the Kripke quantifier is there precisely so that no
    readback-renaming lemma is ever needed — and proving it means relating the
    evaluation of a closure at the fresh variables [s] and [s + n], i.e. a
    renaming theory of the domain. *)
Definition read_shift (G : GCtx) (s : nat) (m : domain_ne) : Prop :=
  forall n (M0 M1 : ne),
    read_ne (@gc_deps G) (@gc_stack G) s m M0 ->
    read_ne (@gc_deps G) (@gc_stack G) (s + n) m M1 ->
    (M1 : exp) = (M0 : exp)[wk_shiftn n]ʷ.

Section Neutral.
  Variables (G1 G2 : GCtx).
  Hypothesis Hext : gext G1 G2.

  (** With it (and [⊢ Γ] at [G1], see section 4 for why), the clause moves:
      read the [G1] clause at [Γ] itself, rebase, weaken at [G2]. *)
  Theorem ne_clause_mono : forall Γ A M m,
      wf_ctx (@gc_deps G1) (@gc_stack G1) Γ ->
      @per_bot G1 m m ->
      read_shift G2 (length Γ) m ->
      ne_clause G1 Γ A M m -> ne_clause G2 Γ A M m.
  Proof.
    intros * HΓ Hbot Hsh H Δ φ M' Hk Hr.
    destruct (Hbot (length Γ)) as [M0 [HM0 _]].
    assert (H0 : wf_exp_eq (@gc_deps G1) (@gc_stack G1) Γ A[wk_id]ʷ M[wk_id]ʷ M0)
      by (apply H; [ apply (@kripke_id G1); exact HΓ | exact HM0 ]).
    rewrite !exp_wk_id in H0.
    apply (gext_exp_eq _ _ Hext) in H0.
    pose proof (@kripke_shiftn G2 _ _ _ Hk) as [Hle Heq].
    pose proof (@kripke_preserves_exp_eq G2 _ _ _ _ _ _ H0 Hk) as H1.
    replace (length Δ) with (length Γ + (length Δ - length Γ)) in Hr by lia.
    rewrite (Hsh _ _ _ (proj1 (proj2 (gext_read _ _ Hext)) _ _ _ HM0) Hr).
    rewrite <- Heq; exact H1.
  Qed.
End Neutral.

(** ** 4. Without [⊢ Γ] at [G1] the model is not monotone at all

    [glu_nat_neut] has no premise tying [Γ] to [G1]; when [Γ] is not a
    context at [G1] its Kripke clause is vacuous.  [G1] has no frame, [G2]
    one frame with a type [c := ℕ : Type@0]; [Γ = ⋅ ▹ c]. *)

Definition p_c : path := p_rel 0 ("c" :: nil).
Definition E_c : gentry := ge_def true false (Type@0) (Some ℕ).
Definition U_c : gunit := gu_mk nil (⋄ ⊳ "c" ↦ E_c).
Definition G1c : GCtx := gc_mk nil nil.
Definition G2c : GCtx := gc_mk nil (U_c :: nil).
Definition Γc : ctx := nil ▹ a_glob p_c.

Lemma wf_G2c : ⊢g nil ⍮ U_c :: nil.
Proof.
  assert (H0 : ⊢g nil ⍮ nil) by (apply wf_gctx_intro, wf_gstack_nil, wf_gdeps_nil).
  assert (H1 : ⊢g nil ⍮ gu_mk nil ⋄ :: nil).
  { apply wf_gctx_intro, wf_gstack_cons; [ apply wf_gstack_nil, wf_gdeps_nil |].
    apply wf_gunit_intro, wf_gmod_nil, wf_ctx_empty; exact H0. }
  apply wf_gctx_intro, wf_gstack_cons; [ apply wf_gstack_nil, wf_gdeps_nil |].
  apply wf_gunit_intro; cbn.
  eapply wf_gmod_ext; [ apply wf_gmod_nil, wf_ctx_empty; exact H0 | | ].
  - apply wf_gentry_def, wf_nat, wf_ctx_empty; exact H1.
  - unfold gm_fresh; cbn; intros [].
Qed.

Lemma lookup_c : nil ⍮ U_c :: nil ∋ᵍ p_c ⇒ ⋅ ⍮ E_c.
Proof.
  unfold p_c, E_c.
  change (@nil exp) with ((@nil exp)[↑ₘ 0]ᵐ).
  change (Type@0) with ((Type@0 : exp)[↑ₘ 0]ᵐ).
  change (Some (ℕ : exp)) with ((Some (ℕ : exp))[↑ₘ 0]ᵐ).
  eapply gcl_rel; [ reflexivity | cbn; apply gml_last ].
Qed.

Lemma wf_Γc_G2 : ⊢ nil ⍮ U_c :: nil ⍮ Γc.
Proof.
  unfold Γc; apply wf_ctx_extend with (i := 0).
  change (Type@0 : exp) with (ctx_pi nil (Type@0)).
  eapply wf_glob; [ constructor; exact wf_G2c | exact lookup_c ].
Qed.

Lemma not_wf_Γc_G1 : ~ ⊢ nil ⍮ nil ⍮ Γc.
Proof.
  intros H; destruct wf_scoped as [Hs _]; destruct (Hs _ _ _ H) as [Hc _].
  cbn in Hc; unfold path_ok in Hc; cbn in Hc; lia.
Qed.

(** The two contexts are related by [gext]: nothing resolves at [G1]. *)
Lemma gext_G1c_G2c : gext G1c G2c.
Proof.
  repeat split; cbn.
  - intros * H; inversion H; subst;
      [ destruct n; discriminate | discriminate ].
  - intros [| n] U H; discriminate.
  - intros [[fp | n] ip] r H; unfold gc_resolve in H; cbn in H;
      [ discriminate | destruct n; discriminate ].
  - intros [n k] T H; unfold gs_param in H; cbn in H; destruct n; discriminate.
  - constructor; exact wf_G2c.
Qed.

Definition m_var0 : domain := ⇑ ℕᵈ (#ᵈ 0).

Lemma glu_nat_G1c : @glu_nat G1c Γc #1 m_var0.
Proof.
  constructor.
  - intros s; eexists; split; constructor.
  - intros * Hk; exfalso; apply not_wf_Γc_G1.
    exact (@kripke_cod G1c _ _ _ Hk).
Qed.

Lemma not_glu_nat_G2c : ~ @glu_nat G2c Γc #1 m_var0.
Proof.
  intros H; inversion H; subst.
  assert (Hk : @wk_kripke G2c Γc Γc wk_id) by (apply (@kripke_id G2c); exact wf_Γc_G2).
  assert (Hr : read_ne nil (U_c :: nil) (List.length Γc) (#ᵈ 0) (#ⁿ 0)) by (cbn; constructor).
  match goal with Hc : forall Δ φ M', _ |- _ => pose proof (Hc _ _ _ Hk Hr) as Heq end.
  destruct wf_scoped as (_ & _ & Hs & _); destruct (Hs _ _ _ _ _ _ Heq) as (_ & HM & _).
  cbn in HM; lia.
Qed.

Theorem glu_nat_not_mono :
  exists G1 G2 Γ M m, gext G1 G2 /\ @glu_nat G1 Γ M m /\ ~ @glu_nat G2 Γ M m.
Proof.
  exists G1c, G2c, Γc, #1, m_var0.
  split; [ exact gext_G1c_G2c | split; [ exact glu_nat_G1c | exact not_glu_nat_G2c ] ].
Qed.

(** ** 5. At [Π] the gluing model inherits the PER model's obstruction

    Whether a value is a glued type at all is exactly whether it is a PER type
    ([per_univ_glu_univ_elem], [glu_univ_elem_per_univ]).  So "a glued type
    at [G1] is a glued type at [G2]" is *equivalent* to monotonicity of
    [per_univ], which is stuck at [Π] (extension_invariance/MonoAttempt.v:
    the argument position is contravariant and [per_bot] grows strictly,
    PERExt.v [per_nat_not_antimono]). *)

Theorem glu_type_mono_iff_per_mono : forall G1 G2,
    (forall i a, (exists P El, @glu_univ_elem G1 i P El a) -> exists P El, @glu_univ_elem G2 i P El a) <->
    (forall i a, @per_univ G1 i a a -> @per_univ G2 i a a).
Proof.
  intros G1 G2; split.
  - intros H i a Ha.
    destruct (H i a (@per_univ_glu_univ_elem G1 _ _ Ha)) as (P & El & HG).
    exact (@glu_univ_elem_per_univ G2 _ _ _ _ HG).
  - intros H i a (P & El & HG).
    apply (@per_univ_glu_univ_elem G2), H.
    exact (@glu_univ_elem_per_univ G1 _ _ _ _ HG).
Qed.

(** ** 6. At a fixed context, a global needs only its own gluing at [⋅]

    The [wf_glob]/[wf_param] cases of the gluing fundamental theorem: from
    [⊩ Γ] and [⋅ ⊩ c : T], [Γ ⊩ c : T] — with the *same* [σ] and [ρ], so not
    even closedness of [c] and [T] is needed (the [⋅] predicate
    [nil_glu_sub_pred] constrains neither).  Soundness of NbE has no δ case:
    its fundamental theorem is over typing only, and the conversion rule goes
    through completeness. *)

Section Closed.
  Context {GC : GCtx}.

  Lemma glu_ctx_env_escape : forall Γ Sb Δ σ ρ,
      glu_ctx_env Sb Γ -> Sb Δ σ ρ -> wf_sub gc_deps gc_stack Δ Γ σ.
  Proof.
    intros * HΓ HS; inversion HΓ; subst;
      match goal with HSb : _ <∙> _ |- _ => apply HSb in HS end;
      [ exact HS | destruct HS; assumption ].
  Qed.

  Lemma glu_ctx_env_nil_inv : forall Sb, glu_ctx_env Sb ⋅ -> Sb <∙> nil_glu_sub_pred.
  Proof. intros * H; inversion H; subst; assumption. Qed.

  Theorem glu_rel_exp_closed_weaken : forall Γ c T,
      glu_rel_ctx Γ ->
      glu_rel_exp ⋅ c T ->
      glu_rel_exp Γ c T.
  Proof.
    intros * [SbΓ HΓ] (Sb0 & H0 & i & Hc).
    exists SbΓ; split; [ exact HΓ | exists i ].
    intros Δ σ ρ HS; apply Hc.
    apply (glu_ctx_env_nil_inv _ H0); cbn.
    pose proof (glu_ctx_env_escape _ _ _ _ _ HΓ HS) as Hσ.
    constructor.
    - eapply wf_sub_dom; exact Hσ.
    - constructor; inversion H0; assumption.
    - intros * Hx; inversion Hx.
  Qed.
End Closed.

(** ** 7. The simplest instance of question 2: one frame grows

    An older member [c] with [⋅ ⊩ c : ℕ] at [G1] keeps it at the grown [G2],
    given [read_shift] (section 3).  This is the whole of what survives: for a
    member of a parameterized frame the type resolution hands back is a
    [ctx_pi] (members are generalized over the frame's telescope), and at [Π]
    the statement needs section 5's PER monotonicity *and* the
    contravariant argument clause of [pi_glu_exp_pred]. *)

Section Nat.
  Variables (G1 G2 : GCtx).
  Hypothesis Hext : gext G1 G2.

  Lemma glu_nat_mono : forall Γ,
      wf_ctx (@gc_deps G1) (@gc_stack G1) Γ ->
      (forall m, @per_bot G1 m m -> read_shift G2 (List.length Γ) m) ->
      forall M a, @glu_nat G1 Γ M a -> @glu_nat G2 Γ M a.
  Proof.
    intros Γ HΓ Hrs M a H; induction H.
    - apply glu_nat_zero; exact (gext_exp_eq _ _ Hext _ _ _ _ H).
    - eapply glu_nat_succ; [ exact (gext_exp_eq _ _ Hext _ _ _ _ H) | auto ].
    - apply glu_nat_neut; [ exact (gext_per_bot _ _ Hext _ _ H) |].
      assert (Hc : ne_clause G1 Γ ℕ M m) by (intros Δ φ M' Hk Hr; cbn; apply H0; assumption).
      pose proof (ne_clause_mono _ _ Hext _ _ _ _ HΓ H (Hrs _ H) Hc) as Hc2.
      intros Δ φ M' Hk Hr; exact (Hc2 _ _ _ Hk Hr).
  Qed.
End Nat.

Lemma kripke_to_nil : forall {GC : GCtx} Δ, wf_ctx gc_deps gc_stack Δ -> exists φ, wk_kripke Δ ⋅ φ.
Proof.
  intros GC Δ; induction Δ as [| A Δ IH]; intros HΔ.
  - exists wk_id; apply kripke_id; exact HΔ.
  - assert (HΔ' : wf_ctx gc_deps gc_stack Δ) by (inversion HΔ; subst; eapply presup_exp_ctx; eassumption).
    destruct (IH HΔ') as [φ Hφ].
    exists (φ ⊙ ↑); eapply kripke_compose; [ apply kripke_shift; exact HΔ | exact Hφ ].
Qed.

Theorem closed_nat_member_survives_grow : forall G1 G2 c,
    gext G1 G2 ->
    (forall m, @per_bot G1 m m -> read_shift G2 0 m) ->
    exp_scoped 0 (gs_cs (@gc_stack G1)) c ->
    @glu_rel_exp G1 ⋅ c ℕ -> @glu_rel_exp G2 ⋅ c ℕ.
Proof.
  intros G1 G2 c Hext Hrs Hsc (Sb0 & H0 & i & Hc).
  assert (Hg1 : ⊢g @gc_deps G1 ⍮ @gc_stack G1) by (inversion H0; assumption).
  assert (Hb1 : wf_ctx (@gc_deps G1) (@gc_stack G1) ⋅) by (constructor; exact Hg1).
  exists nil_glu_sub_pred; split; [ constructor; [ reflexivity | exact (gext_gctx _ _ Hext) ] |].
  exists i; intros Δ σ ρ Hσ; cbn in Hσ.
  assert (Hσ1 : Sb0 ⋅ σ ρ).
  { apply (glu_ctx_env_nil_inv _ H0); cbn.
    constructor; [ exact Hb1 | exact Hb1 | intros * Hx; inversion Hx ]. }
  destruct (Hc _ _ _ Hσ1) as [a m P El Ha Hm HG HEl].
  inversion Ha; subst.
  simp glu_univ_elem in HG; inversion HG; subst.
  match goal with HE : El <∙> _ |- _ => apply HE in HEl end.
  destruct HEl as [HT Hn].
  rewrite (exp_closed_sub _ _ σ Hsc) in *; cbn in HT |- *.
  econstructor.
  - apply (gext_eval _ _ Hext); constructor.
  - apply (gext_eval _ _ Hext); exact Hm.
  - simp glu_univ_elem; apply glu_univ_elem_core_nat; reflexivity.
  - destruct (@kripke_to_nil G2 Δ (wf_sub_dom _ _ _ _ _ Hσ)) as [φ Hφ].
    split.
    + pose proof (@kripke_preserves_exp_eq G2 _ _ _ _ _ _ (gext_exp_eq _ _ Hext _ _ _ _ HT) Hφ) as H'.
      cbn in H'; exact H'.
    + pose proof (glu_nat_mono _ _ Hext _ Hb1 Hrs _ _ Hn) as Hn2.
      pose proof (@glu_nat_resp_wk G2 _ _ _ Hn2 _ _ Hφ) as Hn3.
      rewrite (exp_closed_wk _ _ φ Hsc) in Hn3.
      rewrite (exp_closed_sub _ _ σ Hsc); exact Hn3.
Qed.

Print Assumptions glu_nat_not_mono.
Print Assumptions ne_clause_mono.
Print Assumptions glu_type_mono_iff_per_mono.
Print Assumptions glu_rel_exp_closed_weaken.
Print Assumptions closed_nat_member_survives_grow.
