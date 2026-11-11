(** * Glued Module Values

    The gluing of module values ([glu_dmod]) read through substitutions
    and equations of module expressions, the environment of a body glued
    along the body's context ([glu_body_env]), and the closure of a glued
    unit's literal glued as the literal ([glu_lit_modexp_at]): the
    producer of the slot clause of the context gluing. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import LetPeeling.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas DescTyping LookupSound.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases UnitCases.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Values Mem.
From Mctt.Core.Completeness.Consequences Require Import AnnotatedUpto.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Slot Premise of a Context Gluing *)

(** A glued context extended by a slot or a definition with a module part
    glues the unit's literal at every glued environment of the context. *)
Lemma glu_ctx_env_lit_inversion : forall {Γ TSb e U Sb},
    EG Γ ∈ glu_ctx_env ↘ TSb ->
    EG (e :: Γ) ∈ glu_ctx_env ↘ Sb ->
    centry_unit e = Some U ->
    forall Δ σ ρ h, Δ ⊢ˢ σ ® ρ ∈ TSb -> ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h -> glu_dmod Δ σ Γ (me_lit U) h.
Proof.
  intros * HΓ HeΓ HU * Hσ Hh.
  inversion HeΓ; subst; cbn [centry_unit] in HU; try discriminate; injection HU as <-.
  all: match goal with
       | H0 : glu_ctx_env ?T0 _, Hv : forall (_ : ctx) (_ : sub) (_ : env) (_ : dmod), ?T0 _ _ _ -> _ |- _ =>
           eapply Hv; [ apply (functional_glu_ctx_env HΓ H0); exact Hσ | exact Hh ]
       end.
Qed.

(** ** Reading a Glued Module Value Through a Substitution *)

(** A factorization of [σ1] weakened, through [ζ2], gives one of [σ0]
    weakened, through [ζ ⨟ ζ2], when [σ0] is [ζ ⨟ σ1]. *)
Lemma glu_sub_through_compose : forall {Δ σ0 Γ0 Γ1 ζ σ1 Δ' φ Γ2 ζ2 σ2},
    Γ1 ⊢ˢ ζ : Γ0 ->
    Δ ⊢ˢ σ0 ≈ ζ ⨟ σ1 : Γ0 ->
    glu_sub_through Δ σ1 Γ1 Δ' φ Γ2 ζ2 σ2 ->
    glu_sub_through Δ σ0 Γ0 Δ' φ Γ2 (ζ ⨟ ζ2) σ2.
Proof.
  intros * Hζ Heq [Hφ Hζ2 Hσ2 E].
  constructor; [ exact Hφ | exact (wf_sub_compose _ _ _ _ _ _ _ Hζ Hζ2) | exact Hσ2 |].
  eapply wf_sub_eq_trans; [ eapply wf_sub_eq_sb_wk; [ exact Heq | exact Hφ ] |].
  eapply wf_sub_eq_respects_sb_eq; [| symmetry; apply sb_compose_assoc ].
  assert (Hw : sb_eq (ζ ⨟ sb_wk σ1 φ) (sb_wk (ζ ⨟ σ1) φ)).
  { rewrite (sb_wk_compose (ζ ⨟ σ1)), sb_compose_assoc, <- sb_wk_compose; reflexivity. }
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| exact Hw ].
  apply wf_sub_eq_sym; eapply wf_sub_eq_compose_right; [ exact Hζ | exact E ].
Qed.

(** A module value glued as [H0[σ0]] is glued as [H0[ζ][σ1]] when [σ0]
    is [ζ ⨟ σ1]: the factorizations of [σ1] are ones of [σ0]. *)
Lemma glu_dmod_through :
  (forall Δ σ0 Γ0 H0 h, glu_dmod Δ σ0 Γ0 H0 h ->
     forall Γ1 ζ σ1, Γ1 ⊢ˢ ζ : Γ0 -> Δ ⊢ˢ σ1 : Γ1 -> Δ ⊢ˢ σ0 ≈ ζ ⨟ σ1 : Γ0 -> glu_dmod Δ σ1 Γ1 H0[ζ]ᵐ h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module *)
    intros * Hσ HH0 HH0p Hl Hlen Hargs _ Γ1 ζ σ1 Hζ Hσ1 Heq.
    eapply glu_dmod_global; [ exact Hσ1 | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) | | exact Hl | exact Hlen | exact Hargs ].
    rewrite modexp_sub_sub.
    eapply wf_me_trans; [| exact HH0p ].
    apply wf_me_sym; exact (sub_eq_preserves_modexp _ _ _ _ _ HH0 _ _ _ Heq).
  - (** A body *)
    intros * Hσ HH0 Hmem Hsub IHsub Γ1 ζ σ1 Hζ Hσ1 Heq.
    apply glu_dmod_body; [ exact Hσ1 | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst Hm; rewrite modexp_sub_sub in Hm |- *.
      exact (Hg _ _ _ _ _ _ _ _ (glu_sub_through_compose Hζ Heq Hst) Hm).
    + intros * Hp Hu Hb Hc; exact (IHsub _ _ _ _ _ _ _ Hp Hu Hb Hc _ _ _ Hζ Hσ1 Heq).
  - (** A value lacking a parameter *)
    intros * Hσ HH0 Hn Hpar Hex Happ _ Γ1 ζ σ1 Hζ Hσ1 Heq.
    eapply glu_dmod_fun; [ exact Hσ1 | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) | exact Hn | | exact Hex | ].
    + intros * Hst Hm; rewrite modexp_sub_sub in Hm.
      exact (Hpar _ _ _ _ _ _ _ _ _ _ (glu_sub_through_compose Hζ Heq Hst) Hm).
    + intros * Hst Hm; rewrite modexp_sub_sub in Hm; rewrite (modexp_sub_sub H0 ζ ζ0).
      exact (Happ _ _ _ _ _ _ _ _ _ _ (glu_sub_through_compose Hζ Heq Hst) Hm).
Qed.

(** ** Reading a Glued Module Value at an Equal Module Expression *)

(** [H0] denotes what [H1] does at every substitution: their members,
    submodules and applications are looked up alike. *)
Definition same_denote (Γ0 : ctx) (H0 H1 : modexp) : Prop :=
  forall Γ1 ζ R, Γ1 ⊢ˢ ζ : Γ0 -> mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ R -> mdenote gc_deps gc_stack Γ1 H1[ζ]ᵐ R.

(** Denoting alike at every substitution, so at every substitution of a
    substitution. *)
Lemma same_denote_sub : forall {Γ0 Γ1 ζ H0 H1}, Γ1 ⊢ˢ ζ : Γ0 -> same_denote Γ0 H0 H1 -> same_denote Γ1 H0[ζ]ᵐ H1[ζ]ᵐ.
Proof.
  intros * Hζ Hs Γ2 ζ' R Hζ' Hm; rewrite modexp_sub_sub in *.
  exact (Hs _ _ _ (wf_sub_compose _ _ _ _ _ _ _ Hζ Hζ') Hm).
Qed.

(** Selection keeps denoting alike, from a module expression that names
    no stored module at any substitution: its selections are looked up
    in what it denotes, not by path. *)
Lemma same_denote_mem : forall {Γ0 H0 H1} y, same_denote Γ0 H0 H1 ->
    (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H0[ζ]ᵐ = None) ->
    same_denote Γ0 (me_mem H0 y) (me_mem H1 y).
Proof.
  intros * Hs Hq Γ1 ζ R Hζ Hm; cbn [modexp_sub] in *.
  inversion Hm; subst;
    try (match goal with Hp : mod_qname (me_mem _ _) = Some _ |- _ =>
           cbn [mod_qname] in Hp; rewrite (Hq _ _ Hζ) in Hp; discriminate end).
  econstructor; [ eapply Hs; eassumption | eassumption .. ].
Qed.

(** Application to the variable of a further parameter keeps denoting
    alike. *)
Lemma same_denote_app_var : forall {Γ0 H0 H1} κ B, same_denote Γ0 H0 H1 ->
    same_denote (Γ0 ▹{κ} B) (me_app H0[Wk]ᵐ #0) (me_app H1[Wk]ᵐ #0).
Proof.
  intros * Hs Γ1 ζ R Hζ Hm; cbn [modexp_sub] in *.
  rewrite !modexp_sub_sub in *.
  inversion Hm; subst;
    try (match goal with Hp : mod_qname (me_app _ _) = Some _ |- _ => cbn in Hp; discriminate end).
  eapply mdenote_app; [| eassumption ].
  eapply Hs; [| eassumption ].
  eapply wf_sub_compose; [ eapply wf_sub_shift; exact (wf_sub_cod _ _ _ _ _ Hζ) | exact Hζ ].
Qed.

(** A well-formed module expression denotes a module with a telescope. *)
Lemma me_mod_tele_exists : forall {Γ H H'}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H' ->
    exists R T, mdenote gc_deps gc_stack Γ H R /\ mdesc_mod_tele R = Some T.
Proof.
  intros * HH.
  destruct (me_denotes _ _ _ _ _ HH) as (R & Rm & HR & HRm).
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH HR) HRm) as Hok.
  destruct (desc_ok_tele _ _ _ _ Hok (mdesc_mod_is_mod _ _ HRm)) as (T & Ht).
  exists R, T; split; [ exact HR | unfold mdesc_mod_tele; rewrite HRm; exact Ht ].
Qed.

(** Selections of equal module expressions denoting alike are equal. *)
Lemma wf_me_mem_same_denote : forall {Γ0 H0 H1} y,
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H1 ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H1 y ≈ me_mem H1 y ->
    same_denote Γ0 (me_mem H1 y) (me_mem H0 y) ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H1 y.
Proof.
  intros * HH HH1 Hs.
  destruct (me_mod_tele_exists HH1) as (R & T & HR & HT).
  assert (HR0 : mdenote gc_deps gc_stack Γ0 (me_mem H0 y) R).
  { pose proof (Hs _ Id R (wf_sub_id _ _ _ (presup_modexp_eq_ctx HH))) as H; rewrite !modexp_sub_id in H; exact (H HR). }
  eapply wf_me_mem; [ exact HH | exact HR0 | exact HT | exact HR | exact HT ].
Qed.

(** A term glued as the member of [H1] is glued as the member of an
    equal [H0] that denotes alike, at the same type: the members are
    equal ([wf_exp_eq_mem_cong]), read where the gluing is. *)
Lemma glu_elem_at_same_denote : forall {Γ1 H0 H1 x R A' Δ σ1 a m} {i : nat} {P El},
    gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ H0 ≈ H1 ->
    mdenote gc_deps gc_stack Γ1 (me_mem H0 x) R ->
    mdenote gc_deps gc_stack Γ1 (me_mem H1 x) R ->
    mdesc_type R = Some A' ->
    Δ ⊢ˢ σ1 : Γ1 ->
    glu_elem_at Δ A'[σ1] (a_mem H1 x)[σ1] a m i P El ->
    glu_elem_at Δ A'[σ1] (a_mem H0 x)[σ1] a m i P El.
Proof.
  intros * HH Hm0 Hm1 HA Hσ [Hu HT HM].
  constructor; [ exact Hu | exact HT |].
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hu | exact HM |].
  apply wf_exp_eq_sym; cbn [exp_sub].
  eapply wf_exp_eq_mem_cong;
    [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hσ)
    | eapply wf_sub_mdenote_mem; [ exact HH | exact Hm0 | exact Hσ ] | eapply mdesc_type_sub; exact HA
    | eapply wf_sub_mdenote_mem; [ exact (wf_modexp_eq_refl_right HH) | exact Hm1 | exact Hσ ] | eapply mdesc_type_sub; exact HA
    | exact (glu_univ_elem_trm_escape _ _ _ _ Hu _ _ _ _ HM) ].
Qed.

(** A slot denotes what its unit's literal does, both ways, at every
    typed substitution: the slot goes to the literal at the substitution,
    or to a slot of that unit ([wf_sub_mod_compat]). *)
Lemma same_denote_slot : forall {Γ y U}, Γ ∋ #y ≔ₘ U ->
    same_denote Γ (me_var y) (me_lit U) /\ same_denote Γ (me_lit U) (me_var y).
Proof.
  intros * Hy; split; intros Γ1 ζ R Hζ Hm;
    destruct (wf_sub_mod_compat _ _ _ _ _ Hζ _ _ Hy) as [E | (z & Ez & Hz)];
    cbn [modexp_sub] in *; rewrite ?E in *; try exact Hm; rewrite Ez in *; cbn [sentry_modexp] in *.
  - inversion Hm; subst; try (match goal with Hp : mod_qname (me_var _) = Some _ |- _ => cbn in Hp; discriminate end).
    match goal with Hl : Γ1 ∋ # z ≔ₘ ?U0 |- _ => pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hz) as -> end.
    apply mdenote_lit; assumption.
  - apply mdenote_lit_inv in Hm; eapply mdenote_slot; [ exact Hz | exact Hm ].
Qed.

(** No typed substitution of a slot, nor any of a literal, names a
    stored module. *)
Lemma mod_qname_sub_var : forall Γ y U Γ1 ζ, Γ ∋ #y ≔ₘ U -> Γ1 ⊢ˢ ζ : Γ -> mod_qname (me_var y)[ζ]ᵐ = None.
Proof.
  intros * Hy Hζ; destruct (wf_sub_mod_compat _ _ _ _ _ Hζ _ _ Hy) as [E | (z & Ez & _)];
    cbn [modexp_sub]; [ rewrite E | rewrite Ez ]; reflexivity.
Qed.

Lemma mod_qname_sub_lit : forall U ζ, mod_qname (me_lit U)[ζ]ᵐ = None.
Proof. reflexivity. Qed.

(** A module value glued as [H1] is glued as an equal [H0] denoting alike
    both ways at every substitution, neither naming a stored module: its
    members are looked up alike and equal ([glu_elem_at_same_denote]),
    and so are its submodules' and its applications'. *)
Lemma glu_dmod_same_denote :
  (forall Δ σ0 Γ0 H1 h, glu_dmod Δ σ0 Γ0 H1 h ->
     forall H0, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H1 -> same_denote Γ0 H0 H1 -> same_denote Γ0 H1 H0 ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H0[ζ]ᵐ = None) ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H1[ζ]ᵐ = None) ->
       glu_dmod Δ σ0 Γ0 H0 h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module *)
    intros * Hσ HH1 HH1p Hl Hlen Hargs _ H0 HH Hs01 Hs10 Hq0 Hq1.
    eapply glu_dmod_global; [ exact Hσ | exact (wf_modexp_eq_refl_left HH) | | exact Hl | exact Hlen | exact Hargs ].
    eapply wf_me_trans; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hσ) | exact HH1p ].
  - (** A body *)
    intros * Hσ HH1 Hmem Hsub IHsub H0 HH Hs01 Hs10 Hq0 Hq1.
    apply glu_dmod_body; [ exact Hσ | exact (wf_modexp_eq_refl_left HH) | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst Hm HA HS HAt.
      pose proof (same_denote_mem x Hs01 Hq0 _ _ _ (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) Hm) as Hm1.
      destruct (Hg _ _ _ _ _ _ _ _ Hst Hm1 HA HS HAt) as (i & P & El & Hgl).
      exists i, P, El.
      eapply glu_elem_at_same_denote;
        [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst))
        | exact Hm | exact Hm1 | exact HA | exact (glu_sub_through_rest _ _ _ _ _ _ _ _ Hst) | exact Hgl ].
    + intros * Hp Hu Hb Hc.
      pose proof (Hsub _ _ _ _ _ _ _ Hp Hu Hb Hc) as Hg1.
      assert (HH1y : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H0 y).
      { apply (wf_modexp_eq_refl_left (H' := me_mem H1 y)).
        eapply wf_me_mem_same_denote; [ exact HH | | exact (same_denote_mem y Hs10 Hq1) ].
        destruct Hg1; assumption. }
      eapply IHsub; [ exact Hp | exact Hu | exact Hb | exact Hc | | exact (same_denote_mem y Hs01 Hq0)
                    | exact (same_denote_mem y Hs10 Hq1) | intros Γ2 ζ Hζ; cbn; rewrite (Hq0 _ _ Hζ); reflexivity
                    | intros Γ2 ζ Hζ; cbn; rewrite (Hq1 _ _ Hζ); reflexivity ].
      eapply wf_me_mem_same_denote; [ exact HH | | exact (same_denote_mem y Hs10 Hq1) ].
      destruct Hg1; assumption.
  - (** A value lacking a parameter *)
    intros * Hσ HH1 Hn Hpar Hex Happ IHapp H0 HH Hs01 Hs10 Hq0 Hq1.
    eapply glu_dmod_fun; [ exact Hσ | exact (wf_modexp_eq_refl_left HH) | exact Hn | | exact Hex | ].
    + intros * Hst Hm; exact (Hpar _ _ _ _ _ _ _ _ _ _ Hst (Hs01 _ _ _ (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) Hm)).
    + intros * Hst Hm HT Hv HS HB * Hu HP HN Hhc.
      pose proof (Hs01 _ _ _ (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) Hm) as Hm1.
      pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hst Hm1 HT Hv HS HB _ _ _ _ _ _ Hu HP HN Hhc) as Hg1.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      pose proof (same_denote_sub Hζ Hs01) as Hs01'; pose proof (same_denote_sub Hζ Hs10) as Hs10'.
      eapply IHapp; [ exact Hst | exact Hm1 | exact HT | exact Hv | exact HS | exact HB | exact Hu | exact HP | exact HN | exact Hhc
                    | | exact (same_denote_app_var _ _ Hs01') | exact (same_denote_app_var _ _ Hs10')
                    | intros; reflexivity | intros; reflexivity ].
      (** The applications are equal: the arguments' and the parameters'
          premises are those of [H1]'s application *)
      assert (HHg : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_app H1[ζ]ᵐ[Wk]ᵐ #0 ≈ me_app H1[ζ]ᵐ[Wk]ᵐ #0)
        by (destruct Hg1; assumption).
      destruct (proj1 (modexp_gen _ _ _ _ _ HHg)) as [HH1w (R' & T' & B' & T1' & S' & HR' & HT' & Hv' & HB' & HS' & HN')].
      assert (HR0 : mdenote gc_deps gc_stack (Γ1 ▹{domain_kind a} B) H0[ζ]ᵐ[Wk]ᵐ R').
      { apply (Hs10' (Γ1 ▹{domain_kind a} B) Wk R'); [ eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg) | exact HR' ]. }
      assert (HHw : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ H0[ζ]ᵐ[Wk]ᵐ ≈ H1[ζ]ᵐ[Wk]ᵐ).
      { eapply sub_preserves_modexp; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) |].
        eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg). }
      eapply wf_me_app; [ exact HHw | exact HR0 | exact HT' | exact Hv' | exact HB' | exact HS' | exact HN'
                        | apply wf_exp_eq_refl; exact HN' | exact HR' | exact HT' | exact Hv' | exact HB' | exact HS' | exact HN' ].
Qed.

(** ** The Environment of a Body, Glued *)

(** The tail of a substitution extended by a module part is the
    substitution. *)
Lemma sb_eq_wk_extend_mod : forall σ H, sb_eq σ (Wk ⨟ (σ ,,ₘ H)).
Proof. intros σ H x; reflexivity. Qed.

Lemma sb_eq_wk_extend_dm : forall σ M H, sb_eq σ (Wk ⨟ (σ ,,ᵈ M ‖ H)).
Proof. intros σ M H x; reflexivity. Qed.

(** [σ,,M[σ]] into a definition entry, the head stored at the closure of
    the type as a body's environment stores it ([eval_body_env_def]), as
    [cons_def_glu_sub_pred_helper] at the type's value. *)
Lemma cons_def_glu_sub_pred_closure : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El M m},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    Γ ⊢ M : A ->
    ⟦ A ⟧ ρ ↘ a ->
    glu_term_value M ρ (domain_kind a) m ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
    Δ ⊢ˢ σ,,M[σ] ® ρ ↦ m ⦂ entry_type_closure A ρ ∈ cons_def_glu_sub_pred i Γ A M Sb.
Proof.
  intros * HSb Hσg HA HM Ha Hm Hglu HMσ.
  assert (Hσ : Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  assert (HMσt : Δ ⊢ M[σ] : A[σ]) by (eapply glu_univ_elem_trm_escape; eassumption).
  assert (Δ ⊢ˢ σ,,M[σ] : Γ ▸ A ≔ M)
    by (eapply wf_sub_extend_def; [ exact Hσ | exact HA | apply type_sort_abs_kind; constructor | exact HM
                                  | exact HMσt | apply wf_exp_eq_refl; exact HMσt ]).
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMσ HR) as Hmm.
  econstructor; [ eassumption | exact Ha | exact Hglu | | | | | ].
  - rewrite exp_sub_shift_extend; exact HMσ.
  - intros Hev; exists m; split; [ destruct (domain_kind a); [ exact Hm | inversion Hev | exact Hm ] |].
    exact (per_head_of Ha Ha HR Hmm).
  - (** The stored type is the closure of the type, of the type's value *)
    eexists; split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ _ i a P El _ Hglu _); [ econstructor; exact Ha | rewrite exp_sub_shift_extend; exact HMσ ].
  - split; [ exact (proj1 (entry_readable_of_elem_closure Ha Ha HR Hmm)) | cbn; lia ].
  - first [ exact Hσg | cbn; exact Hσg | eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | exact Hσg | mauto 3 ] ].
Qed.

(** The definitions of a body, filled in, are of the sorts of the kinds
    they are tagged with: the syntactic counterpart of [body_sorts_valid],
    as a well-formed unit's description has it ([desc_ok_open]). *)
Fixpoint body_sorts_typed (Φ : gmod) (Γ : ctx) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' _ E => body_sorts_typed Φ' Γ /\
      forall A M σ, entry_tm E = Some (A, M) -> gm_fill Φ' = Some σ ->
        exists i : nat, Γ ⊢ A[σ] : abs_kind_sort (entry_kind E) Typeω@i
  | gm_open _ _ _ _ => True
  end.

(** [σ,,M] into an assumption entry, the head stored at the closure of the
    type, as a module application stores its argument
    ([eval_appm_local]). *)
Lemma cons_glu_sub_pred_closure : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El M c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M : A[σ] ® c ∈ El ->
    Δ ⊢ˢ σ,,M ® ρ ↦ c ⦂ entry_type_closure A ρ ∈ cons_glu_sub_pred i Γ κ A Sb.
Proof.
  intros * HSb Hσg HA Ha Hglu Hc.
  assert (Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  assert (Δ ⊢ M : A[σ]) by (eapply glu_univ_elem_trm_escape; eassumption).
  assert (⊢ Γ ▹{κ} A) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
  assert (Δ ⊢ˢ σ,,M : Γ ▹{κ} A).
  { apply wf_sub_extend_gen; [ assumption | assumption | | |].
    - intros B Hlk; inversion Hlk; subst; rewrite exp_sub_shift_extend; assumption.
    - intros B L Hlk; inversion Hlk.
    - intros U Hlk; inversion Hlk. }
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ Hc HR) as Hcc.
  econstructor; [ eassumption | exact Ha | exact Hglu | | | | ].
  - rewrite exp_sub_shift_extend; exact Hc.
  - eexists; split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ _ i a P El _ Hglu _); [ econstructor; exact Ha | rewrite exp_sub_shift_extend; exact Hc ].
  - split; [ exact (proj1 (entry_readable_of_elem_closure Ha Ha HR Hcc)) | cbn; lia ].
  - first [ exact Hσg | cbn; exact Hσg | eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | exact Hσg | mauto 3 ] ].
Qed.

(** The environment of a body that can be filled in, over a glued
    environment of its context, is glued along the body's context at the
    substitution filling the body in after the context's: entry by entry,
    a definition's head its body's value there at the kind it is tagged
    with, which is its type's ([body_sorts_typed]), a module's its unit's
    closure there, related to itself (the completeness of the unit's
    literal), and glued by the slot premise of the body context's
    gluing. *)
Lemma glu_body_env : forall Φ Γ TSb,
    EG Γ ∈ glu_ctx_env ↘ TSb ->
    body_sorts_typed Φ Γ ->
    forall ζ, gm_fill Φ = Some ζ ->
    forall Sb, EG body_ctx Φ ++ Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ TSb ->
    exists σ' ρ', sb_eq σ' (ζ ⨟ σ) /\ ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' /\ Δ ⊢ˢ σ' ® ρ' ∈ Sb.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros Γ TSb HΓ Hsv ζ Hf Sb HSb Δ σ ρ Hσ; cbn in Hf; [| | discriminate ].
  - injection Hf as <-; cbn in HSb.
    assert (E : TSb <∙> Sb) by (eapply functional_glu_ctx_env; eassumption).
    exists σ, ρ; split; [ intros x; reflexivity | split; [ constructor | apply E; exact Hσ ] ].
  - cbn [body_sorts_typed] in Hsv; destruct Hsv as [Hsv HsvE].
    destruct E as [b pv κ A [M |] | pv [Δy Dy] | ? ? ? ? ? | pv A M [Δy Dy] | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [ζ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HSb.
    + (** A definition *)
      destruct (glu_rel_ctx_tail (ex_intro _ _ HSb)) as [TSb0 HTSb0].
      destruct (IH _ _ HΓ Hsv _ eq_refl _ HTSb0 _ _ _ Hσ) as (σ0 & ρ0 & Eσ0 & Hb0 & Hσ0).
      destruct (glu_ctx_env_cons_def_clean_inversion HTSb0 HSb) as (i & κ' & HA & HM & _ & HMg & ESb).
      destruct (HMg _ _ _ Hσ0) as [a m P El Ea Hm Hglu HMσ].
      (** The kind of the type's value is the tag: the type is of the sort
          of the tag's kind, filled in, and of its own kind *)
      destruct (HsvE A M ζ0 eq_refl eq_refl) as [iA HAf]; cbn [entry_kind] in HAf.
      pose proof (glu_ctx_env_sub_escape HTSb0 _ _ _ Hσ0) as Hσ0s.
      assert (Hκ : κ' = κ).
      { pose proof (wf_gm_fill _ _ _ _ _ (glu_ctx_env_wf_ctx HTSb0) Hf0) as Hζ0.
        assert (HAζ : Γ ⊢ A[ζ0] : abs_kind_sort κ' Typeω@i)
          by (replace (abs_kind_sort κ' Typeω@i) with ((abs_kind_sort κ' Typeω@i)[ζ0]) by (rewrite abs_kind_sort_sub; reflexivity);
              exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hζ0)).
        exact (exp_eq_same_kind _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HAζ) (sort_kind_abs_kind_sort _ _) HAf (sort_kind_abs_kind_sort _ _)). }
      subst κ'.
      assert (Hka : domain_kind a = κ).
      { assert (HAσ : Δ ⊢ A[σ0] : abs_kind_sort κ Typeω@i)
          by (replace (abs_kind_sort κ Typeω@i) with ((abs_kind_sort κ Typeω@i)[σ0]) by (rewrite abs_kind_sort_sub; reflexivity);
            exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ0s)).
        exact (proj1 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HMσ) HAσ)). }
      exists (σ0 ,, M[σ0]), (ρ0 ↦ m ⦂ entry_type_closure A ρ0); split; [| split ].
      * intros [| x]; cbn; [ f_equal; rewrite exp_sub_sub; apply exp_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity
                           | exact (Eσ0 x) ].
      * destruct (evaluated_kind_or_propositional κ) as [Hk | ->].
        -- eapply eval_body_env_def; [ exact Hk | exact Hb0 |].
           rewrite Hka in Hm; destruct Hk; exact Hm.
        -- rewrite Hka in Hm; cbn in Hm; subst m; apply eval_body_env_def_proof; exact Hb0.
      * apply ESb; eapply cons_def_glu_sub_pred_closure; eassumption.
    + (** A submodule *)
      inversion HSb as [| | | ? ? TSb0 ? HTSb0 HU HUv ESb |]; subst.
      destruct (IH _ _ HΓ Hsv _ eq_refl _ HTSb0 _ _ _ Hσ) as (σ0 & ρ0 & Eσ0 & Hb0 & Hσ0).
      destruct (glu_ctx_env_per_ctx_env HTSb0) as [R0 HR0].
      pose proof (glu_ctx_env_per_env HTSb0 HR0 Hσ0) as Hρ0.
      pose proof (glu_ctx_env_sub_escape HTSb0 _ _ _ Hσ0) as Hσ0s.
      assert (HUl : gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ Γ ⊢ᵐ me_lit (gu_mk Δy Dy) ≈ me_lit (gu_mk Δy Dy))
        by (apply wf_me_lit; exact HU).
      destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR0 _ _ Hρ0)
        as (h & h' & Hh & Hh' & Hhh).
      pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
      exists (σ0 ,,ₘ me_lit (gu_mk Δy Dy)[σ0]ᵘ), (ρ0 ↦ᵐ h ⦂ gu_mk Δy Dy); split; [| split ].
      * intros [| x]; cbn; [ f_equal; f_equal; rewrite gunit_sub_sub; apply gunit_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity
                           | exact (Eσ0 x) ].
      * eapply eval_body_env_mod; [ exact Hb0 | apply eval_me_lit_iff; exact Hh ].
      * apply ESb; econstructor.
        -- apply wf_sub_extend_mod; [ exact Hσ0s | exact HU | eapply sub_preserves_unit; eassumption ].
        -- exists h; split; [ exact Hh | exact Hhh ].
        -- eapply (proj1 glu_dmod_resp_sub_eq); [ exact (HUv _ _ _ _ Hσ0 Hh) |].
           apply wf_sub_eq_of_sb_eq; [ exact Hσ0s | apply sb_eq_wk_extend_mod ].
        -- eexists; reflexivity.
        -- split; [ apply mod_entry_readable | cbn; exact (gunit_scoped_free_bound _ _ (wf_unit_eq_scoped_left _ _ _ _ _ HU)) ].
        -- exact Hσ0.
    + (** A definition with a module part: as a definition and as a
          submodule *)
      destruct (glu_rel_ctx_tail (ex_intro _ _ HSb)) as [TSb0 HTSb0].
      destruct (IH _ _ HΓ Hsv _ eq_refl _ HTSb0 _ _ _ Hσ) as (σ0 & ρ0 & Eσ0 & Hb0 & Hσ0).
      destruct (glu_ctx_env_cons_dm_clean_inversion HTSb0 HSb) as (i & HA & HM & Hwe & _ & HMg & ESb).
      pose proof (glu_ctx_env_lit_inversion (e := ce_dm A M (gu_mk Δy Dy)) HTSb0 HSb eq_refl) as HUv.
      destruct (HMg _ _ _ Hσ0) as [a m P El Ea Hm Hglu HMσ].
      destruct (glu_ctx_env_per_ctx_env HTSb0) as [R0 HR0].
      pose proof (glu_ctx_env_per_env HTSb0 HR0 Hσ0) as Hρ0.
      pose proof (glu_ctx_env_sub_escape HTSb0 _ _ _ Hσ0) as Hσ0s.
      inversion Hwe; subst.
      match goal with H : _ ⍮ _ ⍮ _ ⊢ᵘ gu_mk nil (md_alias _) ≈ _ |- _ => rename H into HU end.
      assert (Hka : domain_kind a = ak_relevant).
      { assert (HAσ : Δ ⊢ A[σ0] : abs_kind_sort ak_relevant Typeω@i) by (cbn; exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ0s)).
        exact (proj1 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HMσ) HAσ)). }
      rewrite Hka in Hm; cbn in Hm.
      assert (HUl : gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ Γ ⊢ᵐ me_lit (gu_mk nil (md_alias E)) ≈ me_lit (gu_mk nil (md_alias E)))
        by (apply wf_me_lit; exact HU).
      destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR0 _ _ Hρ0)
        as (h & h' & Hh & Hh' & Hhh).
      pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
      exists (σ0 ,,ᵈ M[σ0] ‖ me_lit (gu_mk nil (md_alias E))[σ0]ᵘ),
             (ρ0 ↦ᵈ m ⦂ entry_type_closure A ρ0 ‖ h ⦂ gu_mk nil (md_alias E)); split; [| split ].
      * intros [| x]; cbn; [ f_equal; [ rewrite exp_sub_sub; apply exp_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity
                                      | f_equal; rewrite gunit_sub_sub; apply gunit_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity ]
                           | exact (Eσ0 x) ].
      * eapply eval_body_env_dm; [ exact Hb0 | exact Hm | apply eval_me_lit_iff; exact Hh ].
      * assert (HMσt : Δ ⊢ M[σ0] : A[σ0]) by (eapply glu_univ_elem_trm_escape; eassumption).
        destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
        pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMσ HR) as Hmm.
        apply ESb; econstructor;
          [ eapply wf_sub_extend_dm; eauto; first [ apply wf_exp_eq_refl; exact HMσt | eapply sub_preserves_unit; eassumption ]
          | exact Ea | exact Hglu | rewrite exp_sub_shift_extend; exact HMσ
          | exists m; split; [ exact Hm | exact (per_head_of Ea Ea HR Hmm) ]
          | exists h; split; [ exact Hh | exact Hhh ]
          | eapply (proj1 glu_dmod_resp_sub_eq); [ exact (HUv _ _ _ _ Hσ0 Hh) |];
            apply wf_sub_eq_of_sb_eq; [ exact Hσ0s | apply sb_eq_wk_extend_dm ]
          | eexists; split; [ reflexivity |];
            refine (mk_glu_stored_type _ _ _ _ _ i a P El _ Hglu _);
            [ apply eval_entry_type_closure; exact Ea | rewrite exp_sub_shift_extend; exact HMσ ]
          | split; [ exact (proj1 (dm_entry_readable_of_elem_closure Ea Ea HR Hmm h h (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E))))
                   | cbn; exact (gunit_scoped_free_bound _ _ (wf_unit_eq_scoped_left _ _ _ _ _ HU)) ]
          | exact Hσ0 ].
Qed.

(** ** Module Expressions with the Same Module Part *)

(** Applying a description to an argument applies its module part: the
    module part of the result is that of the module part applied, both
    ways. *)
Lemma mdesc_at_mod_part : forall R N R' Rm, mdesc_at R N = Some R' -> mdesc_mod R = Some Rm ->
    exists Rm', mdesc_at Rm N = Some Rm' /\ mdesc_mod R' = mdesc_mod Rm'.
Proof.
  induction R as [r A om | Δ Φ Φx | Θ p T Φ Ns | Θ A M Rm0 IH]; intros N R' Rm Ha Hm; cbn [mdesc_mod] in Hm;
    try discriminate.
  - injection Hm as <-; exists R'; split; [ exact Ha | reflexivity ].
  - injection Hm as <-; exists R'; split; [ exact Ha | reflexivity ].
  - cbn [mdesc_at] in Ha; destruct (mdesc_at Rm0 N) as [Rm0' |] eqn:E; [| discriminate ].
    destruct (IH _ _ _ E Hm) as (Rm' & HRm' & EM).
    exists Rm'; split; [ exact HRm' |].
    destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; injection Ha as <-; cbn [mdesc_mod]; exact EM.
Qed.

Lemma mdesc_at_of_mod_part : forall R N Rm Rm', mdesc_mod R = Some Rm -> mdesc_at Rm N = Some Rm' ->
    exists R', mdesc_at R N = Some R' /\ mdesc_mod R' = mdesc_mod Rm'.
Proof.
  induction R as [r A om | Δ Φ Φx | Θ p T Φ Ns | Θ A M Rm0 IH]; intros N Rm Rm' Hm Ha; cbn [mdesc_mod] in Hm;
    try discriminate.
  - injection Hm as <-; exists Rm'; split; [ exact Ha | reflexivity ].
  - injection Hm as <-; exists Rm'; split; [ exact Ha | reflexivity ].
  - destruct (IH _ _ _ Hm Ha) as (Rm0' & E & EM).
    cbn [mdesc_at]; rewrite E.
    destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; eexists; split; [ reflexivity | cbn [mdesc_mod]; exact EM
                                                                       | reflexivity | exact EM ].
Qed.

(** [H0] has the module part [H1] has, at every typed substitution. *)
Definition same_part (Γ0 : ctx) (H0 H1 : modexp) : Prop :=
  forall Γ1 ζ R0 Rm, Γ1 ⊢ˢ ζ : Γ0 -> mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ R0 -> mdesc_mod R0 = Some Rm ->
    exists R1, mdenote gc_deps gc_stack Γ1 H1[ζ]ᵐ R1 /\ mdesc_mod R1 = Some Rm.

(** Denoting alike is having the same module part. *)
Lemma same_part_of_denote : forall {Γ0 H0 H1}, same_denote Γ0 H0 H1 -> same_part Γ0 H0 H1.
Proof. intros * Hs Γ1 ζ R Rm Hζ Hm HRm; exists R; split; [ exact (Hs _ _ _ Hζ Hm) | exact HRm ]. Qed.

(** A description with no module part applied has none. *)
Lemma mdesc_at_no_mod : forall R N R', mdesc_mod R = None -> mdesc_at R N = Some R' -> mdesc_mod R' = None.
Proof.
  induction R as [r A om | | | Θ A M Rm0 IH]; intros N R' Hm Ha; cbn [mdesc_mod] in Hm; try discriminate.
  - cbn in Ha; destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; reflexivity.
  - cbn [mdesc_at] in Ha; destruct (mdesc_at Rm0 N) as [Rm0' |] eqn:E; [| discriminate ].
    pose proof (IH _ _ Hm E) as H.
    destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; injection Ha as <-; [ cbn [mdesc_mod] |]; exact H.
Qed.

(** Selections are looked up in the module part: from module expressions
    with the same module part naming no stored module, they denote alike. *)
Lemma same_denote_mem_part : forall {Γ0 H0 H1} y, same_part Γ0 H0 H1 ->
    (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H0[ζ]ᵐ = None) ->
    (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H1[ζ]ᵐ = None) ->
    same_denote Γ0 (me_mem H0 y) (me_mem H1 y).
Proof.
  intros * Hs Hq0 Hq1 Γ1 ζ R Hζ Hm; cbn [modexp_sub] in *.
  inversion Hm; subst;
    try (match goal with Hp : mod_qname (me_mem _ _) = Some _ |- _ =>
           cbn [mod_qname] in Hp; rewrite (Hq0 _ _ Hζ) in Hp; discriminate end).
  match goal with H0m : mdenote _ _ _ (modexp_sub H0 ζ) ?R0, Hmd : mdesc_mod ?R0 = Some _ |- _ =>
    destruct (Hs _ _ _ _ Hζ H0m Hmd) as (R2 & HR2 & Ep) end.
  eapply mdenote_mem; [ exact HR2 | exact Ep | eassumption | eassumption | eassumption ].
Qed.

(** Application to the variable of a further parameter keeps the module
    part. *)
Lemma same_part_app_var : forall {Γ0 H0 H1} κ B, same_part Γ0 H0 H1 ->
    same_part (Γ0 ▹{κ} B) (me_app H0[Wk]ᵐ #0) (me_app H1[Wk]ᵐ #0).
Proof.
  intros * Hs Γ1 ζ R Rm Hζ Hm HRm; cbn [modexp_sub] in *.
  rewrite !modexp_sub_sub in *.
  inversion Hm; subst;
    try (match goal with Hp : mod_qname (me_app _ _) = Some _ |- _ => cbn in Hp; discriminate end).
  match goal with H0m : mdenote _ _ _ (modexp_sub H0 _) ?R0, Ha : mdesc_at ?R0 _ = Some _ |- _ =>
    destruct (mdesc_mod R0) as [Rm0 |] eqn:E0;
      [| exfalso; rewrite (mdesc_at_no_mod _ _ _ E0 Ha) in HRm; discriminate ];
    destruct (Hs _ _ _ _ (wf_sub_compose _ _ _ _ _ _ _ (wf_sub_shift _ _ _ _ (wf_sub_cod _ _ _ _ _ Hζ)) Hζ) H0m E0)
      as (R1 & HR1 & E1);
    destruct (mdesc_at_mod_part _ _ _ _ Ha E0) as (Rm' & HRm' & EM) end.
  destruct (mdesc_at_of_mod_part _ _ _ _ E1 HRm') as (R1' & HR1' & EM').
  exists R1'; split; [ eapply mdenote_app; [ exact HR1 | exact HR1' ] | rewrite EM', <- EM; exact HRm ].
Qed.

Lemma same_part_sub : forall {Γ0 Γ1 ζ H0 H1}, Γ1 ⊢ˢ ζ : Γ0 -> same_part Γ0 H0 H1 -> same_part Γ1 H0[ζ]ᵐ H1[ζ]ᵐ.
Proof.
  intros * Hζ Hs Γ2 ζ' R Rm Hζ' Hm HRm; rewrite modexp_sub_sub in *.
  exact (Hs _ _ _ _ (wf_sub_compose _ _ _ _ _ _ _ Hζ Hζ') Hm HRm).
Qed.

(** A described module part with a telescope gives the telescope. *)
Lemma mdesc_mod_tele_part : forall R R' T, mdesc_mod_tele R = Some T -> (exists Rm, mdesc_mod R = Some Rm /\ mdesc_mod R' = Some Rm) ->
    mdesc_mod_tele R' = Some T.
Proof. intros * HT (Rm & E & E'); unfold mdesc_mod_tele in *; rewrite E in HT; rewrite E'; exact HT. Qed.

(** A module value glued as [H1] is glued as an equal [H0] with the same
    module part both ways at every substitution, neither naming a stored
    module: its members are looked up alike ([same_denote_mem_part]) and
    equal ([glu_elem_at_same_denote]), and so are its submodules' and its
    applications'. *)
Lemma glu_dmod_same_part :
  (forall Δ σ0 Γ0 H1 h, glu_dmod Δ σ0 Γ0 H1 h ->
     forall H0, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H1 -> same_part Γ0 H0 H1 -> same_part Γ0 H1 H0 ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H0[ζ]ᵐ = None) ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> mod_qname H1[ζ]ᵐ = None) ->
       glu_dmod Δ σ0 Γ0 H0 h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module *)
    intros * Hσ HH1 HH1p Hl Hlen Hargs _ H0 HH Hs01 Hs10 Hq0 Hq1.
    eapply glu_dmod_global; [ exact Hσ | exact (wf_modexp_eq_refl_left HH) | | exact Hl | exact Hlen | exact Hargs ].
    eapply wf_me_trans; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hσ) | exact HH1p ].
  - (** A body *)
    intros * Hσ HH1 Hmem Hsub IHsub H0 HH Hs01 Hs10 Hq0 Hq1.
    apply glu_dmod_body; [ exact Hσ | exact (wf_modexp_eq_refl_left HH) | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst Hm HA HS HAt.
      pose proof (same_denote_mem_part x Hs01 Hq0 Hq1 _ _ _ (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) Hm) as Hm1.
      destruct (Hg _ _ _ _ _ _ _ _ Hst Hm1 HA HS HAt) as (i & P & El & Hgl).
      exists i, P, El.
      eapply glu_elem_at_same_denote;
        [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst))
        | exact Hm | exact Hm1 | exact HA | exact (glu_sub_through_rest _ _ _ _ _ _ _ _ Hst) | exact Hgl ].
    + intros * Hp Hu Hb Hc.
      pose proof (Hsub _ _ _ _ _ _ _ Hp Hu Hb Hc) as Hg1.
      pose proof (same_denote_mem_part y Hs01 Hq0 Hq1) as Hd01.
      pose proof (same_denote_mem_part y Hs10 Hq1 Hq0) as Hd10.
      assert (HHy : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H1 y)
        by (eapply wf_me_mem_same_denote; [ exact HH | destruct Hg1; assumption | exact Hd10 ]).
      eapply IHsub; [ exact Hp | exact Hu | exact Hb | exact Hc | exact HHy
                    | exact (same_part_of_denote Hd01) | exact (same_part_of_denote Hd10)
                    | intros Γ2 ζ Hζ; cbn; rewrite (Hq0 _ _ Hζ); reflexivity
                    | intros Γ2 ζ Hζ; cbn; rewrite (Hq1 _ _ Hζ); reflexivity ].
  - (** A value lacking a parameter *)
    intros * Hσ HH1 Hn Hpar Hex Happ IHapp H0 HH Hs01 Hs10 Hq0 Hq1.
    eapply glu_dmod_fun; [ exact Hσ | exact (wf_modexp_eq_refl_left HH) | exact Hn | | exact Hex | ].
    + intros * Hst Hm HT.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      assert (HRm : exists Rm, mdesc_mod RH = Some Rm)
        by (unfold mdesc_mod_tele in HT; destruct (mdesc_mod RH); [ eexists; reflexivity | discriminate ]).
      destruct HRm as [Rm HRm].
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (RH1 & Hm1 & HRm1).
      exact (Hpar _ _ _ _ _ _ _ _ _ _ Hst Hm1 (mdesc_mod_tele_part _ _ _ HT (ex_intro _ Rm (conj HRm HRm1)))).
    + intros * Hst Hm HT Hv HS HB * Hu HP HN Hhc.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      assert (HRm : exists Rm, mdesc_mod RH = Some Rm)
        by (unfold mdesc_mod_tele in HT; destruct (mdesc_mod RH); [ eexists; reflexivity | discriminate ]).
      destruct HRm as [Rm HRm].
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (RH1 & Hm1 & HRm1).
      pose proof (mdesc_mod_tele_part _ _ _ HT (ex_intro _ Rm (conj HRm HRm1))) as HT1.
      pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hst Hm1 HT1 Hv HS HB _ _ _ _ _ _ Hu HP HN Hhc) as Hg1.
      pose proof (same_part_sub Hζ Hs01) as Hs01'; pose proof (same_part_sub Hζ Hs10) as Hs10'.
      eapply IHapp; [ exact Hst | exact Hm1 | exact HT1 | exact Hv | exact HS | exact HB | exact Hu | exact HP | exact HN
                    | exact Hhc | | exact (same_part_app_var _ _ Hs01') | exact (same_part_app_var _ _ Hs10')
                    | intros; reflexivity | intros; reflexivity ].
      (** The applications are equal: their premises are those of [H1]'s
          application, the module parts being the same *)
      assert (HHg : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_app H1[ζ]ᵐ[Wk]ᵐ #0 ≈ me_app H1[ζ]ᵐ[Wk]ᵐ #0)
        by (destruct Hg1; assumption).
      destruct (proj1 (modexp_gen _ _ _ _ _ HHg)) as [HH1w (R' & T' & B' & T1' & S' & HR' & HT' & Hv' & HB' & HS' & HN')].
      assert (HRm' : exists Rm', mdesc_mod R' = Some Rm')
        by (unfold mdesc_mod_tele in HT'; destruct (mdesc_mod R'); [ eexists; reflexivity | discriminate ]).
      destruct HRm' as [Rm' HRm'].
      destruct (Hs10' (Γ1 ▹{domain_kind a} B) Wk R' Rm' ltac:(eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg)) HR' HRm')
        as (R0 & HR0 & HRm0).
      pose proof (mdesc_mod_tele_part _ _ _ HT' (ex_intro _ Rm' (conj HRm' HRm0))) as HT0.
      assert (HHw : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ H0[ζ]ᵐ[Wk]ᵐ ≈ H1[ζ]ᵐ[Wk]ᵐ).
      { eapply sub_preserves_modexp; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) |].
        eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg). }
      eapply wf_me_app; [ exact HHw | exact HR0 | exact HT0 | exact Hv' | exact HB' | exact HS' | exact HN'
                        | apply wf_exp_eq_refl; exact HN' | exact HR' | exact HT' | exact Hv' | exact HB' | exact HS' | exact HN' ].
Qed.

(** What a well-formed unit denotes, substituted, is what the substituted
    unit denotes ([mdenote_sub_all]). *)
Lemma udenote_sub_compat : forall {Γp U U' D0 Γ' σ},
    gc_deps ⍮ gc_stack ⍮ Γp ⊢ᵘ U ≈ U' -> udenote gc_deps gc_stack Γp None U D0 -> sub_mod_compat σ Γ' Γp ->
    udenote gc_deps gc_stack Γ' None U[σ]ᵘ (mdesc_sub D0 σ).
Proof.
  intros * HU HD Hc.
  pose proof (wf_gctx_closed _ _ _ (presup_unit_eq_ctx HU)) as Hcl.
  pose proof (wf_unit_eq_scoped_left _ _ _ _ _ HU) as Hs.
  pose proof (proj1 (proj1 wf_scoped _ _ _ (presup_unit_eq_ctx HU))) as HΓs.
  eapply (proj1 (proj2 (mdenote_sub_all _ _ Hcl))); [ exact HD | apply slots_ok_ctx; exact HΓs | left; exact Hs | exact Hc ].
Qed.

(** The submodule [y] of a saturated literal body has the module part of
    its unit's literal, the entries before it filled in, at every typed
    substitution, both ways: reading the entry fills the entries before it
    in ([mdesc_read]), and denoting commutes with substitution. *)
Lemma same_part_lit_sel : forall Γ Φ y Φ' E Uy ζ,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open nil Φ ≈ gu_open nil Φ ->
    gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) -> entry_unit E = Some Uy -> gm_fill Φ' = Some ζ ->
    gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Γ ⊢ᵘ Uy ≈ Uy ->
    (forall pv A M, E = ge_def_mod pv A M Uy -> exists E', Uy = gu_mk nil (md_alias E')) ->
    same_part Γ (me_mem (me_lit (gu_open nil Φ)) y) (me_lit Uy[ζ]ᵘ) /\
    same_part Γ (me_lit Uy[ζ]ᵘ) (me_mem (me_lit (gu_open nil Φ)) y).
Proof.
  intros * HU Hp HE Hf HUy HEdm.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hg.
  destruct (me_denotes _ _ _ _ _ (wf_me_lit _ _ _ _ _ HUy)) as (D0 & ? & HRU & _).
  apply mdenote_lit_inv in HRU.
  pose proof (gm_fill_nopens _ _ Hf) as Hn0.
  split; intros Γ1 ζ1 R Rm Hζ1 Hm HRm; cbn [modexp_sub] in *;
    destruct (gm_fill_sub Φ' 0 ζ1 ζ Hf) as (τ & Hfτ & Eτ); cbn [sb_qn] in Hfτ, Eτ; rewrite PeanoNat.Nat.add_0_r in Eτ;
    pose proof (sub_mod_compat_ext (body_ctx Φ') _ _ _ (wf_sub_mod_compat _ _ _ _ _ Hζ1)) as Hc1;
    rewrite (length_body_ctx _ Hn0) in Hc1;
    pose proof (udenote_sub_compat HUy HRU Hc1) as HD1;
    pose proof (wf_sub_compose _ _ _ _ _ _ _ (wf_gm_fill _ _ _ _ _ (presup_unit_eq_ctx HUy) Hf) Hζ1) as Hc.
  - (** The selection reads the entry's unit at the body's substituted
        prefix, filled in: the unit filled in, substituted *)
    inversion Hm; subst; try (cbn in *; discriminate).
    match goal with H0 : mdenote _ _ _ (me_lit _) _ |- _ => apply mdenote_lit_inv in H0; inversion H0; subst end.
    match goal with H11 : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn [mdesc_body] in H11; injection H11 as <- end.
    match goal with H10 : body_xp _ _ _ (gmod_sub Φ ζ1) ?Φx |- _ =>
      pose proof (body_xp_expand _ _ _ _ _ H10) as EΦx; rewrite gm_expand_sub in EΦx; subst Φx end.
    match goal with H3 : mdesc_mod (mdesc_open _ _ _) = Some _ |- _ => cbn [mdesc_mod] in H3; injection H3 as <- end.
    match goal with H4 : mdesc_entry _ y = Some _ |- _ =>
      cbn [mdesc_entry] in H4; rewrite gm_prefix_upto_sub, Hp in H4; cbn [option_map] in H4 end.
    destruct E as [b pv κ A [M |] | pv U0 | ? ? ? ? ? | pv A M U0 | ? ? ? ?]; cbn [entry_unit] in HE; try discriminate;
      injection HE as <-.
    all: match goal with H4 : match gmod_sub _ _ with _ => _ end = Some _ |- _ => cbn [gmod_sub] in H4; injection H4 as <- <- <- end.
    all: match goal with H6 : edenote _ _ _ _ _ _ |- _ => rewrite List.app_nil_r, (body_ctx_sub _ _ Hn0) in H6; inversion H6; subst end.
    all: match goal with H8 : mdesc_read _ _ = Some _ |- _ => cbn [mdesc_read] in H8; rewrite Hfτ in H8; cbn [option_map] in H8;
           injection H8 as <-; rewrite mdesc_up_nil in HRm end.
    all: cbn [mdesc_entry_path] in *.
    1: match goal with H5 : udenote _ _ _ None _ ?R1 |- _ =>
         pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ H5 _ HD1) as -> end.
    2: match goal with H8 : udenote _ _ _ None (gu_mk _ (md_alias _)) ?R1, H7 : gu_mk _ (md_alias _) = _ |- _ =>
         rewrite <- H7 in HD1; pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ H8 _ HD1) as -> end;
       cbn [mdesc_sub mdesc_mod] in HRm.
    all: rewrite (mdesc_sub_sub_ext _ _ _ _ Eτ) in HRm.
    all: exists (mdesc_sub D0 (ζ ⨟ ζ1)); split; [| exact HRm ].
    all: apply mdenote_lit; rewrite gunit_sub_sub; exact (udenote_sub_compat HUy HRU (wf_sub_mod_compat _ _ _ _ _ Hc)).
  - (** The literal filled in is read as the selection *)
    apply mdenote_lit_inv in Hm; rewrite gunit_sub_sub in Hm.
    pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ Hm _ (udenote_sub_compat HUy HRU (wf_sub_mod_compat _ _ _ _ _ Hc))) as ->.
    destruct (me_denotes _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU)) as (DL & ? & HDL & _).
    apply mdenote_lit_inv in HDL.
    pose proof (udenote_sub_compat HU HDL (wf_sub_mod_compat _ _ _ _ _ Hζ1)) as HDL1.
    inversion HDL; subst.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    match goal with Hx : body_xp _ _ _ Φ ?Φx |- _ => pose proof (body_xp_expand _ _ _ _ _ Hx) as ->; clear Hx end.
    cbn [mdesc_sub tele_sub List.length sb_qn] in HDL1.
    destruct E as [b pv κ A [M |] | pv U0 | ? ? ? ? ? | pv A M U0 | ? ? ? ?]; cbn [entry_unit] in HE; try discriminate;
      injection HE as <-.
    + exists (mdesc_up nil (mdesc_sub (mdesc_sub D0 (sb_qn (gm_binders Φ') ζ1)) τ)); split.
      * eapply mdenote_mem; [ apply mdenote_lit; exact HDL1 | reflexivity | cbn [mdesc_entry]; rewrite gm_prefix_upto_sub, Hp; reflexivity | |].
        -- cbn [mdesc_entry_path gentry_sub]; rewrite List.app_nil_r, (body_ctx_sub _ _ Hn0); constructor; exact HD1.
        -- transitivity (option_map (fun σ0 => mdesc_up nil (mdesc_sub (mdesc_sub D0 (sb_qn (gm_binders Φ') ζ1)) σ0)) (gm_fill (gmod_sub Φ' ζ1)));
             [ reflexivity | rewrite Hfτ; reflexivity ].
      * rewrite mdesc_up_nil, (mdesc_sub_sub_ext _ _ _ _ Eτ); exact HRm.
    + destruct (HEdm _ _ _ eq_refl) as [E' ->].
      set (q1 := sb_qn (gm_binders Φ') ζ1) in *.
      exists (mdesc_up nil (mdesc_sub (mdesc_dm nil A[q1] M[q1] (mdesc_sub D0 q1)) τ)); split.
      * eapply mdenote_mem; [ apply mdenote_lit; exact HDL1 | reflexivity | cbn [mdesc_entry]; rewrite gm_prefix_upto_sub, Hp; reflexivity | |].
        -- cbn [mdesc_entry_path gentry_sub]; rewrite List.app_nil_r, (body_ctx_sub _ _ Hn0).
           cbn [gunit_sub moddef_sub tele_sub List.length] in HD1 |- *; constructor; exact HD1.
        -- transitivity (option_map (fun σ0 => mdesc_up nil (mdesc_sub (mdesc_dm nil A[q1] M[q1] (mdesc_sub D0 q1)) σ0)) (gm_fill (gmod_sub Φ' ζ1)));
             [ reflexivity | rewrite Hfτ; reflexivity ].
      * rewrite mdesc_up_nil; cbn [mdesc_sub mdesc_mod]; rewrite (mdesc_sub_sub_ext _ _ _ _ Eτ); exact HRm.
Qed.

(** A literal given its outermost parameter denotes as the literal
    instantiated, both ways at every typed substitution ([mdenote_beta]). *)
Lemma same_denote_beta : forall Γ0 Δ κ X D N,
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) D ≈ gu_mk (Δ ++ ce_ass κ X :: nil) D ->
    same_denote Γ0 (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N) (me_lit (gu_mk Δ D)[Id,,N]ᵘ) /\
    same_denote Γ0 (me_lit (gu_mk Δ D)[Id,,N]ᵘ) (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N).
Proof.
  intros * HU.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hg.
  assert (Hgen : forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 ->
            exists R', mdenote gc_deps gc_stack Γ1 (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N)[ζ]ᵐ R' /\
                       mdenote gc_deps gc_stack Γ1 (me_lit (gu_mk Δ D)[Id,,N]ᵘ)[ζ]ᵐ R').
  { intros Γ1 ζ Hζ.
    pose proof (sub_preserves_unit _ _ _ _ _ _ _ HU Hζ) as HUζ.
    rewrite !gunit_sub_mk, tele_sub_app in HUζ.
    rewrite List.length_app in HUζ; cbn [List.length tele_sub Nat.add] in HUζ.
    rewrite PeanoNat.Nat.add_1_r, sb_qn_S in HUζ; cbn [sb_qn] in HUζ.
    destruct (me_denotes _ _ _ _ _ (wf_me_lit _ _ _ _ _ HUζ)) as (R0 & ? & HR0 & _).
    apply mdenote_lit_inv in HR0.
    destruct (mdenote_beta _ _ _ _ _ _ _ N[ζ] HUζ _ HR0) as (R' & HR1 & HR2 & _).
    exists R'; split.
    - cbn [modexp_sub]; rewrite gunit_sub_mk, tele_sub_app, List.length_app; cbn [List.length tele_sub Nat.add].
      rewrite PeanoNat.Nat.add_1_r, sb_qn_S; cbn [sb_qn]; exact HR1.
    - cbn [modexp_sub]; rewrite gunit_sub_sub.
      change (q (sb_qn (length Δ) ζ)) with (sb_qn (S (length Δ)) ζ) in HR2.
      rewrite sb_qn_S, <- (gunit_sub_mk Δ D (q ζ)), gunit_sub_sub in HR2.
      erewrite gunit_sub_sb_eq; [ exact HR2 |].
      rewrite sb_q_compose_extend_gen, sb_extend_compose, sb_compose_id_right, sb_compose_id_left; reflexivity. }
  split; intros Γ1 ζ R Hζ Hm; destruct (Hgen _ _ Hζ) as (R' & HR1 & HR2).
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ HR1); exact HR2.
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ HR2); exact HR1.
Qed.

(** ** The Closure of a Glued Unit's Literal *)

Lemma gm_prefix_upto_in_names : forall Φ z P, gm_prefix_upto Φ z = Some P -> List.In z (gm_names Φ).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros z P Hp; cbn in Hp |- *; [ discriminate | |].
  - destruct (String.eqb_spec z y) as [-> | Hne]; [ left; reflexivity | right; eapply IH; exact Hp ].
  - destruct (existsb (String.eqb z) (map import_item_name its)); [ discriminate |].
    apply List.in_or_app; right; eapply IH; exact Hp.
Qed.

(** The definitions of a body with distinct names are of the sorts of their
    tags when each, looked up, is. *)
Lemma body_sorts_typed_of_lookups : forall Φ Γ, List.NoDup (gm_names Φ) ->
    (forall y Φ0 E A M σ, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) -> gm_fill Φ0 = Some σ ->
       exists i : nat, Γ ⊢ A[σ] : abs_kind_sort (entry_kind E) Typeω@i) ->
    body_sorts_typed Φ Γ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros Γ Hnd Hl; cbn [body_sorts_typed]; [ exact I | | exact I ].
  cbn [gm_names] in Hnd; inversion Hnd as [| ? ? Hy Hnd' ]; subst.
  split.
  - apply IH; [ exact Hnd' |]; intros z Φ0 E0 A M σ Hp HE Hf.
    apply (Hl z Φ0 E0 A M σ); [| exact HE | exact Hf ].
    cbn; destruct (String.eqb_spec z y) as [-> | Hne]; [| exact Hp ].
    exfalso; apply Hy; exact (gm_prefix_upto_in_names _ _ _ Hp).
  - intros A M σ HE Hf; apply (Hl y Φ E A M σ); [ cbn; rewrite String.eqb_refl; reflexivity | exact HE | exact Hf ].
Qed.

(** A member of a saturated literal body, glued as its body at the body's
    environment, is glued as the member of the literal at every
    factorization: the type a lookup reads is the type filled in
    ([body_mem_desc]), the member is its δ-reduct, the body filled in,
    and the two are moved along the factorization by the substitution
    lemmas. *)
Lemma glu_lit_body_member : forall Γ sm Φ Φ' x E A M Δ σ (i : nat) a m P El σ'' ζ,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_body sm Φ) ≈ gu_mk nil (md_body sm Φ) ->
    gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) ->
    gm_fill Φ' = Some ζ -> ⊢ body_ctx Φ' ++ Γ ->
    body_ctx Φ' ++ Γ ⊢ A : abs_kind_sort (domain_kind a) Typeω@i -> body_ctx Φ' ++ Γ ⊢ M : A ->
    sb_eq σ'' (ζ ⨟ σ) -> Δ ⊢ˢ σ'' : body_ctx Φ' ++ Γ ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ''] : A[σ''] ® m ∈ El ->
    forall Δ' φ Γ1 ζ1 σ1 R A', glu_sub_through Δ σ Γ Δ' φ Γ1 ζ1 σ1 ->
      mdenote gc_deps gc_stack Γ1 (me_mem (me_lit (gu_mk nil (md_body sm Φ)))[ζ1]ᵐ x) R -> mdesc_type R = Some A' ->
      glu_elem_at Δ' A'[σ1] (a_mem (me_lit (gu_mk nil (md_body sm Φ)))[ζ1]ᵐ x)[σ1] a m i P El.
Proof.
  intros * HU Hp Ht Hf HC HA HM Eσ Hσ'' Hglu HMg * [Hφ Hζ1 Hσ1 Heq] Hm HA'.
  cbn [modexp_sub gunit_sub] in Hm |- *.
  (** A closed body has no description outside its path *)
  destruct sm.
  2:{ exfalso; inversion Hm; subst; try (cbn in *; discriminate).
      match goal with H0 : mdenote _ _ _ (me_lit _) _ |- _ => apply mdenote_lit_inv in H0; inversion H0; subst end.
      cbn in *; discriminate. }
  (** The lookup: the member's type is its type filled in, its reduct its
      body filled in ([body_mem_desc]), at the substituted body *)
  assert (Hx : exists Φx, body_xp gc_deps gc_stack (nil ++ Γ1) (gmod_sub Φ (sb_qn 0 ζ1)) Φx).
  { inversion Hm; subst; try (cbn in *; discriminate).
    match goal with H0 : mdenote _ _ _ (me_lit _) _ |- _ => apply mdenote_lit_inv in H0; inversion H0; subst end.
    eexists; eassumption. }
  destruct Hx as [Φx Hx].
  pose proof (body_xp_expand _ _ _ _ _ Hx) as EΦx; rewrite gm_expand_sub in EΦx; subst Φx.
  destruct (body_mem_desc _ _ (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) _ _ _ _ _ _ _ Hx Hm HA')
    as (Φ0w & Ew & A0 & M0 & τ & Hpw & Htw & Hfw & EA' & Ered & _).
  destruct (gm_prefix_sub_inv _ _ _ _ _ Hpw) as (Φ0 & E0 & Hp0 & -> & ->).
  rewrite Hp in Hp0; injection Hp0 as <- <-.
  destruct (entry_tm_sub_inv _ _ _ _ Htw) as (A1 & M1 & Ht1 & -> & ->).
  rewrite Ht in Ht1; injection Ht1 as <- <-.
  destruct (gm_fill_sub Φ' 0 ζ1 ζ Hf) as (τ' & Hf' & Eτ).
  rewrite Hfw in Hf'; injection Hf' as <-.
  cbn [ctx_pi_at ctx_fn sb_qn] in *.
  rewrite PeanoNat.Nat.add_0_r in Eτ.
  assert (EX : forall X, X[sb_qn (gm_binders Φ') ζ1][τ] = X[ζ][ζ1])
    by (intros X; rewrite !exp_sub_sub; apply exp_sub_sb_eq; exact Eτ).
  rewrite EX in EA', Ered; subst A'.
  pose proof (wf_gm_fill _ _ _ _ _ HC Hf) as Hζ.
  assert (HUl : gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ me_lit (gu_open nil Φ)[ζ1]ᵘ ≈ me_lit (gu_open nil Φ)[ζ1]ᵘ)
    by exact (sub_preserves_modexp _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) Hζ1).
  pose proof (wf_exp_eq_mem_delta _ _ _ _ _ _ _ _ HUl Hm HA' Ered) as Hδ.
  (** The factorization, read at the body's context *)
  assert (Hw : sb_eq (sb_wk σ'' φ) (ζ ⨟ sb_wk σ φ))
    by (rewrite (sb_wk_compose σ''), Eσ, sb_compose_assoc, <- sb_wk_compose; reflexivity).
  assert (Hs : Δ' ⊢ˢ ζ ⨟ (ζ1 ⨟ σ1) ≈ sb_wk σ'' φ : body_ctx Φ' ++ Γ).
  { eapply wf_sub_eq_respects_sb_eq; [| symmetry; exact Hw ].
    apply wf_sub_eq_sym; eapply wf_sub_eq_compose_right; [ exact Hζ | exact Heq ]. }
  (** The body's gluing, weakened, moved to the filled-in type and to the
      member *)
  pose proof (glu_univ_elem_exp_monotone _ _ _ _ Hglu _ _ _ _ _ _ HMg Hφ) as HMw.
  rewrite !exp_wk_sub in HMw.
  assert (EA : Δ' ⊢ A[ζ][ζ1][σ1] ≈ A[sb_wk σ'' φ] : abs_kind_sort (domain_kind a) Typeω@(large_level i)).
  { rewrite !exp_sub_sub.
    pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HA) Hs) as H.
    rewrite abs_kind_sort_sub in H; exact H. }
  assert (EM : Δ' ⊢ M[ζ][ζ1][σ1] ≈ M[sb_wk σ'' φ] : A[ζ][ζ1][σ1])
    by (rewrite !exp_sub_sub; exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HM) Hs)).
  pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hglu _ _ _ _ _ HMw (wf_exp_eq_sym _ _ _ _ _ _ EA)) as HM1.
  constructor; [ exact Hglu | exact (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HM1) |].
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu | exact HM1 |].
  etransitivity; [ apply wf_exp_eq_sym; exact EM |].
  apply wf_exp_eq_sym; exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hδ Hσ1).
Qed.

(** A glued context's suffix is glued. *)
Lemma glu_rel_ctx_app_r : forall Ψ Γ, ⊩ (Ψ ++ Γ) -> ⊩ Γ.
Proof. induction Ψ as [| e Ψ IH]; intros Γ H; [ exact H | apply IH; exact (glu_rel_ctx_tail H) ]. Qed.

(** A body with an environment can be filled in: its entries are
    definitions with bodies and modules. *)
Lemma eval_body_env_fill : forall Φ ρ ρ', ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> exists ζ, gm_fill Φ = Some ζ.
Proof.
  intros * Hb; induction Hb; cbn [gm_fill];
    try (destruct IHHb as [ζ ->]; eexists; reflexivity); eexists; reflexivity.
Qed.

(** A prefix of a body whose definitions are of the sorts of their tags
    has the same property. *)
Lemma body_sorts_typed_prefix : forall Φ Γ x Φ', gm_noopen Φ -> body_sorts_typed Φ Γ ->
    gm_prefix_upto Φ x = Some Φ' -> body_sorts_typed Φ' Γ.
Proof.
  induction Φ as [| Φ IH y E | ? ? ? ? ? ?]; intros Γ x Φ' Hno Hst Hp; cbn in Hp, Hno; [ discriminate | | contradiction ].
  destruct (String.eqb x y); [ injection Hp as <-; exact Hst |].
  cbn [body_sorts_typed] in Hst; exact (IH _ _ _ Hno (proj1 Hst) Hp).
Qed.

(** The term member [x] of a glued literal body's closure, at a glued
    environment: its body's value in the body's environment, glued as the
    literal's member ([glu_lit_body_member]) from the body context's
    gluing ([glu_body_env]). *)
Lemma glu_lit_body_mem_field : forall Γ sm Φ Sb Δ σ ρ x Φ' E A M ρ',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_body sm Φ) ≈ gu_mk nil (md_body sm Φ) ->
    ⊩ (body_ctx (gm_expand Φ) ++ Γ) -> body_sorts_typed (gm_expand Φ) Γ ->
    EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
    gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) ->
    evaluated_kind (entry_kind E) -> ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
    exists a m, glu_body_member Δ σ Γ (me_lit (gu_mk nil (md_body sm Φ))) x A M ρ' a m.
Proof.
  intros * HU HC Hst HSb Hσ Hp Ht Hk Hb.
  pose proof (body_sorts_typed_prefix _ _ _ _ (gm_noopen_expand Φ) Hst Hp) as Hst'.
  cbn [body_sorts_typed] in Hst'; destruct Hst' as [Hst' HsvE].
  destruct (eval_body_env_fill _ _ _ Hb) as [ζ Hf].
  destruct (HsvE _ _ _ Ht Hf) as [iA HAf].
  destruct (gm_prefix_upto_body_ctx _ _ _ Hp) as [Ψ EΨ].
  assert (HCx : ⊩ (body_ctx (gm_ext Φ' x E) ++ Γ))
    by (apply (glu_rel_ctx_app_r Ψ); rewrite List.app_assoc, <- EΨ; exact HC).
  destruct HCx as [SbE HSbE].
  (** The entry is a definition, or a definition with a module part *)
  destruct E as [b pv κ A0 [M0 |] | ? ? | ? ? ? ? ? | pv A0 M0 U0 | ? ? ? ?]; cbn [entry_tm] in Ht; try discriminate;
    injection Ht as -> ->; cbn [body_ctx app entry_kind] in HSbE, HAf, Hk.
  all: destruct (glu_rel_ctx_tail (ex_intro _ _ HSbE)) as [SbP HSbP].
  all: destruct (glu_body_env _ _ _ HSb Hst' _ Hf _ HSbP _ _ _ Hσ) as (σ'' & ρ'' & Eσ & Hb'' & Hσ'').
  all: pose proof (functional_eval_body_env _ _ _ _ Hb'' Hb) as ->.
  all: pose proof (glu_ctx_env_sub_escape HSbP _ _ _ Hσ'') as Hσ''s.
  all: pose proof (glu_ctx_env_wf_ctx HSbP) as HCP.
  all: pose proof (wf_gm_fill _ _ _ _ _ HCP Hf) as Hζ.
  - destruct (glu_ctx_env_cons_def_clean_inversion HSbP HSbE) as (i & κ' & HA & HM & _ & HMg & _).
    destruct (HMg _ _ _ Hσ'') as [a m P El Ea Hm Hglu HMσ].
    assert (HAσ : Δ ⊢ A[σ''] : abs_kind_sort κ' Typeω@i)
      by (replace (abs_kind_sort κ' Typeω@i) with ((abs_kind_sort κ' Typeω@i)[σ'']) by (rewrite abs_kind_sort_sub; reflexivity);
          exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ''s)).
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HMσ) HAσ) as [Hka _].
    assert (Hκ : κ' = κ).
    { assert (HAζ : Γ ⊢ A[ζ] : abs_kind_sort κ' Typeω@i)
        by (replace (abs_kind_sort κ' Typeω@i) with ((abs_kind_sort κ' Typeω@i)[ζ]) by (rewrite abs_kind_sort_sub; reflexivity);
            exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hζ)).
      exact (exp_eq_same_kind _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HAζ) (sort_kind_abs_kind_sort _ _) HAf (sort_kind_abs_kind_sort _ _)). }
    subst κ'.
    assert (Em : ⟦ M ⟧ ρ' ↘ m) by (rewrite Hκ in Hm; destruct Hk; exact Hm).
    exists a, m; constructor; [ exact Ea | exact Em |].
    intros * Hst1 Hm1 HA1 _ _.
    exists i, P, El.
    exact (glu_lit_body_member _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU Hp eq_refl Hf HCP HA HM Eσ Hσ''s Hglu HMσ _ _ _ _ _ _ _ Hst1 Hm1 HA1).
  - destruct (glu_ctx_env_cons_dm_clean_inversion HSbP HSbE) as (i & HA & HM & _ & _ & HMg & _).
    destruct (HMg _ _ _ Hσ'') as [a m P El Ea Hm Hglu HMσ].
    assert (HAσ : Δ ⊢ A[σ''] : abs_kind_sort ak_relevant Typeω@i) by (cbn; exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ''s)).
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HMσ) HAσ) as [Hka _].
    assert (Em : ⟦ M ⟧ ρ' ↘ m) by (rewrite Hka in Hm; exact Hm).
    exists a, m; constructor; [ exact Ea | exact Em |].
    intros * Hst1 Hm1 HA1 _ _.
    exists i, P, El.
    assert (HA' : body_ctx Φ' ++ Γ ⊢ A : abs_kind_sort (domain_kind a) Typeω@i) by (rewrite Hka; exact HA).
    exact (glu_lit_body_member _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU Hp eq_refl Hf HCP HA' HM Eσ Hσ''s Hglu HMσ _ _ _ _ _ _ _ Hst1 Hm1 HA1).
Qed.

(** The submodule [y] of a glued literal body's closure: its unit's
    closure in the body's environment, glued as the unit's literal by the
    body context's slot premise, then read through the fill
    ([glu_dmod_through]) and moved to the selection, which has the same
    module part ([same_part_lit_sel], [glu_dmod_same_part]). *)
Lemma glu_lit_body_sub_field : forall Γ Φ Sb Δ σ ρ y Φ' E Δy Dy ρ' h',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open nil Φ ≈ gu_open nil Φ ->
    ⊩ (body_ctx (gm_expand Φ) ++ Γ) -> body_sorts_typed (gm_expand Φ) Γ ->
    EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
    gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) -> entry_unit E = Some (gu_mk Δy Dy) ->
    ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> ⟦ Δy ⊢ Dy ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' ->
    glu_dmod Δ σ Γ (me_mem (me_lit (gu_open nil Φ)) y) h'.
Proof.
  intros * HU HC Hst HSb Hσ Hp HE Hb Hc.
  pose proof (body_sorts_typed_prefix _ _ _ _ (gm_noopen_expand Φ) Hst Hp) as Hst'.
  cbn [body_sorts_typed] in Hst'; destruct Hst' as [Hst' _].
  destruct (eval_body_env_fill _ _ _ Hb) as [ζ Hf].
  destruct (gm_prefix_upto_body_ctx _ _ _ Hp) as [Ψ EΨ].
  assert (HCx : ⊩ (body_ctx (gm_ext Φ' y E) ++ Γ))
    by (apply (glu_rel_ctx_app_r Ψ); rewrite List.app_assoc, <- EΨ; exact HC).
  destruct HCx as [SbE HSbE].
  set (U0 := gu_mk Δy Dy) in *.
  (** The entry's unit, well formed in the context before it, an alias if
      the entry is a definition with a module part *)
  assert (HEx : exists e, body_ctx (gm_ext Φ' y E) = e :: body_ctx Φ' /\ centry_unit e = Some U0 /\
            gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Γ ⊢ᵘ U0 ≈ U0 /\
            (forall pv A M, E = ge_def_mod pv A M U0 -> exists E', U0 = gu_mk nil (md_alias E'))).
  { pose proof (glu_ctx_env_wf_ctx HSbE) as HwE.
    destruct E as [? ? ? ? ? | pv U1 | ? ? ? ? ? | pv A M U1 | ? ? ? ?]; cbn [entry_unit] in HE; try discriminate;
      injection HE as ->; cbn [body_ctx app] in HwE |- *; eexists; split; try reflexivity; split; try reflexivity.
    - inversion HwE; subst; split; [ assumption | intros; discriminate ].
    - inversion HwE; subst; split; [ assumption | intros ? ? ? [= <- <- <-]; eexists; reflexivity ]. }
  destruct HEx as (e & Ee & HeU & HUy & HEdm).
  rewrite Ee in HSbE; cbn [app] in HSbE.
  destruct (glu_rel_ctx_tail (ex_intro _ _ HSbE)) as [SbP HSbP].
  destruct (glu_body_env _ _ _ HSb Hst' _ Hf _ HSbP _ _ _ Hσ) as (σ'' & ρ'' & Eσ & Hb'' & Hσ'').
  pose proof (functional_eval_body_env _ _ _ _ Hb'' Hb) as ->.
  pose proof (glu_ctx_env_sub_escape HSbP _ _ _ Hσ'') as Hσ''s.
  pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσs.
  pose proof (wf_gm_fill _ _ _ _ _ (glu_ctx_env_wf_ctx HSbP) Hf) as Hζ.
  (** The unit's literal, glued at the body's environment, read through
      the fill *)
  pose proof (glu_ctx_env_lit_inversion HSbP HSbE HeU _ _ _ _ Hσ'' (proj2 (eval_me_lit_iff _ _ _ _) Hc)) as Hlit.
  pose proof (proj1 glu_dmod_through _ _ _ _ _ Hlit _ _ _ Hζ Hσs (wf_sub_eq_of_sb_eq _ _ _ _ _ _ Hσ''s Eσ)) as Hlitζ.
  cbn [modexp_sub] in Hlitζ.
  (** The selection has the module part of the literal filled in *)
  destruct (same_part_lit_sel _ _ _ _ _ _ _ HU Hp HE Hf HUy HEdm) as [Hs01 Hs10].
  pose proof (sub_preserves_unit _ _ _ _ _ _ _ HUy Hζ) as HUyζ.
  pose proof (wf_me_lit _ _ _ _ _ HUyζ) as HLζ.
  destruct (me_mod_tele_exists HLζ) as (R' & T' & HR' & HT').
  assert (HRm' : exists Rm', mdesc_mod R' = Some Rm')
    by (unfold mdesc_mod_tele in HT'; destruct (mdesc_mod R'); [ eexists; reflexivity | discriminate ]).
  destruct HRm' as [Rm' HRm'].
  pose proof (wf_sub_id _ _ _ (presup_unit_eq_ctx HU)) as HId.
  destruct (Hs10 _ Id _ _ HId ltac:(rewrite modexp_sub_id; exact HR') HRm') as (R0 & HR0 & HRm0).
  rewrite modexp_sub_id in HR0.
  pose proof (mdesc_mod_tele_part _ _ _ HT' (ex_intro _ Rm' (conj HRm' HRm0))) as HT0.
  assert (HH0 : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem (me_lit (gu_open nil Φ)) y ≈ me_mem (me_lit (gu_open nil Φ)) y).
  { pose proof (wf_me_lit _ _ _ _ _ HU) as HL.
    eapply wf_me_mem; [ exact HL | exact HR0 | exact HT0 | exact HR0 | exact HT0 ]. }
  assert (HHeq : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem (me_lit (gu_open nil Φ)) y ≈ me_lit U0[ζ]ᵘ).
  { eapply wf_me_trans; [ exact (lookup_sound _ _ _ _ _ _ HH0 HR0 HRm0) |].
    apply wf_me_sym; exact (lookup_sound _ _ _ _ _ _ HLζ HR' HRm'). }
  eapply (proj1 glu_dmod_same_part); [ exact Hlitζ | exact HHeq | exact Hs01 | exact Hs10 | intros; reflexivity | intros; reflexivity ].
Qed.

(** A well-formed saturated literal body's definitions are of the sorts of
    their tags, as its description has it ([desc_ok_open]). *)
Lemma body_sorts_typed_of_unit : forall Γ Φ,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open nil Φ ≈ gu_open nil Φ -> body_sorts_typed (gm_expand Φ) Γ.
Proof.
  intros * HU.
  pose proof (wf_me_lit _ _ _ _ _ HU) as HL.
  destruct (me_denotes _ _ _ _ _ HL) as (R & ? & HR & _).
  pose proof (me_desc_ok _ _ _ _ _ _ HL HR) as Hok.
  apply mdenote_lit_inv in HR; inversion HR; subst.
  match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
  match goal with Hx : body_xp _ _ _ Φ ?Φx |- _ => pose proof (body_xp_expand _ _ _ _ _ Hx) as ->; clear Hx end.
  inversion Hok; subst.
  apply body_sorts_typed_of_lookups; [ assumption |].
  intros * Hp Ht Hf.
  match goal with Hs : forall y Φ0 E A M σ, _ -> _ -> _ -> exists i, _ |- _ => exact (Hs _ _ _ _ _ _ Hp Ht Hf) end.
Qed.

(** The closure of a saturated literal body, at a glued environment, is
    glued as the literal: its members and submodules are
    ([glu_lit_body_mem_field], [glu_lit_body_sub_field]). *)
Lemma glu_lit_body_modexp_at : forall Γ Φ,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open nil Φ ≈ gu_open nil Φ ->
    ⊩ (body_ctx (gm_expand Φ) ++ Γ) -> body_sorts_typed (gm_expand Φ) Γ ->
    glu_modexp_at Γ (me_lit (gu_open nil Φ)).
Proof.
  intros * HU HC Hst Sb HSb Δ σ ρ Hσ.
  exists (dm_local nil (md_body sm_open (gm_expand Φ)) ρ); split; [ apply eval_me_lit_iff; constructor |].
  apply glu_dmod_body; [ exact (glu_ctx_env_sub_escape HSb _ _ _ Hσ) | exact (wf_me_lit _ _ _ _ _ HU) | |];
    rewrite (gm_expand_noopen _ (gm_noopen_expand Φ)).
  - intros * Hp Ht Hk Hb; eapply glu_lit_body_mem_field; eassumption.
  - intros * Hp Hu Hb Hc; eapply glu_lit_body_sub_field; eassumption.
Qed.

End Fixed_GCtx.
