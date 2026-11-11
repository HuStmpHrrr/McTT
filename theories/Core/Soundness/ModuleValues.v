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
From Mctt.Core.Completeness.Modules Require Import ValidUnit Values.
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

End Fixed_GCtx.
