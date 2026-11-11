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

End Fixed_GCtx.
