(** * Deep Descriptions

    What a module expression denotes is deep ([glu_desc_deep]) when the
    module expression's parts are ([glu_desc_deep_of_source]): the unit its
    module part stands for ([mdesc_unit]), the right-hand side of
    [wf_me_delta_sel], is then glued at each instance.  The proof follows
    how the description is denoted, at the source of a sound embedding, so
    that each stored module it reads is a location of the source.  Its steps
    are the description given an argument ([glu_desc_deep_at]), abstracted
    ([glu_desc_deep_up]), moved by a substitution preserving instances
    ([glu_desc_deep_stable]), and an entry of a body or of a stored module
    read ([glu_desc_deep_read_open], [glu_desc_deep_read_closed]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas LookupSound Presup Paths DescTyping.
From Mctt.Core.Soundness Require Import LogicalRelation ModuleValues Instances Extensions UnitEqCases UnitDeep Selection MemberGluing.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Reading the module part *)

(** A description is deep as its module part is. *)
Lemma glu_desc_deep_mod : forall Γ R Rm, mdesc_mod R = Some Rm -> glu_desc_deep Γ R <-> glu_desc_deep Γ Rm.
Proof.
  intros * Hm; unfold glu_desc_deep; rewrite Hm, (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ Hm)); reflexivity.
Qed.

(** A definition with a module part is deep as its module part is. *)
Lemma glu_desc_deep_dm_intro : forall Γ Θd A M Rm, glu_desc_deep Γ Rm -> glu_desc_deep Γ (mdesc_dm Θd A M Rm).
Proof. intros * H; exact H. Qed.

(** A description with no module part is deep. *)
Lemma glu_desc_deep_no_mod : forall Γ R, mdesc_mod R = None -> glu_desc_deep Γ R.
Proof. intros * Hm; unfold glu_desc_deep; rewrite Hm; exact I. Qed.

(** Source and grown target descriptions agree under [glu_desc_deep]: a
    closed description grows in its stored body only, which
    [glu_desc_deep] does not read. *)
Lemma glu_desc_deep_grows : forall Θ1 Ξ1 Θ2 Ξ2 Γ R1 R2,
    mdesc_grows Θ1 Ξ1 Θ2 Ξ2 R1 R2 -> glu_desc_deep Γ R1 -> glu_desc_deep Γ R2.
Proof.
  induction 1 as [R Hc | Θ' T Φ1 Φ2 Ns p _ _ | Θd A M R1 R2 Hd IH]; intros HR; [ exact HR | exact HR | exact (IH HR) ].
Qed.

(** No argument is glued. *)
Lemma glu_args_deep_nil : forall Γ T, glu_args_deep Γ T nil.
Proof. intros * Trest Tfilled _ _ [| k] *; cbn; discriminate. Qed.

(** A closed module at no outside parameter and no argument is deep. *)
Lemma glu_desc_deep_closed_nil : forall Γ p T Φ,
    glu_rel_ctx_types Γ -> glu_desc_deep Γ (mdesc_closed nil p T Φ nil).
Proof. intros * HΓ; split; [ exact HΓ | apply glu_args_deep_nil ]. Qed.

(** ** Abstraction *)

(** A deep description abstracted over an extension glued at the
    instances is deep. *)
Lemma glu_desc_deep_up : forall Γ Δ R,
    glu_rel_ext_under_sub Γ Δ -> glu_desc_deep (Δ ++ Γ) R -> glu_desc_deep Γ (mdesc_up Δ R).
Proof.
  intros * HΔ HR; unfold glu_desc_deep in *; rewrite mdesc_mod_up.
  destruct (mdesc_mod R) as [[| Δ0 Φ Φx | Θ' p T Φ Ns |] |]; cbn [option_map mdesc_up]; try exact I.
  - exact (glu_unit_deep_params_join _ _ _ _ HΔ HR).
  - destruct HR as [HΘ HN]; split; [ exact (glu_rel_ext_under_sub_app_join _ _ _ HΔ HΘ) | rewrite <- app_assoc; exact HN ].
Qed.

(** And conversely, a deep abstracted description is deep under the
    parameters. *)
Lemma glu_desc_deep_up_inv : forall Γ Δ R, glu_desc_deep Γ (mdesc_up Δ R) -> glu_desc_deep (Δ ++ Γ) R.
Proof.
  intros * HR; unfold glu_desc_deep in *; rewrite mdesc_mod_up in HR.
  destruct (mdesc_mod R) as [[| Δ0 Φ Φx | Θ' p T Φ Ns |] |]; cbn [option_map mdesc_up] in HR; try exact I.
  - cbn [glu_unit_deep] in HR |- *; destruct HR as [HΦ HΦu]; rewrite app_assoc in HΦ; rewrite <- app_assoc in HΦu.
    split; [ exact (glu_rel_ext_under_sub_app_split _ _ _ HΦ) | exact HΦu ].
  - destruct HR as [HΘ HN]; split; [ exact (glu_rel_ext_under_sub_app_split _ _ _ HΘ) | rewrite app_assoc; exact HN ].
Qed.

(** ** Substitutions preserving instances *)

(** The arguments of a closed telescope, glued at the instances of [Δ],
    moved by a substitution preserving instances, are glued at those of
    [Γ]: the telescope, closed, is moved to itself ([tele_insts_sub]). *)
Lemma glu_args_deep_stable : forall Δ T Ns Γ σ, all_assumptions T -> ctx_scoped 0 T ->
    glu_args_deep Δ T Ns -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ ->
    glu_args_deep Γ T (List.map (fun M => M[σ]) Ns).
Proof.
  intros * Ha Hs HN HΓ Hσ Trest Tfilled ET Hl k N A HNk HAk.
  rewrite length_map in Hl.
  rewrite List.nth_error_map in HNk; destruct (List.nth_error Ns k) as [N0 |] eqn:HN0; [| discriminate ]; injection HNk as <-.
  subst T; apply List.Forall_app in Ha as [_ HaF]; apply ctx_scoped_app_iff in Hs as [_ HsF].
  rewrite <- (tele_insts_sub Tfilled 0 Id Id σ Ns HaF HsF ltac:(intros; lia)), List.nth_error_map in HAk.
  destruct (List.nth_error (tele_insts Tfilled Id Ns) k) as [A0 |] eqn:HA0; [| discriminate ]; injection HAk as <-.
  exact (glu_rel_exp_under_sub_stable _ _ _ _ _ (HN _ _ eq_refl Hl _ _ _ HN0 HA0) HΓ Hσ).
Qed.

(** A deep description moved by a substitution preserving instances, whose
    module components are deep, is deep ((b) on an open module part; the
    outside parameters and the arguments of a closed one, its telescope
    closed as stored ([mdesc_canonical])). *)
Lemma glu_desc_deep_stable : forall Θc Ξc, ⊢ᵍ Θc ⍮ Ξc -> forall Δ R Γ σ,
    mdesc_canonical Θc Ξc R -> glu_desc_deep Δ R -> glu_rel_ctx_types Γ -> glu_rel_sub_stable Γ σ Δ ->
    glu_rel_sub_mods_deep Γ σ -> glu_desc_deep Γ (mdesc_sub R σ).
Proof.
  intros Θc Ξc Hgc * Hc HR HΓ Hσ Hm.
  destruct (mdesc_mod R) as [Rm |] eqn:Hmod.
  2:{ apply glu_desc_deep_no_mod; destruct (mdesc_mod (mdesc_sub R σ)) eqn:E; [| reflexivity ].
      destruct (mdesc_mod_sub_inv _ _ _ E) as (R' & HR' & _); congruence. }
  apply (proj2 (glu_desc_deep_mod _ _ _ (mdesc_mod_sub _ _ σ Hmod))).
  apply (proj1 (glu_desc_deep_mod _ _ _ Hmod)) in HR.
  pose proof (mdesc_canonical_mod _ _ _ _ Hc Hmod) as Hcm.
  pose proof (mdesc_mod_is_mod _ _ Hmod) as Him.
  destruct Rm as [| Δ0 Φ Φx | Θ' p T Φ Ns |]; cbn in Him; try contradiction; cbn [mdesc_sub];
    unfold glu_desc_deep in HR |- *; cbn [mdesc_mod] in HR |- *.
  - pose proof (glu_unit_deep_stable _ _ _ _ HR HΓ Hσ Hm) as H; rewrite gunit_sub_mk in H; exact H.
  - destruct HR as [HΘ HN].
    destruct (glu_rel_ext_under_sub_stable _ _ _ _ HΘ HΓ Hσ) as [HΘσ Hst].
    cbn in Hcm.
    pose proof (loc_closed _ _ Hgc _ _ _ Hcm) as [HsT _].
    pose proof (gc_loc_tele_all_assumptions _ _ Hgc _ _ _ (gc_loc_of_loc _ _ Hgc _ _ _ Hcm)) as HaT.
    split; [ exact HΘσ |].
    exact (glu_args_deep_stable _ _ _ _ _ HaT HsT HN (glu_rel_ext_under_sub_ctx_types _ _ HΘσ) Hst).
Qed.

(** ** Application *)

(** One more argument, glued at the instances at the next parameter of a
    closed telescope instantiated by the arguments before it, as
    [args_ok_snoc] types it. *)
Lemma glu_args_deep_snoc : forall Γ T Ns N C T1', glu_args_deep Γ T Ns -> all_assumptions T ->
    tele_view (List.firstn (length T - length Ns) T) = Some (C, T1') ->
    glu_rel_exp_under_sub Γ N C[sb_of_list Id Ns] -> glu_args_deep Γ T (Ns ++ N :: nil).
Proof.
  intros * HN Ha Hv HN0 Trest Tfilled ET Hl k N1 A HNk HAk.
  rewrite length_app in Hl; cbn in Hl.
  destruct Tfilled as [| e Tf]; cbn in Hl; [ lia |].
  assert (Hl' : length Tf = length Ns) by lia; clear Hl; rename Hl' into Hl.
  subst T; apply List.Forall_app in Ha as [_ HaF]; apply List.Forall_cons_iff in HaF as [(κ & C' & ->) HaF].
  assert (ET : Trest ++ ce_ass κ C' :: Tf = (Trest ++ ce_ass κ C' :: nil) ++ Tf) by (rewrite <- app_assoc; reflexivity).
  rewrite ET in Hv, HN.
  replace (List.firstn (length ((Trest ++ ce_ass κ C' :: nil) ++ Tf) - length Ns) ((Trest ++ ce_ass κ C' :: nil) ++ Tf))
    with (Trest ++ ce_ass κ C' :: nil) in Hv
    by (rewrite length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all;
        reflexivity).
  rewrite tele_view_last in Hv; injection Hv as <- <-.
  change (ce_ass κ C' :: Tf) with ((ce_ass κ C' :: nil) ++ Tf) in HAk.
  rewrite tele_insts_app in HAk by (first [ exact HaF | lia ]).
  destruct (Nat.lt_ge_cases k (length Ns)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HNk by exact Hk.
    rewrite List.nth_error_app1 in HAk by (rewrite length_tele_insts by exact HaF; lia).
    exact (HN _ _ eq_refl Hl _ _ _ HNk HAk).
  - rewrite List.nth_error_app2 in HNk by exact Hk.
    rewrite List.nth_error_app2 in HAk by (rewrite length_tele_insts by exact HaF; lia).
    rewrite length_tele_insts in HAk by exact HaF.
    rewrite <- Hl, Nat.min_id in HAk.
    destruct (k - length Ns) as [| k'] eqn:Ek; cbn in HNk, HAk; [| destruct k'; discriminate ].
    injection HNk as <-; rewrite Hl, Ek in HAk; cbn in HAk; injection HAk as <-; exact HN0.
Qed.

(** A deep description given an argument glued at the instances at its
    next parameter is deep: an open module by (c); a closed one with
    outside parameters left fills the outermost of them, moved by the
    substitution of the argument ([glu_rel_ext_under_sub_stable],
    [glu_args_deep_stable]); with none it records the argument
    ([glu_args_deep_snoc]).  The parameters are assumptions, as the
    description is typed. *)
Lemma glu_desc_deep_at : forall Θc Ξc, ⊢ᵍ Θc ⍮ Ξc -> forall Γ R N R' T B T1,
    desc_ok Θc Ξc Γ R -> glu_desc_deep Γ R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    glu_rel_exp_under_sub Γ N B -> mdesc_at R N = Some R' -> glu_desc_deep Γ R'.
Proof.
  intros Θc Ξc Hgc * Hok HR HT Hv HN Ha.
  unfold mdesc_mod_tele in HT; destruct (mdesc_mod R) as [Rm |] eqn:Hmod; [| discriminate ].
  destruct (mdesc_mod_at _ _ _ _ Hmod Ha) as (Rm' & Ha' & Hmod').
  apply (proj2 (glu_desc_deep_mod _ _ _ Hmod')).
  apply (proj1 (glu_desc_deep_mod _ _ _ Hmod)) in HR.
  pose proof (desc_ok_mod _ _ Hgc _ _ _ Hok Hmod) as Hokm.
  clear R R' Hok Ha Hmod Hmod'.
  inversion Hokm as [| Γ0 Δ Φw Φ lΔ HΦ Hn Hent HaΔ Hsh Hnd HUw HRΔ Htg HLΔ
                    | Γ0 Θ' T0 Φ Ns Θ0 Ξ0 p lΘ Hg0 Hsub0 Hloc Ha0 Hs0 HT0 HΘ' Hargs HaΘ HRΘ HLΘ HFΘ |];
    subst; cbn in HT; try discriminate.
  - (* an open module: (c) *)
    injection HT as <-.
    destruct (tele_view_ass _ _ _ HaΔ Hv) as (κ & ->).
    cbn [mdesc_at] in Ha'; rewrite rev_app_distr in Ha'; cbn [rev app tele_split] in Ha'; rewrite rev_involutive in Ha'.
    injection Ha' as <-.
    unfold glu_desc_deep in HR |- *; cbn [mdesc_mod] in HR |- *.
    pose proof HR as HR0; cbn [glu_unit_deep] in HR0; destruct HR0 as [HΦe _].
    pose proof (glu_rel_ext_under_sub_app_inv _ (glu_rel_ext_under_sub_app_inv _ HΦe)) as HB; cbn [glu_rel_ext_under_sub] in HB.
    destruct HB as [_ (S & HS & HBS)].
    pose proof (glu_unit_deep_beta _ _ _ _ _ _ _ HR (glu_rel_exp_under_sub_wf HBS) HS HN) as H.
    cbn [moddef_sub] in H.
    rewrite (gmod_sub_sb_eq Φw _ _ (sb_compose_id_left _)); exact H.
  - (* a closed module *)
    destruct (Nat.leb (length Ns) (length T0)) eqn:Hle; [| discriminate ]; injection HT as <-.
    apply Nat.leb_le in Hle.
    clear HRΘ HLΘ HFΘ Hargs; induction Θ' as [| e Θ1 _] using List.rev_ind.
    { (* no outside parameter: the argument recorded *)
      cbn [mdesc_at rev tele_split] in Ha'; injection Ha' as <-.
      unfold glu_desc_deep in HR |- *; cbn [mdesc_mod] in HR |- *.
      destruct HR as [HΓ HNs]; split; [ exact HΓ |].
      rewrite List.app_nil_r, tele_view_sub in Hv.
      destruct (tele_view (List.firstn (length T0 - length Ns) T0)) as [[C T1'] |] eqn:Hv0; cbn in Hv; [| discriminate ].
      injection Hv as <- _.
      rewrite (List.map_ext _ (fun M => M) (fun M => exp_sub_id M)), List.map_id.
      exact (glu_args_deep_snoc _ _ _ _ _ _ HNs Ha0 Hv0 HN). }
    { (* an outside parameter: the outermost filled *)
      apply List.Forall_app in HaΘ as [HaΘ1 He]; apply List.Forall_cons_iff in He as [(κ & X & ->) _].
      rewrite app_assoc, tele_view_last in Hv; injection Hv as <- _.
      cbn [mdesc_at] in Ha'; rewrite rev_app_distr in Ha'; cbn [rev app tele_split] in Ha'; rewrite rev_involutive in Ha'.
      injection Ha' as <-.
      unfold glu_desc_deep in HR |- *; cbn [mdesc_mod] in HR |- *.
      destruct HR as [HΘ HNs].
      pose proof (glu_rel_ext_under_sub_app_inv _ HΘ) as HX; cbn [glu_rel_ext_under_sub] in HX.
      destruct HX as [HΓ (S & HS & HXS)].
      pose proof (glu_rel_sub_stable_extend_id _ _ _ _ _ (glu_rel_exp_under_sub_wf HXS) HS HN) as Hst.
      destruct (glu_rel_ext_under_sub_stable _ _ _ _ (glu_rel_ext_under_sub_app_split _ _ _ HΘ) HΓ Hst) as [HΘ1N Hst1].
      split; [ exact HΘ1N |].
      rewrite (List.map_ext _ (fun M => M[sb_qn (length Θ1) (Id,,N)])
                 (fun M => exp_sub_sb_eq M _ _ (sb_compose_id_left _))).
      rewrite <- app_assoc in HNs.
      exact (glu_args_deep_stable _ _ _ _ _ Ha0 Hs0 HNs (glu_rel_ext_under_sub_ctx_types _ _ HΘ1N) Hst1). }
Qed.

(** ** Arguments at a telescope *)

(** The arguments of a telescope are those of the telescope extended
    inside: they fill its outermost parameters. *)
Lemma glu_args_deep_ext : forall Γ T Ns Δ0, glu_args_deep Γ T Ns -> length Ns <= length T -> glu_args_deep Γ (Δ0 ++ T) Ns.
Proof.
  intros * HN Hl Trest Tfilled ET Hlf.
  destruct (List.app_eq_app _ _ _ _ ET) as (X & [[-> E2] | [-> E2]]).
  - (* the filled parameters cover the whole telescope: it is all of it *)
    destruct X as [| x X]; [ cbn in E2; subst Tfilled; exact (HN nil T eq_refl Hlf) |].
    subst Tfilled; rewrite length_app in Hlf; cbn in Hlf; lia.
  - exact (HN X Tfilled E2 Hlf).
Qed.

(** Arguments glued at a telescope, filling its outermost parameters, are
    glued at the instantiated parameters, as [args_ok_insts] types
    them. *)
Lemma glu_args_deep_insts : forall Γ T Ns, glu_args_deep Γ T Ns -> all_assumptions T -> length Ns <= length T ->
    forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts T Id Ns) k = Some A -> glu_rel_exp_under_sub Γ N A.
Proof.
  intros * HN Ha Hl k N A HNk HAk.
  assert (Hk : k < length Ns) by (apply List.nth_error_Some; congruence).
  remember (length T - length Ns) as n eqn:En.
  rewrite <- (firstn_skipn n T) in Ha, HAk.
  rewrite <- (List.app_nil_r Ns) in HAk.
  apply List.Forall_app in Ha as [_ HaF].
  rewrite tele_insts_app in HAk by (first [ exact HaF | rewrite length_skipn; lia ]).
  rewrite List.nth_error_app1 in HAk by (rewrite length_tele_insts by exact HaF; rewrite length_skipn; lia).
  exact (HN _ _ (eq_sym (firstn_skipn n T)) ltac:(rewrite length_skipn; lia) _ _ _ HNk HAk).
Qed.

(** A deep description abstracted over a telescope glued at the
    instances, given arguments glued at the instances for its outermost
    parameters, is deep: the semantic [ats_up_ok], each argument
    substituted in by [glu_desc_deep_stable]. *)
Lemma glu_desc_deep_ats_up : forall Θc Ξc, ⊢ᵍ Θc ⍮ Ξc -> forall Ns Γ Δa R R',
    all_assumptions Δa -> length Ns <= length Δa -> glu_rel_ext_under_sub Γ Δa ->
    mdesc_canonical Θc Ξc R -> glu_desc_deep (Δa ++ Γ) R ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> glu_rel_exp_under_sub Γ N A) ->
    mdesc_ats (mdesc_up Δa R) Ns = Some R' -> glu_desc_deep Γ R'.
Proof.
  intros Θc Ξc Hgc; induction Ns as [| N Ns IH]; intros * Ha Hl HΔ Hc HR HNs Hats.
  - cbn in Hats; injection Hats as <-; exact (glu_desc_deep_up _ _ _ HΔ HR).
  - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
    apply List.Forall_app in Ha as [Ha1 He]; apply List.Forall_cons_iff in He as [(κC & C & ->) _].
    rewrite tele_insts_snoc in HNs.
    pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
    cbn [mdesc_ats] in Hats; rewrite mdesc_at_up in Hats.
    pose proof (glu_rel_ext_under_sub_app_inv _ HΔ) as HC; cbn [glu_rel_ext_under_sub] in HC.
    destruct HC as [HΓ (Srt & HS & HCS)].
    pose proof (glu_rel_sub_stable_extend_id _ _ _ _ _ (glu_rel_exp_under_sub_wf HCS) HS HN) as Hst.
    destruct (glu_rel_ext_under_sub_stable _ _ _ _ (glu_rel_ext_under_sub_app_split _ _ _ HΔ) HΓ Hst) as [HΔ1N Hst1].
    pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΔ1N) as HΔ1Γ.
    rewrite <- app_assoc in HR.
    refine (IH _ _ _ _ (all_assumptions_sub _ _ Ha1) _ HΔ1N (mdesc_canonical_sub _ _ _ _ Hc)
              (glu_desc_deep_stable _ _ Hgc _ _ _ _ Hc HR HΔ1Γ Hst1
                 (glu_rel_sub_mods_deep_qn _ _ _ (glu_rel_ctx_types_wf HΔ1Γ) (glu_rel_sub_mods_deep_extend_id _ _))) _ Hats).
    + rewrite length_tele_sub; rewrite length_app in Hl; cbn in Hl; lia.
    + intros k N1 A HN1 HA.
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
      exact (HNs (S k) N1 A HN1 HA).
Qed.

(** ** Entries of a deep body *)

(** The entries of a deep body before one of them: an extension glued at
    the instances, with deep module entries. *)
Lemma glu_unit_deep_prefix_open : forall Γ Δ Φw y Φ' E,
    glu_unit_deep Γ (gu_mk Δ (md_body sm_open Φw)) -> gm_prefix_upto (gm_expand Φw) y = Some (gm_ext Φ' y E) ->
    glu_rel_ext_under_sub Γ (body_ctx Φ' ++ Δ) /\ glu_gmod_units_deep (Δ ++ Γ) Φ'.
Proof.
  intros * HU Hp; cbn [glu_unit_deep] in HU; destruct HU as [HΦ HΦu].
  destruct (gm_prefix_body_ctx _ _ _ (gm_noopen_expand Φw) Hp) as (Ψ & EΨ).
  rewrite EΨ, <- app_assoc in HΦ.
  pose proof (glu_rel_ext_under_sub_app_inv _ HΦ) as HΦ'.
  pose proof (glu_gmod_units_deep_prefix _ _ _ _ (gm_noopen_expand Φw) Hp (glu_gmod_units_deep_expand _ _ HΦu)) as Hy.
  destruct E as [? ? ? ? [] | | | | ]; cbn [body_ctx app glu_rel_ext_under_sub glu_gmod_units_deep] in HΦ', Hy;
    split; first [ apply HΦ' | apply Hy | exact Hy ].
Qed.

(** The unit of an entry of a deep body is deep, at the entries before
    it. *)
Lemma glu_unit_deep_entry_open : forall Γ Δ Φw y Φ' E U,
    glu_unit_deep Γ (gu_mk Δ (md_body sm_open Φw)) -> gm_prefix_upto (gm_expand Φw) y = Some (gm_ext Φ' y E) ->
    entry_unit E = Some U -> glu_unit_deep (body_ctx Φ' ++ Δ ++ Γ) U.
Proof.
  intros * HU Hp HE; cbn [glu_unit_deep] in HU; destruct HU as [_ HΦu].
  pose proof (gm_noopen_prefix_upto _ _ _ (gm_noopen_expand Φw) Hp) as Hn'; cbn [gm_noopen] in Hn'.
  pose proof (glu_gmod_units_deep_prefix _ _ _ _ (gm_noopen_expand Φw) Hp (glu_gmod_units_deep_expand _ _ HΦu)) as Hy.
  destruct E as [? ? ? ? ? | ? U0 | ? ? ? ? ? | ? ? ? U0 | ? ? ? ?]; cbn [entry_unit] in HE; try discriminate;
    injection HE as <-; cbn [glu_gmod_units_deep] in Hy; rewrite (gm_expand_noopen _ Hn') in Hy; exact (proj2 Hy).
Qed.

(** ** Deep module parts of contexts *)

(** Assumptions add no module part. *)
Lemma glu_ctx_deep_app_ass : forall Δ Γ, all_assumptions Δ -> glu_ctx_deep Γ -> glu_ctx_deep (Δ ++ Γ).
Proof.
  induction 1 as [| e Δ (κ & A & ->) _ IH]; intros HΓ; [ exact HΓ |].
  apply glu_ctx_deep_cons_term; [ reflexivity | exact (IH HΓ) ].
Qed.

(** A path names no literal and no application. *)
Lemma glu_modexp_parts_deep_mems : forall Γ fp ch, glu_modexp_parts_deep Γ (me_mems (me_unit fp) ch).
Proof.
  intros Γ fp ch; assert (H : forall E, glu_modexp_parts_deep Γ E -> glu_modexp_parts_deep Γ (me_mems E ch))
    by (induction ch as [| y ch IH]; intros E HE; [ exact HE | apply IH; exact HE ]).
  apply H; exact I.
Qed.

(** An alias under no parameter whose target has no literal and no
    application, glued at the instances, is deep. *)
Lemma glu_unit_deep_alias_nil : forall Γ E,
    glu_rel_ctx_types Γ -> glu_rel_unit_under_sub Γ (gu_mk nil (md_alias E)) -> glu_modexp_parts_deep Γ E ->
    glu_unit_deep Γ (gu_mk nil (md_alias E)).
Proof.
  intros * HΓ HU HE; constructor; [ exact HΓ | | exact HE ].
  constructor; [ exact HΓ |]; intros Γ' τ Hτ.
  pose proof (HU _ _ Hτ) as H; rewrite gunit_sub_mk in H; cbn [glu_unit_at moddef_sub] in H.
  exact (proj2 H).
Qed.

(** The module parts of the entries of a body without opens, glued at the
    instances, with deep module entries, are deep: a module entry's and a
    definition with a module part's unit by the body, and the alias of the
    module of an inductive or a record type, a path, by its gluing. *)
Lemma glu_ctx_deep_body : forall Φ Γ0, gm_noopen Φ ->
    glu_rel_ext_under_sub Γ0 (body_ctx Φ) -> glu_gmod_units_deep Γ0 Φ -> glu_ctx_deep Γ0 -> glu_ctx_deep (body_ctx Φ ++ Γ0).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg _]; intros Γ0 Hn HΦ HΦu HΓ0; cbn [gm_noopen] in Hn; [ exact HΓ0 | | contradiction ].
  destruct E as [b pv κ A [M |] | pv U | pv pq k D ΦD | pv A M U | pv p R ΦR];
    cbn [body_ctx app glu_rel_ext_under_sub glu_gmod_units_deep] in HΦ, HΦu |- *; try rewrite (gm_expand_noopen _ Hn) in HΦu;
    destruct HΦ as [HΦ He]; pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΦ) as HΦΓ.
  - apply glu_ctx_deep_cons_term; [ reflexivity | exact (IH _ Hn HΦ HΦu HΓ0) ].
  - apply glu_ctx_deep_cons_term; [ reflexivity | exact (IH _ Hn HΦ HΦu HΓ0) ].
  - destruct HΦu as [HΦu HU]; eapply glu_ctx_deep_cons_unit; [ reflexivity | exact HU | exact (IH _ Hn HΦ HΦu HΓ0) ].
  - cbn [glu_rel_entry_under_sub] in He; destruct He as [_ HUg].
    eapply glu_ctx_deep_cons_unit;
      [ reflexivity | exact (glu_unit_deep_alias_nil _ _ HΦΓ HUg (glu_modexp_parts_deep_mems _ _ _)) | exact (IH _ Hn HΦ HΦu HΓ0) ].
  - destruct HΦu as [HΦu HU]; eapply glu_ctx_deep_cons_unit; [ reflexivity | exact HU | exact (IH _ Hn HΦ HΦu HΓ0) ].
  - cbn [glu_rel_entry_under_sub] in He; destruct He as [_ HUg].
    eapply glu_ctx_deep_cons_unit;
      [ reflexivity | exact (glu_unit_deep_alias_nil _ _ HΦΓ HUg (glu_modexp_parts_deep_mems _ _ _)) | exact (IH _ Hn HΦ HΦu HΓ0) ].
Qed.

(** An entry of a deep open module read ([reader_open]): its description,
    deep at the entries before it, filled in ((d)) and abstracted over the
    parameters. *)
Lemma glu_desc_deep_read_open : forall Θc Ξc, ⊢ᵍ Θc ⍮ Ξc -> forall Γ Δ Φw y Φ' E σ R,
    glu_unit_deep Γ (gu_mk Δ (md_body sm_open Φw)) ->
    gm_prefix_upto (gm_expand Φw) y = Some (gm_ext Φ' y E) -> gm_fill Φ' = Some σ ->
    mdesc_canonical Θc Ξc R -> glu_desc_deep (body_ctx Φ' ++ Δ ++ Γ) R ->
    glu_desc_deep Γ (mdesc_up Δ (mdesc_sub R σ)).
Proof.
  intros Θc Ξc Hgc * HU Hp Hf Hc HR.
  pose proof (gm_noopen_prefix_upto _ _ _ (gm_noopen_expand Φw) Hp) as Hn'; cbn [gm_noopen] in Hn'.
  destruct (glu_unit_deep_prefix_open _ _ _ _ _ _ HU Hp) as [HΦ' HΦ'u].
  pose proof (glu_rel_ext_under_sub_app_inv _ HΦ') as HΔ.
  pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΔ) as HΔΓ.
  apply (glu_desc_deep_up _ _ _ HΔ).
  exact (glu_desc_deep_stable _ _ Hgc _ _ _ _ Hc HR HΔΓ (glu_rel_sub_stable_fill _ _ _ _ Hn' HΦ' Hf)
           (glu_rel_sub_mods_deep_fill _ _ _ _ Hn' HΦ' HΦ'u Hf)).
Qed.

(** ** Entries of a stored module *)

(** The module part of a description read at arguments ([mdesc_ats_read])
    is its module part given them ([mdesc_mod_ats]): a definition with a
    module part gives them to its module part as a module. *)
Lemma mdesc_mod_ats_read : forall Ns R Rm R1, mdesc_mod R = Some Rm -> mdesc_ats_read R Ns = Some R1 ->
    exists Rm1, mdesc_ats Rm Ns = Some Rm1 /\ mdesc_mod R1 = Some Rm1.
Proof.
  intros * Hm Ha; destruct (mdesc_ats_read_inv _ _ _ Ha) as [Ha' | (A & M & Rm0 & r & B & M' & Rm' & -> & -> & _ & E)];
    [ exact (mdesc_mod_ats _ _ _ _ Hm Ha') |].
  cbn in Hm |- *; exact (mdesc_mod_ats _ _ _ _ Hm E).
Qed.

(** An entry of a stored module read at the arguments recorded and
    abstracted over the outside parameters ([reader_closed]) is deep when
    its module part given the arguments is, under the outside
    parameters. *)
Lemma glu_desc_deep_read_closed_gen : forall Γ Θ' Ns M R R1 Rm,
    glu_rel_ext_under_sub Γ Θ' -> mdesc_mod R = Some Rm -> mdesc_ats_read R Ns = Some R1 ->
    (forall Rm1, mdesc_ats Rm Ns = Some Rm1 -> glu_desc_deep (Θ' ++ Γ) Rm1) ->
    glu_desc_deep Γ (mdesc_up Θ' (mdesc_named Θ' Ns M R1)).
Proof.
  intros * HΘ Hm Ha HRm.
  destruct (mdesc_mod_ats_read _ _ _ _ Hm Ha) as (Rm1 & Ha1 & Hm1).
  apply (glu_desc_deep_up _ _ _ HΘ).
  apply (proj2 (glu_desc_deep_mod _ _ Rm1 ltac:(rewrite mdesc_mod_named; exact Hm1))).
  exact (HRm _ Ha1).
Qed.

(** An alias stored in a module over the telescope [T], its parameters
    [Δ0 ++ T], read under outside parameters [Θ'] at arguments for [T]: its
    description, closed, is deep under [Θ'] ([glu_desc_deep_stable] at a
    renaming), so under its parameters, and given the arguments
    ([glu_desc_deep_ats_up]). *)
Lemma glu_desc_deep_ats_alias : forall Θc Ξc, ⊢ᵍ Θc ⍮ Ξc -> forall Γ Θ' T Ns Δ0 R0m Rm1,
    glu_rel_ext_under_sub Γ Θ' -> glu_rel_ext_under_sub (Θ' ++ Γ) (Δ0 ++ T) ->
    all_assumptions Δ0 -> all_assumptions T -> length Ns <= length T ->
    mdesc_canonical Θc Ξc R0m -> mdesc_scoped 0 (mdesc_up (Δ0 ++ T) R0m) -> glu_desc_deep Γ (mdesc_up (Δ0 ++ T) R0m) ->
    glu_args_deep (Θ' ++ Γ) T Ns -> mdesc_ats (mdesc_up (Δ0 ++ T) R0m) Ns = Some Rm1 -> glu_desc_deep (Θ' ++ Γ) Rm1.
Proof.
  intros Θc Ξc Hgc * HΘ HΔ Ha0 HaT Hle Hc Hs HR HNs Hats.
  pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΘ) as HΘΓ.
  pose proof (wf_wk_shiftn_app' _ _ _ _ (glu_rel_ctx_types_wf HΘΓ)) as Hφ.
  pose proof (glu_desc_deep_stable _ _ Hgc _ _ _ _ (mdesc_canonical_up _ _ _ _ Hc) HR HΘΓ (glu_rel_sub_stable_wk _ _ _ Hφ)
                (glu_rel_sub_mods_deep_wk _ _)) as Hw.
  rewrite (mdesc_closed_sub _ _ Hs) in Hw.
  assert (HaΔ : all_assumptions (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
  apply (glu_desc_deep_ats_up _ _ Hgc Ns (Θ' ++ Γ) (Δ0 ++ T) R0m Rm1 HaΔ ltac:(rewrite length_app; lia) HΔ Hc
           (glu_desc_deep_up_inv _ _ _ Hw)); [| exact Hats ].
  exact (glu_args_deep_insts _ _ _ (glu_args_deep_ext _ _ _ Δ0 HNs Hle) HaΔ ltac:(rewrite length_app; lia)).
Qed.

End Fixed_GCtx.

(** ** From the source of a sound embedding *)

Section FromSource.
  Variables (Θs : gdeps) (Ξs : gstack) (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hgs : ⊢ᵍ Θs ⍮ Ξs.
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis Hμ : glu_gctx_embedding Θs Ξs Θ Ξ.
  #[local] Instance GCt : GCtx := gc_mk Θ Ξ.

  (** An alias entry, or a definition with a module part, of a module
      stored at the source is stored there as an alias. *)
  Lemma src_child_alias : forall p T Φ y Φ0 E0 Δ E,
      loc Θs Ξs p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) ->
      entry_unit E0 = Some (gu_mk Δ (md_alias E)) -> gc_module Θs Ξs (qname_in p y) = Some (mr_alias (gu_mk Δ (md_alias E))).
  Proof.
    intros * Hl Hp HE.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ1 & E1 & [= <- <-] & Hent).
    destruct (gm_entry_head _ _ _ Hent) as (z & ip & [= <- <-] & Hin).
    destruct (loc_read _ _ Hgs _ _ _ Hl _ Hin nil) as (_ & _ & Hm & _).
    rewrite <- qname_in_app in Hm; rewrite Hm, (proj1 (gm_child_of_entry _ _ _ T Hent)); cbn [gm_submodule].
    rewrite String.eqb_refl.
    destruct E0 as [? ? ? ? ? | ? U | ? ? ? ? ? | ? ? ? U | ? ? ? ?]; cbn [entry_unit] in HE; try discriminate;
      injection HE as ->; reflexivity.
  Qed.

  (** Such a stored alias is typed and deep at every context glued with its
      types: over no context by the stored entry's validity
      ([gc_module_alias_wf]) and the embedding
      ([glu_gctx_embedding_alias_deep]), then weakened, being closed. *)
  Lemma src_child_alias_at : forall Γ p T Φ y Φ0 E0 Δ E,
      loc Θs Ξs p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) ->
      entry_unit E0 = Some (gu_mk Δ (md_alias E)) -> ⊢ Θs ⍮ Ξs ⍮ Γ -> glu_rel_ctx_types Γ ->
      unit_full Θs Ξs Γ (gu_mk Δ (md_alias E)) /\ glu_unit_deep Γ (gu_mk Δ (md_alias E)).
  Proof.
    intros * Hl Hp HE HΓs HΓ.
    pose proof (src_child_alias _ _ _ _ _ _ _ _ Hl Hp HE) as Hm.
    (** The stored alias is closed *)
    pose proof (proj2 (loc_closed _ _ Hgs _ _ _ Hl)) as HcΦ.
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn [body_closed] in HcE; destruct HcE as [_ HcE].
    assert (Hs : gunit_scoped 0 (gu_mk Δ (md_alias E)))
      by (destruct E0 as [? ? ? ? ? | ? U | ? ? ? ? ? | ? ? ? U | ? ? ? ?]; cbn [entry_unit] in HE; try discriminate;
          injection HE as ->; [ exact HcE | exact (proj2 (proj2 HcE)) ]).
    (** Weakened from no context *)
    pose proof (glu_rel_ctx_types_wf HΓ) as HΓt.
    assert (Hφs : Θs ⍮ Ξs ⍮ Γ ⊢ʷ wk_shiftn (length Γ) : ⋅)
      by (pose proof (wf_wk_shiftn_app' Θs Ξs Γ nil ltac:(rewrite app_nil_r; exact HΓs)) as H; rewrite app_nil_r in H; exact H).
    assert (Hφ : Γ ⊢ʷ wk_shiftn (length Γ) : ⋅)
      by (pose proof (wf_wk_shiftn_app' Θ Ξ Γ nil ltac:(rewrite app_nil_r; exact HΓt)) as H; rewrite app_nil_r in H; exact H).
    split.
    - pose proof (wk_preserves_unit _ _ _ _ _ _ _ (gc_module_alias_wf _ _ Hgs _ _ _ _ _ (gc_loc_of_loc _ _ Hgs _ _ _ Hl) Hm) Hφs) as HU.
      rewrite <- gunit_sub_of_wk, gunit_closed_sub in HU by exact Hs.
      exact (proj1 (unit_full_of_eq _ _ _ _ _ HU)).
    - pose proof (glu_unit_deep_wk _ _ _ _ (glu_gctx_embedding_alias_deep _ _ _ _ Hμ _ _ Hm) HΓ Hφ) as HU.
      rewrite gunit_closed_sub in HU by exact Hs; exact HU.
  Qed.

  (** The unit of an entry of a module stored at the source, as read there
      ([ge_read]), when it is open or an alias, is typed and deep at every
      context glued with its types: a stored submodule is closed, and the
      unit of a definition with a module part is an alias
      ([ge_coherent]). *)
  Lemma src_child_entry_at : forall Γ p T Φ y Φ0 E0,
      loc Θs Ξs p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) -> ⊢ Θs ⍮ Ξs ⍮ Γ -> glu_rel_ctx_types Γ ->
      forall U, entry_unit (ge_read T E0) = Some U -> unit_oa U -> unit_full Θs Ξs Γ U /\ glu_unit_deep Γ U.
  Proof.
    intros * Hl Hp HΓs HΓ U HU Hoa.
    pose proof (proj2 (loc_closed _ _ Hgs _ _ _ Hl)) as HcΦ.
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn [body_closed] in HcE; destruct HcE as [_ HcE].
    pose proof (gm_coherent_prefix _ _ _ _ _ (loc_coherent _ _ Hgs _ _ _ Hl) Hp) as HcE0.
    destruct E0 as [? ? ? ? ? | pv [Δ [sm Φy | E]] | ? ? ? ? ? | pv A M [Δ [sm Φy | E]] | ? ? ? ?];
      cbn [ge_read entry_unit] in HU; try discriminate.
    - (* a stored submodule is closed *)
      destruct HcE as (-> & _ & _); injection HU as <-; contradiction.
    - injection HU as <-; exact (src_child_alias_at _ _ _ _ _ _ _ _ _ Hl Hp eq_refl HΓs HΓ).
    - (* a definition with a module part has an alias as its unit *)
      destruct HcE0 as (_ & Δ0 & E0 & HU0 & _); discriminate.
    - injection HU as <-; exact (src_child_alias_at _ _ _ _ _ _ _ _ _ Hl Hp eq_refl HΓs HΓ).
  Qed.

  (** An entry of a deep closed description of the source read
      ([reader_closed]), the entry's own description deep: a definition is
      no module; a stored submodule, an inductive type's module and a record
      type's are stored over the module's telescope extended, given the
      module's arguments ([glu_args_deep_ext]); an alias, and a definition
      with a module part, are over the telescope extended, given the
      arguments ([glu_desc_deep_ats_alias]). *)
  Lemma glu_desc_deep_read_closed : forall Γ Θ' p T Φ Ns y Φ0 E0 R R',
      desc_ok Θs Ξs Γ (mdesc_closed Θ' p T Φ Ns) -> loc Θs Ξs p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) ->
      edenote Θs Ξs Γ (Some (qname_in p y)) (ge_read T E0) R ->
      glu_desc_deep Γ R -> glu_desc_deep Γ (mdesc_closed Θ' p T Φ Ns) ->
      mdesc_read (reader_closed Θ' Ns (apps (a_mem (qname_mod p) y) Ns)) R = Some R' ->
      glu_desc_deep Γ R'.
  Proof.
    intros * Hok Hl Hp Hed HR HP Hr.
    inversion Hok as [| | ? ? ? ? ? Θ1 Ξ1 ? lΘ Hg1 Hs1 Hl1 HaT HsT HT HΘ' Hargs HaΘ HRΘ HLΘ HFΘ |]; subst.
    pose proof (args_ok_length _ _ _ _ _ Hargs) as Hle.
    destruct HP as [HΘ HNs].
    pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΘ) as HΘΓ.
    cbn [mdesc_read] in Hr; destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
    pose proof (proj2 (loc_closed _ _ Hgs _ _ _ Hl)) as HcΦ.
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn [body_closed] in HcE; destruct HcE as [_ HcE].
    pose proof (gm_coherent_prefix _ _ _ _ _ (loc_coherent _ _ Hgs _ _ _ Hl) Hp) as HcE0.
    assert (HS : slots_ok 0 Γ) by (intros ? ? Hx; lia).
    pose proof (proj1 (proj2 (proj2 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hgs))))) as Hsc.
    (** A stored module of the telescope extended, given the arguments *)
    assert (Hbody : forall pc Δ0 Φc, mdesc_mod R = Some (mdesc_closed nil pc (Δ0 ++ T) Φc nil) ->
                    glu_desc_deep Γ (mdesc_up Θ' (mdesc_named Θ' Ns (apps (a_mem (qname_mod p) y) Ns) R1))).
    { intros * Hm; apply (glu_desc_deep_read_closed_gen _ _ _ _ _ _ _ HΘ Hm Ha).
      intros Rm1 Ha1; rewrite mdesc_ats_closed_nil in Ha1; injection Ha1 as <-.
      split; [ exact HΘΓ | exact (glu_args_deep_ext _ _ _ _ HNs Hle) ]. }
    destruct E0 as [b pv r A oM | pv [Δ [sm Φy | E]] | pv pq k D ΦD | pv A M [Δ [sm Φy | E]] | pv pr Rr ΦR];
      cbn [ge_read] in Hed.
    - (* a definition: no module *)
      inversion Hed; subst; apply glu_desc_deep_no_mod.
      cbn [mdesc_ats_read] in Ha; destruct (mdesc_ats_term _ _ _ _ _ Ha) as (A' & om' & ->).
      exact (mdesc_mod_named_term _ _ _ _ _ _ _).
    - (* a stored submodule *)
      destruct HcE as (-> & _ & _).
      inversion Hed as [| ? ? ? ? ? Hu | | |]; subst.
      inversion Hu as [? ? ? ? ? ? ? Hx Hb |]; subst.
      cbn in Hb; injection Hb as <-.
      exact (Hbody _ _ _ eq_refl).
    - (* an alias *)
      destruct HcE0 as (Δ0 & -> & Ha0).
      pose proof (Hsc _ _ _ _ Hed 0 HS (or_introl HcE)) as Hs.
      inversion Hed as [| ? ? ? ? ? Hu | | |]; subst.
      inversion Hu as [| ? ? ? ? R0 R0m Hm0 Hmd]; subst.
      pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgs Hm0) Hmd) as Hc.
      destruct (src_child_alias_at _ _ _ _ _ _ _ _ _ Hl Hp eq_refl HΘ' HΘΓ) as [_ HUd]; cbn [glu_unit_deep] in HUd.
      apply (glu_desc_deep_read_closed_gen _ _ _ _ _ _ (mdesc_up (Δ0 ++ T) R0m) HΘ
               ltac:(rewrite mdesc_mod_up, (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ Hmd)); reflexivity) Ha).
      intros Rm1 Ha1.
      exact (glu_desc_deep_ats_alias _ _ Hgs _ _ _ _ _ _ _ HΘ (glu_alias_deep_parts_params _ _ _ _ HUd) Ha0 HaT Hle Hc Hs HR
               HNs Ha1).
    - (* an inductive type's module, stored at the type's path over the
         uniform parameters *)
      inversion Hed as [| | ? ? ? ? ? ? ? Mk pm Tm Φm HMk Hpm Hlm | |]; subst.
      pose proof (proj2 (loc_entry _ _ Hgs _ _ _ Hl _ _) Hent) as HeΘ.
      destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeΘ) as [_ Hml].
      pose proof (ind_selfpath_path _ _ _ _ (ind_mlookup_selfpath _ _ Hgs _ _ _ _ Hml)) as Hmp.
      rewrite Hmp in Hpm; injection Hpm as <-.
      pose proof (loc_child_ind _ _ Hgs _ _ _ _ _ _ _ _ _ Hl Hent) as Hbm.
      rewrite (gc_loc_of_loc _ _ Hgs _ _ _ (or_intror Hbm)) in Hlm; injection Hlm as <- <-.
      destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
      apply (Hbody (qname_in p y) Δ0 ΦD); unfold ind_former_desc; cbn [mdesc_mod]; rewrite HΔ0; reflexivity.
    - (* a definition with a module part has an alias as its unit *)
      destruct HcE0 as (_ & ? & ? & [=] & _).
    - (* a definition with a module part: its module part, an alias *)
      destruct HcE0 as (_ & Δ0 & E' & [= -> <-] & Ha0).
      pose proof (Hsc _ _ _ _ Hed 0 HS HcE) as Hs.
      inversion Hed as [| | | ? ? ? ? ? ? ? Rm Hu |]; subst.
      inversion Hu as [| ? ? ? ? R0 R0m Hm0 Hmd]; subst.
      pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgs Hm0) Hmd) as Hc.
      destruct (src_child_alias_at _ _ _ _ _ _ _ _ _ Hl Hp eq_refl HΘ' HΘΓ) as [_ HUd]; cbn [glu_unit_deep] in HUd.
      apply (glu_desc_deep_read_closed_gen _ _ _ _ (mdesc_dm nil A M (mdesc_up (Δ0 ++ T) R0m)) _ (mdesc_up (Δ0 ++ T) R0m) HΘ
               ltac:(cbn [mdesc_mod]; rewrite mdesc_mod_up, (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ Hmd)); reflexivity) Ha).
      intros Rm1 Ha1.
      exact (glu_desc_deep_ats_alias _ _ Hgs _ _ _ _ _ _ _ HΘ (glu_alias_deep_parts_params _ _ _ _ HUd) Ha0 HaT Hle Hc
               (proj2 (proj2 Hs)) HR HNs Ha1).
    - (* a record type's module, stored at the type's path over its module
         telescope *)
      inversion Hed as [| | | | ? ? ? ? ? ? Tm Φm Hlm]; subst.
      pose proof (loc_child_record _ _ Hgs _ _ _ _ _ _ _ _ Hl Hent) as Hbm.
      rewrite (gc_loc_of_loc _ _ Hgs _ _ _ (or_intror Hbm)) in Hlm; injection Hlm as <- <-.
      destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
      apply (Hbody (qname_in p y) (ce_ass (sort_exp_kind (record_sort Rr)) (record_self pr Rr) :: Δ0) ΦR).
      unfold record_former_desc, record_mod_tele; cbn [mdesc_mod]; rewrite HΔ0; reflexivity.
  Qed.

  (** What a module expression of the source denotes is deep when its parts
      are, at a context glued with its types whose module parts are deep, by
      induction on how it is denoted: a unit's description when the unit,
      open or an alias, is typed and deep, and an entry's when its unit
      is. *)
  Theorem glu_desc_deep_of_source_all :
    (forall Γ E R, mdenote Θs Ξs Γ E R -> Θs ⍮ Ξs ⍮ Γ ⊢ᵐ E ≈ E -> glu_rel_ctx_types Γ -> glu_ctx_deep Γ ->
       glu_modexp_parts_deep Γ E -> glu_desc_deep Γ R) /\
    (forall Γ o U R, udenote Θs Ξs Γ o U R -> glu_rel_ctx_types Γ -> glu_ctx_deep Γ ->
       (unit_oa U -> unit_full Θs Ξs Γ U /\ glu_unit_deep Γ U) -> glu_desc_deep Γ R) /\
    (forall Γ o E R, edenote Θs Ξs Γ o E R -> glu_rel_ctx_types Γ -> glu_ctx_deep Γ ->
       (forall U, entry_unit E = Some U -> unit_oa U -> unit_full Θs Ξs Γ U /\ glu_unit_deep Γ U) -> glu_desc_deep Γ R) /\
    (forall Γ Φ Φx, body_xp Θs Ξs Γ Φ Φx -> True) /\
    (forall Γ H its gs, items_gen Θs Ξs Γ H its gs -> True).
  Proof.
    pose proof (gctx_embedding_resolution _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hsub.
    apply mdenote_all_ind; intros; try exact I.
    (** A stored module at no argument, and a type former of one *)
    all: try solve [ try unfold ind_former_desc; try unfold record_former_desc;
                     lazymatch goal with |- glu_desc_deep _ (mdesc_dm _ _ _ _) => apply glu_desc_deep_dm_intro | _ => idtac end;
                     apply glu_desc_deep_closed_nil; assumption ].
    - (* a slot: its unit, deep as the context's module parts are *)
      match goal with Hl : _ ∋ # _ ≔ₘ _, HH : _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _, HΓ : glu_rel_ctx_types _, Hd : glu_ctx_deep _,
                      IH : glu_rel_ctx_types _ -> _ |- _ =>
        apply (IH HΓ Hd); intros _;
        exact (conj (proj1 (unit_full_of_eq _ _ _ _ _ (ctx_lookup_mod_wf _ _ _ _ _ (presup_modexp_eq_ctx HH) Hl)))
                    (glu_ctx_deep_lookup _ _ _ Hl HΓ Hd)) end.
    - (* a literal: its unit, a part *)
      match goal with HH : _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _, HΓ : glu_rel_ctx_types _, Hd : glu_ctx_deep _,
                      Hp : glu_modexp_parts_deep _ (me_lit _), IH : glu_rel_ctx_types _ -> _ |- _ =>
        apply (IH HΓ Hd); intros _; exact (conj (proj1 (modexp_gen _ _ _ _ _ HH)) Hp) end.
    - (* an application: the head's description given the argument, glued
         at its parameter as the argument's part says *)
      rename H1 into HHN, H2 into HΓ, H3 into Hd, H4 into Hp, H0 into IH, m into Hm, e into Ha.
      destruct (proj1 (modexp_gen _ _ _ _ _ HHN)) as (HH & R0 & T & B & T1 & Srt & HmR0 & HT & Hv & HB & HSrt & HN).
      rewrite (proj1 (mdenote_functional_all _ _ Hgs) _ _ _ HmR0 _ Hm) in HT.
      destruct Hp as [HpH Harg].
      destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ Hm) as (Rt & HmRt & Hgr).
      pose proof (glu_app_arg_deep_arg _ _ _ Harg _ _ _ _ HmRt (mdesc_grows_mtele _ _ _ _ _ _ _ Hgr HT) Hv) as HNg.
      exact (glu_desc_deep_at _ _ Hgs _ _ _ _ _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) (IH HH HΓ Hd HpH) HT Hv HNg Ha).
    - (* a selection: the selected module's description deep, its entry
         read in it *)
      rename H0 into IH, H1 into IHe, H2 into HHy, H3 into HΓ, H4 into Hd, H5 into Hp, m into Hm, e into Hmd, e0 into He,
        e1 into Hed, e2 into Hr.
      pose proof (proj1 (modexp_gen _ _ _ _ _ HHy)) as HH; cbn [gen_m] in HH.
      pose proof (proj1 (glu_desc_deep_mod _ _ _ Hmd) (IH HH HΓ Hd Hp)) as HR0m.
      pose proof (desc_ok_mod _ _ Hgs _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd) as Hok.
      pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgs Hm) Hmd) as Hc.
      pose proof (wf_mdenote_mod_xp _ _ _ _ _ _ _ HH Hm Hmd) as Hxp.
      pose proof (mdesc_mod_is_mod _ _ Hmd) as Him.
      destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in Him; try contradiction.
      + (* an open module: its entry, deep at the entries before it
           ([glu_ctx_deep_body]), read there *)
        cbn [mdesc_xp] in Hxp; pose proof (body_xp_expand _ _ _ _ _ Hxp) as ->.
        cbn [mdesc_entry] in He.
        destruct (gm_prefix_upto (gm_expand Φw) y) as [[| Φ' x E' | ? ? ?] |] eqn:Hpe; try discriminate.
        destruct (gm_prefix_entry _ _ _ Hpe) as (? & ? & [= <- -> <-] & _).
        assert (HE' : E = E' /\ Γy = body_ctx Φ' ++ Δ /\ rd = reader_open Δ Φ')
          by (destruct E' as [[|] pv ra A [M |] | pv U | | pv A M U | ]; try discriminate; injection He as <- <- <-; auto).
        destruct HE' as (-> & -> & ->); clear He.
        cbn [mdesc_read] in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
        inversion Hok as [| ? ? ? ? lΔ HΦ Hn Hent HaΔ Hsh Hnd HUw HRΔ Htg HLΔ | |]; subst.
        pose proof (gm_noopen_prefix_upto _ _ _ (gm_noopen_expand Φw) Hpe) as Hn'; cbn [gm_noopen] in Hn'.
        destruct (glu_unit_deep_prefix_open _ _ _ _ _ _ HR0m Hpe) as [HΦ' HΦ'u].
        pose proof (glu_rel_ext_under_sub_ctx_types _ _ HΦ') as HΦΓ.
        pose proof (glu_ctx_deep_body _ _ Hn' (glu_rel_ext_under_sub_app_split _ _ _ HΦ') HΦ'u
                      (glu_ctx_deep_app_ass _ _ HaΔ Hd)) as HΦd.
        rewrite <- app_assoc in IHe, Hed, HΦΓ.
        assert (HcR : mdesc_canonical Θs Ξs R)
          by (exact ((proj1 (proj2 (proj2 (mdenote_canon_all _ _ Hgs)))) _ _ _ _ Hed (fun _ _ _ _ Ho _ => ltac:(discriminate Ho)))).
        refine (glu_desc_deep_read_open _ _ Hgs _ _ _ _ _ _ _ _ HR0m Hpe Hf HcR (IHe HΦΓ HΦd _)).
        (** The entry's unit, typed as the expanded body extends a
            well-formed context, deep as the body's units are *)
        intros U HU _; split; [| exact (glu_unit_deep_entry_open _ _ _ _ _ _ _ HR0m Hpe HU) ].
        destruct (gm_prefix_body_ctx _ _ _ (gm_noopen_expand Φw) Hpe) as (Ψ & EΨ).
        rewrite EΨ, <- app_assoc in HΦ; pose proof (ctx_app_wf_tail _ _ _ _ HΦ) as HΦ1.
        destruct E' as [? ? ? ? ? | ? U0 | ? ? ? ? ? | ? ? ? U0 | ? ? ? ?]; cbn [entry_unit] in HU; try discriminate;
          injection HU as <-; cbn [body_ctx app] in HΦ1.
        * exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (ctx_decomp_mod HΦ1)))).
        * exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (proj2 (proj2 (ctx_decomp_dm HΦ1)))))).
      + (* a stored module: its entry, stored at the source *)
        cbn [mdesc_entry] in He.
        destruct (gm_prefix_upto Φ y) as [[| Φ0 x E0 | ? ? ?] |] eqn:Hpe; try discriminate.
        injection He as <- <- <-.
        destruct (gm_prefix_entry _ _ _ Hpe) as (? & ? & [= <- -> <-] & _).
        cbn [mdesc_entry_path app] in Hed, IHe.
        cbn in Hc.
        pose proof (presup_modexp_eq_ctx HHy) as HΓs.
        exact (glu_desc_deep_read_closed _ _ _ _ _ _ _ _ _ _ _ Hok Hc Hpe Hed
                 (IHe HΓ Hd (src_child_entry_at _ _ _ _ _ _ _ Hc Hpe HΓs HΓ)) HR0m Hr).
    - (* a body: an open one is the unit, a closed one stored *)
      rename H0 into HΓ, H2 into HU, e into Hb.
      destruct sm; cbn in Hb.
      + injection Hb as <-; exact (proj2 (HU I)).
      + destruct o; cbn in Hb; [ injection Hb as <-; exact (glu_desc_deep_closed_nil _ _ _ _ HΓ) | discriminate ].
    - (* an alias: what its target denotes, abstracted *)
      rename H0 into HΓ, H1 into Hd, H2 into HU, H into IH, e into Hmd.
      destruct (HU I) as [Hf HUd]; cbn [unit_full] in Hf; cbn [glu_unit_deep] in HUd; destruct HUd as [HΔ HE HEp].
      apply (glu_desc_deep_up _ _ _ HΔ).
      apply (proj1 (glu_desc_deep_mod _ _ _ Hmd)).
      exact (IH (unit_alias_target _ _ _ _ _ Hf) (glu_rel_ext_under_sub_ctx_types _ _ HΔ)
                (glu_ctx_deep_app_ass _ _ (unit_alias_ass _ _ _ _ _ Hf) Hd) HEp).
    - (* a module entry: its unit *)
      rename H0 into HΓ, H1 into Hd, H2 into HU, H into IH.
      exact (IH HΓ Hd (HU _ eq_refl)).
    - (* a definition with a module part: its module part *)
      rename H0 into HΓ, H1 into Hd, H2 into HU, H into IH.
      exact (IH HΓ Hd (HU _ eq_refl)).
  Qed.

  (** What a module expression typed at the source denotes is deep when
      the expression's parts are. *)
  Lemma glu_desc_deep_of_source : forall Γ E R, mdenote Θs Ξs Γ E R ->
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ E ≈ E -> glu_rel_ctx_types Γ -> glu_ctx_deep Γ -> glu_modexp_parts_deep Γ E ->
      glu_desc_deep Γ R.
  Proof. exact (proj1 glu_desc_deep_of_source_all). Qed.

End FromSource.
