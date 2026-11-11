(** * The Unit Equations in the Gluing Model

    A unit equation glues its context and both its units at the instances
    ([glu_unit_eq]).  A unit is glued at a context ([glu_unit_at]) when its
    expansions' contexts, extensions of the context, are glued at every
    renaming of it, and so are its module entries' units, at the contexts
    before them.  At an instance of the context, both follow from the
    extension rules' gluing ([glu_rel_ext_under_sub]): the instance moved by
    a renaming is an instance, lifted through the body's context it is one
    of the extended context, whose domain is the body's context moved; and
    each module entry is glued at the instances of the context before
    it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Soundness Require Import LogicalRelation Instances Extensions.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** The context of a grafted body without opens: the grafted entries over
    the base's. *)
Lemma body_ctx_graft : forall B A, gm_noopen B -> body_ctx (gm_graft A B) = body_ctx B ++ body_ctx A.
Proof.
  induction B as [| B IH x E | B IH H its Bg _]; intros A Hn; cbn in *; [ reflexivity | | contradiction ].
  destruct E as [? ? ? ? [] | | | | ]; cbn; rewrite IH by exact Hn; reflexivity.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A suffix of a glued extension is glued. *)
Lemma glu_rel_ext_under_sub_app_inv : forall {Γ Ψ2} Ψ1,
    glu_rel_ext_under_sub Γ (Ψ1 ++ Ψ2) ->
    glu_rel_ext_under_sub Γ Ψ2.
Proof. induction Ψ1 as [| e Ψ1 IH]; cbn; [ intros; assumption | intros [H _]; exact (IH H) ]. Qed.

(** An extension glued at the instances, moved by an instance of its base:
    glued at every renaming of the instance's domain, by the instance moved
    by the renaming, lifted. *)
Lemma glu_rel_ext_under_renaming_of_inst : forall {Γ Ψ Γ' τ},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_sub_inst Γ' τ Γ ->
    glu_rel_ext_under_renaming Γ' (tele_sub Ψ τ).
Proof.
  intros * HΨ Hτ Γ'' φ Hφ HΓ''.
  rewrite tele_wk_sub.
  exact (glu_rel_sub_inst_ctx _ _ _ (glu_rel_ext_under_sub_inst HΨ _ _ (glu_rel_sub_inst_wk Hτ Hφ HΓ''))).
Qed.

(** Extensions glued at every renaming compose, the inner one over a well
    formed context. *)
Lemma glu_rel_ext_under_renaming_app : forall {Γ Δ Ψ},
    ⊢ Δ ++ Γ ->
    glu_rel_ext_under_renaming Γ Δ ->
    glu_rel_ext_under_renaming (Δ ++ Γ) Ψ ->
    glu_rel_ext_under_renaming Γ (Ψ ++ Δ).
Proof.
  intros * HwΔ HΔ HΨ Γ'' φ Hφ HΓ''.
  pose proof (HΔ _ _ Hφ HΓ'') as HΔ'.
  assert (HwΔ' : ⊢ tele_wk Δ φ ++ Γ'') by (destruct HΔ' as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  rewrite tele_wk_app, <- app_assoc.
  apply HΨ; [ apply wf_wk_ext; assumption | exact HΔ' ].
Qed.

(** The context of a body's expansion, moved by a substitution, is the
    expansion's context moved. *)
Lemma body_ctx_expand_sub : forall Φ σ, body_ctx (gm_expand (gmod_sub Φ σ)) = tele_sub (body_ctx (gm_expand Φ)) σ.
Proof. intros; rewrite gm_expand_sub; apply body_ctx_sub, gm_noopen_nopens, gm_noopen_expand. Qed.

(** An expansion binds as many entries as its context has. *)
Lemma length_body_ctx_expand : forall Φ, List.length (body_ctx (gm_expand Φ)) = gm_binders Φ.
Proof. intros; rewrite length_body_ctx, gm_binders_expand; [ reflexivity | apply gm_noopen_nopens, gm_noopen_expand ]. Qed.

(** The module entries of a body over the extension [Δ] of [Γ], moved by
    an instance of [Γ] lifted through [Δ], the expansion's context over
    [Δ] glued at the instances: each module entry's unit is glued at the
    instances of the context before it, here at the instance lifted through
    the entries before it.  The fragment of an open is a body over the
    entries before the open. *)
Lemma glu_gmod_units_inst : forall Φ Γ Δ,
    glu_rel_ext_under_sub Γ (body_ctx (gm_expand Φ) ++ Δ) ->
    forall Γ' τ, glu_rel_sub_inst Γ' τ Γ ->
    glu_gmod_units (tele_sub Δ τ ++ Γ') (gmod_sub Φ (sb_qn (List.length Δ) τ)).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg IHg]; intros Γ Δ HΦ Γ' τ Hτ; cbn [gmod_sub glu_gmod_units]; [ exact I | |].
  - (** The unit of an entry, at the instance lifted through the entries
        before it *)
    assert (Hat : forall U, glu_rel_ext_under_sub Γ (body_ctx (gm_expand Φ) ++ Δ) ->
              glu_rel_unit_under_sub ((body_ctx (gm_expand Φ) ++ Δ) ++ Γ) U ->
              glu_unit_at (body_ctx (gm_expand (gmod_sub Φ (sb_qn (List.length Δ) τ))) ++ tele_sub Δ τ ++ Γ')
                U[sb_qn (gm_binders Φ) (sb_qn (List.length Δ) τ)]ᵘ).
    { intros U HΦ0 HU.
      pose proof (HU _ _ (glu_rel_ext_under_sub_inst HΦ0 _ _ Hτ)) as HUτ.
      rewrite tele_sub_app, <- app_assoc, List.length_app, length_body_ctx_expand in HUτ.
      rewrite body_ctx_expand_sub, (gunit_sub_sb_eq _ _ _ (sb_qn_add _ _ _)); exact HUτ. }
    cbn [gm_expand] in HΦ.
    destruct E as [b pv κ A [M |] | pv U | pv pq k D ΦD | pv A M U | pv p R ΦR];
      cbn [body_ctx gentry_sub glu_gmod_units app glu_rel_ext_under_sub] in HΦ |- *.
    + destruct HΦ as [HΦ _]; exact (IH _ _ HΦ _ _ Hτ).
    + destruct HΦ as [HΦ _]; exact (IH _ _ HΦ _ _ Hτ).
    + destruct HΦ as [HΦ [_ HU]]; split; [ exact (IH _ _ HΦ _ _ Hτ) | exact (Hat _ HΦ HU) ].
    + destruct HΦ as [HΦ _]; exact (IH _ _ HΦ _ _ Hτ).
    + destruct HΦ as [HΦ (? & ? & [? ? ? ? HU])]; split; [ exact (IH _ _ HΦ _ _ Hτ) | exact (Hat _ HΦ HU) ].
    + destruct HΦ as [HΦ _]; exact (IH _ _ HΦ _ _ Hτ).
  - (** An open: the entries before it, and its fragment over them *)
    cbn [gm_expand] in HΦ.
    rewrite body_ctx_graft, <- app_assoc in HΦ by apply gm_noopen_expand.
    split; [ exact (IH _ _ (glu_rel_ext_under_sub_app_inv _ HΦ) _ _ Hτ) |].
    pose proof (IHg _ _ HΦ _ _ Hτ) as Hg.
    rewrite tele_sub_app, <- app_assoc, List.length_app, length_body_ctx_expand in Hg.
    rewrite body_ctx_expand_sub, (gmod_sub_sb_eq _ _ _ (sb_qn_add _ _ _)); exact Hg.
Qed.

(** A body unit moved by an instance, the expansion's context over the
    parameters glued at the instances: its expansion's context is the
    extension moved, glued at every renaming, and its module entries are
    glued. *)
Lemma glu_unit_at_body_inst : forall Γ Δ sm Φ,
    glu_rel_ext_under_sub Γ (body_ctx (gm_expand Φ) ++ Δ) ->
    forall Γ' τ, glu_rel_sub_inst Γ' τ Γ -> glu_unit_at Γ' (gu_mk Δ (md_body sm Φ))[τ]ᵘ.
Proof.
  intros * HΦ Γ' τ Hτ; rewrite gunit_sub_mk; cbn [moddef_sub glu_unit_at]; split.
  - rewrite body_ctx_expand_sub, <- tele_sub_app; exact (glu_rel_ext_under_renaming_of_inst HΦ Hτ).
  - exact (glu_gmod_units_inst Φ Γ Δ HΦ Γ' τ Hτ).
Qed.

(** An alias moved by an instance, its parameters and its target over
    them glued at the instances: the target at the instance lifted through
    the parameters. *)
Lemma glu_unit_at_alias_inst : forall Γ Δ E,
    glu_rel_ext_under_sub Γ Δ ->
    glu_rel_modexp_under_sub (Δ ++ Γ) E ->
    forall Γ' τ, glu_rel_sub_inst Γ' τ Γ -> glu_unit_at Γ' (gu_mk Δ (md_alias E))[τ]ᵘ.
Proof.
  intros * HΔ HE Γ' τ Hτ; rewrite gunit_sub_mk; cbn [moddef_sub glu_unit_at]; split.
  - exact (glu_rel_ext_under_renaming_of_inst HΔ Hτ).
  - exact (glu_rel_modexp_under_sub_inst _ _ HE _ _ (glu_rel_ext_under_sub_inst HΔ _ _ Hτ)).
Qed.

(** A unit over the extension [Δ0] of [Γ], glued there, with [Δ0] glued at
    every renaming of [Γ]: the unit over both telescopes is glued at
    [Γ]. *)
Lemma glu_unit_at_flatten : forall Γ Δ0 Δ1 D,
    ⊢ Δ0 ++ Γ ->
    glu_rel_ext_under_renaming Γ Δ0 ->
    glu_unit_at (Δ0 ++ Γ) (gu_mk Δ1 D) ->
    glu_unit_at Γ (gu_mk (Δ1 ++ Δ0) D).
Proof.
  intros * Hw HΔ0; destruct D as [sm Φ | E]; cbn [glu_unit_at].
  - intros [H1 H2]; split.
    + rewrite app_assoc; exact (glu_rel_ext_under_renaming_app Hw HΔ0 H1).
    + rewrite <- app_assoc; exact H2.
  - intros [H1 H2]; split; [ exact (glu_rel_ext_under_renaming_app Hw HΔ0 H1) | rewrite <- app_assoc; exact H2 ].
Qed.

End Fixed_GCtx.

(** Expanding a grafted body is grafting the expansions. *)
Lemma gm_expand_graft : forall B A, gm_expand (gm_graft A B) = gm_graft (gm_expand A) (gm_expand B).
Proof.
  induction B as [| B IH x E | B IH H its Bg _]; intros A; cbn [gm_graft gm_expand];
    [ reflexivity | rewrite IH; reflexivity | rewrite IH, gm_graft_assoc; reflexivity ].
Qed.

Section Fixed_GCtx_Expansions.
  Context {GC : GCtx}.

(** The module entries of a body grafted on another: those of the base,
    and those of the fragment over the base's expansion. *)
Lemma glu_gmod_units_graft : forall B A Γ,
    glu_gmod_units Γ A ->
    glu_gmod_units (body_ctx (gm_expand A) ++ Γ) B ->
    glu_gmod_units Γ (gm_graft A B).
Proof.
  assert (E : forall A B, body_ctx (gm_expand (gm_graft A B)) = body_ctx (gm_expand B) ++ body_ctx (gm_expand A))
    by (intros; rewrite gm_expand_graft; apply body_ctx_graft, gm_noopen_expand).
  induction B as [| B IH x En | B IH H its Bg _]; intros A Γ HA HB; cbn [gm_graft]; [ exact HA | |].
  - destruct En as [b pv κ T oM | pv U | pv pq k D ΦD | pv T M U | pv p R ΦR]; cbn [glu_gmod_units] in HB |- *;
      try exact (IH _ _ HA HB).
    + destruct HB as [HB HU]; split; [ exact (IH _ _ HA HB) | rewrite E, <- app_assoc; exact HU ].
    + destruct HB as [HB HU]; split; [ exact (IH _ _ HA HB) | rewrite E, <- app_assoc; exact HU ].
  - cbn [glu_gmod_units] in HB |- *; destruct HB as [HB HBg].
    split; [ exact (IH _ _ HA HB) | rewrite E, <- app_assoc; exact HBg ].
Qed.

(** The module entries of a body's expansion: those of the body, and those
    of the fragments its opens store, grafted. *)
Lemma glu_gmod_units_expand : forall Φ Γ, glu_gmod_units Γ Φ -> glu_gmod_units Γ (gm_expand Φ).
Proof.
  pose proof (fun Φ => gm_expand_noopen _ (gm_noopen_expand Φ)) as Eidem.
  induction Φ as [| Φ IH x En | Φ IH H its Φg IHg]; intros Γ HΦ; cbn [gm_expand]; [ exact HΦ | |].
  - destruct En as [b pv κ T oM | pv U | pv pq k D ΦD | pv T M U | pv p R ΦR]; cbn [glu_gmod_units] in HΦ |- *;
      try exact (IH _ HΦ).
    + destruct HΦ as [HΦ HU]; split; [ exact (IH _ HΦ) | rewrite Eidem; exact HU ].
    + destruct HΦ as [HΦ HU]; split; [ exact (IH _ HΦ) | rewrite Eidem; exact HU ].
  - cbn [glu_gmod_units] in HΦ; destruct HΦ as [HΦ HΦg].
    apply glu_gmod_units_graft; [ exact (IH _ HΦ) | rewrite Eidem; exact (IHg _ HΦg) ].
Qed.

(** *** Deep units ([glu_unit_deep]) *)

(** An extension glued at the instances extends its context to one glued
    with its types. *)
Lemma glu_rel_ext_under_sub_ctx_types : forall Γ Ψ, glu_rel_ext_under_sub Γ Ψ -> glu_rel_ctx_types (Ψ ++ Γ).
Proof.
  intros Γ; induction Ψ as [| e Ψ IH]; cbn [glu_rel_ext_under_sub app]; [ intros H; exact H |].
  intros [HΨ He]; pose proof (IH HΨ) as HΨΓ.
  destruct e as [κ A | A M | U | A M U]; cbn [glu_rel_entry_under_sub] in He.
  - destruct He as (S & HS & HA); exact (glu_rel_ctx_types_extend HA HS).
  - destruct He as (S & [HS HA HM]); exact (glu_rel_ctx_types_extend_def HA HS HM).
  - destruct He as [HU HUg]; exact (glu_rel_ctx_types_extend_mod HΨΓ HU HUg).
  - destruct He as (i & E & [-> HA HM HU HUg]); exact (glu_rel_ctx_types_extend_dm HA HM HU HUg).
Qed.

(** A glued extension split: its outer part is an extension of the context
    its inner part extends. *)
Lemma glu_rel_ext_under_sub_app_split : forall Γ Ψ2 Ψ1,
    glu_rel_ext_under_sub Γ (Ψ1 ++ Ψ2) -> glu_rel_ext_under_sub (Ψ2 ++ Γ) Ψ1.
Proof.
  intros Γ Ψ2; induction Ψ1 as [| e Ψ1 IH]; cbn [app glu_rel_ext_under_sub].
  - intros H; exact (glu_rel_ext_under_sub_ctx_types _ _ H).
  - intros [H He]; split; [ exact (IH H) | rewrite app_assoc; exact He ].
Qed.

(** Glued extensions compose: [glu_rel_ext_under_sub_app_split] inverted. *)
Lemma glu_rel_ext_under_sub_app_join : forall Γ Ψ2 Ψ1,
    glu_rel_ext_under_sub Γ Ψ2 -> glu_rel_ext_under_sub (Ψ2 ++ Γ) Ψ1 -> glu_rel_ext_under_sub Γ (Ψ1 ++ Ψ2).
Proof.
  intros Γ Ψ2; induction Ψ1 as [| e Ψ1 IH]; cbn [app glu_rel_ext_under_sub]; intros H2.
  - intros _; exact H2.
  - intros [H1 He]; split; [ exact (IH H2 H1) | rewrite <- app_assoc; exact He ].
Qed.

(** A deep unit over an extension [Δ] of [Γ], abstracted over [Δ]: deep
    over [Γ], [Δ] its outer parameters. *)
Lemma glu_unit_deep_params_join : forall Γ Δ Δy D,
    glu_rel_ext_under_sub Γ Δ -> glu_unit_deep (Δ ++ Γ) (gu_mk Δy D) -> glu_unit_deep Γ (gu_mk (Δy ++ Δ) D).
Proof.
  intros * HΔ HU; destruct D as [sm Φ | E]; cbn [glu_unit_deep] in HU |- *.
  - destruct HU as [HΦ HΦu]; rewrite <- app_assoc.
    split; [ rewrite app_assoc; exact (glu_rel_ext_under_sub_app_join _ _ _ HΔ HΦ) | exact HΦu ].
  - destruct HU as [HΔy HE Hl]; rewrite <- app_assoc.
    constructor; [ exact (glu_rel_ext_under_sub_app_join _ _ _ HΔ HΔy) | rewrite <- app_assoc; exact HE | exact Hl ].
Qed.

(** The deep module entries of a body grafted on another, as
    [glu_gmod_units_graft]. *)
Lemma glu_gmod_units_deep_graft : forall B A Γ,
    glu_gmod_units_deep Γ A ->
    glu_gmod_units_deep (body_ctx (gm_expand A) ++ Γ) B ->
    glu_gmod_units_deep Γ (gm_graft A B).
Proof.
  assert (E : forall A B, body_ctx (gm_expand (gm_graft A B)) = body_ctx (gm_expand B) ++ body_ctx (gm_expand A))
    by (intros; rewrite gm_expand_graft; apply body_ctx_graft, gm_noopen_expand).
  induction B as [| B IH x En | B IH H its Bg _]; intros A Γ HA HB; cbn [gm_graft]; [ exact HA | |].
  - destruct En as [b pv κ T oM | pv U | pv pq k D ΦD | pv T M U | pv p R ΦR]; cbn [glu_gmod_units_deep] in HB |- *;
      try exact (IH _ _ HA HB).
    + destruct HB as [HB HU]; split; [ exact (IH _ _ HA HB) | rewrite E, <- app_assoc; exact HU ].
    + destruct HB as [HB HU]; split; [ exact (IH _ _ HA HB) | rewrite E, <- app_assoc; exact HU ].
  - cbn [glu_gmod_units_deep] in HB |- *; destruct HB as [HB HBg].
    split; [ exact (IH _ _ HA HB) | rewrite E, <- app_assoc; exact HBg ].
Qed.

(** The deep module entries of a body's expansion, as
    [glu_gmod_units_expand]. *)
Lemma glu_gmod_units_deep_expand : forall Φ Γ, glu_gmod_units_deep Γ Φ -> glu_gmod_units_deep Γ (gm_expand Φ).
Proof.
  pose proof (fun Φ => gm_expand_noopen _ (gm_noopen_expand Φ)) as Eidem.
  induction Φ as [| Φ IH x En | Φ IH H its Φg IHg]; intros Γ HΦ; cbn [gm_expand]; [ exact HΦ | |].
  - destruct En as [b pv κ T oM | pv U | pv pq k D ΦD | pv T M U | pv p R ΦR]; cbn [glu_gmod_units_deep] in HΦ |- *;
      try exact (IH _ HΦ).
    + destruct HΦ as [HΦ HU]; split; [ exact (IH _ HΦ) | rewrite Eidem; exact HU ].
    + destruct HΦ as [HΦ HU]; split; [ exact (IH _ HΦ) | rewrite Eidem; exact HU ].
  - cbn [glu_gmod_units_deep] in HΦ; destruct HΦ as [HΦ HΦg].
    apply glu_gmod_units_deep_graft; [ exact (IH _ HΦ) | rewrite Eidem; exact (IHg _ HΦg) ].
Qed.

(** The module entries of a body are deep when the module parts of its
    expansion's context over [Γ] are: each is the module part of the
    entry in that context. *)
Lemma glu_gmod_units_deep_of_ctx : forall Φ Γ, glu_ctx_deep (body_ctx (gm_expand Φ) ++ Γ) -> glu_gmod_units_deep Γ Φ.
Proof.
  induction Φ as [| Φ IH x En | Φ IH H its Φg IHg]; intros Γ HΦ; cbn [glu_gmod_units_deep]; [ exact I | |].
  - cbn [gm_expand] in HΦ.
    assert (HΦ0 : glu_ctx_deep (body_ctx (gm_expand Φ) ++ Γ))
      by (destruct En as [? ? ? ? [] | | | | ]; cbn [body_ctx app] in HΦ; exact (glu_ctx_deep_tail _ _ HΦ)).
    destruct En as [b pv κ T oM | pv U | pv pq k D ΦD | pv T M U | pv p R ΦR]; cbn [glu_gmod_units_deep];
      try exact (IH _ HΦ0).
    + split; [ exact (IH _ HΦ0) | exact (HΦ nil _ _ U eq_refl eq_refl) ].
    + split; [ exact (IH _ HΦ0) | exact (HΦ nil _ _ U eq_refl eq_refl) ].
  - cbn [gm_expand] in HΦ; rewrite body_ctx_graft, <- app_assoc in HΦ by apply gm_noopen_expand.
    split; [ exact (IH _ (glu_ctx_deep_suffix _ _ HΦ)) | exact (IHg _ HΦ) ].
Qed.

End Fixed_GCtx_Expansions.

(** ** The Rules

    A unit equation glues its context and both its units.  A body unit and
    an alias are glued by the extensions their rules glue, an alias of a
    literal by the literal under the alias's parameters, an expansion by
    the body it expands, and symmetry and transitivity by their
    premises. *)

#[local] Generalizable All Variables.

(** A body unit: each side's expansion's context over its parameters is an
    extension the rule glues. *)
Lemma glu_unit_eq_body :
  `( body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx ++ Δ) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx ++ Δ) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx' ++ Δ') /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx' ++ Δ') ->
     glu_unit_eq Θ Ξ Γ (gu_open Δ Φ) (gu_open Δ' Φ') ).
Proof.
  intros * HΦx HΦx' [HΔ _] [HB _] [HB' _].
  apply body_xp_expand in HΦx, HΦx'; subst Φx Φx'.
  constructor; intros Θ2 Ξ2 Hμ; destruct (HΔ _ _ Hμ) as [HΔg HΔd].
  - split; [ exact (glu_rel_ext_under_sub_ctx HΔg) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
  - destruct (HB _ _ Hμ) as [HBg HBd]; rewrite <- app_assoc in HBd.
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_body_inst _ _ _ _ HBg _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; split; [ exact HBg | exact (glu_gmod_units_deep_of_ctx _ _ HBd) ].
  - destruct (HB' _ _ Hμ) as [HBg HBd]; rewrite <- app_assoc in HBd.
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_body_inst _ _ _ _ HBg _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; split; [ exact HBg | exact (glu_gmod_units_deep_of_ctx _ _ HBd) ].
Qed.

(** An alias: each side's parameters are an extension the rule glues, and
    each side's target over them a module expression it glues. *)
Lemma glu_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ' ->
     glu_modexp Θ Ξ (Δ ++ Γ) E /\ glu_modexp Θ Ξ (Δ ++ Γ) E' ->
     glu_modexp Θ Ξ (Δ' ++ Γ) E' /\ glu_modexp Θ Ξ (Δ' ++ Γ) E' ->
     glu_unit_eq Θ Ξ Γ (gu_mk Δ (md_alias E)) (gu_mk Δ' (md_alias E')) ).
Proof.
  intros * [HΔ HΔ'] [HE _] [HE' _].
  constructor; intros Θ2 Ξ2 Hμ; destruct (HΔ _ _ Hμ) as [HΔg HΔd].
  - split; [ exact (glu_rel_ext_under_sub_ctx HΔg) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
  - destruct (HE _ _ Hμ) as [HEi HEp _].
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_alias_inst _ _ _ HΔg HEi _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; constructor; [ exact HΔg | exact HEi | exact HEp ].
  - destruct (HΔ' _ _ Hμ) as [HΔg' _]; destruct (HE' _ _ Hμ) as [HEi HEp _].
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_alias_inst _ _ _ HΔg' HEi _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; constructor; [ exact HΔg' | exact HEi | exact HEp ].
Qed.

(** An alias of a literal: the alias by its parameters and its target, the
    literal, glued at the instances by the construction
    ([glu_rel_modexp_under_sub_lit]); the literal over both telescopes by
    the literal, glued at the instance lifted through the alias's
    parameters. *)
Lemma glu_unit_eq_flatten :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
     glu_unit_eq Θ Ξ (Δ ++ Γ) (gu_mk Δ' D) (gu_mk Δ' D) ->
     glu_unit_eq Θ Ξ Γ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))) (gu_mk (Δ' ++ Δ) D) ).
Proof.
  intros * [HΔ _] HUt [HUc HU _].
  constructor; intros Θ2 Ξ2 Hμ; destruct (HΔ _ _ Hμ) as [HΔg HΔd].
  - split; [ exact (glu_rel_ext_under_sub_ctx HΔg) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
  - glu_gctx_embedding_wf.
    destruct (HUc _ _ Hμ) as [HUcg _]; destruct (HU _ _ Hμ) as [HUi HUd _].
    pose proof (glu_rel_modexp_under_sub_lit HUcg (Hwu _ _ _ HUt) HUi) as HL.
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_alias_inst _ _ _ HΔg HL _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; constructor; [ exact HΔg | exact HL | cbn [glu_modexp_parts_deep]; exact HUd ].
  - destruct (HU _ _ Hμ) as [HUi HUd _].
    constructor; [ intros Γ' τ Hτ | exact (glu_unit_deep_params_join _ _ _ _ HΔg HUd) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    pose proof (glu_rel_ext_under_sub_inst HΔg _ _ Hτ) as Hτ'.
    pose proof (HUi _ _ Hτ') as H.
    rewrite gunit_sub_mk in H |- *.
    rewrite tele_sub_app, List.length_app, <- (moddef_sub_sb_eq _ _ _ (sb_qn_add _ _ _)).
    apply glu_unit_at_flatten; [| exact (glu_rel_ext_under_renaming_of_inst HΔg Hτ) | exact H ].
    destruct (glu_rel_sub_inst_ctx _ _ _ Hτ') as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb).
Qed.

(** A body and its expansion: the expansion's context is the body's, and
    its module entries are the body's and those of its opens' fragments. *)
Lemma glu_unit_eq_expand :
  `( glu_unit_eq Θ Ξ Γ (gu_open Δ Φ) (gu_open Δ Φ) ->
     glu_unit_eq Θ Ξ Γ (gu_open Δ Φ) (gu_open Δ (gm_expand Φ)) ).
Proof.
  intros * [HΓ HU _]; constructor; [ exact HΓ | exact HU |].
  intros Θ2 Ξ2 Hμ; destruct (HU _ _ Hμ) as [HUi HUd HUcd]; constructor; [ intros Γ' τ Hτ | | exact HUcd ].
  - pose proof (HUi _ _ Hτ) as H.
    rewrite gunit_sub_mk in H |- *; cbn [moddef_sub glu_unit_at] in H |- *.
    destruct H as [H1 H2]; split.
    + rewrite !gm_expand_sub in *; rewrite (gm_expand_noopen _ (gm_noopen_expand _)); exact H1.
    + rewrite <- gm_expand_sub; exact (glu_gmod_units_expand _ _ H2).
  - cbn [glu_unit_deep] in HUd |- *; destruct HUd as [H1 H2]; split.
    + rewrite (gm_expand_noopen _ (gm_noopen_expand _)); exact H1.
    + exact (glu_gmod_units_deep_expand _ _ H2).
Qed.

Lemma glu_unit_eq_sym :
  `( glu_unit_eq Θ Ξ Γ U U' ->
     glu_unit_eq Θ Ξ Γ U' U ).
Proof. intros * [HΓ HU HU']; constructor; assumption. Qed.

Lemma glu_unit_eq_trans :
  `( glu_unit_eq Θ Ξ Γ U U' ->
     glu_unit_eq Θ Ξ Γ U' U'' ->
     glu_unit_eq Θ Ξ Γ U U'' ).
Proof. intros * [HΓ HU _] [_ _ HU'']; constructor; assumption. Qed.

(** *** Extensions by a module part

    A module slot and a definition with a module part: the unit, well
    formed at the target and glued at the instances of the context before
    the entry, by the rule's unit premise on each side. *)

Lemma glu_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     glu_unit_eq Θ Ξ (Ψ ++ Γ) U U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     glu_unit_eq Θ Ξ (Ψ' ++ Γ) U' U' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▹ₘ U) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▹ₘ U') ).
Proof.
  intros * [HΨ HΨ'] HUU [_ HU _] HU' [_ HU'g _].
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUU (wf_unit_eq_sym _ _ _ _ _ HUU)) as HUw.
  split; intros Θ2 Ξ2 Hμ; glu_gctx_embedding_wf.
  - destruct (HΨ _ _ Hμ) as [HΨg HΨd]; destruct (HU _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg | split; [ exact (Hwu _ _ _ HUw) | exact HUi ] ] |].
    exact (glu_ctx_deep_cons_unit (ce_mod U) _ U eq_refl HUd HΨd).
  - destruct (HΨ' _ _ Hμ) as [HΨg HΨd]; destruct (HU'g _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg | split; [ exact (Hwu _ _ _ HU') | exact HUi ] ] |].
    exact (glu_ctx_deep_cons_unit (ce_mod U') _ U' eq_refl HUd HΨd).
Qed.

Lemma glu_ext_eq_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ M' : A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E') ->
     glu_unit_eq Θ Ξ (Ψ ++ Γ) (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E')) ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ gu_mk nil (md_alias E') ≈ gu_mk nil (md_alias E') ->
     glu_unit_eq Θ Ξ (Ψ' ++ Γ) (gu_mk nil (md_alias E')) (gu_mk nil (md_alias E')) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▸ₘ A' ≔ M' ‖ gu_mk nil (md_alias E')) ).
Proof.
  intros * [HΨ HΨ'] HA HM HA' HM' HUU [_ HU _] HU' [_ HU'g _].
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUU (wf_unit_eq_sym _ _ _ _ _ HUU)) as HUw.
  split; intros Θ2 Ξ2 Hμ; glu_gctx_embedding_wf.
  - destruct (HΨ _ _ Hμ) as [HΨg HΨd]; destruct (HU _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg |] |].
    + do 2 eexists; constructor; [ reflexivity | exact (proj1 (HA _ _ Hμ)) | exact (proj1 (HM _ _ Hμ)) | exact (Hwu _ _ _ HUw) | exact HUi ].
    + exact (glu_ctx_deep_cons_unit (ce_dm A M (gu_mk nil (md_alias E))) _ _ eq_refl HUd HΨd).
  - destruct (HΨ' _ _ Hμ) as [HΨg HΨd]; destruct (HU'g _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg |] |].
    + do 2 eexists; constructor; [ reflexivity | exact (proj1 (HA' _ _ Hμ)) | exact (proj1 (HM' _ _ Hμ)) | exact (Hwu _ _ _ HU') | exact HUi ].
    + exact (glu_ctx_deep_cons_unit (ce_dm A' M' (gu_mk nil (md_alias E'))) _ _ eq_refl HUd HΨd).
Qed.
