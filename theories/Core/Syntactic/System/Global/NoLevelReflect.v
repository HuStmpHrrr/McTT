(** * No Member of a Type of Levels, Moved Back

    [Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R] is preserved by a well-typed substitution
    ([sub_preserves_wf]); this file proves the converse for a typed
    description ([no_level_reflect]): if its image has no member of a type
    of levels, neither has it.  A substitution changes the types and terms
    a description holds, never the kinds it is tagged with, and an open
    body's module entries denote, where they are, descriptions whose images
    are what the moved entries denote ([mdenote_sub_all]).  The judgment is
    also moved along the parameters a description is abstracted over
    ([no_level_up], [no_level_up_iff]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Structural.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas DescTyping Presup Paths LookupSound.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Auxiliary Facts *)

(** ⊢ⁿˡ along a well-typed substitution ([sub_preserves_wf]). *)
Lemma sub_preserves_no_level : forall Θ Ξ Γ Δ R σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ⁿˡ R -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_sub R σ.
Proof.
  intros * H Hσ; destruct sub_preserves_wf as (_ & _ & _ & _ & _ & _ & _ & Hn); exact (Hn _ _ _ _ H _ _ Hσ).
Qed.

(** A substitution keeps an entry's kind. *)
Lemma entry_kind_sub : forall E σ, entry_kind (gentry_sub E σ) = entry_kind E.
Proof. intros [] σ; reflexivity. Qed.

(** A choice of descriptions, one for each name a body has a prefix up
    to: the body has finitely many entries, so one for each is a
    function. *)
Lemma prefix_choice : forall Φ (P : String.string -> gmod -> mdesc -> Prop),
    (forall y Φy, gm_prefix_upto Φ y = Some Φy -> exists R, P y Φy R) ->
    exists f : String.string -> mdesc, forall y Φy, gm_prefix_upto Φ y = Some Φy -> P y Φy (f y).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg]; intros P Hex.
  - exists (fun _ => mdesc_open nil gm_nil gm_nil); intros * Hp; discriminate.
  - destruct (Hex x (gm_ext Φ x E)) as [R0 HR0]; [ cbn; rewrite String.eqb_refl; reflexivity |].
    destruct (IH (fun y Φy R => String.eqb y x = false -> P y Φy R)) as [f Hf].
    { intros y Φy Hp; destruct (String.eqb y x) eqn:Ey.
      - exists R0; discriminate.
      - destruct (Hex y Φy) as [R HR]; [ cbn; rewrite Ey; exact Hp |]; exists R; intros _; exact HR. }
    exists (fun y => if String.eqb y x then R0 else f y); intros y Φy Hp; cbn in Hp.
    destruct (String.eqb y x) eqn:Ey; [ injection Hp as <-; apply String.eqb_eq in Ey; subst y; exact HR0 |].
    exact (Hf _ _ Hp Ey).
  - destruct (IH (fun y Φy R => existsb (String.eqb y) (map import_item_name its) = false -> P y Φy R)) as [f Hf].
    { intros y Φy Hp; destruct (existsb (String.eqb y) (map import_item_name its)) eqn:Ey.
      - exists (mdesc_open nil gm_nil gm_nil); discriminate.
      - destruct (Hex y Φy) as [R HR]; [ cbn; rewrite Ey; exact Hp |]; exists R; intros _; exact HR. }
    exists f; intros y Φy Hp; cbn in Hp.
    destruct (existsb (String.eqb y) (map import_item_name its)) eqn:Ey; [ discriminate |].
    exact (Hf _ _ Hp Ey).
Qed.

(** ** Along the Parameters a Description Is Abstracted Over *)

(** A module description abstracted over parameters: an open body's
    entries are read in the same context, the parameters joined to its
    own; a closed module's reading does not depend on the context. *)
Lemma no_level_up_mod : forall Θ Ξ X Δ Γ, mdesc_is_mod X ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ X -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_up Δ X.
Proof.
  intros * Hm H; destruct X as [| Δo Φw Φx | Θ' p T Φ Ns |]; cbn in Hm; try contradiction;
    inversion H as [| ? ? ? ? ? md ? Hn Hx Hk Hu Hl | |]; subst; cbn [mdesc_up].
  - apply wf_no_level_open with (member_descs := md); [ exact Hn | | exact Hk | |].
    + apply ext_of_ctx'; pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as X; rewrite !List.app_assoc in X |- *; exact X.
    + intros * Hp HU; pose proof (Hu _ _ _ _ Hp HU) as X; rewrite !List.app_assoc in X |- *; exact X.
    + intros * Hp HU; pose proof (Hl _ _ _ _ Hp HU) as X; rewrite !List.app_assoc in X |- *; exact X.
  - eapply wf_no_level_closed; eassumption.
Qed.

(** The same back. *)
Lemma no_level_up_mod_inv : forall Θ Ξ X Δ Γ, mdesc_is_mod X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_up Δ X -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ X.
Proof.
  intros * Hm H; destruct X as [| Δo Φw Φx | Θ' p T Φ Ns |]; cbn in Hm; try contradiction;
    cbn [mdesc_up] in H; inversion H as [| ? ? ? ? ? md ? Hn Hx Hk Hu Hl | |]; subst.
  - apply wf_no_level_open with (member_descs := md); [ exact Hn | | exact Hk | |].
    + apply ext_of_ctx'; pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as X; rewrite !List.app_assoc in X |- *; exact X.
    + intros * Hp HU; pose proof (Hu _ _ _ _ Hp HU) as X; rewrite !List.app_assoc in X |- *; exact X.
    + intros * Hp HU; pose proof (Hl _ _ _ _ Hp HU) as X; rewrite !List.app_assoc in X |- *; exact X.
  - eapply wf_no_level_closed; eassumption.
Qed.

(** Any description abstracted over parameters: a term keeps its tag, a
    definition with a module part its module part, abstracted alike. *)
Lemma no_level_up_iff : forall Θ Ξ X Δ Γ, Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ X <-> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_up Δ X.
Proof.
  intros * ; destruct X as [r A om | Δo Φw Φx | Θ' p T Φ Ns | Θd A M Rm].
  - cbn [mdesc_up]; split; intros H; inversion H; subst; constructor; assumption.
  - split; [ apply no_level_up_mod; exact I | apply no_level_up_mod_inv; exact I ].
  - split; [ apply no_level_up_mod; exact I | apply no_level_up_mod_inv; exact I ].
  - cbn [mdesc_up]; split; intros H; inversion H; subst; constructor; intros Rm' HRm'.
    + rewrite mdesc_mod_up in HRm'; destruct (mdesc_mod Rm) as [X0 |] eqn:E0; cbn in HRm'; [ injection HRm' as <- | discriminate ].
      apply no_level_up_mod; [ exact (mdesc_mod_is_mod _ _ E0) |].
      eauto.
    + apply no_level_up_mod_inv; [ exact (mdesc_mod_is_mod _ _ HRm') |].
      match goal with Hm : forall Rm', mdesc_mod _ = Some Rm' -> _ |- _ =>
        apply Hm; rewrite mdesc_mod_up, HRm'; reflexivity end.
Qed.

(** The module part of a description with none of a type of levels has
    none. *)
Lemma no_level_mod_of : forall Θ Ξ Γ X X', Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ X -> mdesc_mod X = Some X' -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ X'.
Proof.
  intros * H Hm; destruct X; cbn in Hm; try discriminate; try (injection Hm as <-; exact H).
  inversion H; subst; auto.
Qed.

(** A description with a module part has none of a type of levels when its
    module part has none, but for a term part of a type of levels: none
    when it has no term part, or one of a type of a universe. *)
Lemma no_level_of_mod : forall Θ Ξ Γ X X0, mdesc_mod X = Some X0 ->
    (forall X', mdesc_mod X = Some X' -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ X') -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ X.
Proof.
  intros * H0 H; destruct X; cbn in H0, H; try discriminate.
  - exact (H _ eq_refl).
  - exact (H _ eq_refl).
  - constructor; exact H.
Qed.

(** A description with a module part has no member of a type of levels
    exactly when its module part has none. *)
Lemma no_level_mod_iff : forall Θ Ξ Γ X X0, mdesc_mod X = Some X0 -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ X <-> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ X0.
Proof.
  intros * H0; split; intros H.
  - exact (no_level_mod_of _ _ _ _ _ H H0).
  - eapply no_level_of_mod; [ exact H0 |]; intros X' HX'; rewrite H0 in HX'; injection HX' as <-; exact H.
Qed.

(** A term is read by its tag only. *)
Lemma no_level_term_iff : forall Θ Ξ Γ Γ' r A om A' om',
    Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_term r A om <-> Θ ⍮ Ξ ⍮ Γ' ⊢ⁿˡ mdesc_term r A' om'.
Proof. intros; split; intros H; inversion H; subst; constructor; assumption. Qed.

(** An open body is read through its expansion only, not its body as
    written. *)
Lemma no_level_open_written : forall Θ Ξ Γ Δ Φ1 Φ2 Φx,
    Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_open Δ Φ1 Φx -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_open Δ Φ2 Φx.
Proof. intros * H; inversion H; subst; eapply wf_no_level_open; eassumption. Qed.

(** ** Reflected Along a Substitution *)

(** A typed description has no member of a type of levels when its image
    under a well-typed substitution has none.  By induction on the typing:
    a term keeps its tag; an open body keeps its entries' tags, and each
    module entry denotes a typed description whose image the moved entry
    denotes; a closed module is read where it is stored, apart from the
    context; a definition with a module part, by its module part, moved
    under its outer parameters. *)
Theorem no_level_reflect : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ R, desc_ok Θ Ξ Γ R ->
    forall Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ⁿˡ mdesc_sub R σ -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R.
Proof.
  intros Θ Ξ Hg.
  induction 1 as [Γ r A om iA HA HM
                 | Γ Δo Φw Φ lΔ HΦ Hn Hent IH HaΔ Hsh Hnd HUw HRΔ Htg HLΔ
                 | Γ Θ' T Φ Ns Θ0 Ξ0 p lΘ Hg0 Hsub0 Hloc Ha Hs HT HΘ' Hargs HaΘ HRΘ HLΘ HFΘ
                 | Γ Θd A M Rm lΘ iA HΘd HaΘd HA HM HRm IH HRΘd HLΘd HFΘd ];
    intros Δ σ Hσ Hns; cbn [mdesc_sub] in Hns.
  - (* a term *)
    inversion Hns; subst; constructor; assumption.
  - (* an open body *)
    inversion Hns as [| ? ? ? ? ? md' ? Hn' Hx' Hk' Hu' Hl' | |]; subst.
    pose proof (gm_noopen_nopens _ Hn) as Hnx.
    destruct (prefix_choice Φ (fun y Φy R => forall Φ0 E U, Φy = gm_ext Φ0 y E -> entry_unit E = Some U ->
                                  udenote Θ Ξ (body_ctx Φ0 ++ Δo ++ Γ) None U R)) as [md Hmd].
    { intros y Φy Hp.
      destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & _).
      destruct (entry_unit E) as [U |] eqn:HE; [| exists (mdesc_open nil gm_nil gm_nil); intros * [= <- <-]; congruence ].
      destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
      pose proof HΦ as HΦ'; rewrite HΨ in HΦ'.
      pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ'; exact HΦ')) as HΦ0.
      destruct (body_ext_unit_wf _ _ _ _ _ _ _ HΦ0 HE) as [_ HU].
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R HR] & _).
      exists R; intros * [= <- <-] HE'; rewrite HE in HE'; injection HE' as <-; exact HR. }
    apply wf_no_level_open with (member_descs := md); [ exact Hn | | | |].
    + apply ext_of_ctx'; rewrite <- List.app_assoc; exact HΦ.
    + (* the definitions keep their tags *)
      intros y Φ0 E A0 M0 Hp HE.
      rewrite <- (entry_kind_sub E (sb_qn (gm_binders Φ0) (sb_qn (length Δo) σ))).
      eapply Hk'; [ rewrite gm_prefix_upto_sub, Hp; reflexivity | exact (entry_tm_sub _ _ _ _ HE) ].
    + intros * Hp HE; exact (Hmd _ _ Hp _ _ _ eq_refl HE).
    + (* each module entry, by its image *)
      intros y Φ0 E U Hp HE.
      pose proof (Hmd _ _ Hp _ _ _ eq_refl HE) as HR.
      destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
      pose proof (gm_prefix_upto_nopens _ _ _ Hp Hnx) as Hn0; cbn [gm_nopens] in Hn0.
      pose proof HΦ as HΦ'; rewrite HΨ in HΦ'.
      pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ'; exact HΦ')) as HΦ0.
      destruct (body_ext_unit_wf _ _ _ _ _ _ _ HΦ0 HE) as [HΓ0 HU].
      set (σy := sb_qn (length (body_ctx Φ0 ++ Δo)) σ).
      assert (HΓ0' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δo) σ ++ Δ)
        by (eapply ctx_sub_wf_gen; [ exact Hσ | rewrite <- List.app_assoc; exact HΓ0 ]).
      assert (Hσy : Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δo) σ ++ Δ ⊢ˢ σy : (body_ctx Φ0 ++ Δo) ++ Γ)
        by (apply wf_sub_ext; [ exact Hσ | exact HΓ0' | rewrite <- List.app_assoc; exact HΓ0 ]).
      destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΓs & HUs & _).
      pose proof (proj1 (proj2 (mdenote_sub_all _ _ (wf_gstack_closed _ _ Hg))) _ _ _ _ HR _
                    (slots_ok_ctx _ HΓs) (or_introl HUs) _ _
                    (wf_sub_mod_compat _ _ _ _ _ ltac:(rewrite <- List.app_assoc in Hσy; exact Hσy))) as HRs.
      rewrite tele_sub_app, <- List.app_assoc in HRs.
      replace (U[σy]ᵘ) with (gunit_sub U (sb_qn (gm_binders Φ0) (sb_qn (length Δo) σ))) in HRs
        by (unfold σy; rewrite List.length_app, (length_body_ctx _ Hn0), sb_qn_plus; reflexivity).
      rewrite <- (body_ctx_sub _ _ Hn0) in HRs.
      assert (Hp' : gm_prefix_upto (gmod_sub Φ (sb_qn (length Δo) σ)) y
                    = Some (gm_ext (gmod_sub Φ0 (sb_qn (length Δo) σ)) y
                                   (gentry_sub E (sb_qn (gm_binders Φ0) (sb_qn (length Δo) σ)))))
        by (rewrite gm_prefix_upto_sub, Hp; reflexivity).
      pose proof (entry_unit_sub _ (sb_qn (gm_binders Φ0) (sb_qn (length Δo) σ)) _ HE) as HE'.
      pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HRs _ (Hu' _ _ _ _ Hp' HE')) as Heq.
      pose proof (Hl' _ _ _ _ Hp' HE') as Hny; rewrite <- Heq in Hny.
      eapply (IH y Φ0 E U Hp HE _ HR).
      * rewrite tele_sub_app in Hσy; rewrite <- !List.app_assoc in Hσy; exact Hσy.
      * rewrite (body_ctx_sub _ _ Hn0) in Hny; exact Hny.
  - (* a closed module *)
    inversion Hns; subst; eapply wf_no_level_closed; eassumption.
  - (* a definition with a module part *)
    inversion Hns; subst.
    match goal with H : forall Rm', mdesc_mod _ = Some Rm' -> _ |- _ => rename H into Hm' end.
    constructor; intros X' HX'.
    rewrite mdesc_mod_up in HX'; destruct (mdesc_mod Rm) as [X0 |] eqn:EX0; cbn in HX'; [ injection HX' as <- | discriminate ].
    pose proof (mdesc_mod_is_mod _ _ EX0) as HX0.
    pose proof (Hm' _ (mdesc_mod_sub _ _ σ ltac:(rewrite mdesc_mod_up, EX0; reflexivity))) as Hn1.
    rewrite mdesc_up_sub in Hn1.
    apply no_level_up_mod_inv in Hn1; [| destruct X0; cbn in HX0 |- *; first [ contradiction | exact I ] ].
    assert (Hσq : Θ ⍮ Ξ ⍮ tele_sub Θd σ ++ Δ ⊢ˢ sb_qn (length Θd) σ : Θd ++ Γ)
      by (apply wf_sub_ext; [ exact Hσ | eapply ctx_sub_wf_gen; [ exact Hσ | exact HΘd ] | exact HΘd ]).
    assert (HnRm : Θ ⍮ Ξ ⍮ tele_sub Θd σ ++ Δ ⊢ⁿˡ mdesc_sub Rm (sb_qn (length Θd) σ)).
    { eapply no_level_of_mod; [ exact (mdesc_mod_sub _ _ _ EX0) |].
      intros Y HY; rewrite (mdesc_mod_sub _ _ _ EX0) in HY; injection HY as <-; exact Hn1. }
    apply no_level_up_mod; [ exact HX0 |].
    exact (no_level_mod_of _ _ _ _ _ (IH _ _ Hσq HnRm) EX0).
Qed.
