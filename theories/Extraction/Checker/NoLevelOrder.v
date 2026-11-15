(** * Deciding No Member of a Type of Levels Terminates

    [Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R] reads a description through the descriptions of its
    module entries ([wf_no_level_members]): an open body through the units
    of its entries, a filed body through its stored entries, read at [⋅].
    A decision follows those reads.  [no_level_reachable Θ Ξ Γ R] says that following
    them from [R] ends: it is the domain of the decision, by which the
    decision recurses.

    It holds of every description a well-formed module expression denotes,
    when that description reads no open frame ([no_level_reachable_of_desc_ok]).  The
    reads end because a stored alias names only modules filed before it: an
    entry is checked against its frame's body so far ([wf_gmod_ext]), a unit
    against the units filed before it ([wf_gstack_file]), and an alias names
    no module still being defined ([frame_free_target]).  This is the global
    induction [global_valid], with the validity of an alias that what its
    target denotes has the domain ([no_level_entry_motive]). *)

From Stdlib Require Import Lia List PeanoNat String.
Import ListNotations.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping Presup LookupSound.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Domain *)

(** [no_level_reachable Θ Ξ Γ R]: reading [R] as [⊢ⁿˡ] does ends. *)
Inductive no_level_reachable (Θ : gdeps) (Ξ : gstack) : ctx -> mdesc -> Prop :=
(** A term reads nothing *)
| no_level_reachable_term : forall Γ r A om, no_level_reachable Θ Ξ Γ (mdesc_term r A om)
(** An open body: what the unit of each of its module entries denotes,
    where the entry is *)
| no_level_reachable_open : forall Γ Δ Φw Φx,
    (forall y Φ0 E U Ry, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U Ry -> no_level_reachable Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) Ry) ->
    no_level_reachable Θ Ξ Γ (mdesc_open Δ Φw Φx)
(** A filed body, exactly the stored one: what each of its stored entries
    other than a definition denotes, read at [⋅] *)
| no_level_reachable_closed : forall Γ Θ' p T Φ Ns,
    gc_body Θ Ξ p = Some (T, Φ) ->
    (forall y Φ0 E Ry, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> (forall b pv r A oM, E <> ge_def b pv r A oM) ->
       edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) Ry -> no_level_reachable Θ Ξ ⋅ Ry) ->
    no_level_reachable Θ Ξ Γ (mdesc_closed Θ' p T Φ Ns)
(** A definition with a module part, or a type former: its module part *)
| no_level_reachable_dm : forall Γ Θd A M Rm,
    (forall Rm', mdesc_mod Rm = Some Rm' -> no_level_reachable Θ Ξ Γ Rm') ->
    no_level_reachable Θ Ξ Γ (mdesc_dm Θd A M Rm).

(** The reads of a filed body do not depend on where it is read, nor on
    its outside parameters and arguments. *)
Lemma no_level_reachable_closed_any : forall Θ Ξ Γ Γ' Θ1 Θ2 p T Φ Ns1 Ns2,
    no_level_reachable Θ Ξ Γ (mdesc_closed Θ1 p T Φ Ns1) -> no_level_reachable Θ Ξ Γ' (mdesc_closed Θ2 p T Φ Ns2).
Proof. intros * H; inversion H; subst; constructor; assumption. Qed.

(** The module part of a description is read as the description's. *)
Lemma no_level_reachable_mod : forall Θ Ξ Γ R R', no_level_reachable Θ Ξ Γ R -> mdesc_mod R = Some R' -> no_level_reachable Θ Ξ Γ R'.
Proof.
  intros * H; induction H; intros Hm; cbn in Hm; try discriminate.
  - injection Hm as <-; constructor; assumption.
  - injection Hm as <-; econstructor; eassumption.
  - match goal with IH : forall Rm', _ -> no_level_reachable _ _ _ Rm' |- _ => exact (IH _ Hm) end.
Qed.

(** A module abstracted over parameters it is read under is read as it. *)
Lemma no_level_reachable_up : forall Θ Ξ Γ Δ R, mdesc_is_mod R -> no_level_reachable Θ Ξ (Δ ++ Γ) R -> no_level_reachable Θ Ξ Γ (mdesc_up Δ R).
Proof.
  intros * Hm H; destruct R as [r A om | Δo Φw Φx | Θ' p T Φ Ns | Θd A M Rm]; cbn in Hm |- *; try contradiction.
  - inversion H as [| ? ? ? ? Hc | |]; subst; constructor.
    intros * Hp He Hu; rewrite <- List.app_assoc in Hu |- *; exact (Hc _ _ _ _ _ Hp He Hu).
  - exact (no_level_reachable_closed_any _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(** ** The Size of the Bodies Stored in a Body *)

Fixpoint gm_bodies_size (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_open Φ0 _ _ _ => gm_bodies_size Φ0
  | gm_ext Φ0 _ E =>
      S (gm_bodies_size Φ0 +
         match E with
         | ge_mod _ (gu_mk _ (md_body _ Φ')) => gm_bodies_size Φ'
         | ge_ind _ _ _ _ Φ' => gm_bodies_size Φ'
         | ge_record _ _ _ Φ' => gm_bodies_size Φ'
         | _ => 0
         end)
  end.

(** The body an entry stores is smaller than the body storing it. *)
Lemma gm_bodies_size_entry : forall Φ y E, gm_entry Φ (y :: nil) = Some E ->
    match E with
    | ge_mod _ (gu_mk _ (md_body _ Φ')) => gm_bodies_size Φ' < gm_bodies_size Φ
    | ge_ind _ _ _ _ Φ' => gm_bodies_size Φ' < gm_bodies_size Φ
    | ge_record _ _ _ Φ' => gm_bodies_size Φ' < gm_bodies_size Φ
    | _ => True
    end.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * He; cbn in He; [ discriminate | |].
  - destruct (String.eqb y x).
    + injection He as <-; cbn [gm_bodies_size].
      destruct E0 as [| ? [? [? ?| ?]] | | |]; try exact I; lia.
    + specialize (IH _ _ He); cbn [gm_bodies_size].
      destruct E as [| ? [? [? ?| ?]] | | |]; try exact I; lia.
  - exact (IH _ _ He).
Qed.

(** ** Filed Bodies Whose Aliases Are Valid *)

(** The validity of an entry for the domain: what an alias's target
    denotes, under the alias's parameters, has the domain. *)
Definition no_level_entry_motive (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_mod _ (gu_mk Δa (md_alias E')) => forall R, mdenote Θ2 Ξ2 Δa E' R -> no_level_reachable Θ2 Ξ2 Δa R
  | _ => True
  end.

(** Nothing is asked of a body's telescope: the reads of [⊢ⁿˡ] never read
    a telescope, only the entries over it. *)
Definition no_level_frame_motive (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop := True.
(** Nothing is asked of an inductive declaration: [⊢ⁿˡ] reads a member's
    type former only through its module, which is a filed body read by its
    entries, not through the declaration. *)
Definition no_level_ind_motive (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop := True.
(** Nothing is asked of a record declaration, for the same reason: a
    record's type former is read through its module only. *)
Definition no_level_record_motive (Θ2 : gdeps) (Ξ2 : gstack) (R : record_decl) : Prop := True.

(** The validity does not depend on where the entry is read from. *)
Abbreviation no_level_entry_motives := (fun (_ : gdeps) (_ : gstack) => no_level_entry_motive).

(** What an alias denotes read at [⋅], when its target's descriptions
    have the domain. *)
Lemma no_level_reachable_alias_read : forall Θ Ξ Δ E Ry,
    (forall R, mdenote Θ Ξ Δ E R -> no_level_reachable Θ Ξ Δ R) ->
    forall o, udenote Θ Ξ ⋅ o (gu_mk Δ (md_alias E)) Ry -> no_level_reachable Θ Ξ ⋅ Ry.
Proof.
  intros * HV o Hu'; inversion Hu'; subst.
  match goal with Hm : mdenote _ _ (Δ ++ ⋅) E ?R0, Hd : mdesc_mod ?R0 = Some ?R1 |- _ =>
    rewrite List.app_nil_r in Hm;
    apply no_level_reachable_up; [ exact (mdesc_mod_is_mod _ _ Hd) |];
    rewrite List.app_nil_r; exact (no_level_reachable_mod _ _ _ _ _ (HV _ Hm) Hd) end.
Qed.

Section ClosedReach.
  Variables (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg2 : ⊢ᵍ Θ2 ⍮ Ξ2.

  (** A filed body whose aliases are valid has the domain, by the size of
      the bodies it stores. *)
  Lemma closed_no_level_reachable_size : forall n Φ, gm_bodies_size Φ < n -> forall Θs Ξs p T,
      gm_valid no_level_entry_motives no_level_frame_motive no_level_ind_motive no_level_record_motive Θs Ξs Θ2 Ξ2 T Φ -> gc_body Θ2 Ξ2 p = Some (T, Φ) ->
      forall Γ Θ' Ns, no_level_reachable Θ2 Ξ2 Γ (mdesc_closed Θ' p T Φ Ns).
  Proof.
    induction n as [| n IH]; intros Φ Hn * Hv Hb Γ Θ' Ns; [ lia |].
    constructor; [ exact Hb |].
    intros y Φ0 E Ry Hp Hnd Hed.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0' & E' & [= <- <-] & Hent).
    pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hp) as HvE.
    pose proof (gm_bodies_size_entry _ _ _ Hent) as Hsz.
    assert (Hl : loc Θ2 Ξ2 p T Φ) by (right; exact Hb).
    pose proof (loc_closed _ _ Hg2 _ _ _ Hl) as [_ Hc].
    destruct E as [b pv r A oM | pv [Δ [sm Φ' | Ea]] | pv pq k D ΦD | pv A M [Δ [sm Φ' | Ea]] | pv pr R ΦR];
      cbv beta iota in Hsz.
    - exfalso; exact (Hnd _ _ _ _ _ eq_refl).
    - (* a stored body: filed below, smaller *)
      destruct (gm_entry_closed _ _ _ _ Hc Hent) as (k' & -> & _ & Hc')
      ; pose proof (body_closed_noopen _ _ Hc') as Hno.
      cbn [ge_read] in Hed; inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
      match goal with Hx : body_xp _ _ _ Φ' ?Φx, Hd : mdesc_body _ _ _ _ _ = Some _ |- _ =>
        rewrite (body_xp_noopen_id _ _ _ _ _ Hno Hx) in Hd; cbn in Hd; injection Hd as <- end.
      destruct (loc_child_mod _ _ Hg2 _ _ _ Hl _ _ _ _ _ Hent) as [Hb' _].
      cbn [ge_valid] in HvE; destruct HvE as [_ HvE].
      eapply IH; [| exact HvE | exact Hb' ]; lia.
    - (* an alias: by its validity *)
      cbn [ge_read] in Hed; inversion Hed; subst.
      cbn [ge_valid no_level_entry_motive] in HvE.
      eapply no_level_reachable_alias_read; [ exact HvE | eassumption ].
    - (* an inductive type: its type former, its module filed below *)
      cbn [ge_read] in Hed; inversion Hed; subst.
      pose proof (gc_entry_selfpath _ _ Hg2 _ _ _ _ _ _ (proj2 (loc_entry _ _ Hg2 _ _ _ Hl _ _) Hent)) as Hsp.
      match goal with Hpm : ind_mpath _ _ = Some ?pm, Hlm : gc_loc _ _ ?pm = Some _ |- _ =>
        rewrite (ind_selfpath_path _ _ _ _ Hsp) in Hpm; injection Hpm as <-;
        pose proof (loc_child_ind _ _ Hg2 _ _ _ _ _ _ _ _ _ Hl Hent) as Hb';
        unfold gc_loc in Hlm; rewrite (gc_body_not_frame _ _ _ _ Hb'), Hb' in Hlm; injection Hlm as <- <- end.
      constructor; intros Rm' Hm; cbn in Hm; injection Hm as <-.
      cbn [ge_valid] in HvE; destruct HvE as (_ & _ & HvE).
      eapply IH; [| exact HvE | exact Hb' ]; lia.
    - (* a definition with a module part that is a body denotes nothing *)
      cbn [ge_read] in Hed; inversion Hed.
    - (* a definition with a module part: its module part by its validity *)
      cbn [ge_read] in Hed; inversion Hed; subst.
      cbn [ge_valid no_level_entry_motive] in HvE; destruct HvE as [HvE _].
      constructor; intros Rm' Hm.
      match goal with Hu : udenote _ _ _ _ _ ?Rm |- _ =>
        pose proof (no_level_reachable_alias_read _ _ _ _ _ HvE _ Hu) as HR end.
      exact (no_level_reachable_mod _ _ _ _ _ HR Hm).
    - (* a record type: its type former, its module filed below *)
      cbn [ge_read] in Hed; inversion Hed; subst.
      pose proof (loc_child_record _ _ Hg2 _ _ _ _ _ _ _ _ Hl Hent) as Hb'.
      match goal with Hlm : gc_loc _ _ _ = Some _ |- _ =>
        unfold gc_loc in Hlm; rewrite (gc_body_not_frame _ _ _ _ Hb'), Hb' in Hlm; injection Hlm as <- <- end.
      constructor; intros Rm' Hm; cbn in Hm; injection Hm as <-.
      cbn [ge_valid] in HvE; destruct HvE as (_ & _ & HvE).
      eapply IH; [| exact HvE | exact Hb' ]; lia.
  Qed.

  Corollary closed_no_level_reachable : forall Θs Ξs p T Φ,
      gm_valid no_level_entry_motives no_level_frame_motive no_level_ind_motive no_level_record_motive Θs Ξs Θ2 Ξ2 T Φ -> gc_body Θ2 Ξ2 p = Some (T, Φ) ->
      forall Γ Θ' Ns, no_level_reachable Θ2 Ξ2 Γ (mdesc_closed Θ' p T Φ Ns).
  Proof. intros *; exact (closed_no_level_reachable_size (S (gm_bodies_size Φ)) Φ ltac:(lia) Θs Ξs p T). Qed.
End ClosedReach.

(** ** Typed Descriptions, Grown, Have the Domain *)

Section Grown.
  Variables (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis He : gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2.
  (** What [Θ ⍮ Ξ] files and has open is valid read at [Θ2 ⍮ Ξ2] *)
  Hypothesis HΘ : gds_valid no_level_entry_motives no_level_frame_motive no_level_ind_motive no_level_record_motive Θ Ξ Θ2 Ξ2 Θ.
  Hypothesis HΞ : gs_valid no_level_entry_motives no_level_frame_motive no_level_ind_motive no_level_record_motive Θ Ξ Θ2 Ξ2 Ξ.

  Let Hg2 : ⊢ᵍ Θ2 ⍮ Ξ2 := gctx_embedding_with_bodies_wf _ _ _ _ He.
  Let Hs : gc_sub Θ Ξ Θ2 Ξ2 := gc_sub_keeping_bodies_sub _ _ _ _ (gctx_embedding_with_bodies_resolution _ _ _ _ He).

  (** A typed description reading no open frame, read in the bigger
      context, has the domain there: an open body's entries denote typed
      descriptions reading no open frame, and a filed body is valid. *)
  Lemma no_level_reachable_grown : forall Γ R, desc_ok Θ Ξ Γ R -> mdesc_canonical Θ Ξ R -> ~ desc_reads_frame Ξ R ->
      forall R2, mdesc_grows Θ Ξ Θ2 Ξ2 R R2 -> no_level_reachable Θ2 Ξ2 Γ R2.
  Proof.
    induction 1 as [Γ r A om iA HA HM
                   | Γ Δ Φw Φ lΔ HΦ Hn Hent IH HaΔ Hsh Hnd HUw HRΔ Htg HLΔ
                   | Γ Θ' T Φ Ns Θ0 Ξ0 p lΘ Hg0 Hs0 Hloc Ha Hsc HT HΘ' Hargs HaΘ HRΘ HLΘ HFΘ
                   | Γ Θd A M Rm lΘ iA HΘd HaΘd HBt HMt HRm IH HRΘd HLΘd HFΘd];
      intros Hc Hf R2 Hd.
    - inversion Hd; subst; constructor.
    - (* an open body: the same, its entries grown *)
      inversion Hd; subst.
      constructor; intros y Φ0 E U Ry2 Hp HE Hu2.
      destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
      rewrite HΨ, <- List.app_assoc in HΦ.
      destruct (body_ext_unit_wf _ _ _ _ _ _ _ (ctx_app_wf_tail _ _ _ _ HΦ) HE) as [_ HU].
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R1 HR1] & _).
      destruct (proj1 (proj2 (mdenote_grow_all _ _ _ _ Hg Hg2 Hs)) _ _ _ _ HR1 (or_introl eq_refl)) as (R1' & HR1' & Hd1).
      rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg2)) _ _ _ _ Hu2 _ HR1').
      apply (IH _ _ _ _ Hp HE _ HR1); [ exact (mdenote_canon _ _ _ _ _ Hg (mdenote_lit _ _ _ _ _ HR1)) | | exact Hd1 ].
      exact (proj1 (wf_unit_frame_free _ _ _ _ _ HU) _ HR1).
    - (* a filed body: exactly the stored one, valid *)
      apply closed_frame_free_iff in Hf.
      assert (Hb : gc_body Θ Ξ p = Some (T, Φ)) by (destruct Hc as [Hc | Hc]; [ rewrite Hf in Hc; discriminate | exact Hc ]).
      pose proof (gc_sub_body_field _ _ _ _ Hs _ _ _ Hb) as Hb2.
      inversion Hd as [? Hcb | ? ? ? Φ2 ? ? _ Hl2 |]; subst; [ cbn in Hcb; discriminate |].
      destruct (loc_functional _ _ _ _ _ _ _ Hl2 (or_intror Hb2)) as [_ ->].
      destruct (gc_body_valid _ _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hb) as [_ Hv].
      exact (closed_no_level_reachable _ _ Hg2 _ _ _ _ _ Hv Hb2 _ _ _).
    - (* a definition with a module part: its module part *)
      cbn in Hc.
      assert (Hf' : ~ desc_reads_frame Ξ Rm)
        by (intros Hr; apply Hf, (proj2 (desc_reads_frame_dm _ _ _ _ _)), (proj2 (desc_reads_frame_up _ _ _)); exact Hr).
      assert (Hc' : mdesc_canonical Θ Ξ Rm).
      { clear -Hc; revert Hc; induction Rm; cbn; auto. }
      assert (Hdi : exists Rm2, R2 = mdesc_dm Θd A M (mdesc_up Θd Rm2) /\ mdesc_grows Θ Ξ Θ2 Ξ2 Rm Rm2).
      { inversion Hd as [? Hcb | | ? ? ? ? R2' Hd']; subst.
        - exists Rm; split; [ reflexivity | apply mdesc_grows_same; cbn in Hcb; rewrite mdesc_closedb_up in Hcb; exact Hcb ].
        - destruct (mdesc_grows_up_inv _ _ _ _ _ _ _ Hd') as (Rm2 & -> & HRm2); eauto. }
      destruct Hdi as (Rm2 & -> & HRm2).
      pose proof (IH Hc' Hf' _ HRm2) as HR.
      constructor; intros Rm' Hm; rewrite mdesc_mod_up in Hm.
      destruct (mdesc_mod Rm2) as [Rm3 |] eqn:Hm3; cbn in Hm; [ injection Hm as <- | discriminate ].
      exact (no_level_reachable_up _ _ _ _ _ (mdesc_mod_is_mod _ _ Hm3) (no_level_reachable_mod _ _ _ _ _ HR Hm3)).
  Qed.
End Grown.

(** ** Every Stored Alias Is Valid *)

(** An alias's target denotes, wherever its context embeds, a description
    with the domain. *)
Lemma no_level_entry_motive_alias : forall Θ Ξ pv Δ E l (lv : bool) Rt Θ2 Ξ2 (Θs : gdeps) (Ξs : gstack),
    all_assumptions Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    params_evaluated Θ Ξ (gs_tele Ξ) Δ l ->
    levels_flag Θ Ξ ⋅ (Δ ++ gs_tele Ξ) E lv Rt ->
    frame_free_target Θ Ξ (Δ ++ gs_tele Ξ) E ->
    bodies_valid_along_embeddings no_level_entry_motives no_level_frame_motive no_level_ind_motive no_level_record_motive Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    no_level_entry_motive Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * _ _ HE _ _ (R & HR & Hn) HG He _ R2 HR2; cbn [no_level_entry_motive].
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  destruct (gctx_embedding_mdenote _ _ _ _ Hg (gctx_embedding_with_bodies_embedding _ _ _ _ He) _ _ _ HR) as (R2' & HR2' & Hd).
  rewrite (proj1 (mdenote_functional_all _ _ (gctx_embedding_with_bodies_wf _ _ _ _ He)) _ _ _ HR2 _ HR2').
  exact (no_level_reachable_grown _ _ _ _ Hg He HΘ HΞ _ _ (me_desc_ok _ _ _ _ _ _ HE HR) (mdenote_canon _ _ _ _ _ Hg HR) Hn _ Hd).
Qed.

(** A canonical description grows into itself in its own context. *)
Lemma mdesc_grows_canonical_refl : forall Θ Ξ R, mdesc_canonical Θ Ξ R -> mdesc_grows Θ Ξ Θ Ξ R R.
Proof.
  intros Θ Ξ R; induction R as [r A om | Δ Φ Φx | Θ' p T Φ Ns | Θd A M Rm IH]; intros Hc.
  - apply mdesc_grows_same; reflexivity.
  - apply mdesc_grows_same; reflexivity.
  - apply mdesc_grows_closed; exact Hc.
  - apply mdesc_grows_dm, IH; exact Hc.
Qed.

(** Every typed canonical description reading no open frame has the
    domain. *)
Theorem no_level_reachable_of_desc_ok : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ R, desc_ok Θ Ξ Γ R -> mdesc_canonical Θ Ξ R ->
    ~ desc_reads_frame Ξ R -> no_level_reachable Θ Ξ Γ R.
Proof.
  intros * Hg * Hok Hc Hn.
  pose proof (global_valid no_level_entry_motives no_level_frame_motive no_level_ind_motive no_level_record_motive
                ltac:(intros; exact I) ltac:(intros; exact I)
                no_level_entry_motive_alias ltac:(intros; exact I) ltac:(intros; split; exact I)
                ltac:(intros; exact I) ltac:(intros; exact I) _ _ Hg) as HG.
  pose proof (gctx_embedding_with_bodies_refl _ _ Hg) as He.
  destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (no_level_reachable_grown _ _ _ _ Hg He HΘ HΞ _ _ Hok Hc Hn _ (mdesc_grows_canonical_refl _ _ _ Hc)).
Qed.
