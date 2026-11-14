(** * Converting a Module Slot

    A judgment in a context with a module slot [▹ₘ U] holds with the slot's
    unit replaced by an equal one [U'] ([slot_conv_preserves_wf]).  Only
    member lookups read a slot's unit, so the replacement is justified by
    what the two units' lookups show: two descriptions are convertible
    ([desc_conv]) when, under every substitution, each sequence of
    selections and applications ([desc_obs]) reaches on one side what it
    reaches on the other, with convertible types, δ-reducts, telescopes
    and units ([leaf_conv]).  Equal units denote convertible descriptions
    ([udenote_unit_eq]); the descriptions are compared by their lookups,
    never by their shape. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Structural.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas DescTyping Presup Paths LookupSound.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Observations *)

(** One step of a lookup: a selection, or an application to an argument. *)
Inductive desc_step : Set :=
(** The selection of the entry [y] *)
| ds_mem (y : String.string)
(** The application to the argument [N] *)
| ds_app (N : exp).

(** [desc_obs Θ Ξ Γ R s R1]: following the steps [s] from the description
    [R] reaches [R1], as [mdenote_mem] and [mdenote_app] would: a
    selection reads the entry in the module part and the description the
    entry denotes; an application takes an argument of the outermost
    parameter of the module part's telescope. *)
Inductive desc_obs (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : mdesc -> list desc_step -> mdesc -> Prop :=
(** No step: the description itself *)
| desc_obs_nil : forall R, desc_obs Θ Ξ Γ R nil R
(** A selection, then the rest *)
| desc_obs_mem : forall R Rm y Γy E rd R0 R1 s R2,
    mdesc_mod R = Some Rm ->
    mdesc_entry Rm y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (mdesc_entry_path Rm y) E R0 ->
    mdesc_read rd R0 = Some R1 ->
    desc_obs Θ Ξ Γ R1 s R2 ->
    desc_obs Θ Ξ Γ R (ds_mem y :: s) R2
(** An application to an argument of the outermost parameter, then the
    rest *)
| desc_obs_app : forall R T B T1 Srt N R1 s R2,
    mdesc_mod_tele R = Some T ->
    tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
    evaluated_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
    mdesc_at R N = Some R1 ->
    desc_obs Θ Ξ Γ R1 s R2 ->
    desc_obs Θ Ξ Γ R (ds_app N :: s) R2.

#[export]
Hint Constructors desc_obs : mctt.

(** [opt_rel P o o']: both [None], or both [Some] of related values. *)
Definition opt_rel {X : Type} (P : X -> X -> Prop) (o o' : option X) : Prop :=
  match o, o' with
  | None, None => True
  | Some x, Some x' => P x x'
  | _, _ => False
  end.

(** The outermost parameter of the module part of a description: what its
    next argument is checked against ([wf_me_app]). *)
Definition mdesc_head (R : mdesc) : option typ :=
  match mdesc_mod_tele R with
  | Some T => option_map fst (tele_view T)
  | None => None
  end.

(** [leaf_conv Θ Ξ Γ R R']: the two descriptions show the same, up to
    conversion in [Γ], to everything that reads a description: a member's
    type and δ-reduct ([wf_mem], [wf_exp_eq_mem_delta]), a module's
    outermost parameter ([wf_me_app]) and the unit its module part stands for
    ([wf_me_delta_sel]), and whether it is stored at an open frame
    ([frame_free_target]). *)
Record leaf_conv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R R' : mdesc) : Prop := mk_leaf_conv
  { (** The term parts are of one kind *)
    leaf_kind : mdesc_kind R = mdesc_kind R'
    (** Term parts on both sides or on neither, of convertible types, at
        the sort of their kind *)
  ; leaf_type : opt_rel (fun A A' => exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort (mdesc_kind R) Typeω@i)
                  (mdesc_type R) (mdesc_type R')
    (** δ-reducts on both sides or on neither, convertible at the left
        side's type *)
  ; leaf_reduct : forall A, mdesc_type R = Some A ->
      opt_rel (fun M M' => Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) (mdesc_reduct R) (mdesc_reduct R')
    (** Module parts on both sides or on neither, standing for equal
        units *)
  ; leaf_unit : opt_rel (fun Rm Rm' => Θ ⍮ Ξ ⍮ Γ ⊢ᵐ mdesc_unit Rm ≈ mdesc_unit Rm') (mdesc_mod R) (mdesc_mod R')
    (** Outermost parameters of the module parts on both sides or on
        neither, each a refinement of the other: an argument of one is an
        argument of the other ([wf_me_app]) *)
  ; leaf_head : opt_rel (fun B B' => Θ ⍮ Ξ ⍮ Γ ⊢ B ⊆ B' /\ Θ ⍮ Ξ ⍮ Γ ⊢ B' ⊆ B) (mdesc_head R) (mdesc_head R')
    (** Stored at an open frame on both sides or on neither *)
  ; leaf_frame : desc_reads_frame Ξ R <-> desc_reads_frame Ξ R'
    (** With no member of a type of levels on both sides or on neither
        ([wf_no_level_members]).  It is a field, not a consequence of the
        others: the judgment reads the tags of entries no lookup reads, an
        opaque definition of a local body, so it is compared where the two
        descriptions are built, entry by entry *)
  ; leaf_nl : Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R <-> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R' }.

(** [desc_conv Θ Ξ Γ R R']: under every substitution into [Γ], each
    sequence of steps reaches on each side what it reaches on the other,
    the two showing the same ([leaf_conv]). *)
Definition desc_conv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R R' : mdesc) : Prop :=
  forall Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    (forall s R1, desc_obs Θ Ξ Δ (mdesc_sub R σ) s R1 ->
       exists R1', desc_obs Θ Ξ Δ (mdesc_sub R' σ) s R1' /\ leaf_conv Θ Ξ Δ R1 R1') /\
    (forall s R1', desc_obs Θ Ξ Δ (mdesc_sub R' σ) s R1' ->
       exists R1, desc_obs Θ Ξ Δ (mdesc_sub R σ) s R1 /\ leaf_conv Θ Ξ Δ R1 R1').

(** ** Symmetry and Transitivity *)

(** An equation of types at the sort of a kind holds at a larger level. *)
Lemma kind_sort_eq_max : forall Θ Ξ Γ κ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@(max i j).
Proof. intros * H; destruct κ; cbn in *; [ exact (lift_exp_eq_max_left _ _ _ _ _ _ _ H) | exact H | exact H ]. Qed.

(** [opt_rel] the other way round, at the converse relation. *)
Lemma opt_rel_sym : forall {X} (P Q : X -> X -> Prop) o o', (forall x x', P x x' -> Q x' x) -> opt_rel P o o' -> opt_rel Q o' o.
Proof. intros * HPQ H; destruct o, o'; cbn in *; auto. Qed.

(** [opt_rel] chained, at a relation the two compose into. *)
Lemma opt_rel_trans : forall {X} (P Q S : X -> X -> Prop) o o' o'',
    (forall x x' x'', P x x' -> Q x' x'' -> S x x'') -> opt_rel P o o' -> opt_rel Q o' o'' -> opt_rel S o o''.
Proof. intros * HS H1 H2; destruct o, o', o''; cbn in *; eauto; contradiction. Qed.

(** [leaf_conv] the other way round. *)
Lemma leaf_conv_sym : forall Θ Ξ Γ R R', leaf_conv Θ Ξ Γ R R' -> leaf_conv Θ Ξ Γ R' R.
Proof.
  intros * [Hk Ht Hr Hu Hte Hf Hn]; constructor.
  - symmetry; exact Hk.
  - rewrite <- Hk; eapply opt_rel_sym; [| exact Ht ]; intros A A' (i & HA); exists i; apply wf_exp_eq_sym; exact HA.
  - intros A' HA'. destruct (mdesc_type R) as [A |] eqn:EA; [| rewrite HA' in Ht; destruct Ht ].
    rewrite HA' in Ht; cbn in Ht; destruct Ht as (i & HAA).
    specialize (Hr _ eq_refl); eapply opt_rel_sym; [| exact Hr ].
    intros M M' HM; apply wf_exp_eq_sym; exact (wf_exp_eq_conv_kind _ _ _ _ _ _ _ HM HAA).
  - eapply opt_rel_sym; [| exact Hu ]; intros; apply wf_me_sym; assumption.
  - eapply opt_rel_sym; [| exact Hte ]; intros B B' [H1 H2]; split; assumption.
  - symmetry; exact Hf.
  - symmetry; exact Hn.
Qed.

(** [leaf_conv] chained. *)
Lemma leaf_conv_trans : forall Θ Ξ Γ R R' R'', leaf_conv Θ Ξ Γ R R' -> leaf_conv Θ Ξ Γ R' R'' -> leaf_conv Θ Ξ Γ R R''.
Proof.
  intros * [Hk Ht Hr Hu Hte Hf Hn] [Hk' Ht' Hr' Hu' Hte' Hf' Hn']; constructor.
  - congruence.
  - rewrite <- Hk in Ht'; eapply opt_rel_trans; [| exact Ht | exact Ht' ].
    intros A A' A'' (i & H1) (j & H2); exists (max i j).
    eapply wf_exp_eq_trans; [ exact (kind_sort_eq_max _ _ _ _ _ _ _ j H1) |].
    rewrite Nat.max_comm; exact (kind_sort_eq_max _ _ _ _ _ _ _ i H2).
  - intros A HA. specialize (Hr _ HA). rewrite HA in Ht.
    destruct (mdesc_type R') as [A' |] eqn:EA'; [| destruct Ht ]; cbn in Ht; destruct Ht as (i & HAA).
    specialize (Hr' _ eq_refl).
    eapply opt_rel_trans; [| exact Hr | exact Hr' ].
    intros M M' M'' H1 H2; eapply wf_exp_eq_trans; [ exact H1 |].
    exact (wf_exp_eq_conv_kind _ _ _ _ _ _ _ H2 (wf_exp_eq_sym _ _ _ _ _ _ HAA)).
  - eapply opt_rel_trans; [| exact Hu | exact Hu' ]; intros x x' x'' H1 H2; exact (wf_me_trans _ _ _ _ _ _ H1 H2).
  - eapply opt_rel_trans; [| exact Hte | exact Hte' ]; intros B B' B'' [H1 H2] [H3 H4].
    split; eapply wf_subtyp_trans; eassumption.
  - rewrite Hf; exact Hf'.
  - rewrite Hn; exact Hn'.
Qed.

(** [desc_conv] the other way round. *)
Lemma desc_conv_sym : forall Θ Ξ Γ R R', desc_conv Θ Ξ Γ R R' -> desc_conv Θ Ξ Γ R' R.
Proof.
  intros * H Δ σ Hσ; destruct (H _ _ Hσ) as [H1 H2]; split.
  - intros s R1 Hs; destruct (H2 _ _ Hs) as (R0 & Hs0 & Hl); exists R0; split; [ exact Hs0 | exact (leaf_conv_sym _ _ _ _ _ Hl) ].
  - intros s R1 Hs; destruct (H1 _ _ Hs) as (R0 & Hs0 & Hl); exists R0; split; [ exact Hs0 | exact (leaf_conv_sym _ _ _ _ _ Hl) ].
Qed.

(** [desc_conv] chained. *)
Lemma desc_conv_trans : forall Θ Ξ Γ R R' R'', desc_conv Θ Ξ Γ R R' -> desc_conv Θ Ξ Γ R' R'' -> desc_conv Θ Ξ Γ R R''.
Proof.
  intros * H H' Δ σ Hσ; destruct (H _ _ Hσ) as [H1 H2]; destruct (H' _ _ Hσ) as [H1' H2']; split.
  - intros s R1 Hs; destruct (H1 _ _ Hs) as (R2 & Hs2 & Hl); destruct (H1' _ _ Hs2) as (R3 & Hs3 & Hl').
    exists R3; split; [ exact Hs3 | exact (leaf_conv_trans _ _ _ _ _ _ Hl Hl') ].
  - intros s R3 Hs; destruct (H2' _ _ Hs) as (R2 & Hs2 & Hl'); destruct (H2 _ _ Hs2) as (R1 & Hs1 & Hl).
    exists R1; split; [ exact Hs1 | exact (leaf_conv_trans _ _ _ _ _ _ Hl Hl') ].
Qed.

(** ** Observations, Composed and Substituted *)

(** Steps after steps. *)
Lemma desc_obs_concat : forall Θ Ξ Γ R s1 R1 s2 R2,
    desc_obs Θ Ξ Γ R s1 R1 -> desc_obs Θ Ξ Γ R1 s2 R2 -> desc_obs Θ Ξ Γ R (s1 ++ s2) R2.
Proof. intros * H1 H2; induction H1; cbn; [ exact H2 | econstructor; eauto | econstructor; eauto ]. Qed.

(** Steps after steps, taken apart. *)
Lemma desc_obs_concat_inv : forall Θ Ξ Γ s1 s2 R R2,
    desc_obs Θ Ξ Γ R (s1 ++ s2) R2 -> exists R1, desc_obs Θ Ξ Γ R s1 R1 /\ desc_obs Θ Ξ Γ R1 s2 R2.
Proof.
  induction s1 as [| st s1 IH]; intros * H; cbn in H; [ exists R; split; [ constructor | exact H ] |].
  inversion H; subst; match goal with Hs : desc_obs _ _ _ _ (s1 ++ s2) _ |- _ => destruct (IH _ _ _ Hs) as (Rx & Hx1 & Hx2) end;
    exists Rx; (split; [ econstructor; eassumption | exact Hx2 ]).
Qed.

(** In a well-formed global context the steps reach one description. *)
Lemma desc_obs_functional : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ R s R1, desc_obs Θ Ξ Γ R s R1 ->
    forall R2, desc_obs Θ Ξ Γ R s R2 -> R1 = R2.
Proof.
  intros Θ Ξ Hg; pose proof (proj1 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) as He.
  induction 1 as [R | R Rm y Γy E rd R0 R1 s R2 Hm Hen Hd Hr Hs IH | R T B T1 Srt N R1 s R2 Ht Hv HB HS HN Ha Hs IH];
    intros R3 H3; inversion H3; subst; [ reflexivity | |].
  - match goal with Hm' : mdesc_mod R = Some _, Hen' : mdesc_entry _ y = Some _, Hd' : edenote _ _ _ _ _ _,
                    Hr' : mdesc_read _ _ = Some _, Hs' : desc_obs _ _ _ _ s _ |- _ =>
      rewrite Hm in Hm'; injection Hm' as <-; rewrite Hen in Hen'; injection Hen' as <- <- <-;
      pose proof (He _ _ _ _ Hd _ Hd') as <-; rewrite Hr in Hr'; injection Hr' as <-; exact (IH _ Hs') end.
  - match goal with Ha' : mdesc_at R N = Some _, Hs' : desc_obs _ _ _ _ s _ |- _ =>
      rewrite Ha in Ha'; injection Ha' as <-; exact (IH _ Hs') end.
Qed.

(** The steps moved by a substitution: each argument substituted. *)
Definition desc_step_sub (st : desc_step) (σ : sub) : desc_step :=
  match st with
  | ds_mem y => ds_mem y
  | ds_app N => ds_app N[σ]
  end.

(** What a selection from a scoped description reads is scoped. *)
Lemma desc_sel_scoped : forall Θ Ξ, gctx_closed Θ Ξ ->
  forall Γ R Rm y Γy E rd R0 R1 m,
    slots_ok m Γ -> mdesc_scoped m R ->
    mdesc_mod R = Some Rm -> mdesc_entry Rm y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (mdesc_entry_path Rm y) E R0 -> mdesc_read rd R0 = Some R1 ->
    mdesc_scoped m R1.
Proof.
  intros Θ Ξ Hc; pose proof (mdenote_scoped_all _ _ Hc) as (_ & _ & Hse & _).
  intros * HS HR em ee de er.
  pose proof (mdesc_mod_scoped _ _ _ HR em) as HR0m.
  destruct (mdesc_entry_scoped _ _ _ _ _ _ HR0m ee) as (HΓy & HE & Hrd).
  eapply mdesc_read_scoped; [ exact Hrd | exact HΓy | | exact er ].
  eapply Hse; [ exact de | apply slots_ok_app; assumption | exact HE ].
Qed.

(** A selection moved by a substitution sending slots to slots or to
    their units: the same entry, read the same way. *)
Lemma desc_sel_sub : forall Θ Ξ, gctx_closed Θ Ξ ->
  forall Γ R Rm y Γy E rd R0 R1 m Δ σ,
    slots_ok m Γ -> mdesc_scoped m R ->
    mdesc_mod R = Some Rm -> mdesc_entry Rm y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (mdesc_entry_path Rm y) E R0 -> mdesc_read rd R0 = Some R1 ->
    sub_mod_compat σ Δ Γ ->
    exists Γy' E' rd' R0', mdesc_entry (mdesc_sub Rm σ) y = Some (Γy', E', rd') /\
      edenote Θ Ξ (Γy' ++ Δ) (mdesc_entry_path (mdesc_sub Rm σ) y) E' R0' /\
      mdesc_read rd' R0' = Some (mdesc_sub R1 σ).
Proof.
  intros Θ Ξ Hc; pose proof (mdenote_scoped_all _ _ Hc) as (_ & _ & Hse & _).
  pose proof (proj1 (proj2 (proj2 (mdenote_sub_all _ _ Hc)))) as Hes.
  intros * HS HR em ee de er Hσ.
  pose proof (mdesc_mod_scoped _ _ _ HR em) as HR0m.
  destruct (mdesc_entry_scoped _ _ _ _ _ _ HR0m ee) as (HΓy & HE & Hrd).
  destruct Rm as [r A0 om | Δ0 Φ0 Φx0 | Θ0 q0 T0 Φ0 Ns0 | Θd A0 M0 Rm0]; cbn in ee; try discriminate.
  - (* an open body *)
    destruct (mdesc_entry_open_reader Δ0 Φ0 _ _ _ _ _ ee) as (Φ' & -> & ->).
    do 4 eexists; split; [ apply mdesc_entry_sub_open; [ exact (proj2 (proj2 HR0m)) | exact ee ] | split ].
    + rewrite mdesc_entry_path_sub; eapply Hes; [ exact de | apply slots_ok_app; eassumption | exact HE |].
      apply sub_mod_compat_ext; exact Hσ.
    + cbn in er |- *.
      destruct (gm_fill Φ') as [τ |] eqn:Hf; cbn in er; [| discriminate ]; injection er as <-.
      destruct (gm_fill_sub Φ' (length Δ0) σ τ Hf) as (τ' & -> & Heq); cbn; f_equal.
      rewrite mdesc_up_sub; f_equal.
      rewrite length_app, (length_body_ctx _ (gm_fill_nopens _ _ Hf)), (mdesc_sub_sub_ext _ _ _ _ Heq);
        symmetry; apply mdesc_sub_sub_ext; reflexivity.
  - (* a closed body *)
    destruct HR0m as (HΘ0 & HU0 & HNs0).
    destruct (mdesc_entry_closed Θ0 q0 T0 Φ0 Ns0 _ _ _ _ HU0 ee) as (-> & HE0 & ->).
    assert (HR0 : mdesc_scoped 0 R0) by (eapply Hse; [ exact de | intros ? ? Hx; lia | exact HE0 ]).
    exists nil, E, (reader_sub (reader_closed Θ0 Ns0 (apps (a_mem (qname_mod q0) y) Ns0)) σ), R0.
    split; [ apply mdesc_entry_sub_closed; exact ee | split ].
    + rewrite mdesc_entry_path_sub; apply (edenote_closed_any _ _ _ _ _ _ σ HE0).
      rewrite <- (mdesc_closed_sub R0 σ HR0) at 1.
      eapply Hes; [ exact de | cbn; eassumption | eapply entry_sc_mono0; [ exact HE0 | lia ] |]; cbn; assumption.
    + cbn in er |- *.
      destruct (mdesc_ats_read R0 Ns0) as [R2 |] eqn:Ea; [| discriminate ]; injection er as <-.
      rewrite mdesc_up_sub, mdesc_named_sub,
        (mdesc_named_length Θ0 (tele_sub Θ0 σ) Ns0 (List.map (fun M => M[sb_qn (length Θ0) σ]) Ns0))
        by (rewrite ?length_tele_sub, ?length_map; reflexivity).
      rewrite <- (mdesc_closed_sub R0 (sb_qn (length Θ0) σ) HR0) at 1.
      rewrite (mdesc_ats_read_sub _ _ _ _ Ea); reflexivity.
Qed.

(** A sort of an evaluated kind is closed. *)
Lemma evaluated_sort_sub : forall S σ, evaluated_sort S -> S[σ] = S.
Proof. intros * []; reflexivity. Qed.

(** A typed term is scoped in its context. *)
Lemma wf_exp_scoped_of : forall Θ Ξ Γ M A, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> exp_scoped (length Γ) M.
Proof. intros * H; exact (proj1 (proj2 ((proj1 (proj2 wf_scoped)) _ _ _ _ _ H))). Qed.

(** Steps from a scoped description moved by a well-typed substitution:
    the steps moved reach the description reached, moved, which is
    scoped too. *)
Lemma desc_obs_sub : forall Θ Ξ Γ R s R1, desc_obs Θ Ξ Γ R s R1 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> mdesc_scoped (length Γ) R ->
    mdesc_scoped (length Γ) R1 /\
    forall Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      desc_obs Θ Ξ Δ (mdesc_sub R σ) (List.map (fun st => desc_step_sub st σ) s) (mdesc_sub R1 σ).
Proof.
  induction 1 as [R | R Rm y Γy E rd R0 R1 s R2 Hm Hen Hd Hr Hs IH | R T B T1 Srt N R1 s R2 Ht Hv HB HS HN Ha Hs IH];
    intros HΓ HR.
  - split; [ exact HR | intros; constructor ].
  - pose proof (wf_gctx_closed _ _ _ HΓ) as Hc.
    pose proof (slots_ok_ctx _ (wf_ctx_scoped _ _ _ HΓ)) as HSl.
    pose proof (desc_sel_scoped _ _ Hc _ _ _ _ _ _ _ _ _ _ HSl HR Hm Hen Hd Hr) as HR1.
    destruct (IH HΓ HR1) as [HR2 IH']; split; [ exact HR2 |].
    intros Δ σ Hσ.
    destruct (desc_sel_sub _ _ Hc _ _ _ _ _ _ _ _ _ _ Δ σ HSl HR Hm Hen Hd Hr (wf_sub_mod_compat _ _ _ _ _ Hσ))
      as (Γy' & E' & rd' & R0' & Hen' & Hd' & Hr').
    cbn [List.map desc_step_sub]; econstructor; [ exact (mdesc_mod_sub _ _ σ Hm) | exact Hen' | exact Hd' | exact Hr' |].
    exact (IH' _ _ Hσ).
  - assert (HR1 : mdesc_scoped (length Γ) R1) by (eapply mdesc_at_scoped; [ exact HR | exact (wf_exp_scoped_of _ _ _ _ _ HN) | exact Ha ]).
    destruct (IH HΓ HR1) as [HR2 IH']; split; [ exact HR2 |].
    intros Δ σ Hσ; cbn [List.map desc_step_sub].
    eapply desc_obs_app with (B := B[σ]) (Srt := Srt);
      [ exact (mdesc_mod_tele_sub _ _ σ _ HR Ht) | rewrite tele_view_sub, Hv; reflexivity
      | rewrite <- (evaluated_sort_sub Srt σ HS); exact (sub_preserves_exp _ _ _ _ _ _ _ HB Hσ) | exact HS
      | exact (sub_preserves_exp _ _ _ _ _ _ _ HN Hσ) | exact (mdesc_at_sub _ _ _ σ Ha) | exact (IH' _ _ Hσ) ].
Qed.

(** The identity substitution leaves a description as it is. *)
Lemma mdesc_sub_id : forall R, mdesc_sub R Id = R.
Proof.
  induction R as [r A om | Δ Φ Φx | Θ0 p T Φ Ns | Θ0 A M Rm IH]; cbn.
  - rewrite exp_sub_id; destruct om; cbn; [ rewrite exp_sub_id |]; reflexivity.
  - rewrite tele_sub_id, !gmod_sub_id_ext by (apply sb_qn_id_ext; reflexivity); reflexivity.
  - rewrite tele_sub_id; f_equal; rewrite <- List.map_id; apply List.map_ext; intros N.
    apply exp_sub_id_ext, sb_qn_id_ext; reflexivity.
  - rewrite tele_sub_id, IH, !exp_sub_id_ext by (apply sb_qn_id_ext; reflexivity); reflexivity.
Qed.

(** Steps of the left side are steps of the right side, at the identity. *)
Lemma desc_conv_obs_left : forall Θ Ξ Γ R R' s R1, ⊢ Θ ⍮ Ξ ⍮ Γ -> desc_conv Θ Ξ Γ R R' -> desc_obs Θ Ξ Γ R s R1 ->
    exists R1', desc_obs Θ Ξ Γ R' s R1' /\ leaf_conv Θ Ξ Γ R1 R1'.
Proof.
  intros * HΓ H Hs; destruct (H _ _ (wf_sub_id _ _ _ HΓ)) as [H1 _]; rewrite !mdesc_sub_id in H1; exact (H1 _ _ Hs).
Qed.

(** The descriptions two convertible ones reach by the same steps are
    convertible. *)
Lemma desc_conv_obs : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ R R' s R1 R1',
    ⊢ Θ ⍮ Ξ ⍮ Γ -> mdesc_scoped (length Γ) R -> mdesc_scoped (length Γ) R' ->
    desc_conv Θ Ξ Γ R R' -> desc_obs Θ Ξ Γ R s R1 -> desc_obs Θ Ξ Γ R' s R1' -> desc_conv Θ Ξ Γ R1 R1'.
Proof.
  intros Θ Ξ Hg * HΓ HR HR' H Hs Hs' Δ σ Hσ.
  destruct (desc_obs_sub _ _ _ _ _ _ Hs HΓ HR) as [_ Hsσ]; specialize (Hsσ _ _ Hσ).
  destruct (desc_obs_sub _ _ _ _ _ _ Hs' HΓ HR') as [_ Hsσ']; specialize (Hsσ' _ _ Hσ).
  destruct (H _ _ Hσ) as [H1 H2]; split.
  - intros s2 X HX.
    destruct (H1 _ _ (desc_obs_concat _ _ _ _ _ _ _ _ Hsσ HX)) as (X' & HX' & Hl).
    destruct (desc_obs_concat_inv _ _ _ _ _ _ _ HX') as (Y & HY & HY2).
    rewrite (desc_obs_functional _ _ Hg _ _ _ _ HY _ Hsσ') in HY2.
    exists X'; split; [ exact HY2 | exact Hl ].
  - intros s2 X' HX'.
    destruct (H2 _ _ (desc_obs_concat _ _ _ _ _ _ _ _ Hsσ' HX')) as (X & HX & Hl).
    destruct (desc_obs_concat_inv _ _ _ _ _ _ _ HX) as (Y & HY & HY2).
    rewrite (desc_obs_functional _ _ Hg _ _ _ _ HY _ Hsσ) in HY2.
    exists X; split; [ exact HY2 | exact Hl ].
Qed.

(** ** Reflexivity *)

(** The outermost parameter of a well-formed telescope of assumptions is
    a type. *)
Lemma tele_head_wf : forall Θ Ξ Γ X B X1, ⊢ Θ ⍮ Ξ ⍮ X ++ Γ -> all_assumptions X -> tele_view X = Some (B, X1) ->
    exists S, type_sort S /\ Θ ⍮ Ξ ⍮ Γ ⊢ B : S.
Proof.
  intros * HX Ha Hv; destruct (tele_view_ass _ _ _ Ha Hv) as [κ ->].
  rewrite <- List.app_assoc in HX; cbn [List.app] in HX.
  destruct (ctx_decomp_sort_kind (ctx_app_wf_right _ _ _ _ HX)) as [_ (S & HS & HB)].
  exists S; split; [ exact (sort_kind_type_sort _ _ HS) | exact HB ].
Qed.

(** A telescope of assumptions with no outermost parameter is empty. *)
Lemma tele_view_none_ass : forall X, all_assumptions X -> tele_view X = None -> X = nil.
Proof.
  intros X Ha Hv; unfold tele_view in Hv; destruct (rev X) as [| e R] eqn:Er.
  - apply (f_equal (@rev _)) in Er; rewrite rev_involutive in Er; exact Er.
  - assert (Ha' : all_assumptions (rev X)) by (apply List.Forall_rev; exact Ha).
    unfold all_assumptions in Ha'; rewrite Er in Ha'; inversion Ha' as [| ? ? (κ & A & Heq) _]; subst; cbn in Hv; discriminate Hv.
Qed.

(** The outermost parameter of a typed module description is a type. *)
Lemma desc_ok_head : forall Θ Ξ Γ Rm T B T1, desc_ok Θ Ξ Γ Rm -> mdesc_tele Rm = Some T -> tele_view T = Some (B, T1) ->
    exists S, type_sort S /\ Θ ⍮ Ξ ⍮ Γ ⊢ B : S.
Proof.
  intros * Hok Ht Hv.
  destruct Hok as [| Γ Δ Φw Φ l HΦ _ _ HaΔ _ _ _ _ _ _ | Γ Θ' T0 Φ Ns Θ0 Ξ0 p l _ _ _ HaT0 _ HT0 HΘ' Hargs HaΘ' _ _ _ |];
    cbn in Ht; try discriminate.
  - injection Ht as <-; eapply tele_head_wf; [ exact (ctx_app_wf_right _ _ _ _ HΦ) | exact HaΔ | exact Hv ].
  - destruct (Nat.leb (length Ns) (length T0)) eqn:Hle; [ injection Ht as <- | discriminate ].
    destruct (tele_view Θ') as [[B' Y1] |] eqn:Hv'.
    + destruct (tele_view_app_r (tele_sub (firstn (length T0 - length Ns) T0) (sb_of_list Id Ns)) _ _ _ Hv') as [Y1' Hv2].
      rewrite Hv in Hv2; injection Hv2 as <- _.
      exact (tele_head_wf _ _ _ _ _ _ HΘ' HaΘ' Hv').
    + (* no outside parameter: the stored telescope's next one, at the arguments *)
      pose proof (tele_view_none_ass _ HaΘ' Hv') as ->; rewrite List.app_nil_r in Hv; cbn [List.app] in Hargs, HΘ'.
      destruct Hargs as [T2 T3 -> Hl Ha Hs HT3 HN].
      rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_all, List.firstn_O,
        List.app_nil_r, tele_view_sub in Hv.
      destruct (tele_view T2) as [[B0 X1] |] eqn:Hv0; cbn in Hv; [ injection Hv as <- _ | discriminate ].
      destruct (proj1 (List.Forall_app _ _ _) HaT0) as [Ha2 _].
      destruct (tele_head_wf _ _ _ _ _ _ HT0 Ha2 Hv0) as (S & HS & HB0).
      assert (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ns : T3 ++ nil).
      { eapply wf_sub_of_list; [ exact Ha | rewrite List.app_nil_r; exact (ctx_app_wf_right _ _ _ _ HT0)
                               | exact (wf_sub_to_nil _ _ _ HΘ') | symmetry; exact Hl | exact HN ]. }
      rewrite List.app_nil_r in Hσ.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB0 Hσ) as HB.
      exists S; split; [ exact HS |]; inversion HS; subst; exact HB.
Qed.

(** A typed description, of a module part read where it is
    ([mdesc_canonical], [mdesc_xp]), shows the same as itself. *)
Lemma leaf_conv_refl : forall Θ Ξ Γ R, ⊢ Θ ⍮ Ξ ⍮ Γ -> desc_ok Θ Ξ Γ R ->
    (forall Rm, mdesc_mod R = Some Rm -> mdesc_canonical Θ Ξ Rm /\ mdesc_xp Θ Ξ Γ Rm) -> leaf_conv Θ Ξ Γ R R.
Proof.
  intros * HΓ Hok Hm; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (gctx_valid_syn _ _ Hg) as Hv.
  constructor.
  - reflexivity.
  - destruct (mdesc_type R) as [A |] eqn:Et; cbn; [| exact I ].
    destruct (desc_ok_ty_at _ _ _ _ _ Hok Et) as [i HA]; exists i; apply wf_exp_eq_refl; exact HA.
  - intros A Ht; destruct (mdesc_reduct R) as [M |] eqn:Er; cbn; [| exact I ].
    apply wf_exp_eq_refl; exact (proj2 (desc_ok_ty_sorted _ _ Hv _ _ _ Hok Ht) _ Er).
  - destruct (mdesc_mod R) as [Rm |] eqn:Em; cbn; [| exact I ].
    destruct (Hm _ eq_refl) as [Hc Hx].
    exact (proj1 (mdesc_unit_wf _ _ _ _ HΓ (desc_ok_mod _ _ Hg _ _ _ Hok Em) Hc (mdesc_mod_is_mod _ _ Em) Hx)).
  - unfold mdesc_head, mdesc_mod_tele.
    destruct (mdesc_mod R) as [Rm |] eqn:Em; cbn; [| exact I ].
    destruct (mdesc_tele Rm) as [T |] eqn:Et; cbn; [| exact I ].
    destruct (tele_view T) as [[B T1] |] eqn:Ev; cbn; [| exact I ].
    destruct (desc_ok_head _ _ _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok Em) Et Ev) as (S & HS & HB).
    split; eapply wf_subtyp_refl; [ exact HB | exact HS | apply wf_exp_eq_refl; exact HB
                                 | exact HB | exact HS | apply wf_exp_eq_refl; exact HB ].
  - reflexivity.
  - reflexivity.
Qed.

(** [desc_of Θ Ξ Γ R]: [R] is what a well-formed module expression
    denotes. *)
Definition desc_of (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R : mdesc) : Prop :=
  exists H, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H /\ mdenote Θ Ξ Γ H R.

(** What a well-formed module expression denotes, moved by a substitution. *)
Lemma desc_of_sub : forall Θ Ξ Γ R Δ σ, desc_of Θ Ξ Γ R -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ -> desc_of Θ Ξ Δ (mdesc_sub R σ).
Proof.
  intros * (H & HH & Hm) Hσ; exists H[σ]ᵐ.
  split; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hσ) | exact (wf_sub_mdenote _ _ _ _ _ _ _ _ HH Hm Hσ) ].
Qed.

(** What a well-formed module expression denotes is typed, read where it
    is, and scoped. *)
Lemma desc_of_props : forall Θ Ξ Γ R, desc_of Θ Ξ Γ R ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ desc_ok Θ Ξ Γ R /\ mdesc_canonical Θ Ξ R /\ mdesc_xp Θ Ξ Γ R /\ mdesc_scoped (length Γ) R.
Proof.
  intros * (H & HH & Hm); pose proof (presup_modexp_eq_ctx HH) as HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  split; [ exact HΓ | split; [| split; [| split ] ] ].
  - exact (proj1 (proj2 ((proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed))))))) _ _ _ _ _ HH (gctx_valid_syn _ _ Hg))) _ Hm).
  - exact (mdenote_canon _ _ _ _ _ Hg Hm).
  - exact (wf_mdenote_xp _ _ _ _ _ _ HH Hm).
  - exact (wf_mdenote_scoped _ _ _ _ _ _ HH Hm).
Qed.

(** Every step from what a well-formed module expression denotes reaches
    a description that shows the same as itself. *)
Lemma desc_obs_leaf_refl : forall Θ Ξ Γ R s R1, desc_obs Θ Ξ Γ R s R1 -> desc_of Θ Ξ Γ R -> leaf_conv Θ Ξ Γ R1 R1.
Proof.
  induction 1 as [R | R Rm y Γy E rd R0 R1 s R2 Hm Hen Hd Hr Hs IH | R T B T1 Srt N R1 s R2 Ht Hv HB HS HN Ha Hs IH];
    intros HR; destruct (desc_of_props _ _ _ _ HR) as (HΓ & Hok & Hc & Hx & _);
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (gctx_valid_syn _ _ Hg) as Hvs.
  - apply leaf_conv_refl; [ exact HΓ | exact Hok | intros Rm Hm ].
    split; [ exact (mdesc_canonical_mod _ _ _ _ Hc Hm) | exact (mdesc_xp_mod _ _ _ _ _ Hx Hm) ].
  - pose proof (desc_ok_sel _ _ Hg Hvs _ _ _ _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok Hm) Hen Hd Hr) as Hok1.
    destruct (mdesc_mod R1) as [Rm1 |] eqn:Em1.
    + (* a module: what the selection denotes *)
      apply IH; destruct HR as (H & HH & HmH).
      assert (Hm1 : mdenote Θ Ξ Γ (me_mem H y) R1) by (econstructor; eassumption).
      destruct (desc_ok_tele _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok1 Em1) (mdesc_mod_is_mod _ _ Em1)) as [T1 HT1].
      assert (Ht1 : mdesc_mod_tele R1 = Some T1) by (unfold mdesc_mod_tele; rewrite Em1; exact HT1).
      exists (me_mem H y); split; [ eapply wf_me_mem; eassumption | exact Hm1 ].
    + (* a term: no further step *)
      inversion Hs; subst; [| congruence | unfold mdesc_mod_tele in *; rewrite Em1 in *; discriminate ].
      apply leaf_conv_refl; [ exact HΓ | exact Hok1 | intros; congruence ].
  - apply IH; destruct HR as (H & HH & HmH).
    exists (me_app H N); split; [| econstructor; eassumption ].
    eapply wf_me_app; try eassumption; apply wf_exp_eq_refl; exact HN.
Qed.

(** What a well-formed module expression denotes is convertible to
    itself. *)
Lemma desc_conv_refl : forall Θ Ξ Γ R, desc_of Θ Ξ Γ R -> desc_conv Θ Ξ Γ R R.
Proof.
  intros * HR Δ σ Hσ; pose proof (desc_of_sub _ _ _ _ _ _ HR Hσ) as HRσ.
  split; intros s R1 Hs; exists R1; split; try exact Hs; exact (desc_obs_leaf_refl _ _ _ _ _ _ Hs HRσ).
Qed.
