(** * Leaf Conversion of Module Descriptions

    Two descriptions show the same, up to conversion, to everything that
    reads a description ([leaf_conv]): a member's type and δ-reduct, a
    module's outermost parameter and unit, the frame it is stored at and
    its members of a type of levels.  [leaf_conv] is symmetric and
    transitive.  The file also defines the steps of a lookup ([desc_obs])
    and what a well-formed module expression denotes ([desc_of]), with
    the facts about typed descriptions that [ModexpConversion] uses. *)

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

(** ** Substitution *)

(** A sort of an evaluated kind is closed. *)
Lemma evaluated_sort_sub : forall S σ, evaluated_sort S -> S[σ] = S.
Proof. intros * []; reflexivity. Qed.

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

(** ** Typed Descriptions *)

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

(** [desc_of Θ Ξ Γ R]: [R] is what a well-formed module expression
    denotes. *)
Definition desc_of (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R : mdesc) : Prop :=
  exists H, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H /\ mdenote Θ Ξ Γ H R.

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
