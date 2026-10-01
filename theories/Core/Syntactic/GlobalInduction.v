(** * Induction over the Age of a Global Context

    What the two semantic models share about the global rules.  Names are
    absolute and closed entries are stored closed, so a judgment never has to
    be *moved* to another global context: it only has to be *read* in a larger
    one ([gc_ext]: everything it resolves resolves the same way there).  The
    models are not monotone under such an extension (both break at Π), so the
    semantic statement is the Kripke one: a derivation in [Θ1 ⍮ Ξ1] is valid in
    every well-formed extension [Θ2 ⍮ Ξ2] in which what [Θ1 ⍮ Ξ1] resolves is
    valid.  The models prove that ([vread] below); this file proves, once for
    both, that every well-formed context is then valid in itself
    ([global_induction]).

    By age: every item is typed where it was inserted, in a context of older
    items only — a member in its frame as it stood before it ([ins_typed]), a
    member of a filed unit in the unit truncated to it ([closable_file]), a
    parameter in its frame truncated to the parameters before it — and that
    context is extended by the final one. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Extensions *)

Lemma gc_ext_frame : forall Θ Ξ1 Ξ2 U1 U2,
    gc_ext Θ Ξ1 Θ Ξ2 -> length Ξ1 = length Ξ2 ->
    (forall ip E, gu_mod U1 ∋ ip ⇒ E -> gu_mod U2 ∋ ip ⇒ E) ->
    (forall k T, List.nth_error (gu_ptys U1) k = Some T -> List.nth_error (gu_ptys U2) k = Some T) ->
    gc_ext Θ (U1 :: Ξ1) Θ (U2 :: Ξ2).
Proof.
  intros * [Hr Hp] Hlen HU HP; split.
  - intros * Hl; inversion Hl; subst; [| econstructor; eassumption ].
    match goal with H : gs_frame _ _ = Some _ |- _ =>
      destruct (gs_frame_cons_inv _ _ _ _ H) as [[-> ->] | [Hlt Hn]] end.
    + eapply gcl_rel; [ rewrite Hlen; apply gs_frame_top | auto ].
    + assert (Hl0 : Θ ⍮ Ξ1 ∋ᵍ p_rel n ip ⇒ ge_def b pv A B) by (econstructor; eassumption).
      apply Hr in Hl0; inversion Hl0; subst.
      eapply gcl_rel; [ apply gs_frame_push_some; eassumption | eassumption ].
  - unfold gs_param; intros * Hp'.
    destruct (gs_frame (U1 :: Ξ1) (lp_mod lp)) as [V |] eqn:Hn; [| discriminate ].
    destruct (gs_frame_cons_inv _ _ _ _ Hn) as [[Hm ->] | [Hlt Hn']].
    + rewrite Hm, Hlen, gs_frame_top; auto.
    + assert (Hq : gs_param Ξ1 lp = Some T) by (unfold gs_param; rewrite Hn'; exact Hp').
      apply Hp in Hq; unfold gs_param in Hq.
      destruct (gs_frame Ξ2 (lp_mod lp)) as [W |] eqn:Hn2; [| discriminate ].
      rewrite (gs_frame_push_some _ _ _ _ Hn2); exact Hq.
Qed.

(** A frame truncated to its outer parameters, with no member yet, is extended
    by the frame. *)
Lemma gc_ext_trunc : forall Θ Ξ Pa Pb X Φ,
    (forall k T, List.nth_error (ctx_ptys (length Ξ) (Pa ++ Pb)) k = Some T -> List.nth_error X k = Some T) ->
    gc_ext Θ (gu_mk Pb (ctx_ptys (length Ξ) Pb) ⋄ :: Ξ) Θ (gu_mk (Pa ++ Pb) X Φ :: Ξ).
Proof.
  intros * HX; apply gc_ext_frame; [ apply gc_ext_refl | reflexivity | cbn; intros * H; inversion H |].
  intros * Hk; cbn in *; apply HX.
  destruct (ctx_ptys_app (length Ξ) Pa Pb) as [ps ->].
  rewrite List.nth_error_app1; [ exact Hk | apply List.nth_error_Some; congruence ].
Qed.

(** ** 2. A Telescope Read as Parameters *)

(** The binding [D] over the telescope [Pb], read with [Pb] as the parameters
    of a frame at level [length Ξ] whose types extend those of [Pb], is a type
    there. *)
Lemma tele_param_typ : forall Θ Ξ U Pb D i,
    ⊢ Θ ⍮ U :: Ξ ⍮ ⋅ ->
    (forall k T, List.nth_error (ctx_ptys (length Ξ) Pb) k = Some T -> List.nth_error (gu_ptys U) k = Some T) ->
    Θ ⍮ Ξ ⍮ Pb ⊢ D : Type@i ->
    Θ ⍮ U :: Ξ ⍮ ⋅ ⊢ D[sb_params (length Ξ) (length Pb)] : Type@i.
Proof.
  intros * Hb HX HD.
  destruct (push_preserves_wf Θ U Ξ ltac:(eapply ctx_wf_gctx; eassumption)) as (_ & He & _).
  pose proof (He _ _ _ HD) as HD'.
  change (Type@i) with (Type@i[sb_params (length Ξ) (length Pb)]).
  eapply sub_preserves_exp; [ exact HD' |].
  econstructor; [ assumption | eapply presup_exp_ctx; exact HD' |].
  intros x B Hlk; econstructor; [ assumption |].
  unfold gs_param; cbn [lp_mod lp_param]; rewrite gs_frame_top.
  apply HX, ctx_ptys_lookup; assumption.
Qed.

(** ** 3. The induction, over an abstract model *)

Section Induction.
  (** [V Θ Ξ A M]: [M] is a valid term of type [A] at [⋅] in [Θ ⍮ Ξ]. *)
  Variable V : gdeps -> gstack -> exp -> exp -> Prop.

  Definition vtyp (Θ : gdeps) (Ξ : gstack) (X : exp) : Prop := exists i, V Θ Ξ (Type@i) X.

  Definition gent (Θ : gdeps) (Ξ : gstack) (A : exp) (B : option exp) : Prop :=
    vtyp Θ Ξ A /\ (forall M, B = Some M -> V Θ Ξ A M).

  (** What [Θ1 ⍮ Ξ1] resolves, and its parameters' types, are valid in
      [Θ2 ⍮ Ξ2]. *)
  Definition SG Θ1 Ξ1 Θ2 Ξ2 : Prop :=
    forall r b pv A B, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ ge_def b pv A B -> gent Θ2 Ξ2 A B.

  Definition SP (Θ1 : gdeps) (Ξ1 : gstack) Θ2 Ξ2 : Prop :=
    forall lp T, gs_param Ξ1 lp = Some T -> vtyp Θ2 Ξ2 T.

  (** The fundamental theorem of the model, in its Kripke form. *)
  Hypothesis vread : forall Θ1 Ξ1 Θ2 Ξ2 A M,
      Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
      gc_ext Θ1 Ξ1 Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
      SG Θ1 Ξ1 Θ2 Ξ2 -> SP Θ1 Ξ1 Θ2 Ξ2 ->
      V Θ2 Ξ2 A M.

  Definition Good Θ Ξ : Prop :=
    forall Θ2 Ξ2, gc_ext Θ Ξ Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 -> SG Θ Ξ Θ2 Ξ2 /\ SP Θ Ξ Θ2 Ξ2.

  Lemma vread_entry : forall Θ1 Ξ1 Θ2 Ξ2 A B,
      gc_ext Θ1 Ξ1 Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
      SG Θ1 Ξ1 Θ2 Ξ2 -> SP Θ1 Ξ1 Θ2 Ξ2 ->
      (exists i, Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ A : Type@i) ->
      (forall M, B = Some M -> Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A) ->
      gent Θ2 Ξ2 A B.
  Proof.
    intros * He Hg HS HP [i HT] HM; split.
    - exists i; exact (vread _ _ _ _ _ _ HT He Hg HS HP).
    - intros M HB; exact (vread _ _ _ _ _ _ (HM _ HB) He Hg HS HP).
  Qed.

  (** What a frame pushed on top adds is only its own members and
      parameters. *)
  Lemma frame_outer : forall Θ U Ξ Θ2 Ξ2,
      Good Θ Ξ -> gc_ext Θ (U :: Ξ) Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
      (forall r b pv A B, Θ ⍮ U :: Ξ ∋ᵍ r ⇒ ge_def b pv A B -> p_qual r <> qu_rel (length Ξ) ->
         gent Θ2 Ξ2 A B) /\
      (forall lp T, gs_param (U :: Ξ) lp = Some T -> lp_mod lp <> length Ξ -> vtyp Θ2 Ξ2 T).
  Proof.
    intros * HG He Hg.
    destruct (HG _ _ (gc_ext_trans _ _ _ _ _ _ (gc_ext_push1 _ U _) He) Hg) as [HS HP].
    split.
    - intros * Hl Hr; eapply HS, gc_lookup_pop; eassumption.
    - intros * Hp Hm; eapply HP, gs_param_pop; eassumption.
  Qed.

  Lemma good_cons : forall Θ Ξ P Φ,
      wf_gstack Θ Ξ -> Θ ⍮ Ξ ⍮ P ⊢m Φ -> Good Θ Ξ -> Good Θ (gs_push Ξ P Φ).
  Proof.
    intros * HΞ HΦ HG Θ2 Ξ2 He Hg2.
    set (L := length Ξ).
    assert (HP0 : ⊢ Θ ⍮ Ξ ⍮ P) by (eapply wf_gmod_ctx; eassumption).
    destruct (frame_outer _ _ _ _ _ HG He Hg2) as [Ho1 Ho2].
    (* the parameters, outermost first *)
    assert (Hpar : forall Pb Pa, P = Pa ++ Pb -> forall j T,
              List.nth_error (ctx_ptys L Pb) j = Some T -> vtyp Θ2 Ξ2 T).
    { induction Pb as [| D Pb IH]; intros Pa HPe j T Hj; [ destruct j; discriminate |].
      assert (HPe' : P = (Pa ++ D :: nil) ++ Pb) by (rewrite <- List.app_assoc; exact HPe).
      destruct (Nat.lt_ge_cases j (length Pb)).
      - rewrite ctx_ptys_nth_old in Hj by assumption; exact (IH _ HPe' _ _ Hj).
      - assert (Hjl : j < length (ctx_ptys L (D :: Pb))) by (apply List.nth_error_Some; congruence).
        rewrite ctx_ptys_length in Hjl; cbn in Hjl; assert (j = length Pb) as -> by lia.
        rewrite ctx_ptys_nth_last in Hj; injection Hj as <-.
        assert (HDb : ⊢ Θ ⍮ Ξ ⍮ Pb ▹ D) by (rewrite HPe in HP0; eapply ctx_app_wf_right; exact HP0).
        destruct (ctx_decomp_right HDb) as [i HD].
        set (Ut := gu_mk Pb (ctx_ptys L Pb) ⋄).
        assert (HgB : ⊢g Θ ⍮ Ut :: Ξ)
          by (apply wf_gctx_intro, wf_gstack_cons;
              [ assumption | constructor; [ constructor; eapply presup_exp_ctx; eassumption | reflexivity ] ]).
        assert (Het : gc_ext Θ (Ut :: Ξ) Θ (gs_push Ξ P Φ)).
        { pose proof (gc_ext_trunc Θ Ξ (Pa ++ D :: nil) Pb (ctx_ptys L P) Φ) as Ht; rewrite <- HPe' in Ht; apply Ht; intros; assumption. }
        pose proof (gc_ext_trans _ _ _ _ _ _ Het He) as He'.
        destruct (frame_outer _ _ _ _ _ HG He' Hg2) as [Hq1 Hq2].
        exists i; eapply vread; [ apply (tele_param_typ _ _ Ut Pb); [ constructor; exact HgB | intros; assumption | exact HD ]
                                | exact He' | exact Hg2 | |].
        + intros r * Hl.
          destruct r as [[fp | m] ip]; [| destruct (Nat.eq_dec m L) as [-> | Hm] ].
          2:{ apply gc_lookup_top in Hl; inversion Hl. }
          all: eapply Hq1; [ eassumption | cbn; subst L; congruence ].
        + intros [m k] T' Hp.
          destruct (Nat.eq_dec m L) as [-> | Hm]; [| eapply Hq2; [ eassumption | cbn; subst L; congruence ] ].
          apply gs_param_top in Hp; cbn [gu_ptys] in Hp.
          exact (IH _ HPe' _ _ Hp). }
    assert (HparF : forall j T, List.nth_error (ctx_ptys L P) j = Some T -> vtyp Θ2 Ξ2 T)
      by (intros; eapply (Hpar P nil eq_refl); eassumption).
    assert (HSP : forall lp T, gs_param (gs_push Ξ P Φ) lp = Some T -> vtyp Θ2 Ξ2 T).
    { intros [m k] T Hp; destruct (Nat.eq_dec m L) as [-> | Hm].
      - apply gs_param_top in Hp; exact (HparF _ _ Hp).
      - eapply Ho2; [ eassumption | cbn; subst L; congruence ]. }
    (* the members, in insertion order *)
    assert (Hins : ins_typed Θ Ξ P Φ)
      by (destruct presup_global as (_ & _ & _ & _ & _ & Hm & _); exact (Hm _ _ _ _ HΦ)).
    assert (Hmem : forall n Φq ip b pv A B, gm_count Φq < n ->
               gm_ins Φ Φq ip (ge_def b pv A B) -> gent Θ2 Ξ2 A B).
    { induction n as [| n IH]; intros * Hlt Hi; [ lia |].
      pose proof (gm_ins_prefix _ _ _ _ Hi) as Hpq.
      assert (Hgq : ⊢g Θ ⍮ gs_push Ξ P Φq)
        by (eapply ctx_wf_gctx, wf_frame_ctx, wf_gmod_prefix; eassumption).
      assert (Heq : gc_ext Θ (gs_push Ξ P Φq) Θ2 Ξ2)
        by (eapply gc_ext_trans; [ apply gc_ext_grow; exact Hpq | exact He ]).
      destruct (frame_outer _ _ _ _ _ HG Heq Hg2) as [Hq1 Hq2].
      destruct (Hins _ _ _ _ _ _ Hi) as [HT HM].
      apply (vread_entry _ _ _ _ _ _ Heq Hg2); [| | exact HT | exact HM ].
      - intros r * Hl.
        destruct r as [[fp | m] ip0]; [| destruct (Nat.eq_dec m L) as [-> | Hm] ].
        2:{ apply gc_lookup_top in Hl; cbn in Hl.
            destruct (gm_lookup_ins _ _ _ Hl) as [Φr Hir].
            pose proof (gm_ins_count _ _ _ _ Hir).
            eapply IH; [| exact (gm_prefix_ins _ _ _ _ _ Hpq Hir) ]; lia. }
        all: eapply Hq1; [ eassumption | cbn; subst L; congruence ].
      - intros [m k] T Hp; destruct (Nat.eq_dec m L) as [-> | Hm].
        + apply gs_param_top in Hp; exact (HparF _ _ Hp).
        + eapply Hq2; [ eassumption | cbn; subst L; congruence ]. }
    split; [| exact HSP ].
    intros r * Hl.
    destruct r as [[fp | m] ip]; [| destruct (Nat.eq_dec m L) as [-> | Hm] ].
    2:{ apply gc_lookup_top in Hl; cbn in Hl.
        destruct (gm_lookup_ins _ _ _ Hl) as [Φr Hir].
        eapply (Hmem (S (gm_count Φr)) Φr); [ lia | exact Hir ]. }
    all: eapply Ho1; [ eassumption | cbn; subst L; congruence ].
  Qed.

  Lemma gds_lookup_single : forall fp V0 Θ fq W,
      gds_lookup (((fp, V0) :: nil) :: Θ) fq = Some W ->
      (fq = fp /\ W = V0) \/ gds_lookup Θ fq = Some W.
  Proof.
    intros * H; unfold gds_lookup, gd_lookup, path_beq in *; cbn in H.
    destruct (path_eq_dec fq fp) as [-> |]; [ left; injection H as <-; auto | right; exact H ].
  Qed.

  Lemma gds_lookup_single_here : forall fp V0 Θ, gds_lookup (((fp, V0) :: nil) :: Θ) fp = Some V0.
  Proof.
    intros; unfold gds_lookup, gd_lookup, path_beq; cbn.
    destruct (path_eq_dec fp fp); [ reflexivity | contradiction ].
  Qed.

  Lemma good_level : forall Θ0 d,
      wf_gdeps Θ0 -> wf_gdep Θ0 d -> Good Θ0 nil -> Good (d :: Θ0) nil.
  Proof.
    intros * HΘ Hd HG Θ2 Ξ2 He Hg2.
    pose proof (wf_gdep_fresh _ _ Hd) as Hfr.
    assert (Hgrow : Θ0 ⊑ d :: Θ0)
      by (unfold gds_sub; intros; apply gds_lookup_level; assumption).
    assert (He0 : gc_ext Θ0 nil Θ2 Ξ2) by (eapply gc_ext_trans; [ apply gc_ext_levels; exact Hgrow | exact He ]).
    destruct (HG _ _ He0 Hg2) as [HS0 _].
    split; [| unfold gs_param, gs_frame; intros [m k] T Hp; cbn in Hp; destruct m; discriminate ].
    intros r * Hl.
    inversion Hl as [? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? Hf Hm]; subst;
      [ unfold gs_frame in Hn; cbn in Hn; destruct n; discriminate |].
    pose proof Hf as Hl'; unfold gds_lookup in Hl'; cbn [List.concat] in Hl'.
    apply gd_lookup_app_inv in Hl' as [Hl' | Hl'].
    2: { eapply HS0; econstructor; [ exact Hl' | eassumption ]. }
    apply gd_lookup_in in Hl' as Hin.
    pose proof (Hfr _ _ Hin) as Hfp.
    destruct presup_global as (_ & _ & _ & _ & _ & _ & _ & Hfd & _).
    destruct (Hfd _ _ Hd _ _ Hin) as ([PU X ΦU] & -> & HUw & HUi).
    inversion HUw as [? ? ? HU _]; subst; cbn [gu_params gu_mod gu_close] in *.
    assert (Hmem : forall n Φq ip b pv A B, gm_count Φq < n -> gm_ins ΦU Φq ip (ge_def b pv A B) ->
               gent Θ2 Ξ2 (ctx_pi PU A[close 0 (p_abs fp nil) (length PU)]ᵐ)
                 (option_map (fun M => ctx_fn PU M[close 0 (p_abs fp nil) (length PU)]ᵐ) B)).
    { induction n as [| n IH]; intros * Hlt Hi; [ lia |].
      pose proof (gm_ins_prefix _ _ _ _ Hi) as Hpq.
      set (Θq := ((fp, gu_mk PU nil (gm_close 0 (p_abs fp nil) PU Φq)) :: nil) :: Θ0).
      assert (HwUq : Θ0 ⍮ nil ⍮ PU ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
      assert (Hgq : ⊢g Θq ⍮ nil).
      { apply wf_gctx_intro, wf_gstack_nil, wf_gdeps_cons; [ assumption |].
        apply (wf_gdep_cons Θ0 nil (gu_mk PU (ctx_ptys 0 PU) Φq));
          [ apply wf_gdep_nil; assumption | constructor; [ exact HwUq | reflexivity ] | exact Hfp
          | unfold gd_fresh; cbn; tauto ]. }
      assert (Hgq' : Θ0 ⊑ Θq).
      { unfold gds_sub; intros; apply gds_lookup_level; [| assumption ].
        intros fq' V' [[= <- <-] | []]; exact Hfp. }
      assert (Hlq : gc_ext Θq nil Θ2 Ξ2).
      { eapply gc_ext_trans; [| exact He ]; split; [| auto ].
        intros * H; inversion H as [? ? ? ? ? ? ? Hn' Hm' | ? ? ? ? ? ? ? Hf' Hm']; subst;
          [ unfold gs_frame in Hn'; cbn in Hn'; destruct n0; discriminate |].
        destruct (gds_lookup_single _ _ _ _ _ Hf') as [[-> ->] | Hb].
        - eapply gcl_abs; [ exact Hf | cbn in *; eapply gm_prefix_lookup; [ apply gm_close_prefix, Hpq | exact Hm' ] ].
        - econstructor; [ apply Hgrow; exact Hb | eassumption ]. }
      destruct (closable_file Θ0 Θq fp PU ΦU Φq HU HUi (gds_lookup_single_here _ _ _) Hgq'
                  ltac:(constructor; exact Hgq) (S (gm_count Φq)) Φq _ _ _ _ _ ltac:(lia) Hi
                  (gmp_refl _)) as [[i HT] HM].
      apply (vread_entry _ _ _ _ _ _ Hlq Hg2).
      - intros r * H; inversion H as [? ? ? ? ? ? ? Hn' Hm' | ? ? ? ? ? ? ? Hf' Hm']; subst;
          [ unfold gs_frame in Hn'; cbn in Hn'; destruct n0; discriminate |].
        destruct (gds_lookup_single _ _ _ _ _ Hf') as [[-> ->] | Hb].
        + cbn [gu_mod] in Hm'.
          destruct (gm_close_lookup_inv _ _ _ _ _ _ Hm' _ eq_refl) as (bq & pvq & Aq & Bq & Hm0 & Heq).
          injection Heq as -> -> -> ->.
          destruct (gm_lookup_ins _ _ _ Hm0) as [Φr Hir].
          pose proof (gm_ins_count _ _ _ _ Hir).
          eapply (IH Φr); [ lia | exact (gm_prefix_ins _ _ _ _ _ Hpq Hir) ].
        + eapply HS0; econstructor; eassumption.
      - unfold gs_param, gs_frame; intros [m k] T Hp; cbn in Hp; destruct m; discriminate.
      - eapply ctx_pi_wf0; eassumption.
      - intros M' HB; match type of HB with option_map _ ?X = _ => destruct X as [M1 |] end; cbn in HB; inversion HB; subst.
        eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ]. }
    cbn [gu_mod] in Hm.
    destruct (gm_close_lookup_inv _ _ _ _ _ _ Hm _ eq_refl) as (b0 & pv0 & A0 & B0 & Hm0 & Heq).
    injection Heq as -> -> -> ->.
    destruct (gm_lookup_ins _ _ _ Hm0) as [Φq Hi].
    exact (Hmem (S (gm_count Φq)) Φq _ _ _ _ _ ltac:(lia) Hi).
  Qed.

  Lemma good_deps : forall Θ, wf_gdeps Θ -> Good Θ nil.
  Proof.
    induction 1 as [| Θ d HΘ IH Hd].
    - intros Θ2 Ξ2 He _; split.
      + intros r * Hl; inversion Hl; subst; [ unfold gs_frame in *; cbn in *; destruct n; discriminate | discriminate ].
      + unfold gs_param, gs_frame; intros [m k] T Hp; cbn in Hp; destruct m; discriminate.
    - apply good_level; assumption.
  Qed.

  Lemma good_stack : forall Ξ Θ, wf_gstack Θ Ξ -> Good Θ Ξ.
  Proof.
    induction Ξ as [| U Ξ IH]; intros * H; inversion H; subst.
    - apply good_deps; assumption.
    - match goal with Hu : _ ⍮ _ ⊢u _ |- _ => inversion Hu as [? ? ? Hm Hpt]; subst end.
      destruct U as [P X Φ]; cbn in Hpt, Hm; subst X.
      apply good_cons; auto.
  Qed.

  (** Every resolved global's type and body, and every parameter's type, is
      valid at [⋅] in the context itself. *)
  Theorem global_induction : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> SG Θ Ξ Θ Ξ /\ SP Θ Ξ Θ Ξ.
  Proof.
    intros * Hg; exact (good_stack _ _ (wf_gctx_stack _ _ Hg) _ _ (gc_ext_refl _ _) Hg).
  Qed.
End Induction.
