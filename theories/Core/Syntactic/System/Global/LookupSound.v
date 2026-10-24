(** * Lookup is Sound

    What a well-formed module expression denotes ([mdenote], [Γ ⊢ H ⇝ R]) is
    what a unit equal to it describes: [H] is equal to a unit [K], a filed
    module at arguments [P N⃗] or a literal [(U)], and [K] denotes the same
    module part. *)

From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export MemberWf.
From Mctt.Core.Syntactic.System Require Export Lemmas.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Parts of a Well-formed Unit

    The parts of a well-formed unit ([unit_full]) are invariant under moving
    parameters between the unit and the context, so a well-formed unit stays
    well formed when abstracted over the context's top or given its
    outermost parameter. *)

(** A unit of the context after [Δ], abstracted over [Δ]. *)
Lemma unit_full_abs : forall Θ Ξ Γ Δ U, unit_full Θ Ξ (Δ ++ Γ) U -> tele_ass Δ -> unit_full Θ Ξ Γ (gunit_abs Δ U).
Proof.
  intros * HU HaΔ; destruct U as [Δy [[] Φ | E]]; cbn in HU |- *; try contradiction.
  - destruct HU as (Φx & lv & Hx & HC & Hd & Ho & Ha & Hs & Hsx & Hn).
    exists Φx, lv; rewrite <- !app_assoc.
    refine (conj Hx (conj HC (conj Hd (conj Ho (conj _ (conj Hs (conj Hsx Hn))))))).
    apply List.Forall_app; split; assumption.
  - destruct HU as (HΔ & Ha & HE); rewrite <- !app_assoc; repeat split; try assumption.
    apply List.Forall_app; split; assumption.
Qed.

Lemma unit_full_of_eq : forall Θ Ξ Γ U U',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> unit_full Θ Ξ Γ U /\ unit_full Θ Ξ Γ U'.
Proof.
  induction 1; cbn; try solve [ intuition eauto ].
  - match goal with Hb : body_xp _ _ _ _ Φx |- _ => pose proof (body_xp_nopens _ _ _ _ _ Hb) as Hnp end.
    match goal with Hsx : body_shape Φx Φx' |- _ =>
      rename Hsx into Hsx0;
      destruct (body_shape_fill _ _ Hnp Hsx0) as [Hf Hf'];
      destruct (body_shape_refl _ _ Hsx0) as (Hsx1 & Hsx2 & _) end.
    match goal with Hb1 : body_xp _ _ _ Φ Φx, Hb2 : body_xp _ _ _ Φ' Φx' |- _ =>
      pose proof (body_shape_of_xp _ _ _ _ _ Hb1 Hsx1) as Hs1; pose proof (body_shape_of_xp _ _ _ _ _ Hb2 Hsx2) as Hs2;
      assert (Hnames : gm_names Φ = gm_names Φ')
        by (rewrite <- (body_xp_names _ _ _ _ _ Hb1), <- (body_xp_names _ _ _ _ _ Hb2); exact (proj2 (proj2 (body_shape_refl _ _ Hsx0)))) end.
    match goal with Hx : _ ⍮ _ ⍮ _ ⊢ˣ body_ctx Φx ++ _ ≈ _, Hx' : _ ⍮ _ ⍮ _ ⊢ˣ body_ctx Φx' ++ _ ≈ _ |- _ =>
      pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as Hl; pose proof (ext_eq_ctx_left _ _ _ _ _ Hx') as Hr end.
    rewrite <- app_assoc in Hl, Hr.
    split; do 2 eexists; (split; [ eassumption |]); (split; [ eassumption |]);
      split; [| repeat split; try eassumption; try (rewrite <- Hnames; eassumption)
             | | repeat split; try eassumption; try (rewrite <- Hnames; eassumption) ].
    + intros y Φ0 b pv A M σ Hp Hf0.
      destruct (shape_prefix _ _ _ _ _ Hsx0 Hp) as (Φ0' & E' & Hp' & _ & HE).
      destruct (fill_prefix _ _ _ _ Hf' Hp') as (σ' & Hf0').
      destruct E' as [? ? ? [] | | | | ]; cbn in HE; try contradiction.
      split; eauto.
    + intros y Φ0' b pv A M σ' Hp' Hf0'.
      destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hsx0) Hp') as (Φ0 & E & Hp & _ & HE).
      destruct (fill_prefix _ _ _ _ Hf Hp) as (σ & Hf0).
      destruct E as [? ? ? [] | | | | ]; cbn in HE; try contradiction.
      split; eauto.
  - pose proof (ext_eq_ctx_left _ _ _ _ _ H) as Hl; pose proof (ext_eq_ctx_right _ _ _ _ _ H) as Hr.
    intuition eauto using wf_modexp_eq_refl_left.
  - (* an alias of a literal, and the literal over both telescopes *)
    split; [ repeat split; [ exact (ext_eq_ctx_left _ _ _ _ _ H) | assumption | apply wf_me_lit; assumption ] |].
    exact (unit_full_abs _ _ _ _ _ (proj1 IHwf_unit_eq) H0).
Qed.

Lemma unit_full_ctx : forall Θ Ξ Γ Δ D, unit_full Θ Ξ Γ (gu_mk Δ D) -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ /\ tele_ass Δ.
Proof.
  intros * HU; destruct D as [[] Φ | E]; cbn in HU; try contradiction.
  - destruct HU as (Φx & lv & _ & HC & _ & _ & Ha & _); split; [ exact (ctx_app_wf_tail _ _ _ _ HC) | exact Ha ].
  - destruct HU as (HΔ & Ha & _); split; assumption.
Qed.

(** A unit's innermost parameters [Δy], the others being in the context. *)
Lemma unit_full_unabs : forall Θ Ξ Γ Δ Δy D, unit_full Θ Ξ Γ (gu_mk (Δy ++ Δ) D) -> unit_full Θ Ξ (Δ ++ Γ) (gu_mk Δy D).
Proof.
  intros * HU; destruct D as [[] Φ | E]; cbn in HU |- *; try contradiction.
  - destruct HU as (Φx & lv & Hx & HC & Hd & Ho & Ha & Hs & Hsx & Hn).
    exists Φx, lv; rewrite <- !app_assoc in *.
    refine (conj Hx (conj HC (conj Hd (conj Ho (conj _ (conj Hs (conj Hsx Hn))))))).
    apply List.Forall_app in Ha; apply Ha.
  - destruct HU as (HΔ & Ha & HE); rewrite <- !app_assoc in *; repeat split; try assumption.
    apply List.Forall_app in Ha; apply Ha.
Qed.

(** A unit given its outermost parameter. *)
Lemma unit_full_beta : forall Θ Ξ Γ Δ X D N,
    unit_full Θ Ξ Γ (gu_mk (Δ ++ ce_ass X :: nil) D) -> Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ (gu_mk Δ D)[Id,,N]ᵘ ≈ (gu_mk Δ D)[Id,,N]ᵘ.
Proof.
  intros * HU HN.
  pose proof (unit_full_unabs _ _ _ _ _ _ HU) as HU1; cbn [List.app] in HU1.
  destruct (unit_full_ctx _ _ _ _ _ HU1) as [HC _].
  destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HC)) as [_ [i HX]].
  eapply sub_preserves_unit; [ exact (unit_eq_of_full _ _ _ _ HU1) | exact (wf_sub_single _ _ _ _ _ _ HX HN) ].
Qed.

(** ** Descriptions of Well-formed Module Expressions *)

Lemma me_denotes : forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> exists R Rm, mdenote Θ Ξ Γ H R /\ ds_mod Θ Ξ R = Some Rm.
Proof.
  intros * HH; destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HH) as (_ & HR & _); exact HR.
Qed.

Lemma me_desc_ok : forall Θ Ξ Γ H H' R, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> desc_ok Θ Ξ Γ R.
Proof.
  intros * HH Hm.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH Hv) as (_ & HR & _); exact (HR _ Hm).
Qed.

Lemma desc_ok_tele : forall Θ Ξ Γ Rm, desc_ok Θ Ξ Γ Rm -> ds_is_mod Rm -> exists T, ds_tele Rm = Some T.
Proof.
  intros * Hok Hm; inversion Hok; subst; cbn in Hm |- *; try contradiction; [ eauto |].
  match goal with Ha : args_ok _ _ _ ?T ?Ns |- _ => pose proof (args_ok_length _ _ _ _ _ Ha) as Hl end.
  apply Nat.leb_le in Hl; rewrite Hl; eauto.
Qed.






Lemma ds_is_mod_sub : forall R σ, ds_is_mod R -> ds_is_mod (ds_sub R σ).
Proof. intros * H; destruct R; cbn in *; tauto. Qed.

(** ** What a Well-formed Module Expression is Made of *)

Definition gen_m (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) : Prop :=
  match H with
  | me_lit U => unit_full Θ Ξ Γ U
  | me_mem H0 _ => Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H0 ≈ H0
  | me_app H0 N =>
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H0 ≈ H0 /\
      exists R T B T1 i, mdenote Θ Ξ Γ H0 R /\ ds_mtele Θ Ξ R = Some T /\ tele_view T = Some (B, T1) /\
        Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : B
  | _ => True
  end.

(** A literal given its outermost parameter: the literal is a module whose
    telescope ends in the parameter. *)
Lemma gen_beta : forall Θ Ξ Γ Δ X D N,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) D ≈ gu_mk (Δ ++ ce_ass X :: nil) D -> Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    gen_m Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) /\
    gen_m Θ Ξ Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ).
Proof.
  intros * HU HN.
  pose proof (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as Hf.
  split; [| exact (proj1 (unit_full_of_eq _ _ _ _ _ (unit_full_beta _ _ _ _ _ _ _ Hf HN))) ].
  split; [ apply wf_me_lit; exact HU |].
  pose proof (unit_full_unabs _ _ _ _ _ _ Hf) as Hf1; cbn [List.app] in Hf1.
  destruct (unit_full_ctx _ _ _ _ _ Hf1) as [HC _].
  destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HC)) as [_ [i HX]].
  destruct D as [[] Φ | E]; cbn in Hf; try contradiction.
  - destruct Hf as (Φx & _ & Hx & _).
    exists (ds_open (Δ ++ ce_ass X :: nil) Φ Φx), (Δ ++ ce_ass X :: nil), X, Δ, i.
    split; [ apply dn_lit; eapply un_body; [ exact Hx | reflexivity ] |].
    split; [ reflexivity |]; split; [ apply tele_view_last |]; split; assumption.
  - destruct Hf as (HΔ & _ & HE).
    destruct (me_denotes _ _ _ _ _ HE) as (R & Rm & HR & HRm).
    pose proof (desc_ok_mod _ _ (ctx_wf_gctx _ _ _ HΔ) _ _ _ (me_desc_ok _ _ _ _ _ _ HE HR) HRm) as Hok.
    pose proof (ds_mod_is_mod _ _ _ _ HRm) as Hmod.
    destruct (desc_ok_tele _ _ _ _ Hok Hmod) as (T & Ht).
    exists (ds_up (Δ ++ ce_ass X :: nil) Rm), (T ++ Δ ++ ce_ass X :: nil), X, (T ++ Δ), i.
    split; [ apply dn_lit; eapply un_alias; eassumption |].
    split; [ unfold ds_mtele; rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ Hmod)); apply ds_tele_up; exact Ht |].
    split; [ rewrite app_assoc; apply tele_view_last |]; split; assumption.
Qed.

(** ** The Unit a Typed Module Part Stands for Is Well Formed *)

(** Arguments for a telescope, but the last. *)
Lemma args_ok_init : forall Θ Ξ Γ T Ns N, args_ok Θ Ξ Γ T (Ns ++ N :: nil) ->
    args_ok Θ Ξ Γ T Ns /\ exists T1 C T2, T = T1 ++ ce_ass C :: T2 /\ length T2 = length Ns /\
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ns : T2 ++ Γ /\ (exists i, Θ ⍮ Ξ ⍮ T2 ++ Γ ⊢ C : Typeω@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : C[sb_of_list Id Ns].
Proof.
  intros * [T1 T2 -> Hl Ha Hs HT2 HN].
  destruct T2 as [| e T2']; [ rewrite length_app in Hl; cbn in Hl; lia |].
  inversion Ha as [| ? ? [C ->] Ha']; subst.
  assert (Hl' : length T2' = length Ns) by (rewrite length_app in Hl; cbn in Hl; lia).
  cbn [List.app] in HT2; destruct (ctx_decomp HT2) as [HT2' [i HC]].
  assert (Hins : tele_insts (ce_ass C :: T2') Id (Ns ++ N :: nil) = tele_insts T2' Id Ns ++ C[sb_of_list Id Ns] :: nil).
  { change (ce_ass C :: T2') with ((ce_ass C :: nil) ++ T2').
    rewrite tele_insts_app by (first [ exact Ha' | symmetry; exact Hl' ]); reflexivity. }
  rewrite Hins in HN.
  assert (HNs : forall k M A, nth_error Ns k = Some M -> nth_error (tele_insts T2' Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A).
  { intros k M A HM HA; apply (HN k); [ rewrite nth_error_app1; [ exact HM | apply nth_error_Some; congruence ] |].
    rewrite nth_error_app1; [ exact HA | apply nth_error_Some; congruence ]. }
  split.
  - exists (T1 ++ ce_ass C :: nil) T2'; [ rewrite <- app_assoc; reflexivity | exact Hl' | exact Ha'
                                        | destruct Hs; assumption | exact HT2' | exact HNs ].
  - exists T1, C, T2'; split; [ reflexivity |]; split; [ exact Hl' |].
    split; [ exact (wf_sub_of_list_id _ _ _ _ _ Ha' HT2' (eq_sym Hl') HNs) |].
    split; [ exists i; exact HC |].
    apply (HN (length Ns)); [ rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity |].
    assert (Hlt : length (tele_insts T2' Id Ns) = length Ns) by (rewrite length_tele_insts by exact Ha'; lia).
    rewrite nth_error_app2 by lia; rewrite Hlt, Nat.sub_diag; reflexivity.
Qed.

(** The parent of a stored module is stored. *)
Lemma loc_parent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mq y T Φ, loc Θ Ξ (qname_in mq y) T Φ ->
    exists T' Φ', loc Θ Ξ mq T' Φ'.
Proof.
  intros Θ Ξ Hg * Hl; destruct Hl as [Hf | Hb].
  - unfold gc_frame in Hf.
    destruct (gs_find_tele Ξ (qname_in mq y)) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ht; try discriminate.
    destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T' & Φ' & Hf' & _).
    exists T', Φ'; left; exact Hf'.
  - destruct (gc_body_module _ _ _ _ _ Hb) as [oD Hmd].
    destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hmd) as (Tq & Φq & Hlq & _).
    exists Tq, Φq; exact Hlq.
Qed.

Lemma qname_mod_gen : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> forall p T Φ, loc Θ Ξ p T Φ -> gen_m Θ Ξ Γ (qname_mod p).
Proof.
  intros Θ Ξ Γ HΓ [u ch] T Φ Hl; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  destruct ch as [| y ch] using List.rev_ind; [ exact I |].
  change {| q_unit := u; q_chain := ch ++ y :: nil |} with (qname_in {| q_unit := u; q_chain := ch |} y) in *.
  rewrite qname_mod_in; cbn [gen_m].
  destruct (loc_parent _ _ Hg _ _ _ _ Hl) as (T' & Φ' & Hp).
  exact (loc_modexp_wf _ _ _ HΓ _ _ _ Hp).
Qed.

(** A stored module at typed arguments is well formed, and made of
    well-formed parts. *)
Lemma filed_apps_wf : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> forall p T Φ, loc Θ Ξ p T Φ -> tele_ass T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T ->
    forall Ns, args_ok Θ Ξ Γ T Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns /\ gen_m Θ Ξ Γ (me_apps (qname_mod p) Ns).
Proof.
  intros Θ Ξ Γ HΓ p T Φ Hl Ha Hs HT; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  induction Ns as [| N Ns IH] using List.rev_ind; intros Hargs.
  - split; [ exact (loc_modexp_wf _ _ _ HΓ _ _ _ Hl) | exact (qname_mod_gen _ _ _ HΓ _ _ _ Hl) ].
  - destruct (args_ok_init _ _ _ _ _ _ Hargs) as (Hargs0 & T1 & C & T2 & HTe & Hl2 & Hσ & [i HC] & HN).
    destruct (IH Hargs0) as [HW _].
    destruct (filed_denote _ _ Hg _ _ _ Γ Ns (gc_loc_of_loc _ _ Hg _ _ _ Hl)) as (R & Hm & Hmd).
    assert (Ht : ds_mtele Θ Ξ R = Some (tele_sub (T1 ++ ce_ass C :: nil) (sb_of_list Id Ns) ++ nil)).
    { unfold ds_mtele; rewrite Hmd; cbn [ds_tele].
      replace (Nat.leb (length Ns) (length T)) with true by (symmetry; apply Nat.leb_le; subst T; rewrite length_app; cbn; lia).
      f_equal; f_equal; f_equal; subst T.
      replace (length (T1 ++ ce_ass C :: T2) - length Ns) with (length (T1 ++ ce_ass C :: nil)) by (rewrite !length_app; cbn; lia).
      change (T1 ++ ce_ass C :: T2) with (T1 ++ (ce_ass C :: nil) ++ T2); rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag; cbn.
      rewrite app_nil_r; reflexivity. }
    assert (Hv : tele_view (tele_sub (T1 ++ ce_ass C :: nil) (sb_of_list Id Ns) ++ nil) =
                   Some (C[sb_of_list Id Ns], tele_sub T1 (q (sb_of_list Id Ns))))
      by (rewrite app_nil_r, tele_view_sub, tele_view_last; reflexivity).
    pose proof (sub_preserves_typ _ _ _ _ _ _ _ HC Hσ) as HB; cbn in HB.
    rewrite me_apps_snoc; split.
    + eapply wf_me_app; [ exact HW | exact Hm | exact Ht | exact Hv | exact HB | exact HN | apply wf_exp_eq_refl; exact HN
                        | exact Hm | exact Ht | exact Hv | exact HB | exact HN ].
    + cbn [gen_m]; split; [ exact HW |]; do 5 eexists; repeat split; [ exact Hm | exact Ht | exact Hv | exact HB | exact HN ].
Qed.

(** A body all of whose definitions are typed in its context is typed
    level by level. *)
Lemma body_opens_noopen : forall Φ, gm_noopen Φ -> forall Φx, body_opens Φ Φx = nil.
Proof. induction Φ as [| Φ IH x E | Φ IH H its]; intros Hn Φx; cbn in Hn |- *; [ reflexivity | apply IH, Hn | contradiction ]. Qed.

Lemma ds_unit_wf : forall Θ Ξ Γ Rm, ⊢ Θ ⍮ Ξ ⍮ Γ -> desc_ok Θ Ξ Γ Rm -> ds_canon Θ Ξ Rm -> ds_is_mod Rm ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ ds_unit Rm ≈ ds_unit Rm /\ gen_m Θ Ξ Γ (ds_unit Rm).
Proof.
  intros * HΓ Hok Hc Hm.
  assert (Hlit : forall U, unit_full Θ Ξ Γ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U /\ gen_m Θ Ξ Γ (me_lit U))
    by (intros U HU; split; [ apply wf_me_lit, unit_eq_of_full; exact HU | exact HU ]).
  destruct Rm as [A om | Δ Φw Φ | [| e Θ'] p T Φ Ns | Θ0 p Ns | Θ0 p Ns | ]; cbn in Hm, Hc |- *; try contradiction.
  - (* the written body, its parameters abstracted *)
    apply Hlit; inversion Hok as [| | ? ? ? ? HΦ Hn Hent HaΔ Hsh Hnd HUw | | |]; subst.
    exact (unit_full_abs _ _ _ _ _ (proj1 (unit_full_of_eq _ _ _ _ _ HUw)) HaΔ).
  - inversion Hok as [| | | ? ? ? ? ? Θ1 Ξ1 ? Hg1 Hs1 Hl1 Ha HsT HT HΘ' Hargs HaΘ | |]; subst.
    exact (filed_apps_wf _ _ _ HΓ _ _ _ Hc Ha HsT HT _ Hargs).
  - inversion Hok as [| | | ? ? ? ? ? Θ1 Ξ1 ? Hg1 Hs1 Hl1 Ha HsT HT HΘ' Hargs HaΘ | |]; subst.
    apply Hlit; cbn; split; [ exact HΘ' |]; split; [ exact HaΘ |].
    exact (proj1 (filed_apps_wf _ _ _ HΘ' _ _ _ Hc Ha HsT HT _ Hargs)).
Qed.

Lemma modexp_gen : forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> gen_m Θ Ξ Γ H /\ gen_m Θ Ξ Γ H'.
Proof.
  induction 1; cbn [gen_m]; try solve [ intuition eauto using wf_modexp_eq_refl_left, wf_modexp_eq_refl_right ].
  - exact (unit_full_of_eq _ _ _ _ _ H).
  - split; split; first [ eapply wf_modexp_eq_refl_left; eassumption | eapply wf_modexp_eq_refl_right; eassumption
                        | do 5 eexists; repeat split; eassumption ].
  - split; [ exact I | exact (proj1 (unit_full_of_eq _ _ _ _ _ (ctx_lookup_mod_wf _ _ _ _ _ H H0))) ].
  - (* a selection: the unit its module part stands for *)
    split; [ exact (proj1 IHwf_modexp_eq) |].
    pose proof (presup_modexp_eq_ctx H0) as HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    exact (proj2 (ds_unit_wf _ _ _ _ HΓ (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ H0 H1) H2)
                    (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg H1) H2) (ds_mod_is_mod _ _ _ _ H2))).
  - destruct (gen_beta _ _ _ _ _ _ _ H H0) as [Hl Hr]; split; [ exact Hl |].
    rewrite gunit_sub_mk in Hr; exact Hr.
  - destruct (gen_beta _ _ _ _ _ _ _ H H0) as [Hl Hr]; split; [ exact Hl |].
    rewrite gunit_sub_mk in Hr; exact Hr.
  - split; [| exact (proj1 IHwf_modexp_eq) ].
    pose proof (presup_modexp_eq_ctx H0) as HΓ.
    cbn; repeat split; [ exact HΓ | constructor | exact H0 ].
Qed.

(** ** Parts of Descriptions under Application *)





Lemma ds_ats_term : forall Ns A om R', ds_ats (ds_term A om) Ns = Some R' -> exists A' om', R' = ds_term A' om'.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[X C] |]; [| discriminate ].
  destruct om as [M |]; [ destruct (fn_view M) as [M' |]; [| discriminate ] |]; exact (IH _ _ _ Ha).
Qed.

(** The module part of "R at N" is the module part of [R] at [N]. *)
Lemma ds_mod_at : forall Θ Ξ R Rm N R', ds_mod Θ Ξ R = Some Rm -> ds_at R N = Some R' ->
    exists Rm', ds_at Rm N = Some Rm' /\ ds_mod Θ Ξ R' = Some Rm'.
Proof.
  intros Θ Ξ R; induction R as [| Δ Φ | Θ0 p T Φ Ns | Θ0 p k Ns | Θ0 p Ns | Θd A M Rm0 IH];
    intros Rm N R' Hm Ha; cbn in Hm; try discriminate.
  5: { (* a definition with a module part: its module part *)
       cbn in Ha; destruct (ds_at Rm0 N) as [Rm0' |] eqn:E; [| discriminate ].
       destruct (IH _ _ _ Hm E) as (Rm' & Hat & Hm').
       destruct (tele_split (rev Θd)) as [[[? ?] ?] | ?]; injection Ha as <-; exists Rm'; split; assumption. }
  - injection Hm as <-; exists R'; split; [ exact Ha |].
    apply ds_is_mod_mod; eapply ds_at_is_mod; [| exact Ha ]; exact I.
  - injection Hm as <-; exists R'; split; [ exact Ha |].
    apply ds_is_mod_mod; eapply ds_at_is_mod; [| exact Ha ]; exact I.
  - destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (D & pm & T & Φ & Hl & Hp & Hb & ->).
    cbn in Ha |- *; destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; eexists; split;
      [ reflexivity | cbn; rewrite Hl, Hp, Hb; reflexivity | reflexivity | cbn; rewrite Hl, Hp, Hb; reflexivity ].
  - destruct (ds_mod_record_inv _ _ _ _ _ _ Hm) as (T & Φ & Hb & ->).
    cbn in Ha |- *; destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; eexists; split;
      [ reflexivity | cbn; rewrite Hb; reflexivity | reflexivity | cbn; rewrite Hb; reflexivity ].
Qed.

Lemma ds_mod_at_inv : forall Θ Ξ R Rm N Rm', ds_mod Θ Ξ R = Some Rm -> ds_at Rm N = Some Rm' ->
    exists R', ds_at R N = Some R' /\ ds_mod Θ Ξ R' = Some Rm'.
Proof.
  intros Θ Ξ R; induction R as [| Δ Φ | Θ0 p T Φ Ns | Θ0 p k Ns | Θ0 p Ns | Θd A M Rm0 IH];
    intros Rm N Rm' Hm Ha; cbn in Hm; try discriminate.
  5: { (* a definition with a module part: its module part *)
       destruct (IH _ _ _ Hm Ha) as (R0' & Hat & Hm').
       cbn; rewrite Hat.
       destruct (tele_split (rev Θd)) as [[[? ?] ?] | ?]; eexists; split; first [ reflexivity | exact Hm' ]. }
  - injection Hm as <-; exists Rm'; split; [ exact Ha |].
    apply ds_is_mod_mod; eapply ds_at_is_mod; [| exact Ha ]; exact I.
  - injection Hm as <-; exists Rm'; split; [ exact Ha |].
    apply ds_is_mod_mod; eapply ds_at_is_mod; [| exact Ha ]; exact I.
  - destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (D & pm & T & Φ & Hl & Hp & Hb & ->).
    cbn in Ha |- *; destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; eexists; split;
      [ reflexivity | cbn; rewrite Hl, Hp, Hb; reflexivity | reflexivity | cbn; rewrite Hl, Hp, Hb; reflexivity ].
  - destruct (ds_mod_record_inv _ _ _ _ _ _ Hm) as (T & Φ & Hb & ->).
    cbn in Ha |- *; destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; eexists; split;
      [ reflexivity | cbn; rewrite Hb; reflexivity | reflexivity | cbn; rewrite Hb; reflexivity ].
Qed.

Lemma ds_mod_ats : forall Θ Ξ Ns R Rm R', ds_mod Θ Ξ R = Some Rm -> ds_ats R Ns = Some R' ->
    exists Rm', ds_ats Rm Ns = Some Rm' /\ ds_mod Θ Ξ R' = Some Rm'.
Proof.
  intros Θ Ξ; induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha |- *; [ injection Ha as <-; eauto |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  destruct (ds_mod_at _ _ _ _ _ _ Hm E) as (Rm1 & -> & Hm1).
  exact (IH _ _ _ Hm1 Ha).
Qed.

Lemma ds_mod_ats_inv : forall Θ Ξ Ns R Rm Rm', ds_mod Θ Ξ R = Some Rm -> ds_ats Rm Ns = Some Rm' ->
    exists R', ds_ats R Ns = Some R' /\ ds_mod Θ Ξ R' = Some Rm'.
Proof.
  intros Θ Ξ; induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha |- *; [ injection Ha as <-; eauto |].
  destruct (ds_at Rm N) as [Rm1 |] eqn:E; [| discriminate ].
  destruct (ds_mod_at_inv _ _ _ _ _ _ Hm E) as (R1 & -> & Hm1).
  exact (IH _ _ _ Hm1 Ha).
Qed.

Lemma ds_red_up : forall Θ' R, ds_red (ds_up Θ' R) = option_map (ctx_fn Θ') (ds_red R).
Proof.
  intros; destruct R as [A [M |] | | | Θ0 p k Ns | Θ0 p Ns | Θd A M Rm]; cbn; try reflexivity;
    rewrite ctx_fn_app; reflexivity.
Qed.

Lemma ds_ty_up_inv : forall Θ Ξ Δ R A, ds_ty Θ Ξ (ds_up Δ R) = Some A -> exists A0, ds_ty Θ Ξ R = Some A0 /\ A = ctx_pi Δ A0.
Proof.
  intros * Ht; destruct R as [A0 om | | | Θ' p k Ns | Θ' p Ns | Θd A0 M0 Rm]; cbn in *; try discriminate.
  - injection Ht as <-; eauto.
  - destruct (ind_lookup Θ Ξ p) as [D |]; [| discriminate ].
    destruct (ind_member D k); [| discriminate ]; injection Ht as <-; rewrite ctx_pi_app; eauto.
  - destruct (record_lookup Θ Ξ p) as [Rr |]; [| discriminate ].
    destruct (Nat.leb _ _); [ injection Ht as <-; rewrite ctx_pi_app; eauto | discriminate ].
  - injection Ht as <-; rewrite ctx_pi_app; eauto.
Qed.

(** ** Applied Module Expressions *)

(** A module expression denoting a description abstracted over [Δa], given
    arguments for the outermost parameters of [Δa], is well formed. *)
Lemma wf_apps_up : forall Θ Ξ Ns Γ Δa R H,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H (ds_up Δa R) -> ds_is_mod R ->
    ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> tele_ass Δa -> length Ns <= length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    desc_ok Θ Ξ (Δa ++ Γ) R ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps H Ns ≈ me_apps H Ns.
Proof.
  intros Θ Ξ; induction Ns as [| N Ns IH]; intros * HH Hm Hmod HΔ Ha Hl HNs HR; [ exact HH |].
  pose proof (ctx_wf_gctx _ _ _ HΔ) as Hg.
  destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
  unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
  rewrite tele_insts_snoc in HNs.
  pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
  rewrite <- List.app_assoc in HΔ, HR; cbn [List.app] in HΔ, HR.
  destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [j HC]].
  pose proof (wf_sub_single _ _ _ _ _ _ HC HN) as Hs1.
  assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
  assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass C :: Γ)
    by (apply wf_sub_ext; assumption).
  destruct (desc_ok_tele _ _ _ _ HR Hmod) as (T0 & Ht0).
  assert (HHN : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N).
  { eapply wf_me_app; [ exact HH | exact Hm | | apply (tele_view_last (T0 ++ Δ1)) | exact HC | exact HN
                      | apply wf_exp_eq_refl; exact HN | exact Hm | | apply (tele_view_last (T0 ++ Δ1)) | exact HC | exact HN ].
    all: unfold ds_mtele; rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ Hmod)), (ds_tele_up _ _ _ Ht0), app_assoc; reflexivity. }
  cbn [me_apps].
  eapply (IH Γ (tele_sub Δ1 (Id,,N)) (ds_sub R (sb_qn (length Δ1) (Id,,N)))).
  - exact HHN.
  - eapply dn_app; [ exact Hm | apply ds_at_up ].
  - apply ds_is_mod_sub; exact Hmod.
  - exact HΔN.
  - apply tele_ass_sub; exact Ha1.
  - rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
  - intros k N1 A HN1 HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
    exact (HNs (S k) N1 A HN1 HA).
  - exact (desc_ok_sub _ _ Hg _ _ HR _ _ Hσ).
Qed.

(** [β] for a well-formed literal, its two forms in one. *)
Lemma beta_step : forall Θ Ξ Γ Δ X D N,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) D ≈ gu_mk (Δ ++ ce_ass X :: nil) D -> Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ.
Proof.
  intros * HU HN; rewrite gunit_sub_mk.
  pose proof (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as Hf.
  destruct D as [[] Φ | E]; cbn in Hf; try contradiction; cbn [moddef_sub].
  - apply wf_me_beta_body; assumption.
  - apply wf_me_beta_alias; assumption.
Qed.

(** ** Local Entries Filled in *)

(** A closed entry denotes the same anywhere. *)
Lemma edenote_closed_move : forall Θ Ξ Γ Γ' o E R σ, gctx_closed Θ Ξ -> entry_sc 0 E ->
    edenote Θ Ξ Γ o E R -> sub_mod_compat σ Γ' Γ -> edenote Θ Ξ Γ' o E R.
Proof.
  intros * Hc HE Hd Hσ.
  assert (HS : slots_ok 0 Γ) by (intros ? ? Hx; lia).
  pose proof (proj1 (proj2 (proj2 (mdenote_scoped_all _ _ Hc))) _ _ _ _ Hd _ HS HE) as HR.
  pose proof (proj1 (proj2 (proj2 (mdenote_sub_all _ _ Hc))) _ _ _ _ Hd _ HS HE _ _ Hσ) as Hd'.
  rewrite (ds_closed_sub _ _ HR) in Hd'.
  exact (edenote_closed_any _ _ _ _ _ _ _ HE Hd').
Qed.





(** ** Filed Modules at Arguments *)

(** A module expression is well formed at the arguments another one is,
    when at every prefix of them it takes a first parameter of the same
    type. *)
Lemma apps_transfer : forall Θ Ξ Γ Ns H H',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps H Ns ≈ me_apps H Ns -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H' ->
    (forall Ms Ms' R R' T B T1, Ns = Ms ++ Ms' -> Ms' <> nil ->
       mdenote Θ Ξ Γ (me_apps H Ms) R -> mdenote Θ Ξ Γ (me_apps H' Ms) R' ->
       ds_mtele Θ Ξ R = Some T -> tele_view T = Some (B, T1) ->
       exists T' T1', ds_mtele Θ Ξ R' = Some T' /\ tele_view T' = Some (B, T1')) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps H' Ns ≈ me_apps H' Ns.
Proof.
  intros * Hw HH'; induction Ns as [| N Ns IH] using List.rev_ind; intros Ht; [ exact HH' |].
  rewrite !me_apps_snoc in *.
  destruct (proj1 (modexp_gen _ _ _ _ _ Hw)) as (Hw0 & R & T & B & T1 & i & Hm & HT & Hv & HB & HN); cbn [gen_m] in *.
  assert (IH' : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps H' Ns ≈ me_apps H' Ns).
  { apply IH; [ exact Hw0 |].
    intros * Heq Hne; apply (Ht Ms (Ms' ++ N :: nil)); [ rewrite Heq, app_assoc; reflexivity | destruct Ms'; [ contradiction | discriminate ] ]. }
  destruct (me_denotes _ _ _ _ _ IH') as (R' & _ & Hm' & _).
  destruct (Ht Ns (N :: nil) R R' T B T1 eq_refl ltac:(discriminate) Hm Hm' HT Hv) as (T' & T1' & HT' & Hv').
  eapply wf_me_app; [ exact IH' | exact Hm' | exact HT' | exact Hv' | exact HB | exact HN | apply wf_exp_eq_refl; exact HN
                    | exact Hm' | exact HT' | exact Hv' | exact HB | exact HN ].
Qed.

(** What the telescope of a filed module at arguments is. *)
Lemma filed_apps_mtele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ Γ Ms R, gc_loc Θ Ξ p = Some (T, Φ) ->
    mdenote Θ Ξ Γ (me_apps (qname_mod p) Ms) R -> ds_mtele Θ Ξ R = ds_tele (ds_closed nil p T Φ Ms).
Proof.
  intros * Hg * Hgl Hm.
  destruct (filed_denote _ _ Hg _ _ _ Γ Ms Hgl) as (R0 & Hm0 & Hmod0).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ Hm0).
  unfold ds_mtele; rewrite Hmod0; reflexivity.
Qed.

Lemma tele_view_app_r : forall X Y B Y1, tele_view Y = Some (B, Y1) -> exists Y1', tele_view (X ++ Y) = Some (B, Y1').
Proof.
  intros * Hv; unfold tele_view in *; rewrite rev_app_distr.
  destruct (tele_open_split _ _ _ Hv) as (τ & Hs).
  exact (tele_open_app_inl _ _ _ _ _ Hs).
Qed.

(** A filed module whose telescope ends in another's takes the same first
    parameter at the same arguments. *)
Lemma ds_tele_closed_ext : forall p T Φ pq Δ0 Φ' Ms T0 B T1,
    ds_tele (ds_closed nil p T Φ Ms) = Some T0 -> tele_view T0 = Some (B, T1) ->
    exists T0' T1', ds_tele (ds_closed nil pq (Δ0 ++ T) Φ' Ms) = Some T0' /\ tele_view T0' = Some (B, T1').
Proof.
  intros * Ht Hv; cbn in Ht |- *.
  destruct (Nat.leb (length Ms) (length T)) eqn:Hl; [ injection Ht as <- | discriminate ].
  apply Nat.leb_le in Hl.
  replace (Nat.leb (length Ms) (length (Δ0 ++ T))) with true by (symmetry; apply Nat.leb_le; rewrite length_app; lia).
  replace (length (Δ0 ++ T) - length Ms) with (length Δ0 + (length T - length Ms)) by (rewrite length_app; lia).
  rewrite List.firstn_app, List.firstn_all2 by lia.
  replace (length Δ0 + (length T - length Ms) - length Δ0) with (length T - length Ms) by lia.
  rewrite tele_sub_app; rewrite ?List.app_nil_r in Hv |- *.
  destruct (tele_view_app_r (tele_sub Δ0 (sb_qn (length (firstn (length T - length Ms) T)) (sb_of_list Id Ms))) _ _ _ Hv) as (T1' & Hv').
  eauto.
Qed.

Lemma filed_apps_ext : forall Θ Ξ Γ p T Φ pq Δ0 Φ' Ns, ⊢ᵍ Θ ⍮ Ξ ->
    gc_loc Θ Ξ p = Some (T, Φ) -> gc_loc Θ Ξ pq = Some (Δ0 ++ T, Φ') ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ qname_mod pq ≈ qname_mod pq ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps (qname_mod pq) Ns ≈ me_apps (qname_mod pq) Ns.
Proof.
  intros * Hg Hp Hq Hw Hw'.
  apply (apps_transfer _ _ _ _ _ _ Hw Hw').
  intros * _ _ Hm Hm' Ht Hv.
  rewrite (filed_apps_mtele _ _ Hg _ _ _ _ _ _ Hp Hm) in Ht.
  rewrite (filed_apps_mtele _ _ Hg _ _ _ _ _ _ Hq Hm').
  exact (ds_tele_closed_ext _ _ _ _ _ _ _ _ _ _ Ht Hv).
Qed.

Lemma loc_child_ind : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ y pv pq k D ΦD, loc Θ Ξ p T Φ ->
    gm_entry Φ (y :: nil) = Some (ge_ind pv pq k D ΦD) -> gc_body Θ Ξ (qname_in p y) = Some (ind_uparams D, ΦD).
Proof.
  intros * Hg * Hl He.
  destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin).
  destruct (loc_read _ _ Hg _ _ _ Hl _ Hin nil) as (_ & _ & _ & Hb).
  rewrite qname_in_app, Hb; exact (proj1 (gm_entry_subbody_ind _ T _ _ _ _ _ _ He)).
Qed.

(** The module of a stored record type is stored at its path, over the
    record's parameters and a value of it. *)
Lemma loc_child_record : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ y pv pr R ΦR, loc Θ Ξ p T Φ ->
    gm_entry Φ (y :: nil) = Some (ge_record pv pr R ΦR) -> gc_body Θ Ξ (qname_in p y) = Some (record_mod_tele pr R, ΦR).
Proof.
  intros * Hg * Hl He.
  destruct (gm_entry_head _ _ _ He) as (z & ip & [= <- <-] & Hin).
  destruct (loc_read _ _ Hg _ _ _ Hl _ Hin nil) as (_ & _ & _ & Hb).
  rewrite qname_in_app, Hb; exact (proj1 (gm_entry_subbody_record _ T _ _ _ _ _ He)).
Qed.

(** A module expression over a closed telescope is well formed on top of
    any context. *)
Lemma modexp_tele_weaken : forall Θ Ξ Δa Γ E E',
    Θ ⍮ Ξ ⍮ Δa ⊢ᵐ E ≈ E' -> ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ᵐ E ≈ E'.
Proof.
  intros * HE HΓ.
  pose proof (presup_modexp_eq_ctx HE) as HΔ.
  pose proof (ctx_wf_gctx _ _ _ HΔ) as Hg.
  pose proof (wf_ctx_scoped _ _ _ HΔ) as Hs.
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HE) as (_ & HsE & HsE').
  pose proof (ctx_app_wf_tail _ _ _ _ HΓ) as HΓ0.
  assert (Hw : Θ ⍮ Ξ ⍮ Γ ⊢ˢ ι (wk_shiftn (length Γ)) : ⋅).
  { apply wf_sub_of_wk; rewrite <- (List.app_nil_r Γ) at 1; apply wf_wk_shiftn_app;
      [ rewrite List.app_nil_r; exact HΓ0 | constructor; exact Hg ]. }
  assert (Hσ : Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ˢ sb_qn (length Δa) (ι (wk_shiftn (length Γ))) : Δa ++ ⋅).
  { pose proof (wf_sub_ext _ _ Δa _ _ _ Hw) as Hx; rewrite tele_sub_closed in Hx by exact Hs.
    apply Hx; [ exact HΓ | rewrite List.app_nil_r; exact HΔ ]. }
  rewrite List.app_nil_r in Hσ.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HE Hσ) as HE2.
  assert (Hfix : forall x, x < length Δa -> sb_qn (length Δa) (ι (wk_shiftn (length Γ))) x = se_var x)
    by (intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ]).
  rewrite (proj1 (proj2 syn_scoped_sub_id) _ _ _ HsE Hfix), (proj1 (proj2 syn_scoped_sub_id) _ _ _ HsE' Hfix) in HE2.
  exact HE2.
Qed.


(** ** A δ-reduct Applied

    A term equal to a δ-reduct abstracted over [Δa], applied to arguments
    for the outermost parameters of [Δa], is equal to the δ-reduct the
    description reads at the arguments, by [β]. *)
Lemma ats_up_red_eq : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa R M M0 A0,
    ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> tele_ass Δa -> length Ns <= length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    ds_ty Θ Ξ R = Some A0 -> ds_red R = Some M0 ->
    (exists i, Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ A0 : Typeω@i) -> Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ M0 : A0 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ ctx_fn Δa M0 : ctx_pi Δa A0 ->
    exists R' A' M', ds_ats (ds_up Δa R) Ns = Some R' /\ ds_ty Θ Ξ R' = Some A' /\ ds_red R' = Some M' /\
      Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns ≈ M' : A'.
Proof.
  intros Θ Ξ Hg; pose proof (wf_gstack_closed _ _ Hg) as Hc.
  induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs Ht Hr [i HA0] HM0 HM.
  - exists (ds_up Δa R), (ctx_pi Δa A0), (ctx_fn Δa M0).
    split; [ reflexivity |]; split; [ apply ds_ty_up; exact Ht |]; split; [ rewrite ds_red_up, Hr; reflexivity | exact HM ].
  - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
    unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
    rewrite tele_insts_snoc in HNs.
    pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
    rewrite <- List.app_assoc in HΔ, HA0, HM0; cbn [List.app] in HΔ, HA0, HM0.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [j HC]].
    pose proof (wf_sub_single _ _ _ _ _ _ HC HN) as Hs1.
    assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
    assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass C :: Γ)
      by (apply wf_sub_ext; assumption).
    destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HA0) as [k HB].
    pose proof (ctx_fn_wf _ _ _ _ _ _ _ HΔ HA0 HM0) as HF.
    rewrite ctx_pi_app, ctx_fn_app in HM; cbn [ctx_pi ctx_fn] in HM.
    assert (HMN : Θ ⍮ Ξ ⍮ Γ ⊢ M $ N ≈ (ctx_fn Δ1 M0)[Id,,N] : (ctx_pi Δ1 A0)[Id,,N]).
    { eapply wf_exp_eq_trans.
      - eapply wf_exp_eq_app_cong; [ eapply lift_exp_max_left; exact HC | eapply lift_exp_max_right; exact HB | exact HM
                                   | apply wf_exp_eq_refl; exact HN ].
      - eapply wf_exp_eq_pi_beta; [ eapply lift_exp_max_left; exact HC | eapply lift_exp_max_right; exact HB | exact HF | exact HN ]. }
    rewrite ctx_pi_sub, ctx_fn_sub in HMN.
    cbn [ds_ats]; rewrite ds_at_up.
    apply (IH Γ (tele_sub Δ1 (Id,,N)) _ (M $ N) M0[sb_qn (length Δ1) (Id,,N)] A0[sb_qn (length Δ1) (Id,,N)]).
    + exact HΔN.
    + apply tele_ass_sub; exact Ha1.
    + rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
    + intros k0 N1 A HN1 HA.
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
      exact (HNs (S k0) N1 A HN1 HA).
    + apply ds_ty_sub; [ exact Hc | exact Ht ].
    + apply ds_red_sub; exact Hr.
    + exists i; exact (sub_preserves_exp _ _ _ _ _ _ _ HA0 Hσ).
    + exact (sub_preserves_exp _ _ _ _ _ _ _ HM0 Hσ).
    + exact HMN.
Qed.

(** Equal terms of a [Π] over a telescope, applied to the same arguments. *)
Lemma wf_apps_ctx_pi_eq_n : forall n Θ Ξ Δ Γ B i M M' Ms,
    List.length Δ = n ->
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms ≈ apps M' Ms : B[sb_of_list Id Ms].
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HM Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; cbn; rewrite exp_sub_id; exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [k HA0]].
    destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HB) as [j HPi].
    assert (HM0 : Θ ⍮ Ξ ⍮ Γ ⊢ M0 : A0)
      by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (Happ : Θ ⍮ Ξ ⍮ Γ ⊢ M $ M0 ≈ M' $ M0 : (ctx_pi Δ B)[Id,,M0])
      by (eapply wf_exp_eq_app_cong with (i := max k j);
          [ eapply lift_exp_max_left; exact HA0 | eapply lift_exp_max_right; exact HPi | exact HM | apply wf_exp_eq_refl; exact HM0 ]).
    rewrite ctx_pi_sub in Happ.
    pose proof (wf_sub_single _ _ _ _ _ _ HA0 HM0) as Hs.
    assert (HΔ' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ (Id,,M0) ++ Γ) by (eapply ctx_sub_wf; eassumption).
    pose proof (wf_sub_ext _ _ _ _ _ _ Hs HΔ' HΔ) as Hs'.
    cbn [apps_exp sb_of_list].
    replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
      by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
    eapply (IH _ _ (tele_sub Δ (Id,,M0))); [ rewrite length_tele_sub; lia | apply tele_ass_sub; exact Hass | exact HΔ' | | exact Happ
               | rewrite length_tele_sub; lia |].
    + exact (sub_preserves_exp _ _ _ _ _ _ _ HB Hs').
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN |].
      rewrite tele_insts_snoc; cbn [List.nth_error].
      rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
      apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
Qed.

(** Equal terms of the type of an inductive type's type former, applied to
    arguments for its first uniform parameters. *)
Lemma wf_ind_args_eq : forall Θ Ξ Γ D k Mk Ns M M',
    decl_typed Θ Ξ D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ -> args_ok Θ Ξ Γ (ind_uparams D) Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ind_ty_at D Mk nil -> Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns ≈ apps M' Ns : ind_ty_at D Mk Ns.
Proof.
  intros * HD Hk HΓ [T1 T2 HT Hlen Ha Hs HT2 HN] HM0.
  destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([i Hi] & _).
  pose proof (member_params_wf _ _ _ _ _ HD Hk) as HP.
  assert (Hp : im_params D Mk = (im_nparams Mk ++ T1) ++ T2) by (unfold im_params; rewrite HT, List.app_assoc; reflexivity).
  rewrite Hp in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : ind_ty_at D Mk Ns = (ctx_pi (im_nparams Mk ++ T1) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[sb_of_list Id Ns]).
  { unfold ind_ty_at; rewrite <- length_im_params, Hp.
    replace (length ((im_nparams Mk ++ T1) ++ T2) - length Ns) with (length (im_nparams Mk ++ T1))
      by (rewrite !List.length_app in *; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ctx_pi T2 (ctx_pi (im_nparams Mk ++ T1) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)).
  { rewrite <- ctx_pi_app, <- Hp.
    unfold ind_ty_at in HM0; rewrite <- length_im_params, Nat.sub_0_r, List.firstn_all in HM0; cbn [sb_of_list List.length] in HM0.
    rewrite exp_sub_id in HM0; exact HM0. }
  rewrite Hat; eapply wf_apps_ctx_pi_eq_n; [ reflexivity | exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

(** Equal terms of the type of a record's type former, applied to
    arguments for its outermost parameters. *)
Lemma wf_record_args_eq : forall Θ Ξ Γ R Ns M M',
    record_typed Θ Ξ R -> ⊢ Θ ⍮ Ξ ⍮ Γ -> args_ok Θ Ξ Γ (record_params R) Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : record_ty_at R nil -> Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ns ≈ apps M' Ns : record_ty_at R Ns.
Proof.
  intros * HR HΓ [T1 T2 HT Hlen Ha Hs HT2 HN] HM0.
  pose proof HR as [_ _ HSu _ _].
  destruct (wf_is_univ_typ HSu) as [i Hi].
  pose proof (presup_is_univ_ctx HSu) as HP.
  rewrite HT in Hi, HP.
  destruct (ctx_pi_wf _ _ _ _ _ _ HP Hi) as [j HB].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB HT2) as HB'.
  assert (Hat : record_ty_at R Ns = (ctx_pi T1 (record_sort R))[sb_of_list Id Ns]).
  { unfold record_ty_at; rewrite HT.
    replace (length (T1 ++ T2) - length Ns) with (length T1) by (rewrite List.length_app; lia).
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ctx_pi T2 (ctx_pi T1 (record_sort R))).
  { rewrite <- ctx_pi_app, <- HT.
    unfold record_ty_at in HM0; rewrite Nat.sub_0_r, List.firstn_all in HM0; cbn [sb_of_list List.length] in HM0.
    rewrite exp_sub_id in HM0; exact HM0. }
  rewrite Hat; eapply wf_apps_ctx_pi_eq_n; [ reflexivity | exact Ha | exact HT2 | exact HB' | exact HM | symmetry; exact Hlen | exact HN ].
Qed.

(** ** A Member of a Filed Module at Arguments

    [(P N⃗).x ≈ P.x N⃗], for every term entry [x] of a filed module [P]: a
    filed axiom or abstract definition by [δ] to its name, a transparent
    definition by [δ] on both sides and [β], an inductive type and an
    inductive alias by [δ] on both sides to the type former. *)
Theorem mem_filed_apps : forall Θ Ξ Γ p T Φ Ns x R A,
    gc_loc Θ Ξ p = Some (T, Φ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    mdenote Θ Ξ Γ (me_mem (me_apps (qname_mod p) Ns) x) R -> ds_ty Θ Ξ R = Some A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (me_apps (qname_mod p) Ns) x ≈ apps (a_mem (qname_mod p) x) Ns : A.
Proof.
  intros * Hgl Hw Hm Ht.
  pose proof (presup_modexp_eq_ctx Hw) as HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (gctx_valid_syn _ _ Hg) as Hv.
  pose proof (gc_loc_loc _ _ _ _ _ Hgl) as Hl.
  pose proof (mem_desc_ok _ _ _ _ _ _ _ Hv Hw Hm) as HokR.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hr | ? ? ? ? Hq Hk];
    subst.
  { cbn in Ht; discriminate. }
  { (* an open frame of a member's module: no arguments, both sides alike *)
    destruct Ns as [| N Ns'] using List.rev_ind; [ apply wf_exp_eq_refl; exact (wf_mem_desc _ _ _ _ _ _ _ Hw Hm Ht) |].
    rewrite me_apps_snoc in Hq; discriminate. }
  2: { (* an open frame of a record's module: no arguments, both sides alike *)
    destruct Ns as [| N Ns'] using List.rev_ind; [ apply wf_exp_eq_refl; exact (wf_mem_desc _ _ _ _ _ _ _ Hw Hm Ht) |].
    rewrite me_apps_snoc in Hq; discriminate. }
  destruct (filed_denote _ _ Hg _ _ _ Γ Ns Hgl) as (R0' & Hm0' & Hmd').
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ Hm0'), Hmd' in Hmd; injection Hmd as <-.
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ Hw Hm0') Hmd') as HokP.
  inversion HokP as [| | | ? ? ? ? ? Θ1 Ξ1 ? Hg1 Hs1 Hl1 HaT HsT HT HΘ' Hargs HaΘ | |]; subst; cbn [List.app] in Hargs.
  cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
  injection He as <- <- <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <- <-] & Hent).
  (* the filed member itself, its lookup from the same entry *)
  destruct (filed_denote _ _ Hg _ _ _ Γ nil (gc_loc_of_loc _ _ Hg _ _ _ Hl)) as (Rp & Hmp & Hmdp); cbn [me_apps] in Hmp.
  assert (Hmx : mdenote Θ Ξ Γ (me_mem (qname_mod p) y) (ds_up nil Re))
    by (eapply dn_mem; [ exact Hmp | exact Hmdp | cbn; rewrite Hp; reflexivity | exact Hed
                       | cbn [ds_read]; rewrite ds_ats_read_nil; reflexivity ]).
  pose proof (loc_modexp_wf _ _ _ HΓ _ _ _ Hl) as HwP.
  destruct (loc_valid _ _ _ _ _ Hv Hl) as [_ HvΦ].
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp) as HE0.
  pose proof (gm_coh_prefix _ _ _ _ _ (loc_coh _ _ Hg _ _ _ Hl) Hp) as HcE0.
  pose proof (loc_closed _ _ Hg _ _ _ Hl) as [_ HcΦ].
  pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
  pose proof (closed_tele_wf _ _ _ _ HsT HT HΓ) as HTΓ.
  cbn [ds_read] in Hr; destruct (ds_ats_read Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hr; [ injection Hr as <- | discriminate ].
  destruct E0 as [b pv A' oM | pv [Δ [sm Φy | E'] ] | pv pq kq D ΦD | pv Ad Md Ud | pv Rr ΦR ].
  - (* a definition *)
    cbn in HE0; destruct HE0 as (A0 & -> & [i HA0] & HM0).
    cbn [ge_read] in Hed; inversion Hed; subst; cbn [ds_ats_read] in Hats.
    assert (Hnone : forall Ns0 A1 R2, ds_ats (ds_term A1 None) Ns0 = Some R2 -> exists A2, R2 = ds_term A2 None).
    { induction Ns0 as [| N0 Ns0 IHN]; intros * Ha0; cbn in Ha0; [ injection Ha0 as <-; eauto |].
      destruct (pi_view A1) as [[? ?] |]; [ exact (IHN _ _ Ha0) | discriminate ]. }
    destruct b; [ destruct oM as [M |] |].
    + (* transparent: [δ] on both sides, then [β] *)
      destruct (HM0 M eq_refl) as (M0 & -> & HM).
      assert (Hδx : Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p) y ≈ ctx_fn T M0 : ctx_pi T A0)
        by (eapply wf_exp_eq_mem_delta; [ exact HwP | exact Hmx | reflexivity | reflexivity ]).
      destruct (ats_up_red_eq _ _ Hg Ns Γ T (ds_term A0 (Some M0)) (a_mem (qname_mod p) y) M0 A0 HTΓ HaT
                  (args_ok_length _ _ _ _ _ Hargs) (args_ok_insts _ _ _ _ _ Hargs) eq_refl eq_refl
                  (ex_intro _ i (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΓ)) (closed_tele_weaken_exp _ _ _ _ _ _ HsT HM HTΓ) Hδx)
        as (R' & A'' & M' & Hats' & Ht' & Hr' & Heq).
      cbn [ds_up option_map] in Hats'; rewrite Hats in Hats'; injection Hats' as <-.
      destruct (ds_ats_some_red _ _ _ _ Hats) as (A1 & M1 & ->).
      rewrite ds_named_fix in Hm, Ht by reflexivity.
      cbn in Ht, Ht', Hr'; injection Ht as <-; injection Ht' as <-; injection Hr' as <-.
      eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; [ exact Hw | exact Hm | reflexivity | reflexivity ] |].
      apply wf_exp_eq_sym; exact Heq.
    + (* an axiom: its name, at arguments; read bare, itself *)
      destruct (Hnone _ _ _ Hats) as (A1 & ->); destruct Ns as [| N Ns'].
      * apply wf_exp_eq_refl; exact (wf_mem_desc _ _ _ _ _ _ _ Hw Hm Ht).
      * rewrite ds_named_self in Ht, Hm by (right; discriminate); cbn in Ht; injection Ht as <-.
        eapply wf_exp_eq_mem_delta; [ exact Hw | exact Hm | reflexivity | reflexivity ].
    + (* abstract: likewise *)
      destruct (Hnone _ _ _ Hats) as (A1 & ->); destruct Ns as [| N Ns'].
      * apply wf_exp_eq_refl; exact (wf_mem_desc _ _ _ _ _ _ _ Hw Hm Ht).
      * rewrite ds_named_self in Ht, Hm by (right; discriminate); cbn in Ht; injection Ht as <-.
        eapply wf_exp_eq_mem_delta; [ exact Hw | exact Hm | reflexivity | reflexivity ].
  - (* a body module is no term *)
    assert (Hmm : ds_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
    rewrite ds_ats_read_mod in Hats by exact Hmm.
    pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
    destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Ht by reflexivity; cbn in Ht; discriminate.
  - (* nor is an alias *)
    assert (Hmm : ds_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
    rewrite ds_ats_read_mod in Hats by exact Hmm.
    pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
    destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Ht by reflexivity; cbn in Ht; discriminate.
  - (* an inductive type: the type former, at the arguments *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn [ds_ats_read] in Hats; rewrite ds_ats_ind_nil in Hats; injection Hats as <-; cbn [List.app] in *.
    rewrite ds_named_fix in HokR, Ht, Hm by reflexivity.
    inversion HokR as [| ? ? ? ? ? D1 Mk1 pm1 HlD HMk1 _ _ _ HaU HsU HU HΘ1 Hargs1 HaΘ1 | | | |]; subst; cbn [List.app] in Hargs1.
    cbn in Ht; rewrite HlD, HMk1 in Ht; injection Ht as <-.
    pose proof (good_ind _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hv) (proj2 Hv) HlD) as HD; cbn [syn_VD] in HD.
    assert (Hδx : Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p) y ≈ a_ind pq kq : ind_ty_at D1 Mk1 nil)
      by (eapply wf_exp_eq_mem_delta; [ exact HwP | exact Hmx | cbn; rewrite HlD, HMk1; reflexivity | reflexivity ]).
    pose proof (wf_ind_args_eq _ _ _ _ _ _ _ _ _ HD HMk1 HΓ Hargs1 Hδx) as Heq.
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; [ exact Hw | exact Hm | cbn; rewrite HlD, HMk1; reflexivity | reflexivity ] |].
    apply wf_exp_eq_sym; exact Heq.
  - (* a definition with a module part: its term part as a transparent
       definition, [δ] on both sides, then [β] *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn [ge_valid syn_V] in HE0; destruct HE0 as [_ (A0 & -> & [i HA0] & HM0)].
    destruct (HM0 _ eq_refl) as (M0 & -> & HM).
    cbn [ds_ats_read] in Hats.
    destruct (ds_ats (ds_term (ctx_pi T A0) (Some (ctx_fn T M0))) Ns) as [[B [M1 |] | | | | |] |] eqn:HtA; try discriminate.
    destruct (ds_ats Rm Ns) as [Rm' |] eqn:HRm; [ injection Hats as <- | discriminate ].
    rewrite ds_named_fix in Hm, Ht by reflexivity.
    assert (Hδx : Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p) y ≈ ctx_fn T M0 : ctx_pi T A0)
      by (eapply wf_exp_eq_mem_delta; [ exact HwP | exact Hmx | reflexivity | reflexivity ]).
    destruct (ats_up_red_eq _ _ Hg Ns Γ T (ds_term A0 (Some M0)) (a_mem (qname_mod p) y) M0 A0 HTΓ HaT
                (args_ok_length _ _ _ _ _ Hargs) (args_ok_insts _ _ _ _ _ Hargs) eq_refl eq_refl
                (ex_intro _ i (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΓ)) (closed_tele_weaken_exp _ _ _ _ _ _ HsT HM HTΓ) Hδx)
      as (R' & A'' & M' & Hats' & Ht' & Hr' & Heq).
    cbn [ds_up option_map] in Hats'; rewrite HtA in Hats'; injection Hats' as <-.
    cbn [ds_up ds_ty ds_red List.app ctx_pi ctx_fn] in Ht, Ht', Hr'; injection Ht as <-; injection Ht' as <-; injection Hr' as <-.
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; [ exact Hw | exact Hm | reflexivity | reflexivity ] |].
    apply wf_exp_eq_sym; exact Heq.
  - (* a record type: the type former, at the arguments *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn [ds_ats_read] in Hats; rewrite ds_ats_record_nil in Hats; injection Hats as <-; cbn [List.app] in *.
    rewrite ds_named_fix in HokR, Ht, Hm by reflexivity.
    inversion HokR as [| | | | ? ? ? ? R1 HlR HaU HsU HU HΘ1 Hargs1 HaΘ1 |]; subst; cbn [List.app] in Hargs1.
    cbn in Ht; rewrite HlR in Ht; destruct (Nat.leb _ _) eqn:Hle; [ injection Ht as <- | discriminate ].
    pose proof (record_lookup_typed _ _ Hg Hv _ _ HlR) as HRt.
    assert (Hδx : Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p) y ≈ a_record (qname_in p y) : record_ty_at R1 nil)
      by (eapply wf_exp_eq_mem_delta; [ exact HwP | exact Hmx | cbn; rewrite HlR; reflexivity | reflexivity ]).
    pose proof (wf_record_args_eq _ _ _ _ _ _ _ HRt HΓ
                  (args_ok_record_params _ _ _ _ _ _ Hargs1 (proj1 (Nat.leb_le _ _) Hle)) Hδx) as Heq.
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; [ exact Hw | exact Hm | cbn; rewrite HlR, Hle; reflexivity | reflexivity ] |].
    apply wf_exp_eq_sym; exact Heq.
Qed.

(** ** Members of Module Expressions with One Module Part

    Every term a module expression looks up has a δ-reduct, so two module
    expressions whose module parts agree have equal members: [A.x ≈ P.x]
    for [module A := P]. *)
Lemma mem_same_lookup : forall Θ Ξ Γ H H' x R A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H' ->
    mdenote Θ Ξ Γ (me_mem H x) R -> mdenote Θ Ξ Γ (me_mem H' x) R -> ds_ty Θ Ξ R = Some A -> ds_red R = Some M ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ a_mem H' x : A.
Proof.
  intros * HH HH' Hm Hm' Ht Hr.
  eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; eassumption |].
  apply wf_exp_eq_sym; eapply wf_exp_eq_mem_delta; eassumption.
Qed.

(** A term read from a closed module part has a δ-reduct. *)
Lemma ds_red_closed_read : forall Θ Ξ Θ' M R1 A, ds_ty Θ Ξ (ds_up Θ' (ds_self M R1)) = Some A ->
    exists M', ds_red (ds_up Θ' (ds_self M R1)) = Some M'.
Proof. intros * Ht; destruct R1 as [? [] | | | | |]; cbn in Ht |- *; try discriminate; eauto. Qed.





(** Equal bodies over a telescope of assumptions, abstracted over it. *)
Lemma ctx_fn_eq : forall Θ Ξ Δ Γ A M M' i, tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M ≈ ctx_fn Δ M' : ctx_pi Δ A.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * Ha HΔ HA HM; cbn in *; [ assumption | | |];
    inversion Ha as [| ? ? [? Heq] Ha']; subst; try discriminate.
  inversion HΔ; subst.
  match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Typeω@?k |- _ =>
    eapply IH with (i := max k i); [ exact Ha' | eauto using presup_exp_ctx | |];
    [ eapply wf_pi_large; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
    | eapply wf_exp_eq_fn_cong; [ exact HB | apply wf_exp_eq_refl; exact HB | exact HM ] ]
  end.
Qed.

(** [H.x ≈ λ Θ'. P.x N⃗]: a member of a module expression whose module part
    is a filed module [P] at arguments [N⃗] over outside parameters [Θ'] is
    the filed member at the arguments, abstracted over [Θ']: [A.x ≈ P.x]
    for [module A := P], and [L.c ≈ λ n. P.c] for
    [let module L (n : ℕ) := P].  This is the case of an outside parameter
    or an argument, where the member is read as a name ([ds_named]); read
    bare, it goes by the module expressions ([mem_closed_part]). *)
Lemma ds_ty_named : forall Θ Ξ Θ' Ns M R, ds_ty Θ Ξ (ds_named Θ' Ns M R) = ds_ty Θ Ξ R.
Proof. intros; apply (ds_named_cases (fun R' => ds_ty Θ Ξ R' = ds_ty Θ Ξ R)); [ reflexivity | destruct R as [? [] | | | | |]; reflexivity ]. Qed.

(** An open frame, named by its path, is its module at no arguments and no
    outside parameters. *)
Lemma frame_denote_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H R p T0 Φ0 Θ' pf T Φ Ns,
    mod_qname H = Some p -> gc_frame Ξ p = Some (T0, Φ0) -> mdenote Θ Ξ Γ H R ->
    ds_mod Θ Ξ R = Some (ds_closed Θ' pf T Φ Ns) -> Θ' = nil /\ pf = p /\ Ns = nil.
Proof.
  intros Θ Ξ Hg * Hq Hf Hm Hmd.
  destruct (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm) as (Hu & Hk & Hr).
  destruct (gs_find_ind Ξ p) as [[[pq k] D] |] eqn:Ek.
  - rewrite (Hk _ _ _ eq_refl) in Hmd.
    destruct (ds_mod_ind_frame _ _ Hg _ _ _ _ nil nil Ek) as (? & ? & _ & Hmd'); rewrite Hmd' in Hmd.
    injection Hmd as <- <- _ _ <-; auto.
  - destruct (gs_find_record Ξ p) as [Rr |] eqn:Er.
    + rewrite (Hr _ eq_refl) in Hmd.
      destruct (ds_mod_record_frame _ _ Hg _ _ nil nil Er) as (? & ? & _ & Hmd'); rewrite Hmd' in Hmd.
      injection Hmd as <- <- _ _ <-; auto.
    + rewrite (Hu _ _ (gc_unit_frame _ _ _ _ _ _ Hq Hf Ek Er)) in Hmd; cbn in Hmd.
      injection Hmd as <- <- _ _ <-; auto.
Qed.

(** The module of a member denoted at a record's open frame is that
    frame's parent, itself an open frame, named by its path. *)
Lemma record_frame_mem_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H x p R RH Θ' pf T Φ Ns,
    mod_qname (me_mem H x) = Some p -> gs_find_record Ξ p = Some R -> mdenote Θ Ξ Γ H RH ->
    ds_mod Θ Ξ RH = Some (ds_closed Θ' pf T Φ Ns) -> mod_qname H = Some pf /\ Θ' = nil /\ Ns = nil.
Proof.
  intros Θ Ξ Hg * Hq Hk Hm Hmd.
  cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hk.
  destruct (gs_find_record_tele _ _ _ Hk) as (U & T0 & Ht).
  destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T' & Φ' & Hf & _).
  destruct (frame_denote_mod _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Hq0 Hf Hm Hmd) as (-> & -> & ->); auto.
Qed.

(** The module of a member denoted at an open frame is that frame's parent,
    itself an open frame, named by its path. *)
Lemma ind_frame_mem_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H x p r RH Θ' pf T Φ Ns,
    mod_qname (me_mem H x) = Some p -> gs_find_ind Ξ p = Some r -> mdenote Θ Ξ Γ H RH ->
    ds_mod Θ Ξ RH = Some (ds_closed Θ' pf T Φ Ns) -> mod_qname H = Some pf /\ Θ' = nil /\ Ns = nil.
Proof.
  intros Θ Ξ Hg * Hq Hk Hm Hmd.
  cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hk.
  destruct (gs_find_ind_tele _ _ _ Hk) as (U & T0 & Ht).
  destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T' & Φ' & Hf & _).
  destruct (frame_denote_mod _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Hq0 Hf Hm Hmd) as (-> & -> & ->); auto.
Qed.

Lemma mem_closed_part_named : forall Θ Ξ Γ H RH Θ' p T Φ Ns x R A,
    Θ' <> nil \/ Ns <> nil ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H RH -> ds_mod Θ Ξ RH = Some (ds_closed Θ' p T Φ Ns) ->
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ ctx_fn Θ' (apps (a_mem (qname_mod p) x) Ns) : A.
Proof.
  intros * Hne HH HmH HmdH Hm Ht.
  pose proof (presup_modexp_eq_ctx HH) as HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (wf_gstack_closed _ _ Hg) as Hc.
  pose proof (gctx_valid_syn _ _ Hg) as Hv.
  pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg HmH) HmdH) as Hl; cbn in Hl.
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH HmH) HmdH) as HokP.
  inversion HokP as [| | | ? ? ? ? ? Θ1 Ξ1 ? Hg1 Hs1 Hl1 HaT HsT HT HΘ' Hargs HaΘ | |]; subst.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hr | ? ? ? ? Hq Hk];
    subst.
  { cbn in Ht; discriminate. }
  { destruct (ind_frame_mem_mod _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Hq Hk HmH HmdH) as (_ & -> & ->).
    destruct Hne as [Hne | Hne]; contradiction. }
  2: { destruct (record_frame_mem_mod _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Hq Hk HmH HmdH) as (_ & -> & ->).
       destruct Hne as [Hne | Hne]; contradiction. }
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ HmH), HmdH in Hmd; injection Hmd as <-.
  pose proof (loc_closed _ _ Hg _ _ _ Hl) as HU.
  destruct (ds_entry_closed _ _ _ _ _ _ _ _ _ HU He) as (-> & HE & ->).
  cbn [ds_read] in Hr; destruct (ds_ats_read Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hr; [ injection Hr as <- | discriminate ].
  (* the filed module at the arguments, under the outside parameters *)
  destruct (filed_apps_wf _ _ _ HΘ' _ _ _ Hl HaT HsT HT _ Hargs) as [HW _].
  destruct (filed_denote _ _ Hg _ _ _ (Θ' ++ Γ) Ns (gc_loc_of_loc _ _ Hg _ _ _ Hl)) as (R0' & Hm0' & Hmd').
  assert (Hed' : edenote Θ Ξ (nil ++ Θ' ++ Γ) (ds_epath (ds_closed nil p T Φ Ns) x) E Re).
  { eapply edenote_closed_move; [ exact Hc | exact HE | exact Hed |].
    apply wk_mod_compat_sub; cbn [List.app]; apply (wf_wk_mod_compat Θ Ξ); apply wf_wk_shiftn_app; [ exact HΘ' | exact HΓ ]. }
  assert (Hmx : mdenote Θ Ξ (Θ' ++ Γ) (me_mem (me_apps (qname_mod p) Ns) x) (ds_up nil (ds_named nil Ns (apps (a_mem (qname_mod p) x) Ns) R1))).
  { assert (He' : ds_entry (ds_closed nil p T Φ Ns) x = Some (nil, E, rd_closed nil Ns (apps (a_mem (qname_mod p) x) Ns))).
    { cbn in He |- *; destruct (gm_prefix_upto Φ x) as [[| ? ? ? | ? ? ?] |]; try discriminate.
      injection He as HE1; rewrite HE1; reflexivity. }
    eapply dn_mem; [ exact Hm0' | exact Hmd' | exact He' | exact Hed' | cbn; rewrite Hats; reflexivity ]. }
  rewrite (ds_named_self _ _ Hne) in Ht, Hm.
  change (ds_up Θ' (ds_self (apps (a_mem (qname_mod p) x) Ns) R1)) with (ds_up (nil ++ Θ') (ds_self (apps (a_mem (qname_mod p) x) Ns) R1)) in Ht, Hm.
  rewrite ds_up_cat in Ht, Hm.
  destruct (ds_ty_up_inv _ _ _ _ _ Ht) as (A0 & HA0 & ->).
  destruct (ds_red_closed_read _ _ _ _ _ _ HA0) as (M' & HM').
  assert (HA0x : ds_ty Θ Ξ (ds_up nil (ds_named nil Ns (apps (a_mem (qname_mod p) x) Ns) R1)) = Some A0).
  { rewrite <- HA0; apply (ds_named_cases (fun R' => ds_ty Θ Ξ (ds_up nil R') = ds_ty Θ Ξ (ds_up nil (ds_self (apps (a_mem (qname_mod p) x) Ns) R1))));
      [ destruct R1 as [? [] | | | | |] | ]; reflexivity. }
  destruct (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HW Hmx) HA0x) as [[i Hi] _].
  pose proof (mem_filed_apps _ _ _ _ _ _ _ _ _ _ (gc_loc_of_loc _ _ Hg _ _ _ Hl) HW Hmx HA0x) as Hfa.
  (* the member at the arguments is the filed member at them: by [δ] to
     the δ-reduct, which a term of none is read as *)
  assert (Heq : Θ ⍮ Ξ ⍮ Θ' ++ Γ ⊢ M' ≈ apps (a_mem (qname_mod p) x) Ns : A0).
  { destruct (ds_red R1) as [M1 |] eqn:Er.
    - assert (Hs : ds_self (apps (a_mem (qname_mod p) x) Ns) R1 = R1) by (destruct R1 as [? [] | | | | |]; cbn in Er |- *; congruence).
      rewrite Hs in HM'; cbn [ds_up] in HM'.
      assert (HMx : ds_red (ds_up nil (ds_named nil Ns (apps (a_mem (qname_mod p) x) Ns) R1)) = Some M')
        by (rewrite ds_named_fix by exact Hs; cbn [ds_up]; exact HM').
      eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; eapply wf_exp_eq_mem_delta; [ exact HW | exact Hmx | exact HA0x | exact HMx ] |].
      exact Hfa.
    - destruct R1 as [? [] | | | | |]; cbn in Er, HA0, HM'; try discriminate; injection HM' as <-.
      eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact Hfa | exact Hfa ]. }
  apply (wf_exp_eq_trans _ _ _ _ _ (ctx_fn Θ' M')); [ eapply wf_exp_eq_mem_delta; [ exact HH | exact Hm | exact Ht | rewrite ds_red_up, HM'; reflexivity ] |].
  exact (ctx_fn_eq _ _ _ _ _ _ _ _ HaΘ HΘ' Hi Heq).
Qed.


(** ** Every Module Is Equal to a Unit

    A unit in normal form ([unit_nf]) is a filed module at arguments, a
    local body, or an alias with parameters of a unit in normal form.  A
    well-formed module expression is equal to a unit in normal form that
    denotes the same module part ([lookup_sound]): a slot by its unit, a
    selection by the unit its module part stands for ([ds_unit]), an alias
    with no parameter by its target, and an application by [β]. *)

Inductive unit_nf (Θ : gdeps) (Ξ : gstack) : modexp -> Prop :=
| unf_filed : forall p T Φ Ns, loc Θ Ξ p T Φ -> unit_nf Θ Ξ (me_apps (qname_mod p) Ns)
| unf_body : forall Δ Φ, unit_nf Θ Ξ (me_lit (gu_open Δ Φ))
| unf_alias : forall Δ E, Δ <> nil -> unit_nf Θ Ξ E -> unit_nf Θ Ξ (me_lit (gu_mk Δ (md_alias E))).

Lemma unit_nf_sub : forall Θ Ξ K, unit_nf Θ Ξ K -> forall σ, unit_nf Θ Ξ K[σ]ᵐ.
Proof.
  induction 1 as [p T Φ Ns Hl | Δ Φ | Δ E HΔ HE IH]; intros σ.
  - rewrite me_apps_sub, qname_mod_sub; eapply unf_filed; exact Hl.
  - cbn [modexp_sub]; rewrite gunit_sub_mk; apply unf_body.
  - cbn [modexp_sub]; rewrite gunit_sub_mk; apply unf_alias; [ destruct Δ; [ contradiction | discriminate ] | apply IH ].
Qed.

Lemma ds_unit_nf : forall Θ Ξ Rm, ds_canon Θ Ξ Rm -> ds_is_mod Rm -> unit_nf Θ Ξ (ds_unit Rm).
Proof.
  intros * Hc Hm; destruct Rm as [A om | Δ Φ | [| e Θ'] p T Φ Ns | Θ0 p Ns | Θ0 p Ns | ]; cbn in Hm, Hc |- *; try contradiction.
  - apply unf_body.
  - eapply unf_filed; exact Hc.
  - apply unf_alias; [ discriminate | eapply unf_filed; exact Hc ].
Qed.

Lemma mdenote_lit_inv : forall Θ Ξ Γ U R, mdenote Θ Ξ Γ (me_lit U) R -> udenote Θ Ξ Γ None U R.
Proof. intros * Hm; inversion Hm; subst; first [ cbn in *; discriminate | assumption ]. Qed.

Lemma tele_ass_last : forall Δ, tele_ass Δ -> Δ <> nil -> exists Δ0 X, Δ = Δ0 ++ ce_ass X :: nil.
Proof.
  intros Δ Ha Hn; destruct (List.exists_last Hn) as (Δ0 & e & ->).
  apply List.Forall_app in Ha as [_ Ha]; inversion Ha as [| ? ? [X ->] _]; subst; eauto.
Qed.

Lemma ds_tele_up_inv : forall Δ R T, ds_is_mod R -> ds_tele (ds_up Δ R) = Some T -> exists T0, T = T0 ++ Δ.
Proof.
  intros * Hm Ht; destruct R as [| Δ' Φ | Θ0 p T' Φ Ns | | |]; cbn in Hm, Ht; try contradiction.
  - injection Ht as <-; eauto.
  - destruct (Nat.leb _ _); [ injection Ht as <-; rewrite app_assoc; eauto | discriminate ].
Qed.

Lemma me_apps_qname_not_lit : forall p Ns U, me_apps (qname_mod p) Ns <> me_lit U.
Proof.
  intros * E; destruct Ns as [| N Ns _] using List.rev_ind; [| rewrite me_apps_snoc in E; discriminate ].
  pose proof (mod_qname_qname_mod p) as Hq; cbn [me_apps] in E; rewrite E in Hq; discriminate.
Qed.

(** The last parameter of a literal in normal form given an argument in a
    well-formed application: the argument is of its type. *)
Lemma lit_app_last : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ U N RK, unit_nf Θ Ξ (me_lit U) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit U) N ≈ me_app (me_lit U) N -> mdenote Θ Ξ Γ (me_lit U) RK ->
    exists Δ0 X D, U = gu_mk (Δ0 ++ ce_ass X :: nil) D /\ unit_full Θ Ξ Γ U /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : X.
Proof.
  intros Θ Ξ Hg * Hnf Hw Hm.
  destruct (proj1 (modexp_gen _ _ _ _ _ Hw)) as (HK & R0 & T & B & T1 & i & Hm0 & HT & Hv & HB & HN); cbn [gen_m] in *.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ Hm) in HT.
  pose proof (proj1 (modexp_gen _ _ _ _ _ HK)) as Hf; cbn [gen_m] in Hf.
  apply mdenote_lit_inv in Hm.
  inversion Hnf as [p T0 Φ0 Ns _ HU | Δ Φ HU | Δ E HΔ _ HU]; subst.
  - exfalso; exact (me_apps_qname_not_lit _ _ _ HU).
  - destruct (unit_full_ctx _ _ _ _ _ Hf) as [_ Ha].
    inversion Hm; subst.
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    unfold ds_mtele in HT; cbn in HT; injection HT as <-.
    destruct Δ as [| e Δ']; [ cbn in Hv; discriminate |].
    destruct (tele_ass_last _ Ha ltac:(discriminate)) as (Δ0 & X & HΔ).
    rewrite HΔ, tele_view_last in Hv; injection Hv as <- _.
    exists Δ0, X, (md_body sm_open Φ); rewrite <- HΔ; split; [ reflexivity | split; assumption ].
  - destruct (unit_full_ctx _ _ _ _ _ Hf) as [_ Ha].
    inversion Hm; subst.
    match goal with Hd : ds_mod _ _ _ = Some ?R' |- _ => pose proof (ds_mod_is_mod _ _ _ _ Hd) as Him end.
    unfold ds_mtele in HT; rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ Him)) in HT.
    destruct (ds_tele_up_inv _ _ _ Him HT) as (T0 & ->).
    destruct (tele_ass_last _ Ha HΔ) as (Δ0 & X & HΔ0).
    rewrite HΔ0, app_assoc, tele_view_last in Hv; injection Hv as <- _.
    exists Δ0, X, (md_alias E); rewrite <- HΔ0; split; [ reflexivity | split; assumption ].
Qed.

(** A unit in normal form given an argument is equal to a unit in normal
    form denoting the same module part: a filed module at one more
    argument; a literal by [β], and an alias left with no parameter by its
    target. *)
Lemma unit_nf_step : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ K N RK RK', unit_nf Θ Ξ K ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app K N ≈ me_app K N -> mdenote Θ Ξ Γ K RK -> ds_at RK N = Some RK' ->
    exists K' RK'', unit_nf Θ Ξ K' /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app K N ≈ K' /\ mdenote Θ Ξ Γ K' RK'' /\
      ds_mod Θ Ξ RK'' = ds_mod Θ Ξ RK'.
Proof.
  intros Θ Ξ Hg * Hnf Hw Hm Ha.
  assert (HmA : mdenote Θ Ξ Γ (me_app K N) RK') by (eapply dn_app; eassumption).
  destruct Hnf as [p T Φ Ns Hl | Δ Φ | Δ E HΔ HE].
  - exists (me_app (me_apps (qname_mod p) Ns) N), RK'; split; [ rewrite <- me_apps_snoc; eapply unf_filed; exact Hl |].
    split; [ exact Hw |]; split; [ exact HmA | reflexivity ].
  - destruct (lit_app_last _ _ Hg _ _ _ _ (unf_body _ _ Δ Φ) Hw Hm) as (Δ0 & X & D & HU & Hf & HN).
    injection HU as -> <-.
    pose proof (unit_eq_of_full _ _ _ _ Hf) as HU.
    destruct (mdenote_beta _ _ _ _ _ _ N HU _ (mdenote_lit_inv _ _ _ _ _ Hm)) as (R' & HmA' & HmL & _).
    rewrite <- (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmA' _ HmA).
    eexists; exists R'; split; [| split; [ exact (beta_step _ _ _ _ _ _ _ HU HN) | split; [ exact HmL | reflexivity ] ] ].
    rewrite gunit_sub_mk; apply unf_body.
  - pose proof (unf_alias _ _ _ _ HΔ HE) as Hnf.
    destruct (lit_app_last _ _ Hg _ _ _ _ Hnf Hw Hm) as (Δ0 & X & D & HU & Hf & HN).
    injection HU as -> <-.
    pose proof (unit_eq_of_full _ _ _ _ Hf) as HU.
    destruct (mdenote_beta _ _ _ _ _ _ N HU _ (mdenote_lit_inv _ _ _ _ _ Hm)) as (R' & HmA' & HmL & HmdR').
    rewrite <- (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmA' _ HmA).
    pose proof (beta_step _ _ _ _ _ _ _ HU HN) as Hβ.
    rewrite gunit_sub_mk in Hβ, HmL; cbn [moddef_sub] in Hβ, HmL.
    destruct Δ0 as [| e Δ0'].
    + (* no parameter left: the target *)
      cbn [tele_sub length] in Hβ, HmL.
      pose proof (proj2 (modexp_gen _ _ _ _ _ Hβ)) as Hf'; cbn [gen_m unit_full] in Hf'; destruct Hf' as (_ & _ & HE').
      cbn [List.app] in HE'.
      apply mdenote_lit_inv in HmL; inversion HmL as [| ? ? ? ? R1 R2 HmE HmdE HeqR]; subst.
      rewrite ds_up_nil in HmdR' |- *.
      exists E[sb_qn 0 (Id,,N)]ᵐ, R1; split; [ apply unit_nf_sub; exact HE |].
      split; [ eapply wf_me_trans; [ exact Hβ | apply wf_me_beta_alias0; exact HE' ] |].
      split; [ exact HmE | rewrite HmdE, HmdR'; reflexivity ].
    + eexists; exists R'; split; [| split; [ exact Hβ | split; [ exact HmL | reflexivity ] ] ].
      apply unf_alias; [ discriminate | apply unit_nf_sub; exact HE ].
Qed.

Lemma lookup_sound_all : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> forall Rm, ds_mod Θ Ξ R = Some Rm ->
       exists K RK, unit_nf Θ Ξ K /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ K /\ mdenote Θ Ξ Γ K RK /\ ds_mod Θ Ξ RK = Some Rm) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> o = None -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U -> forall Rm, ds_mod Θ Ξ R = Some Rm ->
       exists K RK, unit_nf Θ Ξ K /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ K /\ mdenote Θ Ξ Γ K RK /\ ds_mod Θ Ξ RK = Some Rm) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> True) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> True).
Proof.
  intros Θ Ξ Hg; apply mdenote_all_ind; try (intros; exact I).
  - (* a loaded unit or an open frame *)
    intros Γ H p T Φ Hq Hu HH Rm Hmd.
    destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq' & Hl); rewrite Hq in Hq'; injection Hq' as <-.
    exists H, (ds_closed nil p T Φ nil); split; [ rewrite (mod_qname_inv _ _ Hq); exact (unf_filed _ _ p T Φ nil Hl) |].
    split; [ exact HH |]; split; [ apply dn_unit; assumption | exact Hmd ].
  - (* the open frame of a member's module: itself, a filed module *)
    intros Γ H p pq k D Hq Hk HH Rm Hmd.
    destruct (ds_mod_ind_frame _ _ Hg _ _ _ _ nil nil Hk) as (T & Φ & Hf & Hmd'); rewrite Hmd' in Hmd; injection Hmd as <-.
    exists H, (ds_ind nil pq k nil); split; [ rewrite (mod_qname_inv _ _ Hq); exact (unf_filed _ _ p T Φ nil (or_introl Hf)) |].
    split; [ exact HH |]; split; [ eapply dn_ind_frame; eassumption | exact Hmd' ].
  - (* a slot: its unit *)
    intros Γ x U R Hx Hu IH HH Rm Hmd.
    pose proof (presup_modexp_eq_ctx HH) as HΓ.
    destruct (IH eq_refl (ctx_lookup_mod_wf _ _ _ _ _ HΓ Hx) Rm Hmd) as (K & RK & Hnf & HK & HmK & HmdK).
    exists K, RK; split; [ exact Hnf |]; split; [ eapply wf_me_trans; [ eapply wf_me_delta_slot; eassumption | exact HK ] |].
    split; assumption.
  - (* a literal *)
    intros Γ U R Hu IH HH Rm Hmd.
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as Hf; cbn [gen_m] in Hf.
    exact (IH eq_refl (unit_eq_of_full _ _ _ _ Hf) Rm Hmd).
  - (* an application: the unit the module is equal to, given the argument *)
    intros Γ H N R R' Hm IH Ha HH Rm Hmd.
    destruct (proj1 (modexp_gen _ _ _ _ _ HH)) as (HH0 & R0 & T & B & T1 & i & Hm0 & HT & Hv & HB & HN); cbn [gen_m] in *.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ Hm) in HT.
    unfold ds_mtele in HT; destruct (ds_mod Θ Ξ R) as [Rm0 |] eqn:Hmd0; [| discriminate ].
    destruct (IH HH0 Rm0 eq_refl) as (K & RK & Hnf & HK & HmK & HmdK).
    destruct (ds_mod_at _ _ _ _ _ _ Hmd0 Ha) as (Rm' & Ha0 & Hmd'); rewrite Hmd in Hmd'; injection Hmd' as <-.
    destruct (ds_mod_at_inv _ _ _ _ _ _ HmdK Ha0) as (RK' & HaK & HmdK').
    assert (HKN : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app K N).
    { eapply wf_me_app; [ exact HK | exact Hm | unfold ds_mtele; rewrite Hmd0; exact HT | exact Hv | exact HB | exact HN
                        | apply wf_exp_eq_refl; exact HN | exact HmK | unfold ds_mtele; rewrite HmdK; exact HT
                        | exact Hv | exact HB | exact HN ]. }
    destruct (unit_nf_step _ _ Hg _ _ _ _ _ Hnf (wf_modexp_eq_refl_right HKN) HmK HaK)
      as (K' & RK'' & Hnf' & HK' & HmK' & HmdK'').
    exists K', RK''; split; [ exact Hnf' |]; split; [ eapply wf_me_trans; eassumption |].
    split; [ exact HmK' | rewrite HmdK''; exact HmdK' ].
  - (* a selection: the unit its module part stands for *)
    intros Γ H y R0 R0m Γy E rd R R' Hm _ Hmd0 He Hed _ Hrd HH Rm Hmd.
    assert (Hsel : mdenote Θ Ξ Γ (me_mem H y) R') by (eapply dn_mem; eassumption).
    pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hsel) Hmd) as Hc.
    pose proof (ds_mod_is_mod _ _ _ _ Hmd) as Him.
    destruct (ds_unit_denote _ _ _ Hg Hc Him Γ (wf_mdenote_mod_xp _ _ _ _ _ _ _ HH Hsel Hmd)) as (RK & HmK & HmdK).
    exists (ds_unit Rm), RK; split; [ exact (ds_unit_nf _ _ _ Hc Him) |].
    split; [ eapply wf_me_delta_sel; eassumption |]; split; assumption.
  - (* the open frame of a record's module: itself, a filed module *)
    intros Γ H p R Hq Hk HH Rm Hmd.
    destruct (ds_mod_record_frame _ _ Hg _ _ nil nil Hk) as (T & Φ & Hf & Hmd'); rewrite Hmd' in Hmd; injection Hmd as <-.
    exists H, (ds_record nil p nil); split; [ rewrite (mod_qname_inv _ _ Hq); exact (unf_filed _ _ p T Φ nil (or_introl Hf)) |].
    split; [ exact HH |]; split; [ eapply dn_record_frame; eassumption | exact Hmd' ].
  - (* a body *)
    intros Γ o Δ sm Φ Φx R Hx _ Hb -> HU Rm Hmd.
    destruct sm; cbn in Hb; [ injection Hb as <- | discriminate ].
    exists (me_lit (gu_open Δ Φ)), (ds_open Δ Φ Φx); split; [ apply unf_body |].
    split; [ apply wf_me_lit; exact HU |]; split; [ apply dn_lit; eapply un_body; [ exact Hx | reflexivity ] | exact Hmd ].
  - (* an alias: with no parameter its target, otherwise over the unit its target is equal to *)
    intros Γ o Δ E R R' Hm IH HR' -> HU Rm Hmd.
    pose proof (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as Hf; cbn [unit_full] in Hf; destruct Hf as (HΔ & Ha & HE).
    destruct (IH HE R' HR') as (K & RK & Hnf & HK & HmK & HmdK).
    pose proof (ds_mod_is_mod _ _ _ _ HR') as Him.
    destruct Δ as [| e Δ'].
    + rewrite ds_up_nil, (ds_is_mod_mod _ _ _ Him) in Hmd; injection Hmd as <-.
      exists K, RK; split; [ exact Hnf |]; split; [ eapply wf_me_trans; [ apply wf_me_beta_alias0; exact HE | exact HK ] |].
      split; assumption.
    + exists (me_lit (gu_mk (e :: Δ') (md_alias K))), (ds_up (e :: Δ') R'); split; [ apply unf_alias; [ discriminate | exact Hnf ] |].
      split; [ apply wf_me_lit; eapply wf_unit_eq_alias;
               [ apply ext_of_ctx; exact HΔ | exact Ha | exact Ha | exact HK | exact (wf_modexp_eq_refl_right HK) ] |].
      split; [ apply dn_lit; eapply un_alias; [ exact HmK | exact HmdK ] | exact Hmd ].
Qed.

(** A well-formed module expression is equal to a unit in normal form
    denoting its module part. *)
Lemma lookup_sound_nf : forall Θ Ξ Γ H R Rm, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H R -> ds_mod Θ Ξ R = Some Rm ->
    exists K RK, unit_nf Θ Ξ K /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ K /\ mdenote Θ Ξ Γ K RK /\ ds_mod Θ Ξ RK = Some Rm.
Proof.
  intros * HH Hm Hmd.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  exact (proj1 (lookup_sound_all _ _ Hg) _ _ _ Hm HH _ Hmd).
Qed.

(** ** Units in Normal Form Are the Units of What They Denote

    A unit in normal form is the unit of the module part it denotes
    ([ds_unit]): a filed module at arguments is itself, a local body its
    own literal as written, and an alias with parameters of a unit in
    normal form the alias of that unit's unit, which flattening merges when
    it is a literal. *)

(** A literal well formed as a module expression is a well-formed unit. *)
Lemma lit_unit_wf : forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * HU; pose proof (proj1 (modexp_gen _ _ _ _ _ HU)) as Hf; cbn [gen_m] in Hf; exact (unit_eq_of_full _ _ _ _ Hf).
Qed.

(** The literal an alias of a literal flattens to is well formed when the
    alias is. *)
Lemma flatten_unit_wf : forall Θ Ξ Γ Δ Δ' D,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ' ++ Δ) D ≈ gu_mk (Δ' ++ Δ) D.
Proof.
  intros * HU; pose proof (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as Hf; cbn [unit_full] in Hf.
  destruct Hf as (HC & Ha & HE).
  eapply wf_unit_eq_refl_right; apply wf_unit_eq_flatten; [ apply ext_of_ctx; exact HC | exact Ha | apply lit_unit_wf; exact HE ].
Qed.

(** An alias with parameters of the unit of a module part is the unit of
    the module part abstracted over the parameters. *)
Lemma alias_unit_up : forall Θ Ξ Γ Δ Rm, Δ <> nil -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ -> tele_ass Δ -> ds_is_mod Rm ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ ds_unit Rm ≈ ds_unit Rm ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit (gu_mk Δ (md_alias (ds_unit Rm))) ≈ ds_unit (ds_up Δ Rm).
Proof.
  intros * Hne HΔ Ha Hm HR.
  destruct Rm as [A om | Δ' Φ | [| e Θ'] p T Φ Ns | Θ0 p Ns | Θ0 p Ns | ]; cbn in Hm; try contradiction; cbn [ds_up ds_unit] in HR |- *.
  - (* a local body: flattened *)
    apply wf_me_lit, wf_unit_eq_flatten; [ exact HΔ | exact Ha | apply lit_unit_wf; exact HR ].
  - (* a filed module at arguments: the alias is the unit *)
    rewrite app_nil_l; destruct Δ as [| e Δ]; [ contradiction |]; apply wf_me_lit, wf_unit_eq_alias;
      [ exact HΔ | exact Ha | exact Ha | exact HR | exact HR ].
  - (* an alias of a filed module at arguments: flattened *)
    apply wf_me_lit, wf_unit_eq_flatten; [ exact HΔ | exact Ha | apply lit_unit_wf; exact HR ].
Qed.

Lemma unit_nf_canon : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall K, unit_nf Θ Ξ K -> forall Γ RK Rm,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ K ≈ K -> mdenote Θ Ξ Γ K RK -> ds_mod Θ Ξ RK = Some Rm -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ K ≈ ds_unit Rm.
Proof.
  intros Θ Ξ Hg K Hnf; induction Hnf as [p T Φ Ns Hl | Δ Φ | Δ E HΔ HE IH]; intros * HK Hm Hmd.
  - destruct (filed_denote _ _ Hg _ _ _ Γ Ns (gc_loc_of_loc _ _ Hg _ _ _ Hl)) as (R0 & Hm0 & Hmd0).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ Hm0), Hmd0 in Hmd; injection Hmd as <-; exact HK.
  - (* a local body: its own literal *)
    apply mdenote_lit_inv in Hm; inversion Hm; subst.
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    cbn in Hmd; injection Hmd as <-; cbn [ds_unit]; exact HK.
  - (* an alias with parameters: its target, then the alias of the target's unit *)
    pose proof (proj1 (modexp_gen _ _ _ _ _ HK)) as Hf; cbn [gen_m unit_full] in Hf; destruct Hf as (HC & Ha & HEE).
    apply mdenote_lit_inv in Hm; inversion Hm as [| ? ? ? ? RE R'' HmE HmdE]; subst.
    pose proof (ds_mod_is_mod _ _ _ _ HmdE) as Him.
    rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ Him)) in Hmd; injection Hmd as <-.
    pose proof (IH _ _ _ HEE HmE HmdE) as HEu.
    eapply wf_me_trans;
      [ apply wf_me_lit, wf_unit_eq_alias;
        [ apply ext_of_ctx; exact HC | exact Ha | exact Ha | exact HEu | exact (wf_modexp_eq_refl_right HEu) ] |].
    apply alias_unit_up; [ exact HΔ | apply ext_of_ctx; exact HC | exact Ha | exact Him | exact (wf_modexp_eq_refl_right HEu) ].
Qed.

(** Lookup is sound: a well-formed module expression is equal to the unit
    of the module part of what it denotes, [H ≈ ⌜R̂⌝]. *)
Theorem lookup_sound : forall Θ Ξ Γ H R Rm, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H R -> ds_mod Θ Ξ R = Some Rm ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ ds_unit Rm.
Proof.
  intros * HH Hm Hmd.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  destruct (lookup_sound_nf _ _ _ _ _ _ HH Hm Hmd) as (K & RK & Hnf & HK & HmK & HmdK).
  eapply wf_me_trans; [ exact HK |].
  exact (unit_nf_canon _ _ Hg _ Hnf _ _ _ (wf_modexp_eq_refl_right HK) HmK HmdK).
Qed.

(** [A.x ≈ P.x], for [module A := P]: the module expression is the filed
    module ([lookup_sound]), and the member reads the same entry of it. *)
Lemma mem_alias_filed : forall Θ Ξ Γ H p T Φ RH x R A,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H RH -> ds_mod Θ Ξ RH = Some (ds_closed nil p T Φ nil) ->
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ a_mem (qname_mod p) x : A.
Proof.
  intros * HH HmH HmdH Hm Ht.
  pose proof (presup_modexp_eq_ctx HH) as HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (lookup_sound _ _ _ _ _ _ HH HmH HmdH) as HHp; cbn [ds_unit me_apps] in HHp.
  pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg HmH) HmdH) as Hl; cbn in Hl.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hr | ? ? ? ? Hq Hk];
    subst.
  { cbn in Ht; discriminate. }
  { (* the open frame of a member's module: [H] is the filed module itself *)
    destruct (ind_frame_mem_mod _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Hq Hk HmH HmdH) as (Hp & _ & _).
    rewrite (mod_qname_inv _ _ Hp) in Hm |- *.
    apply wf_exp_eq_refl; exact (wf_mem_desc _ _ _ _ _ _ _ (wf_modexp_eq_refl_right HHp) Hm Ht). }
  2: { (* the open frame of a record's module: [H] is the filed module itself *)
    destruct (record_frame_mem_mod _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Hq Hk HmH HmdH) as (Hp & _ & _).
    rewrite (mod_qname_inv _ _ Hp) in Hm |- *.
    apply wf_exp_eq_refl; exact (wf_mem_desc _ _ _ _ _ _ _ (wf_modexp_eq_refl_right HHp) Hm Ht). }
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ HmH), HmdH in Hmd; injection Hmd as <-.
  destruct (filed_denote _ _ Hg _ _ _ Γ nil (gc_loc_of_loc _ _ Hg _ _ _ Hl)) as (Rp & Hmp & Hmdp); cbn [me_apps] in Hmp.
  assert (Hmx : mdenote Θ Ξ Γ (me_mem (qname_mod p) x) R)
    by (eapply dn_mem; [ exact Hmp | exact Hmdp | exact He | exact Hed | exact Hr ]).
  eapply wf_exp_eq_mem_cong; [ exact HHp | exact Hm | exact Ht | exact Hmx | exact Ht |].
  exact (wf_mem_desc _ _ _ _ _ _ _ (wf_modexp_eq_refl_right HHp) Hmx Ht).
Qed.

(** [H.x ≈ λ Θ'. P.x N⃗], for a module expression whose module part is a
    filed module [P] at arguments [N⃗] over outside parameters [Θ']: as a
    name ([mem_closed_part_named]), or, read bare, the filed member
    ([mem_alias_filed]). *)
Theorem mem_closed_part : forall Θ Ξ Γ H RH Θ' p T Φ Ns x R A,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H RH -> ds_mod Θ Ξ RH = Some (ds_closed Θ' p T Φ Ns) ->
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ ctx_fn Θ' (apps (a_mem (qname_mod p) x) Ns) : A.
Proof.
  intros * HH HmH HmdH Hm Ht.
  destruct Θ' as [| e Θ'']; [ destruct Ns as [| N Ns'] |].
  - exact (mem_alias_filed _ _ _ _ _ _ _ _ _ _ _ HH HmH HmdH Hm Ht).
  - eapply mem_closed_part_named; [ right; discriminate | eassumption .. ].
  - eapply mem_closed_part_named; [ left; discriminate | eassumption .. ].
Qed.
