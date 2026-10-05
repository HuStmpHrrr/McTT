(** * Member Types Are Types, and Reducts Inhabit Them

    The canonical type of a member of a well-formed module expression is a
    type, and its δ-reduct, when it has one, inhabits it ([member_wf]).  The
    rules of the core do not need this, since [wf_mem] carries both facts as
    premises; a checker does, since it cannot check either of them by
    recursion on the term.  The argument of a module application is checked
    against the domain of the module's arity, and the domain of a member's
    type agrees with it, which the PER model shows ([app_domain]). *)

From Stdlib Require Import Lia List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Consequences.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Completeness Require Import UniverseCases MemberReps MemberSem ModexpCases ModuleCases.
From Mctt.Core.Syntactic.System Require Import MemberWf GlobalPresup MemberLemmas.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Types Below a Universe *)

Lemma pi_typ_absurd : forall Γ A B i k, Γ ⊢ Π A B ≈ Type@i : Type@k -> False.
Proof.
  intros * H.
  destruct (completeness_ty H) as [W [HW1 HW2]].
  inversion HW1; subst; inversion HW2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  congruence.
Qed.

Lemma subtyp_univ_inv : forall Γ X i, Γ ⊢ X ⊆ Type@i -> exists j k, j <= i /\ Γ ⊢ X ≈ Type@j : Type@k.
Proof.
  intros * H.
  destruct (subtyp_spec H) as [[k Hk] | [(j & j' & [k Hk] & [k' Hk'] & Hle) | (A1 & A2 & B1 & B2 & _ & [k Hk] & _)]].
  - exists i, k; split; [ lia | exact Hk ].
  - pose proof (exp_eq_typ_implies_eq_level Hk') as ->.
    exists j, k; split; [ exact Hle | exact Hk ].
  - exfalso; eapply pi_typ_absurd; exact Hk.
Qed.


(** ** A Binding's Value, Read Back Through the Binding *)

(** Under [Γ ▸ D ≔ N], a term is equal to its instance at [N], weakened: the
    variable is equal to [N[↑]ʷ] by δ. *)
Lemma def_ctx_inst : forall Γ D N k X Y,
    Γ ⊢ D : Type@k -> Γ ⊢ N : D -> Γ ▸ D ≔ N ⊢ X : Y ->
    Γ ▸ D ≔ N ⊢ X ≈ X[Id,,N][↑]ʷ : Y.
Proof.
  intros * HD HN HX.
  assert (HC : ⊢ Γ ▸ D ≔ N) by mauto 3.
  assert (Hw : Γ ▸ D ≔ N ⊢s Wk : Γ) by mauto 3.
  assert (HNw : Γ ▸ D ≔ N ⊢ N[Wk] : D[Wk]) by mauto 3.
  assert (Hσ : Γ ▸ D ≔ N ⊢s Wk ,, N[Wk] : Γ ▸ D ≔ N)
    by (eapply wf_sub_extend_def; [ exact Hw | exact HD | exact HN | exact HNw | eapply wf_exp_eq_refl; exact HNw ]).
  replace (X[Id,,N][↑]ʷ) with (X[Wk ,, N[Wk]]).
  2:{ rewrite exp_wk_sub; apply exp_sub_sb_eq; intros [| x]; cbn; [ rewrite exp_sub_of_shift | ]; reflexivity. }
  assert (Heq : Γ ▸ D ≔ N ⊢s Id ≈ Wk ,, N[Wk] : Γ ▸ D ≔ N).
  { constructor; [ mauto 3 | exact Hσ |].
    intros [| x] B Hx; inversion Hx; subst; cbn [sentry_exp sb_id sb_extend exp_sub]; rewrite ?exp_sub_id.
    - rewrite exp_sub_of_shift. eapply wf_exp_eq_var_delta; [ exact HC | constructor ].
    - apply wf_exp_eq_refl; mauto 3. }
  pose proof (sub_eq_preserves_exp _ _ _ _ HX _ _ _ Heq) as H'.
  rewrite !exp_sub_id in H'; exact H'.
Qed.



(** Under [Γ ▹ₘ U], a term is equal to its instance at the literal [⌜U⌝],
    weakened: equal substitutions agree on terms only, and the slot is not a
    term. *)
Lemma mod_ctx_inst : forall Γ U X Y,
    gc_ctx ⍮ Γ ⊢ᵘ U ≈ U -> Γ ▹ₘ U ⊢ X : Y ->
    Γ ▹ₘ U ⊢ X ≈ X[Id ,,ₘ me_lit U][↑]ʷ : Y.
Proof.
  intros * HU HX.
  assert (HC : ⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
  assert (Hw : Γ ▹ₘ U ⊢s Wk : Γ) by mauto 3.
  assert (Hσ : Γ ▹ₘ U ⊢s Wk ,,ₘ me_lit U[Wk]ᵘ : Γ ▹ₘ U)
    by (eapply wf_sub_extend_mod; [ exact Hw | exact HU | eapply sub_preserves_unit; eassumption ]).
  replace (X[Id ,,ₘ me_lit U][↑]ʷ) with (X[Wk ,,ₘ me_lit U[Wk]ᵘ]).
  2:{ rewrite exp_wk_sub; apply exp_sub_sb_eq; intros [| x]; cbn; [| reflexivity ].
      rewrite (gunit_sub_of_wk_ext _ _ _ (symmetry sb_of_wk_shift)); reflexivity. }
  assert (Heq : Γ ▹ₘ U ⊢s Id ≈ Wk ,,ₘ me_lit U[Wk]ᵘ : Γ ▹ₘ U).
  { constructor; [ mauto 3 | exact Hσ |].
    intros [| x] B Hx; inversion Hx; subst; cbn [sentry_exp sb_id sb_extend exp_sub]; rewrite ?exp_sub_id.
    apply wf_exp_eq_refl; mauto 3. }
  pose proof (sub_eq_preserves_exp _ _ _ _ HX _ _ _ Heq) as H'.
  rewrite !exp_sub_id in H'; exact H'.
Qed.

(** ** Local Bindings at the Level of Types *)

Lemma typ_let_inv : forall Γ oD N T i, Γ ⊢ a_let (b_def oD N) T : Type@i ->
    exists D, let_ann oD D /\ (exists k, Γ ⊢ D : Type@k) /\ Γ ⊢ N : D /\ Γ ▸ D ≔ N ⊢ T : Type@i.
Proof.
  intros * H.
  destruct (wf_let_inversion H) as (D & k & C & Hann & HD & HN & HT & Hsub).
  destruct (subtyp_univ_inv _ _ _ Hsub) as (j & k' & Hle & HCj).
  exists D; split; [ exact Hann |].
  split; [ eauto | split; [ exact HN |] ].
  assert (exists l, Γ ▸ D ≔ N ⊢ C : Type@l) as [l HCt] by (gen_presups; eauto).
  pose proof (def_ctx_inst _ _ _ _ _ _ HD HN HCt) as HCi.
  assert (⊢ Γ ▸ D ≔ N) by mauto 3.
  assert (HCw : Γ ▸ D ≔ N ⊢ C[Id,,N][↑]ʷ ≈ Type@j[↑]ʷ : Type@k'[↑]ʷ)
    by (eapply wk_preserves_exp_eq; [ exact HCj | mauto 3 ]).
  cbn in HCw.
  assert (Γ ▸ D ≔ N ⊢ C ≈ Type@j : Type@(max l k')) by mauto 4 using lift_exp_eq_max_left, lift_exp_eq_max_right.
  eapply lift_exp_ge; [ exact Hle |]; mauto 3.
Qed.


Lemma typ_let_mod_inv : forall Γ U T i, Γ ⊢ ℓₘ U in T : Type@i ->
    gc_ctx ⍮ Γ ⊢ᵘ U ≈ U /\ Γ ▹ₘ U ⊢ T : Type@i.
Proof.
  intros * H.
  destruct (wf_let_mod_inversion H) as (C & HU & HT & Hsub).
  destruct (subtyp_univ_inv _ _ _ Hsub) as (j & k' & Hle & HCj).
  split; [ exact HU |].
  assert (exists l, Γ ▹ₘ U ⊢ C : Type@l) as [l HCt] by (gen_presups; eauto).
  pose proof (mod_ctx_inst _ _ _ _ HU HCt) as HCi.
  assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
  assert (HCw : Γ ▹ₘ U ⊢ C[Id ,,ₘ me_lit U][↑]ʷ ≈ Type@j[↑]ʷ : Type@k'[↑]ʷ)
    by (eapply wk_preserves_exp_eq; [ exact HCj | mauto 3 ]).
  cbn in HCw.
  assert (Γ ▹ₘ U ⊢ C ≈ Type@j : Type@(max l k')) by mauto 4 using lift_exp_eq_max_left, lift_exp_eq_max_right.
  eapply lift_exp_ge; [ exact Hle |]; mauto 3.
Qed.

(** ** The [Π] a Type Is *)

Lemma pi_view_wf : forall A Γ i B C, Γ ⊢ A : Type@i -> pi_view A = Some (B, C) ->
    Γ ⊢ A ≈ Π B C : Type@i /\ Γ ⊢ B : Type@i /\ Γ ▹ B ⊢ C : Type@i.
Proof.
  induction A; intros * HA Hp; cbn in Hp; try discriminate.
  - injection Hp as <- <-.
    destruct (wf_pi_inversion' HA) as [HB HC].
    split; [ mauto 3 | split; assumption ].
  - destruct b as [oD N | U];
      (destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection Hp as <- <-).
    + destruct (typ_let_inv _ _ _ _ _ HA) as (D & Hann & [k HD] & HN & HT).
      destruct (IHA _ _ _ _ HT eq_refl) as (HTe & HB' & HC').
      pose proof (wf_sub_single_def _ _ _ _ _ HD HN) as Hσ.
      pose proof (sub_preserves_typ_eq _ _ _ _ _ _ _ HTe Hσ) as HTs; cbn in HTs.
      split; [| split ].
      * eapply wf_exp_eq_trans; [ eapply wf_exp_eq_let_zeta_typ; cycle 3; [ solve_let_ann | eassumption .. ] | exact HTs ].
      * eapply sub_preserves_typ; eassumption.
      * eapply sub_preserves_typ; [ exact HC' | eapply wf_sub_q'; eassumption ].
    + destruct (typ_let_mod_inv _ _ _ _ HA) as (HU & HT).
      destruct (IHA _ _ _ _ HT eq_refl) as (HTe & HB' & HC').
      pose proof (wf_sub_single_mod _ _ _ HU) as Hσ.
      pose proof (sub_preserves_typ_eq _ _ _ _ _ _ _ HTe Hσ) as HTs; cbn in HTs.
      split; [| split ].
      * eapply wf_exp_eq_trans; [ eapply wf_exp_eq_let_mod_zeta_typ; eassumption | exact HTs ].
      * eapply sub_preserves_typ; eassumption.
      * eapply sub_preserves_typ; [ exact HC' | eapply wf_sub_q'; eassumption ].
Qed.

(** ** The Outermost Parameter of an Arity

    An arity is typed by its arity type: its outermost parameter is a type,
    and instantiating it with an argument of that type leaves an arity. *)

Lemma tele_view_wf : forall Γ T i B T1, Γ ⊢ ctx_pi T ⊤ : Type@i -> tele_view T = Some (B, T1) ->
    Γ ⊢ ctx_pi T ⊤ ≈ Π B (ctx_pi T1 ⊤) : Type@i /\ Γ ⊢ B : Type@i /\ Γ ▹ B ⊢ ctx_pi T1 ⊤ : Type@i.
Proof.
  intros * HT Hv; apply pi_view_wf; [ exact HT | rewrite tele_view_pi, Hv; reflexivity ].
Qed.

Lemma tele_inst_wf : forall Γ T i N T', Γ ⊢ ctx_pi T ⊤ : Type@i -> tele_inst T N = Some T' ->
    (forall B T1, tele_view T = Some (B, T1) -> Γ ⊢ N : B) -> Γ ⊢ ctx_pi T' ⊤ : Type@i.
Proof.
  intros * HT Hi HN; unfold tele_inst in Hi.
  destruct (tele_view T) as [[B T1] |] eqn:Hv; [| discriminate ]; injection Hi as <-.
  destruct (tele_view_wf _ _ _ _ _ HT Hv) as (_ & HB & HC).
  pose proof (wf_sub_single _ _ _ _ _ HB (HN _ _ eq_refl)) as Hσ.
  pose proof (sub_preserves_typ _ _ _ _ _ _ HC Hσ) as H; rewrite ctx_pi_sub in H; exact H.
Qed.

(** ** Semantic Equality of Types, Read Back *)

Lemma sem_typ_eq_syn : forall Γ A A' i,
    Γ ⊢ A : Type@i -> Γ ⊢ A' : Type@i -> Γ ⊨ A ≈ A' : Type@i -> Γ ⊢ A ≈ A' : Type@i.
Proof.
  intros * HA HA' H.
  destruct (rel_exp_under_ctx_at_initial_env H)
    as [ρ [j [elem_rel [a [m [m' [Hρ [Ha [Hm [Hm' [Htyp Hrel]]]]]]]]]]].
  destruct (per_elem_then_per_top Htyp Hrel (length Γ)) as [W [HW HW']].
  assert (H1 : nbe_f Γ A Type@i W) by (econstructor; eassumption).
  assert (H2 : nbe_f Γ A' Type@i W) by (econstructor; eassumption).
  pose proof (soundness' HA H1); pose proof (soundness' HA' H2).
  eapply wf_exp_eq_trans; [ eassumption | eapply wf_exp_eq_sym; eassumption ].
Qed.


(** ** Arities Through an Application

    A module expression applied to an argument has a [Π] for its arity, and
    then every member type it has is a [Π] as well, syntactically: an
    argument is still missing at each of its members.  This is read off the
    PER model ([sem_mt]). *)

Lemma wf_modexp_sem_mt : forall Γ H, gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    sem_mt gc_ctx Γ H /\ Γ ⊨ᵐ H ≈ H.
Proof.
  intros * HH.
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & _ & Km).
  pose proof (gctx_sem _ (ctx_wf_gctx _ _ (presup_modexp_eq_ctx HH))) as Hid.
  destruct (Km _ _ _ _ HH _ Hid) as (HR & HS & _).
  destruct GC; split; assumption.
Qed.

Lemma pi_view_lets_some : forall Ψ X, lets_only Ψ ->
    (forall σ, exists B C, pi_view X[σ] = Some (B, C)) ->
    forall σ, exists B C, pi_view (ctx_pi Ψ X)[σ] = Some (B, C).
Proof.
  induction Ψ as [| e Ψ IH]; intros X HL HX σ; cbn [ctx_pi]; [ apply HX |].
  inversion HL as [| ? ? He HL']; subst.
  destruct e as [B0 | B0 M0 | U0]; [ exfalso; exact (He _ eq_refl) | |];
    (apply IH; [ exact HL' |]; intros σ'; cbn;
     destruct (HX (q σ')) as (B & C & ->); eauto).
Qed.

Lemma rep_pos_pi : forall D A k b, rep D A k b -> forall n, k = S n ->
    forall σ, exists B C, pi_view A[σ] = Some (B, C).
Proof.
  induction 1 as [D X i b HD HX Hb | D τ D0 Ψ Δp X m b Hg0 HΔ HΨ HC Hr IH];
    intros n Hk σ; [ discriminate |].
  rewrite exp_sub_sub.
  destruct Δp as [| e0 Δ0] eqn:EΔ.
  - cbn [List.length plus] in Hk; subst m.
    rewrite app_nil_r.
    apply pi_view_lets_some; [ exact HΨ |]; intros; eapply IH; reflexivity.
  - assert (Hne : e0 :: Δ0 <> nil) by discriminate.
    destruct (exists_last Hne) as (l & e & El).
    rewrite <- EΔ in *; rewrite El in *; clear El EΔ e0 Δ0 Hne.
    apply Forall_app in HΔ as [_ He].
    inversion He as [| ? ? [B0 ->] _]; subst.
    rewrite app_assoc, ctx_pi_app; cbn; eauto.
Qed.

Lemma app_arity_pi : forall Γ H T0 B0 T1,
    gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_ctx Γ H nil (mr_mod T0) -> tele_view T0 = Some (B0, T1) ->
    forall ch R, member_type gc_ctx Γ H ch R -> (mres_kind R = mk_term -> ch <> nil) ->
    exists B' C', pi_view (mres_ty R) = Some (B', C').
Proof.
  intros * HH Hm0 Hv * Hm Hch.
  destruct (wf_modexp_sem_mt _ _ HH) as [[_ S2] _].
  destruct (S2 nil _ ch R Hm0 eq_refl Hm Hch) as (m & n & Hr0 & Hr & Hmn); cbn [mres_ty] in Hr0.
  assert (Hp : pi_view (ctx_pi T0 ⊤) = Some (B0, ctx_pi T1 ⊤)) by (rewrite tele_view_pi, Hv; reflexivity).
  destruct (rep_pos_of_pi _ _ _ Hr0 _ _ Hp) as [m' ->].
  destruct n as [| n']; [ lia |].
  destruct (rep_pos_pi _ _ _ _ Hr n' eq_refl Id) as (B' & C' & Hp').
  rewrite exp_sub_id in Hp'; eauto.
Qed.


(** ** Prefixes of Member Chains

    Each prefix of a member chain of a well-formed module is a module.  A
    chain of a unit is read in the unit filed under its path, which is
    well formed at [⋅]. *)

Lemma umt_mod_mod : forall Θ Γ Δ Φ Φ' y pm Uy ch T,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    unit_member_type Θ (self_ent Φ' :: Δ ++ Γ) Uy ch (mr_mod T) ->
    unit_member_type Θ Γ (gu_body Δ Φ) (y :: ch) (mr_mod (T ++ self_ent Φ' :: Δ)).
Proof.
  intros * Hp Hu; change (mr_mod (T ++ self_ent Φ' :: Δ)) with (mres_gen (self_ent Φ' :: Δ) (mr_mod T)).
  eapply umt_mod; [ discriminate | exact Hp | exact Hu ].
Qed.

Lemma umt_alias_mod : forall Θ Γ Δ E ch T,
    member_type Θ (Δ ++ Γ) E ch (mr_mod T) ->
    unit_member_type Θ Γ (gu_mk Δ (md_alias E)) ch (mr_mod (T ++ Δ)).
Proof.
  intros * Hm; change (mr_mod (T ++ Δ)) with (mres_gen Δ (mr_mod T)); apply umt_alias; exact Hm.
Qed.

Theorem member_type_prefix :
  (forall Γ H ch R, member_type gc_ctx Γ H ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
     exists T', member_type gc_ctx Γ H ch1 (mr_mod T')) /\
  (forall Γ U ch R, unit_member_type gc_ctx Γ U ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_ctx ⍮ Γ ⊢ᵘ U ≈ U ->
     exists T', unit_member_type gc_ctx Γ U ch1 (mr_mod T')).
Proof.
  apply member_type_both_ind.
  - intros * Hl Hu IH ch1 ch2 -> Hne2 HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (wf_unit_lookup _ _ _ _ (presup_modexp_eq_ctx HH) Hl)) as [T' HT'].
    eexists; eapply mt_unit; eassumption.
  - intros * Hx Hu IH ch1 ch2 -> Hne2 HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (ctx_lookup_mod_wf _ _ _ _ (presup_modexp_eq_ctx HH) Hx)) as [T' HT'].
    eexists; eapply mt_var; eassumption.
  - intros * Hu IH ch1 ch2 -> Hne2 HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (modexp_parts_of_wf _ _ _ HH)) as [T' HT'].
    eexists; eapply mt_lit; eassumption.
  - intros * Hk Hm IH ch1 ch2 -> Hne2 HH.
    destruct (modexp_parts_of_wf _ _ _ HH) as [HH0 _].
    destruct (IH (y :: ch1) ch2 eq_refl Hne2 HH0) as [T' HT'].
    exists T'; eapply mt_mem; [ cbn; discriminate | exact HT' ].
  - intros * Hm IH Ha ch1 ch2 -> Hne2 HH.
    destruct (modexp_parts_of_wf _ _ _ HH) as [HH' (T0 & B0 & T1 & i & Hm0 & Hv0 & _)].
    destruct (IH ch1 ch2 eq_refl Hne2 HH') as [T' HT'].
    destruct (app_arity_pi _ _ _ _ _ HH' Hm0 Hv0 _ _ HT' ltac:(cbn; discriminate)) as (B' & C' & Hp').
    destruct (mres_app_of_pi _ N _ _ Hp') as (R'' & Ha'').
    destruct (mres_app_ty _ _ _ Ha'') as (_ & _ & _ & _ & Hk'').
    destruct R'' as [A'' | T'']; [ discriminate |].
    exists T''; eapply mt_app; eassumption.
  - intros * Hc Hne2 _.
    symmetry in Hc; apply app_eq_nil in Hc as [_ ->]; contradiction.
  - intros * Hp ch1 ch2 Hc Hne2 _.
    destruct ch1 as [| z ch1]; [ eexists; constructor |].
    injection Hc as -> Hc; symmetry in Hc; apply app_eq_nil in Hc as [_ ->]; contradiction.
  - intros * Hk Hp Hu IH ch1 ch2 Hc Hne2 HU.
    destruct ch1 as [| z ch1]; [ eexists; constructor |].
    injection Hc as -> ->.
    destruct (unit_parts_of_wf _ _ _ HU) as (_ & _ & Hb).
    destruct (body_ok_prefix _ _ _ _ _ _ Hb Hp) as [_ HUy].
    destruct (IH ch1 ch2 eq_refl Hne2 HUy) as [T' HT'].
    eexists; eapply umt_mod_mod; [ exact Hp | exact HT' ].
  - intros * Hm IH ch1 ch2 -> Hne2 HU.
    destruct (unit_parts_of_wf _ _ _ HU) as (_ & _ & HE).
    destruct (IH ch1 ch2 eq_refl Hne2 HE) as [T' HT'].
    eexists; eapply umt_alias_mod; eassumption.
Qed.

Lemma me_mems_wf : forall pre Γ H ch R,
    gc_ctx ⍮ Γ ⊢ᵐ H ≈ H -> member_type gc_ctx Γ H (pre ++ ch) R -> ch <> nil ->
    gc_ctx ⍮ Γ ⊢ᵐ me_mems H pre ≈ me_mems H pre.
Proof.
  induction pre as [| y pre IH]; intros * HH Hm Hne; cbn [me_mems app] in *; [ exact HH |].
  destruct (proj1 member_type_prefix _ _ _ _ Hm (y :: nil) (pre ++ ch) eq_refl
              ltac:(destruct pre, ch; cbn; congruence) HH) as [T' HT'].
  eapply IH; [ eapply wf_me_mem; [ exact HH | exact HT' | exact HT' ] | | exact Hne ].
  eapply mt_mem; [ intros _; destruct pre, ch; cbn; congruence | exact Hm ].
Qed.

Lemma spine_nil_noargs : forall H R p0, modexp_spine H = (R, nil, p0) -> me_noargs H.
Proof.
  induction H; intros * Hs; cbn in Hs |- *; auto.
  - destruct (modexp_spine H) as [[R' args'] p0'] eqn:E; injection Hs as -> -> _; eauto.
  - destruct (modexp_spine H) as [[R' args'] p0'] eqn:E; injection Hs as _ Ha _.
    destruct args'; discriminate.
Qed.

(** ** Member References *)

Lemma member_ref_noargs_wf : forall Γ H ch A i M,
    me_noargs H -> gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_ctx Γ H ch (mr_term A) -> ch <> nil ->
    Γ ⊢ A : Type@i -> member_unfold_ch gc_ctx Γ H ch = Some M -> Γ ⊢ M : A ->
    Γ ⊢ member_ref H ch : A.
Proof.
  intros * Hn HH Hm Hne HA HMe HMt.
  destruct (exists_last Hne) as (pre & x & ->).
  rewrite member_ref_mems.
  eapply wf_mem;
    [ apply me_mems_noargs; exact Hn
    | eapply me_mems_wf; [ exact HH | exact Hm | discriminate ]
    | apply me_mems_member_type; [ exact Hm | discriminate ]
    | exact HA
    | unfold member_unfold; rewrite me_mems_unfold; exact HMe
    | exact HMt ].
Qed.

Lemma member_ref_wf : forall Γ H ch A i,
    gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_ctx Γ H ch (mr_term A) -> ch <> nil -> Γ ⊢ A : Type@i ->
    (forall R args p0, modexp_spine H = (R, args, p0) -> Γ ⊢ apps (member_ref R (p0 ++ ch)) args : A) ->
    (exists M, member_unfold_ch gc_ctx Γ H ch = Some M /\ Γ ⊢ M : A) ->
    Γ ⊢ member_ref H ch : A.
Proof.
  intros * HH Hm Hne HA HR (M & HMe & HMt).
  destruct (modexp_spine H) as [[R args] p0] eqn:Es.
  destruct args as [| N args].
  - eapply member_ref_noargs_wf; [ exact (spine_nil_noargs _ _ _ Es) | eassumption .. ].
  - destruct (exists_last Hne) as (pre & x & ->).
    rewrite member_ref_mems.
    eapply wf_mem_app;
      [ eapply me_mems_wf; [ exact HH | exact Hm | discriminate ]
      | exact (me_mems_spine _ _ _ _ _ Es)
      | discriminate
      | exact HA
      | rewrite <- app_assoc; exact (HR _ _ _ eq_refl) ].
Qed.

(** ** The Domain of a Member's Type *)

Lemma dom_agree : forall Γ H T0 B0 T1 i ch R1 B1 C1 j,
    gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_ctx Γ H nil (mr_mod T0) -> tele_view T0 = Some (B0, T1) -> Γ ⊢ B0 : Type@i ->
    member_type gc_ctx Γ H ch R1 -> (mres_kind R1 = mk_term -> ch <> nil) ->
    Γ ⊢ mres_ty R1 ≈ Π B1 C1 : Type@j -> Γ ⊢ B1 : Type@j ->
    exists k, Γ ⊢ B0 ≈ B1 : Type@k.
Proof.
  intros * HH Hm0 Hv HB0 Hm Hch HA1 HB1.
  destruct (wf_modexp_sem_mt _ _ HH) as [HS HHs].
  assert (Hok : gmod_ok gc_ctx) by exact (wf_gctx_closed _ _ (presup_modexp_eq_ctx HH)).
  destruct (arity_pi _ _ _ _ _ HS Hm0 Hv) as (l & HBl & _ & HAl).
  pose proof (app_domain Hok _ _ _ _ _ _ HS HHs Hm0 HAl HBl _ _ _ _ _ Hm Hch
                (completeness_fundamental_exp_eq _ _ _ _ HA1) (completeness_fundamental_exp _ _ _ HB1)) as Hs.
  exists (max (max i l) j).
  apply sem_typ_eq_syn;
    [ eapply lift_exp_ge; [| exact HB0 ]; lia | eapply lift_exp_ge; [| exact HB1 ]; lia
    | eapply rel_exp_cumu_ge; [| exact Hs ]; lia ].
Qed.

(** ** Member Types Are Types *)

Theorem member_wf :
  (forall Γ H ch R, member_type gc_ctx Γ H ch R ->
     gc_ctx ⍮ Γ ⊢ᵐ H ≈ H -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Type@i) /\
     (mres_kind R = mk_term -> exists M, member_unfold_ch gc_ctx Γ H ch = Some M /\ Γ ⊢ M : mres_ty R) /\
     (mres_kind R = mk_term -> forall Q args p0, modexp_spine H = (Q, args, p0) ->
        Γ ⊢ apps (member_ref Q (p0 ++ ch)) args : mres_ty R)) /\
  (forall Γ U ch R, unit_member_type gc_ctx Γ U ch R ->
     gc_ctx ⍮ Γ ⊢ᵘ U ≈ U -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Type@i) /\
     (mres_kind R = mk_term -> exists M, member_expansion U ch = Some M /\ Γ ⊢ M : mres_ty R)).
Proof.
  apply member_type_both_ind.
  - (* a chain of a unit, read in the unit, which is closed *)
    intros Γ fp U ch R Hl Hu IH HH Hch.
    pose proof (presup_modexp_eq_ctx HH) as HΓ.
    pose proof (wf_gctx_closed _ _ HΓ) as Hc.
    pose proof (gctx_closed_unit_lookup _ _ _ Hc Hl) as HUs.
    destruct (IH (wf_unit_lookup _ _ _ _ HΓ Hl) Hch) as ([i HA] & HMu).
    pose proof (mres_ty_scoped _ _ (proj2 (member_type_scoped _ Hc) _ _ _ _ Hu I HUs)) as HAs.
    assert (HAΓ : Γ ⊢ mres_ty R : Type@i) by (eapply closed_weaken_exp; [ exact HΓ | exact HA | exact HAs | exact I ]).
    assert (HMΓ : mres_kind R = mk_term -> exists M, member_unfold_ch gc_ctx Γ (me_unit fp) ch = Some M /\ Γ ⊢ M : mres_ty R).
    { intros e; destruct (HMu e) as (M & HMe & HMt).
      exists M; split; [ cbn; rewrite Hl; exact HMe |].
      eapply closed_weaken_exp; [ exact HΓ | exact HMt | exact (member_expansion_scoped _ _ _ _ HMe HUs) | exact HAs ]. }
    split; [ eauto | split; [ exact HMΓ |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMΓ e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_unit; [ exact Hl | exact Hu ] | exact Hne | exact HAΓ | exact HMe | exact HMt ].
  - (* a module slot *)
    intros Γ x U ch R Hx Hu IH HH Hch.
    pose proof (presup_modexp_eq_ctx HH) as HΓ.
    destruct (IH (ctx_lookup_mod_wf _ _ _ _ HΓ Hx) Hch) as ([i HA] & HMu).
    assert (HMΓ : mres_kind R = mk_term -> exists M, member_unfold_ch gc_ctx Γ (me_var x) ch = Some M /\ Γ ⊢ M : mres_ty R).
    { intros e; destruct (HMu e) as (M & HMe & HMt).
      exists M; split; [ cbn; rewrite (ctx_find_mod_complete _ _ _ Hx); exact HMe | exact HMt ]. }
    split; [ eauto | split; [ exact HMΓ |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMΓ e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_var; [ exact Hx | exact Hu ] | exact Hne | exact HA | exact HMe | exact HMt ].
  - (* a literal *)
    intros Γ U ch R Hu IH HH Hch.
    destruct (IH (modexp_parts_of_wf _ _ _ HH) Hch) as ([i HA] & HMu).
    split; [ eauto | split; [ exact HMu |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMu e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_lit; exact Hu | exact Hne | exact HA | exact HMe | exact HMt ].
  - (* a selection *)
    intros Γ H y ch R Hk Hm IH HH Hch.
    destruct (modexp_parts_of_wf _ _ _ HH) as [HH0 _].
    destruct (IH HH0 ltac:(intros; discriminate)) as (HA & HMu & HR).
    split; [ exact HA | split; [ exact HMu |] ].
    intros e Q args p0 Hs; cbn in Hs.
    destruct (modexp_spine H) as [[R' args'] p0'] eqn:Es; injection Hs as <- <- <-.
    rewrite <- app_assoc; exact (HR e _ _ _ eq_refl).
  - (* an application *)
    intros Γ H N ch R R' Hm IH Ha HH Hch.
    destruct (modexp_parts_of_wf _ _ _ HH) as [HH' (T0 & B0 & T1 & i0 & Hm0 & Hv0 & HB0 & HN0)].
    destruct (mres_app_ty _ _ _ Ha) as (B & C & Hp & HR' & Hk').
    rewrite HR', Hk'; rewrite Hk' in Hch.
    destruct (IH HH' Hch) as ([j HA] & HMu & HR).
    destruct (pi_view_wf _ _ _ _ _ HA Hp) as (HAe & HB & HC).
    destruct (dom_agree _ _ _ _ _ _ _ _ _ _ _ HH' Hm0 Hv0 HB0 Hm Hch HAe HB) as [k HBB].
    pose proof (wf_conv' _ _ _ _ _ _ HN0 HBB) as HN.
    pose proof (wf_sub_single _ _ _ _ _ HB HN) as Hσ.
    split; [ exists j; exact (sub_preserves_typ _ _ _ _ _ _ HC Hσ) | split ].
    + intros e; destruct (HMu e) as (M & HMe & HMt).
      exists (a_app M N); split; [ cbn; rewrite HMe; reflexivity |].
      eapply wf_app; [ exact HB | exact HC | eapply wf_conv'; [ exact HMt | exact HAe ] | exact HN ].
    + intros e Q args p0 Hs; cbn in Hs.
      destruct (modexp_spine H) as [[Q' args'] p0'] eqn:Es; injection Hs as <- <- <-.
      rewrite apps_snoc.
      eapply wf_app; [ exact HB | exact HC | eapply wf_conv'; [ exact (HR e _ _ _ eq_refl) | exact HAe ] | exact HN ].
  - (* the unit itself *)
    intros Γ Δ Φ HU _; cbn [mres_ty mres_kind].
    split; [| discriminate ].
    destruct (unit_parts_of_wf _ _ _ HU) as (HC & _ & _).
    assert (Δ ++ Γ ⊢ ⊤ : Type@0) by (econstructor; exact HC).
    eapply ctx_pi_wf; eassumption.
  - (* a definition of a body, under its self slot *)
    intros Γ Δ Φ Φ' x pv A M Hp HU _; cbn [mres_ty mres_kind].
    destruct (unit_parts_of_wf _ _ _ HU) as (HC & _ & Hb).
    destruct (body_ok_prefix _ _ _ _ _ _ Hb Hp) as (Hb' & HE).
    destruct M as [M |]; [| contradiction ]; destruct HE as ([i HA] & HM).
    pose proof (self_ctx_wf _ _ _ HC Hb') as HC'.
    split; [ eapply (ctx_pi_wf _ (self_ent Φ' :: Δ)); eassumption |].
    intros _; eexists; split; [ unfold member_expansion; rewrite Hp; reflexivity |].
    eapply (ctx_fn_wf _ (self_ent Φ' :: Δ)); eassumption.
  - (* a member of a submodule of a body, under its self slot *)
    intros Γ Δ Φ Φ' y pm Uy ch R Hk Hp Hu IH HU Hch; rewrite mres_ty_gen, mres_kind_gen in *.
    destruct (unit_parts_of_wf _ _ _ HU) as (HC & _ & Hb).
    destruct (body_ok_prefix _ _ _ _ _ _ Hb Hp) as (Hb' & HUy).
    pose proof (self_ctx_wf _ _ _ HC Hb') as HC'.
    destruct (IH HUy Hk) as ([i HA] & HMu).
    split; [ eapply (ctx_pi_wf _ (self_ent Φ' :: Δ)); eassumption |].
    intros e; destruct (HMu e) as (M1 & HM1e & HM1t).
    pose proof (Hk e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    destruct ch as [| z ch'']; [ exfalso; exact (Hne eq_refl) |].
    eexists; split; [ unfold member_expansion; rewrite Hp; reflexivity |].
    eapply (ctx_fn_wf _ (self_ent Φ' :: Δ)); [ exact HC' | exact HA |].
    eapply member_ref_noargs_wf with (i := i) (M := M1);
      [ exact I | apply wf_me_lit; exact HUy | eapply mt_lit; exact Hu | exact Hne | exact HA
      | cbn; exact HM1e | exact HM1t ].
  - (* a member of an alias unit *)
    intros Γ Δ E ch R Hm IH HU Hch; rewrite mres_ty_gen, mres_kind_gen in *.
    destruct (unit_parts_of_wf _ _ _ HU) as (HC & _ & HE).
    destruct (IH HE Hch) as ([i HA] & HMu & HR).
    split; [ eapply ctx_pi_wf; eassumption |].
    intros e; pose proof (Hch e) as Hne.
    eexists; split; [ exact (member_expansion_alias _ _ _ Hne) |].
    eapply ctx_fn_wf; [ exact HC | exact HA |].
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_wf; [ exact HE | exact Hm | exact Hne | exact HA | exact (HR e) | exact (HMu e) ].
Qed.

End Fixed_GCtx.
