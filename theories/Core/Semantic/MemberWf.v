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
From Mctt.Core.Completeness Require Import UniverseCases MemberReps MemberSem PathCases GlobalSem ModuleCases UnitCases.
From Mctt.Core.Syntactic.System Require Import MemberWf MemberLemmas GlobalModules.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Types Below a Universe *)

(** ** A Binding's Value, Read Back Through the Binding *)

(** Under [Γ ▸ D ≔ N], a term is equal to its instance at [N], weakened: the
    variable is equal to [N[↑]ʷ] by δ. *)
Lemma def_ctx_inst : forall Γ D N k X Y,
    Γ ⊢ D : Typeω@k -> Γ ⊢ N : D -> Γ ▸ D ≔ N ⊢ X : Y ->
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
  pose proof (sub_eq_preserves_exp _ _ _ _ _ HX _ _ _ Heq) as H'.
  rewrite !exp_sub_id in H'; exact H'.
Qed.



(** Under [Γ ▹ₘ U], a term is equal to its instance at the literal [⌜U⌝],
    weakened: equal substitutions agree on terms only, and the slot is not a
    term. *)
Lemma mod_ctx_inst : forall Γ U X Y,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ▹ₘ U ⊢ X : Y ->
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
  pose proof (sub_eq_preserves_exp _ _ _ _ _ HX _ _ _ Heq) as H'.
  rewrite !exp_sub_id in H'; exact H'.
Qed.

(** ** Local Definitions Before a Term

    A term typed under definitions and module slots it does not mention is
    typed without them: they are substituted by their values.  A type
    behind them is equal to itself without them, by ζ. *)

Lemma lets_strengthen : forall Ψ Γ N A, lets_only Ψ -> ⊢ Ψ ++ Γ ->
    Ψ ++ Γ ⊢ N[wk_shiftn (length Ψ)]ʷ : A[wk_shiftn (length Ψ)]ʷ -> Γ ⊢ N : A.
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hl HC HN; cbn [app length] in *.
  - rewrite !(exp_wk_id_ext _ _ wk_shiftn_zero) in HN; exact HN.
  - inversion Hl as [| ? ? He Hl']; subst.
    rewrite <- !(exp_wk_wk_ext _ _ _ _ (wk_shiftn_succ (length Ψ))) in HN.
    destruct e as [B | D M | U]; [ exfalso; eapply He; reflexivity | |].
    + destruct (ctx_decomp_def HC) as (HC' & [k HD] & HM).
      apply IH; [ exact Hl' | exact HC' |].
      assert (Hσ : Ψ ++ Γ ⊢s Id,,M : (Ψ ++ Γ) ▸ D ≔ M)
        by (eapply wf_sub_extend_def; [ apply wf_sub_id; exact HC' | exact HD | exact HM | rewrite exp_sub_id; exact HM
                                     | rewrite !exp_sub_id; apply wf_exp_eq_refl; exact HM ]).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HN Hσ) as H'.
      rewrite !exp_sub_shift_extend, !exp_sub_id in H'; exact H'.
    + destruct (ctx_decomp_mod HC) as (HC' & HU).
      apply IH; [ exact Hl' | exact HC' |].
      assert (Hσ : Ψ ++ Γ ⊢s Id ,,ₘ me_lit U[Id]ᵘ : (Ψ ++ Γ) ▹ₘ U)
        by (apply wf_sub_extend_mod; [ apply wf_sub_id; exact HC' | exact HU | rewrite gunit_sub_id; exact HU ]).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HN Hσ) as H'.
      rewrite !exp_sub_shift_extend, !exp_sub_id in H'; exact H'.
Qed.

Lemma ctx_pi_cong : forall Ψ Γ X Y i, ⊢ Ψ ++ Γ -> Ψ ++ Γ ⊢ X ≈ Y : Typeω@i ->
    exists j, Γ ⊢ ctx_pi Ψ X ≈ ctx_pi Ψ Y : Typeω@j.
Proof.
  induction Ψ as [| [B | B N | U] Ψ IH]; intros * HC HXY; cbn [app ctx_pi] in *; [ eauto | | | ]; inversion HC; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Typeω@?k |- _ =>
      eapply IH with (i := max k i); [ eauto using presup_exp_ctx |];
      eapply wf_exp_eq_pi_cong; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_eq_max_left; apply wf_exp_eq_refl; exact HB
                                | eapply lift_exp_eq_max_right; exact HXY ] end.
  - eapply IH with (i := i); [ eauto using presup_exp_ctx |].
    match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Typeω@?k, HN : _ ⍮ _ ⍮ _ ⊢ N : B |- _ =>
      assert (Hl : Ψ ++ Γ ⊢ ℓ B ≔ N in X ≈ ℓ B ≔ N in Y : (Typeω@i)[Id,,N]);
      [ eapply wf_exp_eq_let_cong; [ exact HB | apply wf_exp_eq_refl; exact HB | exact HN | apply wf_exp_eq_refl; exact HN
                                   | exact HXY | solve_let_ann | solve_let_ann ] | exact Hl ] end.
  - eapply IH with (i := i); [ eauto using presup_unit_eq_ctx |].
    match goal with HU : _ ⍮ _ ⍮ _ ⊢ᵘ U ≈ U |- _ =>
      assert (Hl : Ψ ++ Γ ⊢ ℓₘ U in X ≈ ℓₘ U in Y : (Typeω@i)[Id ,,ₘ me_lit U]);
      [ eapply wf_exp_eq_let_mod_cong; [ exact HU | exact HXY |];
        eapply wf_let_mod_typ; [ exact HU | gen_presups; eassumption ] | exact Hl ] end.
Qed.

Lemma zeta_lets_typ : forall Ψ Γ A i, lets_only Ψ -> ⊢ Ψ ++ Γ -> Γ ⊢ A : Typeω@i ->
    exists j, Γ ⊢ ctx_pi Ψ A[wk_shiftn (length Ψ)]ʷ ≈ A : Typeω@j.
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hl HC HA; cbn [app length ctx_pi] in *.
  - rewrite (exp_wk_id_ext _ _ wk_shiftn_zero); exists i; apply wf_exp_eq_refl; exact HA.
  - inversion Hl as [| ? ? He Hl']; subst.
    rewrite <- (exp_wk_wk_ext _ _ _ _ (wk_shiftn_succ (length Ψ))).
    assert (HC' : ⊢ Ψ ++ Γ) by (destruct e; inversion HC; subst; eauto using presup_exp_ctx, presup_unit_eq_ctx).
    assert (HAs : (e :: Ψ) ++ Γ ⊢ A[wk_shiftn (length Ψ)]ʷ[wk_shift]ʷ : Typeω@i).
    { rewrite (exp_wk_wk_ext _ _ _ _ (wk_shiftn_succ (length Ψ))).
      eapply wk_preserves_exp with (A := Typeω@i); [ exact HA |].
      replace (S (length Ψ)) with (length (e :: Ψ)) by reflexivity; apply wf_wk_shiftn_app'; exact HC. }
    destruct (IH _ _ _ Hl' HC' HA) as [j2 H2].
    destruct e as [B | D M | U]; [ exfalso; eapply He; reflexivity | |].
    + destruct (ctx_decomp_def HC) as (_ & [k HD] & HM).
      assert (Hz : Ψ ++ Γ ⊢ ℓ D ≔ M in A[wk_shiftn (length Ψ)]ʷ[wk_shift]ʷ ≈ A[wk_shiftn (length Ψ)]ʷ : Typeω@i).
      { pose proof (wf_exp_eq_let_zeta_typ _ _ _ (Some D) _ _ _ _ _ HD HM HAs ltac:(solve_let_ann)) as Hz.
        rewrite exp_sub_shift_extend, exp_sub_id in Hz; exact Hz. }
      destruct (ctx_pi_cong _ _ _ _ _ HC' Hz) as [j1 H1].
      exists (max j1 j2); eapply wf_exp_eq_trans; [ eapply lift_exp_eq_max_left; exact H1 | eapply lift_exp_eq_max_right; exact H2 ].
    + destruct (ctx_decomp_mod HC) as (_ & HU).
      assert (Hz : Ψ ++ Γ ⊢ ℓₘ U in A[wk_shiftn (length Ψ)]ʷ[wk_shift]ʷ ≈ A[wk_shiftn (length Ψ)]ʷ : Typeω@i).
      { pose proof (wf_exp_eq_let_mod_zeta_typ _ _ _ _ _ _ HU HAs) as Hz.
        rewrite exp_sub_shift_extend, exp_sub_id in Hz; exact Hz. }
      destruct (ctx_pi_cong _ _ _ _ _ HC' Hz) as [j1 H1].
      exists (max j1 j2); eapply wf_exp_eq_trans; [ eapply lift_exp_eq_max_left; exact H1 | eapply lift_exp_eq_max_right; exact H2 ].
Qed.

(** The δ-reduct of a name a local open declares, the target's member under
    the body before the open, has the member's type, read past the entries
    the open generates before it. *)
Lemma lets_reduct_wf : forall Γ Ψ Ψg N A i,
    lets_only Ψg -> ⊢ Ψg ++ Ψ ++ Γ ->
    Ψg ++ Ψ ++ Γ ⊢ N[wk_shiftn (length Ψg)]ʷ : A[wk_shiftn (length Ψg)]ʷ ->
    Ψg ++ Ψ ++ Γ ⊢ A[wk_shiftn (length Ψg)]ʷ : Typeω@i ->
    Γ ⊢ ctx_fn Ψ N : ctx_pi (Ψg ++ Ψ) A[wk_shiftn (length Ψg)]ʷ.
Proof.
  intros * Hl HC HN HA.
  pose proof (lets_strengthen _ _ _ _ Hl HC HN) as HN0.
  assert (HA0 : Ψ ++ Γ ⊢ A : Typeω@i) by (eapply lets_strengthen with (A := Typeω@i); [ exact Hl | exact HC | exact HA ]).
  assert (HC0 : ⊢ Ψ ++ Γ) by (eapply ctx_app_wf_right; exact HC).
  pose proof (ctx_fn_wf _ _ _ _ _ _ _ HC0 HA0 HN0) as Hf.
  destruct (zeta_lets_typ _ _ _ _ Hl HC HA0) as [j Hz].
  destruct (ctx_pi_cong _ _ _ _ _ HC0 Hz) as [j' Hc].
  rewrite ctx_pi_app.
  eapply wf_conv'; [ exact Hf | apply wf_exp_eq_sym; exact Hc ].
Qed.

(** The entries of an expansion before a name an open declares, which the
    open generates, are local definitions and module slots. *)
Lemma xp_item_lets : forall Φx x Φ' E Φx0 gs0, body_shape Φx Φx -> gm_nopens Φx = 0 ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x E) -> Φ' = gens_append Φx0 0 gs0 ->
    lets_only (body_ctx (gens_append gm_nil 0 gs0)).
Proof.
  intros * Hs Hn Hp ->.
  pose proof (body_shape_prefix _ _ _ Hs Hp) as Hs'; cbn in Hs'.
  pose proof (gm_prefix_upto_nopens _ _ _ Hn Hp) as Hn'; cbn in Hn'.
  pose proof (body_shape_lets _ (proj1 Hs') Hn') as Hl.
  rewrite gens_body_ctx_base in Hl; apply Forall_app in Hl as [Hl _]; exact Hl.
Qed.

(** ** Local Bindings at the Level of Types *)

Lemma typ_let_inv : forall Γ oD N T i, Γ ⊢ a_let (b_def oD N) T : Typeω@i ->
    exists D, let_ann oD D /\ (exists k, Γ ⊢ D : Typeω@k) /\ Γ ⊢ N : D /\ Γ ▸ D ≔ N ⊢ T : Typeω@i.
Proof.
  intros * H.
  destruct (wf_let_inversion H) as (D & k & C & Hann & HD & HN & HT & Hsub).
  exists D; split; [ exact Hann |].
  split; [ eauto | split; [ exact HN |] ].
  assert (exists l, Γ ▸ D ≔ N ⊢ C : Typeω@l) as [l HCt] by (gen_presups; eauto).
  pose proof (def_ctx_inst _ _ _ _ _ _ HD HN HCt) as HCi.
  assert (⊢ Γ ▸ D ≔ N) by mauto 3.
  (** The body's type is below [Typeω@i] once instantiated; it is equal to that
      instance weakened, and weakening preserves the subtyping, so the body
      is a type of [Typeω@i] by subsumption. *)
  assert (HCw : Γ ▸ D ≔ N ⊢ C[Id,,N][↑]ʷ ⊆ Typeω@i[↑]ʷ)
    by (eapply wk_preserves_subtyp; [ exact Hsub | mauto 3 ]).
  cbn in HCw.
  eapply wf_exp_subtyp'; [ exact HT |].
  etransitivity; [ eapply wf_subtyp_refl'; exact HCi | exact HCw ].
Qed.


Lemma typ_let_mod_inv : forall Γ U T i, Γ ⊢ ℓₘ U in T : Typeω@i ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U /\ Γ ▹ₘ U ⊢ T : Typeω@i.
Proof.
  intros * H.
  destruct (wf_let_mod_inversion H) as (C & HU & HT & Hsub).
  split; [ exact HU |].
  assert (exists l, Γ ▹ₘ U ⊢ C : Typeω@l) as [l HCt] by (gen_presups; eauto).
  pose proof (mod_ctx_inst _ _ _ _ HU HCt) as HCi.
  assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
  assert (HCw : Γ ▹ₘ U ⊢ C[Id ,,ₘ me_lit U][↑]ʷ ⊆ Typeω@i[↑]ʷ)
    by (eapply wk_preserves_subtyp; [ exact Hsub | mauto 3 ]).
  cbn in HCw.
  eapply wf_exp_subtyp'; [ exact HT |].
  etransitivity; [ eapply wf_subtyp_refl'; exact HCi | exact HCw ].
Qed.

(** ** The [Π] a Type Is *)

Lemma pi_view_wf : forall A Γ i B C, Γ ⊢ A : Typeω@i -> pi_view A = Some (B, C) ->
    Γ ⊢ A ≈ Π B C : Typeω@i /\ Γ ⊢ B : Typeω@i /\ Γ ▹ B ⊢ C : Typeω@i.
Proof.
  induction A; intros * HA Hp; cbn in Hp; try discriminate.
  - injection Hp as <- <-.
    destruct (wf_pi_inversion' HA) as [HB HC].
    split; [ mauto 3 | split; assumption ].
  - destruct b as [oD N | U];
      (destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection Hp as <- <-).
    + destruct (typ_let_inv _ _ _ _ _ HA) as (D & Hann & [k HD] & HN & HT).
      destruct (IHA _ _ _ _ HT eq_refl) as (HTe & HB' & HC').
      pose proof (wf_sub_single_def _ _ _ _ _ _ HD HN) as Hσ.
      pose proof (sub_preserves_typ_eq _ _ _ _ _ _ _ _ HTe Hσ) as HTs; cbn in HTs.
      split; [| split ].
      * eapply wf_exp_eq_trans; [ eapply wf_exp_eq_let_zeta_typ; cycle 3; [ solve_let_ann | eassumption .. ] | exact HTs ].
      * eapply sub_preserves_typ; eassumption.
      * eapply sub_preserves_typ; [ exact HC' | eapply wf_sub_q'; eassumption ].
    + destruct (typ_let_mod_inv _ _ _ _ HA) as (HU & HT).
      destruct (IHA _ _ _ _ HT eq_refl) as (HTe & HB' & HC').
      pose proof (wf_sub_single_mod _ _ _ _ HU) as Hσ.
      pose proof (sub_preserves_typ_eq _ _ _ _ _ _ _ _ HTe Hσ) as HTs; cbn in HTs.
      split; [| split ].
      * eapply wf_exp_eq_trans; [ eapply wf_exp_eq_let_mod_zeta_typ; eassumption | exact HTs ].
      * eapply sub_preserves_typ; eassumption.
      * eapply sub_preserves_typ; [ exact HC' | eapply wf_sub_q'; eassumption ].
Qed.

(** ** The Outermost Parameter of an Arity

    An arity is typed by its arity type: its outermost parameter is a type,
    and instantiating it with an argument of that type leaves an arity. *)

Lemma tele_view_wf : forall Γ T i B T1, Γ ⊢ ctx_pi T ⊤ : Typeω@i -> tele_view T = Some (B, T1) ->
    Γ ⊢ ctx_pi T ⊤ ≈ Π B (ctx_pi T1 ⊤) : Typeω@i /\ Γ ⊢ B : Typeω@i /\ Γ ▹ B ⊢ ctx_pi T1 ⊤ : Typeω@i.
Proof.
  intros * HT Hv; apply pi_view_wf; [ exact HT | rewrite tele_view_pi, Hv; reflexivity ].
Qed.

(** ** Semantic Equality of Types, Read Back *)

Lemma sem_typ_eq_syn : forall Γ A A' i,
    Γ ⊢ A : Typeω@i -> Γ ⊢ A' : Typeω@i -> Γ ⊨ A ≈ A' : Typeω@i -> Γ ⊢ A ≈ A' : Typeω@i.
Proof.
  intros * HA HA' H.
  destruct (rel_exp_under_ctx_at_initial_env H)
    as [ρ [j [elem_rel [a [m [m' [Hρ [Ha [Hm [Hm' [Htyp Hrel]]]]]]]]]]].
  destruct (per_elem_then_per_top Htyp Hrel (length Γ)) as [W [HW HW']].
  assert (H1 : nbe_f Γ A Typeω@i W) by (econstructor; eassumption).
  assert (H2 : nbe_f Γ A' Typeω@i W) by (econstructor; eassumption).
  pose proof (soundness' HA H1); pose proof (soundness' HA' H2).
  eapply wf_exp_eq_trans; [ eassumption | eapply wf_exp_eq_sym; eassumption ].
Qed.


(** ** Arities Through an Application

    A module expression applied to an argument has a [Π] for its arity, and
    then every member type it has is a [Π] as well, syntactically: an
    argument is still missing at each of its members.  This is read off the
    PER model ([sem_mt]). *)

Lemma wf_modexp_sem_mt : forall Γ H, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    sem_mt gc_deps gc_stack Γ H /\ Γ ⊨ᵐ H ≈ H.
Proof.
  intros * HH.
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & _ & Km).
  pose proof (gctx_sem _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hid.
  destruct (Km _ _ _ _ _ HH _ _ _ _ Hid) as (HR & HS & _).
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

Lemma app_arity_pi : forall Γ H R0 T0 B0 T1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H nil R0 -> mres_tl R0 = Some T0 -> tele_view T0 = Some (B0, T1) ->
    forall ch R, member_type gc_deps gc_stack Γ H ch R -> (mres_kind R = mk_term -> ch <> nil) ->
    exists B' C', pi_view (mres_ty R) = Some (B', C').
Proof.
  intros * HH Hm0 Htl Hv * Hm Hch.
  destruct (mres_tl_ty _ _ Htl) as [HRty HRk].
  destruct (wf_modexp_sem_mt _ _ HH) as [[_ S2] _].
  destruct (S2 nil _ ch R Hm0 HRk Hm Hch) as (m & n & Hr0 & Hr & Hmn); rewrite HRty in Hr0.
  assert (Hp : pi_view (ctx_pi T0 ⊤) = Some (B0, ctx_pi T1 ⊤)) by (rewrite tele_view_pi, Hv; reflexivity).
  destruct (rep_pos_of_pi _ _ _ Hr0 _ _ Hp) as [m' ->].
  destruct n as [| n']; [ lia |].
  destruct (rep_pos_pi _ _ _ _ Hr n' eq_refl Id) as (B' & C' & Hp').
  rewrite exp_sub_id in Hp'; eauto.
Qed.


(** ** Prefixes of Member Chains

    Each prefix of a member chain of a well-formed module is a module.  A
    chain from a unit need not be a module, since its prefix may be an open
    frame; there the prefixes beyond a module of the chain are modules
    ([mod_base]). *)

Definition mod_base (Γ : ctx) (H : modexp) (ch1 : list String.string) : Prop :=
  gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H \/
  (⊢ Γ /\ exists mq pre suf r0, mod_qname H = Some mq /\ ch1 = pre ++ suf /\
     gc_module gc_deps gc_stack (qname_app mq pre) = Some r0).

(** A well-formed chain from a unit is a module at its own path. *)
Lemma wf_chain_mt : forall Γ H mq, mod_qname H = Some mq -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    exists R T0, member_type gc_deps gc_stack Γ H nil R /\ mres_tl R = Some T0.
Proof.
  intros * Hp HH; pose proof (modexp_parts_of_wf _ _ _ _ HH) as Hparts.
  destruct H as [fp | x | H0 y | H0 N | U]; cbn in Hp, Hparts; try discriminate; [ exact Hparts |].
  destruct Hparts as [(_ & R & A0 & Hm & HT) | (_ & Hm)];
    [ exists R, A0; split; [ eapply mt_mem; [ rewrite (proj2 (mres_tl_ty _ _ HT)); discriminate | exact Hm ] | exact HT ] | exact Hm ].
Qed.

Lemma chain_module : forall Γ H mq R T0, mod_qname H = Some mq -> member_type gc_deps gc_stack Γ H nil R ->
    mres_tl R = Some T0 -> exists r0, gc_module gc_deps gc_stack mq = Some r0.
Proof.
  intros * Hp Hm HT; rewrite (mod_qname_inv _ _ Hp) in Hm; exact (member_type_path_module _ _ _ _ _ _ Hm HT).
Qed.

Lemma mod_base_unit : forall Γ fp ch1, mod_base Γ (me_unit fp) ch1 ->
    ⊢ Γ /\ exists pre suf r0, ch1 = pre ++ suf /\ gc_module gc_deps gc_stack (q_abs fp pre) = Some r0.
Proof.
  intros * [HH | (HΓ & mq & pre & suf & r0 & Hp & -> & Hq)].
  - split; [ exact (presup_modexp_eq_ctx HH) |].
    destruct (wf_chain_mt _ (me_unit fp) (q_abs fp nil) eq_refl HH) as (R0 & A0 & Hm & HT).
    destruct (chain_module _ (me_unit fp) (q_abs fp nil) _ _ eq_refl Hm HT) as [r0 Hq].
    exists nil, ch1, r0; split; [ reflexivity | exact Hq ].
  - cbn in Hp; injection Hp as <-; split; [ exact HΓ |]; exists pre, suf, r0; split; [ reflexivity | exact Hq ].
Qed.

Lemma mod_base_nochain : forall Γ H ch1, mod_base Γ H ch1 -> mod_qname H = None -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * [HH | (_ & mq & _ & _ & _ & Hp & _)] Hn; [ exact HH | congruence ]. Qed.

Lemma mod_base_mem : forall Γ H y ch1, mod_base Γ (me_mem H y) ch1 -> mod_base Γ H (y :: ch1).
Proof.
  intros * [HH | (HΓ & mq & pre & suf & r0 & Hp & -> & Hq)].
  - destruct (modexp_parts_of_wf _ _ _ _ HH) as [(HH0 & _) | (Hne & R0 & A0 & Hm & HT)]; [ left; exact HH0 |].
    destruct (mod_qname H) as [mq0 |] eqn:Hp0; [| cbn in Hne; rewrite Hp0 in Hne; congruence ].
    assert (Hp : mod_qname (me_mem H y) = Some (qname_app mq0 (y :: nil))) by (cbn; rewrite Hp0; reflexivity).
    destruct (chain_module _ _ _ _ _ Hp Hm HT) as [r0 Hq].
    right; split; [ exact (presup_modexp_eq_ctx HH) |].
    exists mq0, (y :: nil), ch1, r0; split; [ exact Hp0 | split; [ reflexivity | exact Hq ] ].
  - cbn in Hp; destruct (mod_qname H) as [mq0 |] eqn:Hp0; [| discriminate ]; injection Hp as <-.
    right; split; [ exact HΓ |].
    exists mq0, (y :: pre), suf, r0; split; [ exact Hp0 | split; [ reflexivity |] ].
    unfold qname_app in *; cbn in *; rewrite <- app_assoc in Hq; exact Hq.
Qed.

Lemma mt_unit_body : forall Θ Ξ Γ fp ch T oD,
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_body T oD) ->
    exists R, member_type Θ Ξ Γ (me_unit fp) ch R /\ mres_tl R = Some T.
Proof. intros * Hm; destruct oD; eexists; split; [ eapply mt_unit_ind; exact Hm | reflexivity | eapply mt_unit_mod; exact Hm | reflexivity ]. Qed.

Lemma mres_tl_gen : forall Δ R T, mres_tl R = Some T -> mres_tl (mres_gen Δ R) = Some (T ++ Δ).
Proof. intros Δ [] * H; cbn in *; congruence. Qed.

Lemma mres_tl_kind : forall R T, mres_tl R = Some T -> mres_kind R = mk_term -> False.
Proof. intros [] * H Hk; cbn in *; congruence. Qed.

Theorem member_type_prefix_gen :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> mod_base Γ H ch1 ->
     exists R' T', member_type gc_deps gc_stack Γ H ch1 R' /\ mres_tl R' = Some T') /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
     exists R' T', unit_member_type gc_deps gc_stack Γ U ch1 R' /\ mres_tl R' = Some T') /\
  (forall Γ Φ Φx, body_xp gc_deps gc_stack Γ Φ Φx -> True) /\
  (forall io Γ H its gs, items_gen gc_deps gc_stack io Γ H its gs -> True).
Proof.
  apply member_type_both_ind; try (intros; exact I).
  - intros * Hne Hr ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    rewrite <- app_assoc in Hr.
    destruct (path_prefix_resolve _ _ Hg _ _ _ _ _ Hq Hr Hne2) as (T1 & oD1 & HT1).
    destruct (mt_unit_body _ _ Γ _ _ _ _ HT1) as (R1 & HR1 & HT); eauto.
  - intros * Hm ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    rewrite <- app_assoc in Hm.
    destruct (path_prefix_module _ _ Hg _ _ _ _ _ Hq Hm) as [(T1 & oD1 & HT1) | (U & r1 & _ & [=])].
    destruct (mt_unit_body _ _ Γ _ _ _ _ HT1) as (R1 & HR1 & HT); eauto.
  - intros * Hm ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    rewrite <- app_assoc in Hm.
    destruct (path_prefix_module _ _ Hg _ _ _ _ _ Hq Hm) as [(T1 & oD1 & HT1) | (U & r1 & _ & [=])].
    destruct (mt_unit_body _ _ Γ _ _ _ _ HT1) as (R1 & HR1 & HT); eauto.
  - intros * Hk Hm Hu IH ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof Hm as Hm'; rewrite <- app_assoc in Hm'.
    destruct (path_prefix_module _ _ Hg _ _ _ _ _ Hq Hm') as [(T1 & oD1 & HT1) | (U' & r1 & HU' & [= <- ->])].
    { destruct (mt_unit_body _ _ Γ _ _ _ _ HT1) as (R1 & HR1 & HT); eauto. }
    destruct (IH r1 ch2 eq_refl Hne2 (gc_alias_unit_wf _ _ Hg _ _ _ Hm)) as (R' & T' & HT' & Htl).
    exists R', T'; split; [| exact Htl ].
    eapply mt_unit_alias; [ intros Hk'; destruct (mres_tl_kind _ _ Htl Hk') | exact HU' | exact HT' ].
  - intros * Hx Hu IH ch1 ch2 -> Hne2 Hb.
    pose proof (mod_base_nochain _ _ _ Hb eq_refl) as HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (ctx_lookup_mod_wf _ _ _ _ _ (presup_modexp_eq_ctx HH) Hx)) as (R' & T' & HT' & Htl).
    exists R', T'; split; [ eapply mt_var; eassumption | exact Htl ].
  - intros * Hu IH ch1 ch2 -> Hne2 Hb.
    pose proof (mod_base_nochain _ _ _ Hb eq_refl) as HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (modexp_parts_of_wf _ _ _ _ HH)) as (R' & T' & HT' & Htl).
    exists R', T'; split; [ eapply mt_lit; eassumption | exact Htl ].
  - intros * Hk Hm IH ch1 ch2 -> Hne2 Hb.
    destruct (IH (y :: ch1) ch2 eq_refl Hne2 (mod_base_mem _ _ _ _ Hb)) as (R' & T' & HT' & Htl).
    exists R', T'; split; [ eapply mt_mem; [ intros Hk'; destruct (mres_tl_kind _ _ Htl Hk') | exact HT' ] | exact Htl ].
  - intros * Hm IH Ha ch1 ch2 -> Hne2 Hb.
    pose proof (mod_base_nochain _ _ _ Hb eq_refl) as HH.
    destruct (modexp_parts_of_wf _ _ _ _ HH) as [HH' (R0 & T0 & B0 & T1 & i & Hm0 & Htl0 & Hv0 & _)].
    destruct (IH ch1 ch2 eq_refl Hne2 (or_introl HH')) as (Rq & Tq & HTq & Htlq).
    destruct (app_arity_pi _ _ _ _ _ _ HH' Hm0 Htl0 Hv0 _ _ HTq ltac:(intros Hk'; destruct (mres_tl_kind _ _ Htlq Hk'))) as (B' & C' & Hp').
    destruct (mres_app_of_pi _ N _ _ Hp') as (R'' & Ha'').
    destruct (mres_app_ty _ _ _ Ha'') as (_ & _ & _ & _ & Hk'').
    destruct Rq as [A' | T2 | T2]; cbn in Htlq; try discriminate;
      destruct R'' as [A'' | T'' | T'']; cbn in Hk''; try discriminate;
      eexists _, T''; (split; [ eapply mt_app; eassumption | reflexivity ]).
  - intros * Hc Hne2 _.
    symmetry in Hc; apply app_eq_nil in Hc as [_ ->]; contradiction.
  - intros * Ht Hbx _ Hp ch1 ch2 Hc Hne2 _.
    destruct ch1 as [| z ch1]; [ eexists _, _; split; [ constructor | reflexivity ] |].
    injection Hc as -> Hc; symmetry in Hc; apply app_eq_nil in Hc as [_ ->]; contradiction.
  - intros * Hk Ht Hbx _ Hp Hu IH ch1 ch2 Hc Hne2 HU.
    destruct ch1 as [| z ch1]; [ eexists _, _; split; [ constructor | reflexivity ] |].
    injection Hc as -> ->.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (Φx2 & Hbx2 & HC & _ & _).
    pose proof (body_xp_functional _ _ _ _ _ _ Hbx Hbx2) as <-.
    destruct (IH ch1 ch2 eq_refl Hne2 (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC Hp)) as (R' & T' & HT' & Htl).
    exists (mres_gen (body_ctx Φ' ++ Δ) R'), (T' ++ body_ctx Φ' ++ Δ); split; [| exact (mres_tl_gen _ _ _ Htl) ].
    eapply umt_mod; [ intros Hk'; destruct (mres_tl_kind _ _ Htl Hk') | exact Ht | exact Hbx | exact Hp | exact HT' ].
  - intros * Ht Hm IH ch1 ch2 -> Hne2 HU.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (_ & _ & HE).
    destruct (IH ch1 ch2 eq_refl Hne2 (or_introl HE)) as (R' & T' & HT' & Htl).
    exists (mres_gen Δ R'), (T' ++ Δ); split; [ apply umt_alias; [ exact Ht | exact HT' ] | exact (mres_tl_gen _ _ _ Htl) ].
Qed.

Corollary member_type_prefix :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
     exists R' T', member_type gc_deps gc_stack Γ H ch1 R' /\ mres_tl R' = Some T') /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
     exists R' T', unit_member_type gc_deps gc_stack Γ U ch1 R' /\ mres_tl R' = Some T').
Proof.
  split; [ intros * Hm * ? ? HH; eapply (proj1 member_type_prefix_gen); [ exact Hm | eassumption .. | left; exact HH ]
         | exact (proj1 (proj2 member_type_prefix_gen)) ].
Qed.

Lemma me_mems_wf : forall pre Γ H ch R,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> member_type gc_deps gc_stack Γ H (pre ++ ch) R -> ch <> nil ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mems H pre ≈ me_mems H pre.
Proof.
  induction pre as [| y pre IH]; intros * HH Hm Hne; cbn [me_mems app] in *; [ exact HH |].
  destruct (proj1 member_type_prefix _ _ _ _ Hm (y :: nil) (pre ++ ch) eq_refl
              ltac:(destruct pre, ch; cbn; congruence) HH) as (R' & T' & HT' & Htl).
  eapply IH; [ eapply wf_me_mem; [ exact HH | exact HT' | exact Htl | exact HT' | exact Htl ] | | exact Hne ].
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
    me_noargs H -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H ch (mr_term A) -> ch <> nil ->
    Γ ⊢ A : Typeω@i -> member_unfold_ch gc_deps gc_stack Γ H ch M -> Γ ⊢ M : A ->
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
    | unfold member_unfold; apply me_mems_unfold; exact HMe
    | exact HMt ].
Qed.

Lemma member_ref_wf : forall Γ H ch A i,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H ch (mr_term A) -> ch <> nil -> Γ ⊢ A : Typeω@i ->
    (forall R args p0, modexp_spine H = (R, args, p0) -> Γ ⊢ apps (member_ref R (p0 ++ ch)) args : A) ->
    (exists M, member_unfold_ch gc_deps gc_stack Γ H ch M /\ Γ ⊢ M : A) ->
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

Lemma dom_agree : forall Γ H R0 T0 B0 T1 i ch R1 B1 C1 j,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H nil R0 -> mres_tl R0 = Some T0 -> tele_view T0 = Some (B0, T1) -> Γ ⊢ B0 : Typeω@i ->
    member_type gc_deps gc_stack Γ H ch R1 -> (mres_kind R1 = mk_term -> ch <> nil) ->
    Γ ⊢ mres_ty R1 ≈ Π B1 C1 : Typeω@j -> Γ ⊢ B1 : Typeω@j ->
    exists k, Γ ⊢ B0 ≈ B1 : Typeω@k.
Proof.
  intros * HH Hm0 Htl0 Hv HB0 Hm Hch HA1 HB1.
  destruct (wf_modexp_sem_mt _ _ HH) as [HS HHs].
  assert (Hok : gmod_ok gc_deps gc_stack).
  { pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    clear - Hg; destruct GC as [Θ Ξ]; exact (gmod_ok_self _ _ Hg). }
  destruct (arity_pi _ _ _ _ _ _ HS Hm0 Htl0 Hv) as (l & HBl & _ & HAl).
  pose proof (app_domain Hok _ _ _ _ _ _ _ HS HHs Hm0 Htl0 HAl HBl _ _ _ _ _ Hm Hch
                (completeness_fundamental_exp_eq _ _ _ _ HA1) (completeness_fundamental_exp _ _ _ HB1)) as Hs.
  exists (max (max i l) j).
  apply sem_typ_eq_syn;
    [ eapply lift_exp_ge; [| exact HB0 ]; lia | eapply lift_exp_ge; [| exact HB1 ]; lia
    | eapply rel_exp_cumu_ge; [| exact Hs ]; lia ].
Qed.

(** ** Member Types Are Types *)

(** A chain from a unit need not be a module to have members: its prefix may
    be an open frame. *)
Definition mod_wf (Γ : ctx) (H : modexp) : Prop :=
  gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H \/ (⊢ Γ /\ mod_qname H <> None).

Lemma mod_wf_ctx : forall Γ H, mod_wf Γ H -> ⊢ Γ.
Proof. intros * [HH | [HΓ _]]; [ exact (presup_modexp_eq_ctx HH) | exact HΓ ]. Qed.

Lemma mod_wf_nochain : forall Γ H, mod_wf Γ H -> mod_qname H = None -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * [HH | (_ & Hn)] Hp; [ exact HH | contradiction ]. Qed.

Lemma mod_wf_mem : forall Γ H y, mod_wf Γ (me_mem H y) -> mod_wf Γ H.
Proof.
  intros * [HH | (HΓ & Hn)].
  - destruct (modexp_parts_of_wf _ _ _ _ HH) as [(HH0 & _) | (Hn & _)]; [ left; exact HH0 |].
    right; split; [ exact (presup_modexp_eq_ctx HH) |]; cbn in Hn; destruct (mod_qname H); congruence.
  - right; split; [ exact HΓ |]; cbn in Hn; destruct (mod_qname H); congruence.
Qed.

(** A definition reached from a unit, as a term, is a global. *)
Lemma unit_ref_glob : forall Γ fp ch b pv A B, ⊢ Γ -> ch <> nil ->
    gc_resolve gc_deps gc_stack (q_abs fp ch) = Some (ge_def b pv A B) ->
    Γ ⊢ member_ref (me_unit fp) ch : A.
Proof.
  intros * HΓ Hne Hr.
  destruct (exists_last Hne) as (pre & x & ->); rewrite member_ref_mems.
  eapply wf_mem_glob; [ exact HΓ | exact (mod_qname_mems pre (me_unit fp) (q_abs fp nil) eq_refl) | exact Hr ].
Qed.

Theorem member_wf_gen :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     mod_wf Γ H -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Typeω@i) /\
     (mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ H ch M /\ Γ ⊢ M : mres_ty R) /\
     (mres_kind R = mk_term -> forall Q args p0, modexp_spine H = (Q, args, p0) ->
        Γ ⊢ apps (member_ref Q (p0 ++ ch)) args : mres_ty R)) /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Typeω@i) /\
     (mres_kind R = mk_term -> exists M, unit_unfold gc_deps gc_stack Γ U ch M /\ Γ ⊢ M : mres_ty R)) /\
  (forall Γ Φ Φx, body_xp gc_deps gc_stack Γ Φ Φx -> True) /\
  (forall io Γ H its gs, items_gen gc_deps gc_stack io Γ H its gs -> True).
Proof.
  apply member_type_both_ind; try (intros; exact I).
  - (* a definition reached from a unit *)
    intros Γ fp ch b pv A B Hne Hr HH Hch; cbn [mres_ty mres_kind].
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    destruct (wf_glob_typ _ _ _ _ _ _ _ _ HΓ Hr) as [i HA].
    assert (HM : member_unfold_ch gc_deps gc_stack Γ (me_unit fp) ch (member_ref (me_unit fp) ch))
      by (eapply muc_unit_def; exact Hr).
    pose proof (unit_ref_glob _ _ _ _ _ _ _ HΓ Hne Hr) as HMt.
    split; [ eauto | split; [ intros _; eauto |] ].
    intros _ Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps]; exact HMt.
  - (* a body module *)
    intros Γ fp ch T Hm HH _; cbn [mres_ty mres_kind].
    split; [| split; discriminate ].
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof (wf_gctx_closed _ _ _ HΓ) as Hc.
    destruct (gc_module_body _ _ _ _ _ Hm) as [Φ HΦ].
    destruct (gc_body_tele_wf _ _ Hg _ _ _ HΦ) as [HT _].
    assert (HTt : T ⊢ ⊤ : Typeω@0) by (apply wf_True_large; exact HT).
    destruct (ctx_pi_wf0 _ _ _ _ _ HTt) as [j Hj].
    assert (Hm0 : member_type gc_deps gc_stack nil (me_unit fp) ch (mr_mod T)) by (eapply mt_unit_mod; exact Hm).
    pose proof (mres_ty_scoped _ _ (proj1 (member_type_scoped _ _) _ _ _ _ Hm0 Hc I I)) as Hs; cbn in Hs.
    exists j; eapply closed_weaken_exp; [ exact HΓ | exact Hj | exact Hs | exact I ].
  - (* the module of an inductive type *)
    intros Γ fp ch T D Hm HH _; cbn [mres_ty mres_kind].
    split; [| split; discriminate ].
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof (wf_gctx_closed _ _ _ HΓ) as Hc.
    destruct (gc_module_body _ _ _ _ _ Hm) as [Φ HΦ].
    destruct (gc_body_tele_wf _ _ Hg _ _ _ HΦ) as [HT _].
    assert (HTt : T ⊢ ⊤ : Typeω@0) by (apply wf_True_large; exact HT).
    destruct (ctx_pi_wf0 _ _ _ _ _ HTt) as [j Hj].
    assert (Hm0 : member_type gc_deps gc_stack nil (me_unit fp) ch (mr_indm T)) by (eapply mt_unit_ind; exact Hm).
    pose proof (mres_ty_scoped _ _ (proj1 (member_type_scoped _ _) _ _ _ _ Hm0 Hc I I)) as Hs; cbn in Hs.
    exists j; eapply closed_weaken_exp; [ exact HΓ | exact Hj | exact Hs | exact I ].
  - (* inside a global alias *)
    intros Γ fp ch U r R Hk Hm Hu IH HH Hch.
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof (wf_gctx_closed _ _ _ HΓ) as Hc.
    destruct (IH (gc_alias_unit_wf _ _ Hg _ _ _ Hm) Hk) as ([i HA] & HMu).
    pose proof (gctx_closed_module _ _ _ _ Hc Hm) as HUs; cbn in HUs.
    pose proof (mres_ty_scoped _ _ (proj2 (member_type_scoped _ _) _ _ _ _ Hu Hc I HUs)) as HAs; cbn in HAs.
    assert (HAΓ : Γ ⊢ mres_ty R : Typeω@i) by (eapply closed_weaken_exp; [ exact HΓ | exact HA | exact HAs | exact I ]).
    assert (HMΓ : mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ (me_unit fp) ch M /\ Γ ⊢ M : mres_ty R).
    { intros e; destruct (HMu e) as (M & HMe0 & HMt).
      destruct (gc_module_alias_unit _ _ _ _ _ Hm) as (Δa & Ea & EU).
      assert (HMe : member_expansion U r = Some M)
        by (subst U; inversion HMe0 as [? ? ? ? Hx ? HMx |]; subst; inversion Hx; subst; exact HMx).
      exists M; split.
      - eapply muc_unit_alias; [ | exact Hm | exact HMe ].
        intros * Hr'; rewrite (gc_module_alias_resolve _ _ Hg _ _ _ Hm) in Hr'; discriminate.
      - eapply closed_weaken_exp; [ exact HΓ | exact HMt | exact (member_expansion_scoped _ _ _ _ HMe HUs) | exact HAs ]. }
    split; [ eauto | split; [ exact HMΓ |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMΓ e) as (M & HMe & HMt).
    (** The member lies in a closed module reached through the alias. *)
    pose proof (Hch e) as Hne.
    pose proof (Hk e) as Hrne.
    destruct R as [A | T | T]; [| discriminate e | discriminate e ]; cbn [mres_ty] in *.
    destruct (exists_last Hne) as (pre & x & ->).
    destruct (gc_module_alias_decomp _ _ Hg _ _ _ Hm) as (qp & y & Hqp & Hy).
    assert (Hb : mod_base Γ (me_unit fp) pre).
    { right; split; [ exact HΓ |].
      destruct (exists_last Hrne) as (r1 & z & Er); subst r.
      assert (Ep : pre = q_chain qp ++ y :: r1).
      { apply (f_equal q_chain) in Hqp; cbn in Hqp.
        replace (q_chain qp ++ y :: r1 ++ z :: nil) with ((q_chain qp ++ y :: r1) ++ z :: nil) in Hqp
          by (rewrite <- app_assoc; reflexivity).
        apply app_inj_tail in Hqp as [-> _]; reflexivity. }
      exists (q_abs fp nil), (q_chain qp ++ y :: nil), r1, (mr_alias U nil).
      split; [ reflexivity | split; [ rewrite Ep, <- app_assoc; reflexivity |] ].
      apply (f_equal q_unit) in Hqp; cbn in Hqp; subst fp.
      destruct qp; exact Hy. }
    assert (Hmt : member_type gc_deps gc_stack Γ (me_unit fp) (pre ++ x :: nil) (mr_term A))
      by (eapply mt_unit_alias; [ intros _; exact Hrne | exact Hm | exact Hu ]).
    destruct (proj1 member_type_prefix_gen _ _ _ _ Hmt pre (x :: nil) eq_refl ltac:(discriminate) Hb) as (R' & T' & HT' & Htl').
    assert (HH' : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mems (me_unit fp) pre ≈ me_mems (me_unit fp) pre).
    { eapply wf_me_glob; [ exact HΓ | exact (mod_qname_mems pre (me_unit fp) (q_abs fp nil) eq_refl) | | exact Htl' ].
      apply me_mems_member_type; [ rewrite app_nil_r; exact HT' | intros Hk'; destruct (mres_tl_kind _ _ Htl' Hk') ]. }
    rewrite member_ref_mems.
    change (a_mem (me_mems (me_unit fp) pre) x) with (member_ref (me_mems (me_unit fp) pre) (x :: nil)).
    eapply member_ref_noargs_wf;
      [ exact (mod_qname_noargs _ _ (mod_qname_mems pre (me_unit fp) (q_abs fp nil) eq_refl)) | exact HH'
      | apply me_mems_member_type; [ exact Hmt | discriminate ] | discriminate | exact HAΓ
      | apply me_mems_unfold; exact HMe | exact HMt ].
  - (* a module slot *)
    intros Γ x U ch R Hx Hu IH HH0 Hch.
    pose proof (mod_wf_nochain _ _ HH0 eq_refl) as HH.
    pose proof (presup_modexp_eq_ctx HH) as HΓ.
    destruct (IH (ctx_lookup_mod_wf _ _ _ _ _ HΓ Hx) Hch) as ([i HA] & HMu).
    assert (HMΓ : mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ (me_var x) ch M /\ Γ ⊢ M : mres_ty R).
    { intros e; destruct (HMu e) as (M & HMe & HMt).
      exists M; split; [ eapply muc_var; [ exact (ctx_find_mod_complete _ _ _ Hx) | exact HMe ] | exact HMt ]. }
    split; [ eauto | split; [ exact HMΓ |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMΓ e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T | T]; [| discriminate e | discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_var; [ exact Hx | exact Hu ] | exact Hne | exact HA | exact HMe | exact HMt ].
  - (* a literal *)
    intros Γ U ch R Hu IH HH0 Hch.
    pose proof (mod_wf_nochain _ _ HH0 eq_refl) as HH.
    destruct (IH (modexp_parts_of_wf _ _ _ _ HH) Hch) as ([i HA] & HMu0).
    assert (HMu : mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ (me_lit U) ch M /\ Γ ⊢ M : mres_ty R)
      by (intros e; destruct (HMu0 e) as (M & HMe & HMt); exists M; split; [ constructor; exact HMe | exact HMt ]).
    split; [ eauto | split; [ exact HMu |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMu e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T | T]; [| discriminate e | discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_lit; exact Hu | exact Hne | exact HA | exact HMe | exact HMt ].
  - (* a selection *)
    intros Γ H y ch R Hk Hm IH HH Hch.
    destruct (IH (mod_wf_mem _ _ _ HH) ltac:(intros; discriminate)) as (HA & HMu & HR).
    split; [ exact HA | split; [ intros e; destruct (HMu e) as (M & HMe & HMt); exists M; split; [ constructor; exact HMe | exact HMt ] |] ].
    intros e Q args p0 Hs; cbn in Hs.
    destruct (modexp_spine H) as [[R' args'] p0'] eqn:Es; injection Hs as <- <- <-.
    rewrite <- app_assoc; exact (HR e _ _ _ eq_refl).
  - (* an application *)
    intros Γ H N ch R R' Hm IH Ha HH0 Hch.
    pose proof (mod_wf_nochain _ _ HH0 eq_refl) as HH.
    destruct (modexp_parts_of_wf _ _ _ _ HH) as [HH' (R0 & T0 & B0 & T1 & i0 & Hm0 & Htl0 & Hv0 & HB0 & HN0)].
    destruct (mres_app_ty _ _ _ Ha) as (B & C & Hp & HR' & Hk').
    rewrite HR', Hk'; rewrite Hk' in Hch.
    destruct (IH (or_introl HH') Hch) as ([j HA] & HMu & HR).
    destruct (pi_view_wf _ _ _ _ _ HA Hp) as (HAe & HB & HC).
    destruct (dom_agree _ _ _ _ _ _ _ _ _ _ _ _ HH' Hm0 Htl0 Hv0 HB0 Hm Hch HAe HB) as [k HBB].
    pose proof (wf_conv' _ _ _ _ _ _ _ HN0 HBB) as HN.
    pose proof (wf_sub_single _ _ _ _ _ _ HB HN) as Hσ.
    split; [ exists j; exact (sub_preserves_typ _ _ _ _ _ _ _ HC Hσ) | split ].
    + intros e; destruct (HMu e) as (M & HMe & HMt).
      exists (a_app M N); split; [ constructor; exact HMe |].
      eapply wf_app; [ exact HB | exact HC | eapply wf_conv'; [ exact HMt | exact HAe ] | exact HN ].
    + intros e Q args p0 Hs; cbn in Hs.
      destruct (modexp_spine H) as [[Q' args'] p0'] eqn:Es; injection Hs as <- <- <-.
      rewrite apps_snoc.
      eapply wf_app; [ exact HB | exact HC | eapply wf_conv'; [ exact (HR e _ _ _ eq_refl) | exact HAe ] | exact HN ].
  - (* the unit itself *)
    intros Γ Δ Φ HU _; cbn [mres_ty mres_kind].
    split; [| discriminate ].
    destruct (unit_parts_of_wf _ _ _ _ HU) as (Φx & _ & HC & _ & _).
    pose proof (ctx_app_wf_right _ _ _ _ HC) as HΔ.
    assert (Δ ++ Γ ⊢ ⊤ : Typeω@0) by (apply wf_True_large; exact HΔ).
    eapply ctx_pi_wf; eassumption.
  - (* a definition of a body: an entry of it, or one an open of it generates *)
    intros Γ Δ Φ Φx Φ' x b pv A B Ht Hbx _ Hp HU _; cbn [mres_ty mres_kind].
    destruct (unit_parts_of_wf _ _ _ _ HU) as (Φx2 & Hbx2 & HC & _ & Hs).
    pose proof (body_xp_functional _ _ _ _ _ _ Hbx Hbx2) as <-; clear Hbx2.
    destruct (body_shape_prefix_def _ _ _ _ _ _ _ Hs Hp) as [M0 ->].
    pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hp) as Hx; cbn in Hx.
    destruct (ctx_decomp_def Hx) as (HC' & [i HA] & HM0).
    split; [ eapply ctx_pi_wf; rewrite <- app_assoc; eassumption |].
    intros _.
    destruct (gm_item_upto Φ x) as [[[[Φ0 H] its1] it] |] eqn:Hi.
    + (* generated: the target's member, read past the entries generated before it *)
      destruct (xp_prefix _ _ _ _ _ Hbx _ _ _ Hp) as [(Φr & Hr & _) | (Φ0' & Φx0 & H' & its1' & it' & its0 & gs0 & g & T & k & Hi' & Hx0 & (RT & HT & HTl) & Hg0 & Hg1 & Hits & HΦ' & HE & Hk)];
        [ rewrite (gm_prefix_item_excl _ _ _ Hr) in Hi; discriminate Hi |].
      rewrite Hi in Hi'; injection Hi' as <- <- <- <-.
      pose proof (xp_item_lets _ _ _ _ _ _ Hs (body_xp_nopens _ _ _ _ _ Hbx) Hp HΦ') as Hl.
      inversion Hg1 as [| ? ? ? ? ? ? ? Hn0 | ? ? ? n d pv0 A2 ? ? Hmt2 Hn0 | ? ? ? ? ? ? ? ? Hmt2 Hn0 | ? ? ? ? ? ? ? ? ? ? ? ? Hmt2 Hq Hio Hn0 | ? ? ? ? ? ? ? ? Hmt2 Hio Hn0 ];
        subst; cbn [ig_entry snd gentry_wk] in HE; try discriminate.
      injection HE as -> -> -> ->.
      eexists; split; [ eapply uu_item; [ exact Hi | exact Hx0 | discriminate ] |].
      cbn [item_ch member_ref].
      rewrite gens_body_ctx_base, <- app_assoc in HC', HA, HM0 |- *.
      rewrite <- (gens_body_ctx_length gs0 0) in HA, HM0 |- *.
      cbn [exp_wk] in HM0 |- *.
      change (a_mem (modexp_wk H (wk_shiftn (length (body_ctx (gens_append gm_nil 0 gs0))))) n)
        with ((a_mem H n)[wk_shiftn (length (body_ctx (gens_append gm_nil 0 gs0)))]ʷ) in HM0.
      rewrite (app_assoc (body_ctx Φx0) Δ Γ) in HC', HA, HM0.
      exact (lets_reduct_wf Γ (body_ctx Φx0 ++ Δ) _ _ _ _ Hl HC' HM0 HA).
    + (* an entry of the body *)
      eexists; split; [ eapply uu_entry; [ constructor; exact Hbx | exact Hi | exact (member_expansion_def _ _ _ _ _ _ _ _ Hp) ] |].
      cbn [body_ctx app ctx_fn].
      eapply ctx_fn_wf; [ rewrite <- app_assoc; exact HC' | rewrite <- app_assoc; exact HA |].
      assert (Hl : body_ctx Φ' ++ Δ ++ Γ ⊢ ℓ A ≔ M0 in #0 : A[↑]ʷ[Id,,M0])
        by (eapply wf_let; [ exact HA | exact HM0 | eapply wf_vlookup; [ exact Hx | constructor ] | solve_let_ann ]).
      rewrite exp_sub_shift_extend, exp_sub_id in Hl.
      rewrite <- app_assoc; exact Hl.
  - (* a member of a submodule of a body: of one of its entries, or of an
       alias an open of it generates *)
    intros Γ Δ Φ Φx Φ' y pm Uy ch R Hk Ht Hbx _ Hp Hu IH HU Hch; rewrite mres_ty_gen, mres_kind_gen in *.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (Φx2 & Hbx2 & HC & _ & Hs).
    pose proof (body_xp_functional _ _ _ _ _ _ Hbx Hbx2) as <-; clear Hbx2.
    pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC Hp) as HUy.
    destruct (IH HUy Hk) as ([i HA] & HMu).
    pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hp) as Hx; cbn in Hx.
    pose proof (proj1 (ctx_decomp_mod Hx)) as HC'.
    split; [ eapply ctx_pi_wf; rewrite <- app_assoc; eassumption |].
    intros e; destruct (HMu e) as (M1 & HM1e & HM1t).
    pose proof (Hk e) as Hne.
    destruct R as [A | T | T]; [| discriminate e | discriminate e ]; cbn [mres_ty] in *.
    destruct (gm_item_upto Φ y) as [[[[Φ0 H] its1] it] |] eqn:Hi.
    + (* generated: the target's member, read past the entries generated before it *)
      destruct (xp_prefix _ _ _ _ _ Hbx _ _ _ Hp) as [(Φr & Hr & _) | (Φ0' & Φx0 & H' & its1' & it' & its0 & gs0 & g & T & k & Hi' & Hx0 & (RT & HT & HTl) & Hg0 & Hg1 & Hits & HΦ' & HE & Hk0)];
        [ rewrite (gm_prefix_item_excl _ _ _ Hr) in Hi; discriminate Hi |].
      rewrite Hi in Hi'; injection Hi' as <- <- <- <-.
      pose proof (xp_item_lets _ _ _ _ _ _ Hs (body_xp_nopens _ _ _ _ _ Hbx) Hp HΦ') as Hl.
      subst Φ'.
      pose proof (wf_gctx_closed _ _ _ Hx) as Hc.
      assert (HE0 : exists E0, Uy = gu_mk nil (md_alias (modexp_wk E0 (wk_shiftn (List.length gs0)))) /\
                      member_ref H (item_ch it ch) = member_ref E0 ch).
      { inversion Hg1; subst; cbn [ig_entry snd gentry_wk] in HE; try discriminate;
          injection HE as _ HE; rewrite gunit_wk_mk in HE; cbn [tele_wk moddef_wk wk_qn List.length] in HE; subst Uy;
          eexists; (split; [ reflexivity |]); cbn [item_ch]; [ reflexivity |].
        destruct ch as [| c ch]; [ contradiction |]; reflexivity. }
      destruct HE0 as (E0 & -> & EM).
      inversion HM1e as [? ? ? ? Hx1 _ HMx |]; subst; inversion Hx1; subst.
      cbn [member_expansion] in HMx; destruct ch as [| c ch]; [ contradiction |]; injection HMx as <-; cbn [ctx_fn] in HM1t.
      inversion Hu as [| | | ? ? ? ? ? _ HmE ]; subst.
      rewrite gens_body_ctx_base, <- app_assoc in HmE.
      destruct (proj1 (member_type_strengthen _ _ Hc) _ _ _ _ HmE _ E0 _ eq_refl
                  ltac:(rewrite app_nil_l, <- (gens_body_ctx_length gs0 0); apply wk_mod_inv_shiftn)) as (R1 & HmE0 & ->).
      destruct R1 as [A1 | T1 | T1]; cbn in H4; [| discriminate H4 | discriminate H4 ]; injection H4 as <-.
      eexists; split; [ eapply uu_item; [ exact Hi | exact Hx0 | destruct it as [[[] ?] ?]; discriminate ] |].
      rewrite EM, gens_body_ctx_base, <- app_assoc.
      rewrite gens_body_ctx_base, <- !app_assoc in HC', HA, HM1t.
      rewrite <- (gens_body_ctx_length gs0 0) in HA, HM1t |- *.
      change (match ch with nil => _ | _ => _ end)
        with (member_ref (modexp_wk E0 (wk_shiftn (length (body_ctx (gens_append gm_nil 0 gs0))))) (c :: ch)) in HM1t.
      rewrite <- member_ref_wk in HM1t.
      rewrite (app_assoc (body_ctx Φx0) Δ Γ) in HC', HA, HM1t.
      exact (lets_reduct_wf Γ (body_ctx Φx0 ++ Δ) _ _ _ _ Hl HC' HM1t HA).
    + (* an entry of the body *)
      eexists; split; [ eapply uu_entry; [ constructor; exact Hbx | exact Hi | exact (member_expansion_mod _ _ _ _ _ _ _ Hne Hp) ] |].
      cbn [body_ctx app ctx_fn].
      eapply ctx_fn_wf; [ rewrite <- app_assoc; exact HC' | rewrite <- app_assoc; exact HA |].
      rewrite <- app_assoc.
      pose proof (wf_wk_shift _ _ _ _ Hx) as Hw.
      assert (HR : ce_mod Uy :: body_ctx Φ' ++ Δ ++ Γ ⊢ member_ref (me_var 0) ch : A[↑]ʷ).
      { pose proof (wf_gctx_closed _ _ _ Hx) as Hc.
        pose proof (proj2 (member_type_wk _ _ Hc) _ _ _ _ Hu _ _ (wf_wk_mod_compat _ _ _ _ _ Hw)) as Hmt.
        eapply member_ref_noargs_wf with (i := i) (M := M1[↑]ʷ);
          [ exact I
          | eapply wf_me_var; [ exact Hx | apply mod_here ]
          | eapply mt_var; [ apply mod_here | exact Hmt ]
          | exact Hne
          | eapply wk_preserves_typ; eassumption
          | eapply muc_var; [ reflexivity | eapply unit_unfold_wk; [ exact Hc | exact HM1e | exact (wf_wk_mod_compat _ _ _ _ _ Hw) ] ]
          | eapply wk_preserves_exp; eassumption ]. }
      assert (Hl : body_ctx Φ' ++ Δ ++ Γ ⊢ ℓₘ Uy in member_ref (me_var 0) ch : A[↑]ʷ[Id ,,ₘ me_lit Uy])
        by (eapply wf_let_mod; [ exact HUy | eapply wk_preserves_typ; eassumption | exact HR ]).
      rewrite exp_sub_shift_extend, exp_sub_id in Hl; exact Hl.
  - (* a member of an alias unit *)
    intros Γ Δ E ch R Ht Hm IH HU Hch; rewrite mres_ty_gen, mres_kind_gen in *.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & HE).
    destruct (IH (or_introl HE) Hch) as ([i HA] & HMu & HR).
    split; [ eapply ctx_pi_wf; eassumption |].
    intros e; pose proof (Hch e) as Hne.
    eexists; split; [ eapply uu_entry; [ constructor | exact I | exact (member_expansion_alias _ _ _ Hne) ] |].
    eapply ctx_fn_wf; [ exact HC | exact HA |].
    destruct R as [A | T | T]; [| discriminate e | discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_wf; [ exact HE | exact Hm | exact Hne | exact HA | exact (HR e) | exact (HMu e) ].
Qed.

Corollary member_wf :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Typeω@i) /\
     (mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ H ch M /\ Γ ⊢ M : mres_ty R) /\
     (mres_kind R = mk_term -> forall Q args p0, modexp_spine H = (Q, args, p0) ->
        Γ ⊢ apps (member_ref Q (p0 ++ ch)) args : mres_ty R)) /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Typeω@i) /\
     (mres_kind R = mk_term -> exists M, unit_unfold gc_deps gc_stack Γ U ch M /\ Γ ⊢ M : mres_ty R)).
Proof.
  split; [ intros * Hm HH; exact (proj1 member_wf_gen _ _ _ _ Hm (or_introl HH)) | exact (proj1 (proj2 member_wf_gen)) ].
Qed.

(** ** What a Local Open Generates Is Well-Formed

    The entries an open of a well-formed module generates are well-formed:
    a definition is the member at its type, an alias the module or its
    submodule, each read past the entries generated before it. *)
Lemma gens_ext_wf_gen : forall io Γ1 H its gs, items_gen gc_deps gc_stack io Γ1 H its gs -> io = None ->
    forall Γ0 Ψ, Γ1 = Ψ ++ Γ0 -> gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ H ≈ H ->
    forall Φg, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φg ++ Ψ ≈ body_ctx Φg ++ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx (gens_append Φg (List.length (body_ctx Φg)) gs) ++ Ψ ≈
                                body_ctx (gens_append Φg (List.length (body_ctx Φg)) gs) ++ Ψ.
Proof.
  induction 1 as [| io Γ1 H d pv its gs _ IH | io Γ1 H n d pv A its gs Hm _ IH | io Γ1 H n d pv T its gs Hm _ IH
                 | it Γ1 H n d pv T mp Δ p Ns its gs Hm Hq Hi _ IH | it Γ1 H n d pv T its gs Hm Hn _ IH ];
    intros Eio Γ0 Ψ -> HH Φg HX; cbn [gens_append ig_entry]; try exact HX.
  all: pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- app_assoc in HC.
  all: pose proof (wf_wk_shiftn_app' _ _ _ _ HC) as Hw.
  4-5: discriminate.
  - assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias H) ≈ gu_mk nil (md_alias H))
      by (apply wf_unit_eq_alias; [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HH | exact HH ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_mod pv (gunit_wk (gu_mk nil (md_alias H)) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Eio Γ0 Ψ eq_refl HH).
    cbn [body_ctx app]; apply wf_ext_eq_mod; [ exact HX | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
  - destruct (proj1 member_wf _ _ _ _ Hm HH ltac:(intros; discriminate)) as ([i HA] & HMu & HR); cbn [mres_ty] in *.
    assert (HM : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ a_mem H n : A)
      by (change (a_mem H n) with (member_ref H (n :: nil));
          eapply member_ref_wf; [ exact HH | exact Hm | discriminate | exact HA | exact (HR eq_refl) | exact (HMu eq_refl) ]).
    pose proof (wk_preserves_typ _ _ _ _ _ _ _ HA Hw) as HA1.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HM Hw) as HM1.
    cbn [gentry_wk option_map].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_def true pv A[wk_shiftn (length (body_ctx Φg))]ʷ
                                               (Some (a_mem H n)[wk_shiftn (length (body_ctx Φg))]ʷ))))).
    apply (IH Eio Γ0 Ψ eq_refl HH).
    rewrite app_assoc in HA1, HM1; cbn [body_ctx app].
    eapply wf_ext_eq_def; [ exact HX | exact HA1 | apply wf_exp_eq_refl; exact HA1 | exact HM1 | apply wf_exp_eq_refl; exact HM1
                          | exact HA1 | exact HM1 ].
  - assert (HE : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ me_mem H n ≈ me_mem H n)
      by (eapply wf_me_mem; [ exact HH | exact Hm | reflexivity | exact Hm | reflexivity ]).
    assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias (me_mem H n)) ≈ gu_mk nil (md_alias (me_mem H n)))
      by (apply wf_unit_eq_alias; [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HE | exact HE ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_mod pv (gunit_wk (gu_mk nil (md_alias (me_mem H n))) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Eio Γ0 Ψ eq_refl HH).
    cbn [body_ctx app]; apply wf_ext_eq_mod; [ exact HX | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
Qed.

(** An open's entries, after the body before it. *)
Corollary gens_ext_wf : forall Γ0 Ψ Φx H its gs,
    items_gen gc_deps gc_stack None (body_ctx Φx ++ Ψ ++ Γ0) H its gs ->
    gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Ψ ++ Γ0 ⊢ᵐ H ≈ H ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φx ++ Ψ ≈ body_ctx Φx ++ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx (gens_append Φx 0 gs) ++ Ψ ≈ body_ctx (gens_append Φx 0 gs) ++ Ψ.
Proof.
  intros * Hg HH HX.
  rewrite gens_body_ctx_base, <- app_assoc.
  rewrite app_assoc in Hg, HH.
  pose proof (gens_ext_wf_gen _ _ _ _ _ Hg eq_refl Γ0 (body_ctx Φx ++ Ψ) eq_refl HH gm_nil HX) as H'.
  exact H'.
Qed.

End Fixed_GCtx.
