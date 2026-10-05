(** * Normal Forms of Member Types by Evaluation

    The member type of a definition [x] of a module [H] holds the bodies
    before [x] literally, as [ℓₘ]-binders, and member types of aliases and
    submodules hold them again for every sibling they instantiate.  The
    checker needs only the normal form of the member type, and when [H]
    takes no more argument it gets it without building the member type:
    it evaluates [H] in the initial environment, takes the type value of
    [x] there ([sel_ty], [h ⦂ₜ x Θ ↘ a]) and reads it back.

    This is sound because a well-formed module expression is valid in its
    members ([wf_modexp_sem_mt]): its value types [x] at the value of the
    member type ([mtyped]), and that value is related to the one
    [sel_ty] gives ([mtyped_sel_ty]), so both read back to the same normal
    form ([sel_ty_nbe]). *)

From Stdlib Require Import List Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Semantic Require Import Realizability MemberWf.
From Mctt.Core.Completeness Require Import UniverseCases MemberCases MemberTyping MemberSem.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The type value [sel_ty] gives is related to the one at which the module
    value types the member. *)
Lemma mtyped_sel_ty : forall h x a,
    h ⦂ₜ x gc_ctx ↘ a ->
    forall a', mtyped h (x :: nil) mk_term a' -> exists i R, per_univ_elem i R a' a.
Proof.
  induction 1 as [| ? ? ? ? ? ? ? Hl He Hs IH]; intros a' Hm;
    inversion Hm; subst;
    (** an unsaturated value has no [sel_ty] *)
    try (match goal with Hx : exists _ _ _, _ = dm_local _ _ _ /\ _ |- _ =>
      destruct Hx as (ρ0 & U0 & args0 & Heq & Hlt);
      destruct U0 as [Δ0 [Φ0 | E0]]; cbn in Heq; inversion Heq; subst; cbn in Hlt; lia end);
    repeat match goal with H1 : ?a = Some _, H2 : ?a = Some _ |- _ => rewrite H1 in H2; inversion H2; subst; clear H2 end;
    functional_eval_rewrite_clear;
    repeat match goal with H1 : eval_modexp _ ?E ?r ?h1, H2 : eval_modexp _ ?E ?r ?h2 |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst; clear H2 end;
    eauto.
Qed.

(** The type value [sel_ty] gives reads back to the normal form of the
    member type. *)
Theorem sel_ty_nbe : forall Γ H x A h a B R,
    sem_mt gc_ctx Γ H ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    member_type gc_ctx Γ H (x :: nil) (mr_term A) ->
    forall ρ, initial_env_f Γ ρ ->
    ⟦ H ⟧ᵐ gc_ctx ⍮ ρ ↘ h ->
    h ⦂ₜ x gc_ctx ↘ a ->
    Rtyp a in length Γ ↘ B ->
    nbe_ty_f Γ A B.
Proof.
  intros * [S1 _] HR Hm ρ Hρ Hh Hs HB.
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ1 & ρ2 & Hρ1 & Hρ2 & Hr).
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ2 = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (proj2 (S1 _ _ Hm ltac:(discriminate)) _ _ HR Hr _ Hh) as (a' & Ha' & Hma'); cbn in Ha', Hma'.
  destruct (mtyped_sel_ty _ _ _ Hs _ Hma') as (i & E & HE).
  destruct (per_univ_then_per_top_typ HE (length Γ)) as (C & HC1 & HC2).
  pose proof (functional_read_typ _ _ _ _ HC2 HB) as ->.
  econstructor; eassumption.
Qed.

(** The form the checker uses: for a well-formed module expression. *)
Corollary sel_ty_nbe_wf : forall Γ H x A h a B ρ,
    ⊢ Γ ->
    gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_ctx Γ H (x :: nil) (mr_term A) ->
    initial_env_f Γ ρ ->
    ⟦ H ⟧ᵐ gc_ctx ⍮ ρ ↘ h ->
    h ⦂ₜ x gc_ctx ↘ a ->
    Rtyp a in length Γ ↘ B ->
    nbe_ty_f Γ A B.
Proof.
  intros * HΓ HH Hm Hρ Hh Hs HB.
  destruct (sem_ctx_per_ctx_env (completeness_fundamental_ctx _ HΓ)) as [R HR].
  eapply sel_ty_nbe; [ exact (proj1 (wf_modexp_sem_mt _ _ HH)) | exact HR | eassumption .. ].
Qed.
(** ** The Next Parameter of a Module Value

    The checker checks the argument [N] of [me_app H N] against the normal
    form of [H]'s next parameter type, read back from the value of [H]
    ([nextdom]), without building [H]'s arity, which holds the bodies
    before [H] literally.  [nextdom_nbe_wf] shows this is the normal form
    of the arity's outermost parameter ([tele_view]). *)

Lemma nextparam_nextdom : forall w a, nextparam w a -> forall a', nextdom w a' -> a = a'.
Proof.
  induction 1 as [ρ Δ Φ args A a Hn Ha | ρ Δ E args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH];
    intros a' H'; inversion H'; subst;
    try (eapply nextparam_functional; [ | eassumption ]; econstructor; eassumption);
    try match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
  match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
  eauto.
Qed.

Lemma nextdom_functional : forall w a, nextdom w a -> forall a', nextdom w a' -> a = a'.
Proof.
  induction 1 as [w a Hn | h ch a Hn IH | ρ Δ E args h a Hl HE Hn IH]; intros a' H'.
  - eapply nextparam_nextdom; eassumption.
  - inversion H'; subst; [ match goal with Hp : nextparam _ _ |- _ => inversion Hp end | eauto ].
  - inversion H'; subst.
    + symmetry; eapply nextparam_nextdom; [ eassumption | econstructor; eassumption ].
    + match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      eauto.
Qed.

(** A saturated value takes no argument. *)
Lemma msat_nextdom : forall w, msat w -> forall a, ~ nextdom w a.
Proof.
  induction 1 as [ρ Δ Φ args Hl | ρ Δ E args h Hl HE Hs IH]; intros a Hn.
  - eapply nextdom_body_sat; eassumption.
  - inversion Hn; subst.
    + match goal with Hp : nextparam _ _ |- _ => inversion Hp; subst end.
      * match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
      * match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
        eapply IH, nd_param; eassumption.
    + match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      eapply IH; eassumption.
Qed.

(** A local value still lacking an argument types its members at [Π]s. *)
Lemma mtyped_unsat_pi : forall ρ U args ch k a,
    List.length args < List.length (gu_params U) -> mtyped (dm_local ρ U args) ch k a ->
    exists a1 ρB B, a = Πᵈ a1 ρB B.
Proof.
  intros ρ [Δ [Φ | E]] * Hl Hm; cbn in Hl, Hm; inversion Hm; subst; eauto;
    try lia;
    match goal with Hs : msat _ |- _ => inversion Hs; subst; lia end.
Qed.

(** A value that takes an argument has a [Π] for its arity. *)
Lemma mtyped_nextdom_pi : forall w ch k a, mtyped w ch k a -> ch = nil -> k = mk_mod ->
    forall a', nextdom w a' -> exists a1 ρB B, a = Πᵈ a1 ρB B.
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros Hc Hk' a' Hn; subst; try discriminate; eauto.
  - exfalso; exact (msat_nextdom _ Hs _ Hn).
  - inversion Hn; subst.
    + match goal with Hp : nextparam _ _ |- _ => inversion Hp; subst end.
      * match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
      * match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
        eapply IH; [ reflexivity | reflexivity | apply nd_param; eassumption ].
    + match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      eapply IH; [ reflexivity | reflexivity | eassumption ].
  - eapply mtyped_unsat_pi; eassumption.
Qed.

(** An arity without an assumption is [⊤] behind definitions. *)
Lemma tele_view_none_top : forall T, tele_view T = None ->
    forall ρ a, ⟦ ctx_pi T ⊤ ⟧ gc_ctx ⍮ ρ ↘ a -> a = ⊤ᵈ.
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  intros R; rewrite rev_involutive.
  induction R as [| [B | B N | U] R IH]; intros Hv ρ a Ha; rewrite ?ctx_pi_rev_cons in Ha; cbn in Hv.
  - cbn in Ha; inversion Ha; reflexivity.
  - discriminate.
  - destruct (tele_open R) as [[? ?] |]; [ discriminate |].
    inversion Ha; subst; eauto.
  - destruct (tele_open R) as [[? ?] |]; [ discriminate |].
    inversion Ha; subst; eauto.
Qed.

(** The value of a well-formed module expression takes an argument exactly
    when its arity has a parameter; the argument's type value then reads
    back to the parameter's normal form. *)
Theorem nextdom_nbe_wf : forall Γ H T h a ρ,
    ⊢ Γ -> gc_ctx ⍮ Γ ⊢ᵐ H ≈ H -> member_type gc_ctx Γ H nil (mr_mod T) ->
    initial_env_f Γ ρ -> ⟦ H ⟧ᵐ gc_ctx ⍮ ρ ↘ h -> nextdom h a ->
    exists B T1 C, tele_view T = Some (B, T1) /\ Rtyp a in length Γ ↘ C /\ nbe_ty_f Γ B C.
Proof.
  intros * HΓ HH Hm Hρ Hh Hn.
  destruct (wf_modexp_sem_mt _ _ HH) as [HS _].
  pose proof HS as [S1 _].
  destruct (sem_ctx_per_ctx_env (completeness_fundamental_ctx _ HΓ)) as [R HR].
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ1 & ρ2 & Hρ1 & Hρ2 & Hr).
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ2 = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (proj2 (S1 _ _ Hm ltac:(discriminate)) _ _ HR Hr _ Hh) as (a0 & Ha0 & Hma0).
  cbn [mres_ty mres_kind] in Ha0, Hma0.
  destruct (tele_view T) as [[B T1] |] eqn:Hv.
  2: { exfalso.
       pose proof (tele_view_none_top _ Hv _ _ Ha0) as ->.
       destruct (mtyped_nextdom_pi _ _ _ _ Hma0 eq_refl eq_refl _ Hn) as (? & ? & ? & ?); discriminate. }
  destruct (arity_pi _ _ _ _ _ HS Hm Hv) as (l & _ & _ & HA0).
  destruct (rel_exp_of_typ_inversion_simple_at HR HA0 _ _ Hr) as (x0 & p0 & Hx0 & Hp0 & [Rp0 HRp0]).
  functional_eval_rewrite_clear.
  inversion Hp0; subst.
  destruct (mtyped_arity_pi _ _ Hma0 _ _ _ _ _ HRp0) as (an & j & R0 & Hn1 & Hb).
  pose proof (nextdom_functional _ _ Hn1 _ Hn) as ->.
  destruct (per_univ_then_per_top_typ Hb (length Γ)) as (C & HC1 & HC2).
  exists B, T1, C; split; [ reflexivity | split; [ exact HC2 | econstructor; eassumption ] ].
Qed.

(** When the arity has a parameter, the value takes an argument. *)
Lemma nextdom_of_arity : forall Γ H T B T1 h ρ,
    ⊢ Γ -> gc_ctx ⍮ Γ ⊢ᵐ H ≈ H -> member_type gc_ctx Γ H nil (mr_mod T) -> tele_view T = Some (B, T1) ->
    initial_env_f Γ ρ -> ⟦ H ⟧ᵐ gc_ctx ⍮ ρ ↘ h -> exists a, nextdom h a.
Proof.
  intros * HΓ HH Hm Hv Hρ Hh.
  destruct (wf_modexp_sem_mt _ _ HH) as [HS _].
  pose proof HS as [S1 _].
  destruct (sem_ctx_per_ctx_env (completeness_fundamental_ctx _ HΓ)) as [R HR].
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ1 & ρ2 & Hρ1 & Hρ2 & Hr).
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ2 = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (proj2 (S1 _ _ Hm ltac:(discriminate)) _ _ HR Hr _ Hh) as (a0 & Ha0 & Hma0).
  cbn [mres_ty mres_kind] in Ha0, Hma0.
  destruct (arity_pi _ _ _ _ _ HS Hm Hv) as (l & _ & _ & HA0).
  destruct (rel_exp_of_typ_inversion_simple_at HR HA0 _ _ Hr) as (x0 & p0 & Hx0 & Hp0 & [Rp0 HRp0]).
  functional_eval_rewrite_clear.
  inversion Hp0; subst.
  destruct (mtyped_arity_pi _ _ Hma0 _ _ _ _ _ HRp0) as (an & _ & _ & Hn1 & _); eauto.
Qed.
End Fixed_GCtx.
