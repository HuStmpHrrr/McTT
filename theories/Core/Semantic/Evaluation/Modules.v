(** * Evaluation of Members

    How the evaluation of a member relates to the evaluation of the terms it
    is equal to: a member of an applied module is its root's member applied
    to the arguments, a member of a module with no argument is selection from
    the module's value, and a member's generalized type and body evaluate as
    the unit's own entries do. *)

From Stdlib Require Import List.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Semantic.Evaluation Require Import Definitions Lemmas.
Import Domain_Notations Syntax_Notations.

Section Members.
  Variables (Θ : gctx).

  (** ** Lists of Arguments *)

  Lemma eval_exps_app : forall Ms Ns ρ ms ns,
      ⟦ Ms ⟧* Θ ⍮ ρ ↘ ms -> ⟦ Ns ⟧* Θ ⍮ ρ ↘ ns -> ⟦ Ms ++ Ns ⟧* Θ ⍮ ρ ↘ ms ++ ns.
  Proof. induction 1; intros; cbn; [ assumption | econstructor; eauto ]. Qed.

  Lemma eval_exps_app_inv : forall Ms Ns ρ ls,
      ⟦ Ms ++ Ns ⟧* Θ ⍮ ρ ↘ ls -> exists ms ns, ls = ms ++ ns /\ ⟦ Ms ⟧* Θ ⍮ ρ ↘ ms /\ ⟦ Ns ⟧* Θ ⍮ ρ ↘ ns.
  Proof.
    induction Ms; intros * H; cbn in H.
    - exists nil, ls; repeat split; [ constructor | assumption ].
    - inversion H; subst. destruct (IHMs _ _ _ ltac:(eassumption)) as (ms1 & ns1 & -> & ? & ?).
      exists (m :: ms1), ns1; split; [ reflexivity | split; [ econstructor; eassumption | assumption ] ].
  Qed.

  Lemma eval_apps_app : forall f ms ns r,
      $*| f & ms ++ ns | Θ ↘ r <-> exists g, $*| f & ms | Θ ↘ g /\ $*| g & ns | Θ ↘ r.
  Proof.
    intros f ms; revert f; induction ms; intros; cbn; split.
    - intros H; exists f; split; [ constructor | assumption ].
    - intros (g & Hg & H); inversion Hg; subst; assumption.
    - intros H; inversion H; subst.
      destruct (proj1 (IHms _ _ _) ltac:(eassumption)) as (g & ? & ?).
      exists g; split; [ econstructor |]; eassumption.
    - intros (g & Hg & H); inversion Hg; subst; econstructor; [ eassumption |].
      apply IHms; eauto.
  Qed.

  Lemma eval_mems_inv : forall pre H ρ h,
      ⟦ me_mems H pre ⟧ᵐ Θ ⍮ ρ ↘ h -> exists h0, ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h0 /\ h0 ·ₘ* pre Θ ↘ h.
  Proof.
    induction pre as [| y pre IH]; intros * Hh; cbn [me_mems] in Hh.
    - exists h; split; [ exact Hh | constructor ].
    - destruct (IH _ _ _ Hh) as (h1 & Hh1 & Hc); inversion Hh1; subst.
      eexists; split; [ eassumption | econstructor; eassumption ].
  Qed.

  Lemma eval_mems_intro : forall pre H ρ h0 h,
      ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h0 -> h0 ·ₘ* pre Θ ↘ h -> ⟦ me_mems H pre ⟧ᵐ Θ ⍮ ρ ↘ h.
  Proof.
    induction pre as [| y pre IH]; intros * Hh Hc; cbn [me_mems]; inversion Hc; subst; [ exact Hh |].
    eapply IH; [ econstructor; eassumption | eassumption ].
  Qed.

  (** [apps M args] evaluates by applying [M]'s value to the arguments'. *)
  Lemma eval_apps_exp : forall args M ρ r,
      ⟦ apps M args ⟧ Θ ⍮ ρ ↘ r <->
      exists f ns, ⟦ M ⟧ Θ ⍮ ρ ↘ f /\ ⟦ args ⟧* Θ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ↘ r.
  Proof.
    induction args as [| N args IH]; intros; cbn; split.
    - intros H; exists r, nil; repeat split; [ assumption | constructor | constructor ].
    - intros (f & ns & Hf & Hns & Ha); inversion Hns; subst; inversion Ha; subst; assumption.
    - intros H; apply IH in H as (f1 & ns & Hf1 & Hns & Ha).
      inversion Hf1; subst.
      eexists _, (_ :: ns); repeat split; [ eassumption | econstructor; eassumption | econstructor; eassumption ].
    - intros (f & ns & Hf & Hns & Ha); inversion Hns; subst; inversion Ha; subst.
      apply IH; do 2 eexists; repeat split; [ econstructor; eassumption | eassumption | eassumption ].
  Qed.

  (** ** Chains of Selections *)

  Lemma eval_selmc_app : forall pre ch h r,
      h ·ₘ* (pre ++ ch) Θ ↘ r <-> exists h1, h ·ₘ* pre Θ ↘ h1 /\ h1 ·ₘ* ch Θ ↘ r.
  Proof.
    induction pre as [| y pre IH]; intros; cbn; split.
    - intros H; exists h; split; [ constructor | assumption ].
    - intros (h1 & H1 & H); inversion H1; subst; assumption.
    - intros H; inversion H; subst.
      destruct (proj1 (IH _ _ _) ltac:(eassumption)) as (h2 & ? & ?).
      exists h2; split; [ econstructor |]; eassumption.
    - intros (h1 & H1 & H); inversion H1; subst.
      econstructor; [ eassumption |]; apply IH; eauto.
  Qed.

  Lemma eval_selmc_snoc : forall pre y h h0 r,
      h ·ₘ* pre Θ ↘ h0 -> h0 ·ₘ y Θ ↘ r -> h ·ₘ* (pre ++ [y]) Θ ↘ r.
  Proof.
    intros; apply eval_selmc_app; exists h0; split; [ assumption | econstructor; [ eassumption | constructor ] ].
  Qed.

  Lemma eval_selmc_snoc_inv : forall pre y h r,
      h ·ₘ* (pre ++ [y]) Θ ↘ r -> exists h0, h ·ₘ* pre Θ ↘ h0 /\ h0 ·ₘ y Θ ↘ r.
  Proof.
    intros * H; apply eval_selmc_app in H as (h0 & ? & Hy).
    inversion Hy; subst; match goal with H : eval_selmc _ _ nil _ |- _ => inversion H; subst end.
    eauto.
  Qed.

  Lemma eval_selc_app : forall pre h ch r,
      ch <> nil ->
      h ·ₜ* (pre ++ ch) Θ ↘ r <-> exists h1, h ·ₘ* pre Θ ↘ h1 /\ h1 ·ₜ* ch Θ ↘ r.
  Proof.
    induction pre as [| y pre IH]; intros * Hch; cbn; split.
    - intros H; exists h; split; [ constructor | assumption ].
    - intros (h1 & H1 & H); inversion H1; subst; assumption.
    - intros H.
      assert (Hne : pre ++ ch <> nil) by (intros E; apply app_eq_nil in E as [_ ->]; contradiction).
      inversion H; subst; [ exfalso; apply Hne; congruence |].
      destruct (proj1 (IH _ _ _ Hch) ltac:(eassumption)) as (h2 & ? & ?).
      exists h2; split; [ econstructor |]; eassumption.
    - intros (h1 & H1 & H); inversion H1; subst.
      econstructor; [ eassumption |]; apply IH; [ assumption |]; eauto.
  Qed.

  (** The value of a module expression with no argument is selection along its
      chain from its root's value. *)
  Lemma eval_modexp_noargs : forall H ρ,
      me_noargs H ->
      forall R pre, modexp_spine H = (R, nil, pre) ->
      forall h, ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h <-> exists hr, ⟦ R ⟧ᵐ Θ ⍮ ρ ↘ hr /\ hr ·ₘ* pre Θ ↘ h.
  Proof.
    induction H as [qp | x | H IH y | H IH N | U]; intros ρ Hn R pre Hs h; cbn in Hs, Hn.
    1,2,5: injection Hs as <- <-; split;
      [ intros; eexists; split; [ eassumption | constructor ]
      | intros (hr & ? & Hc); inversion Hc; subst; assumption ].
    2: contradiction.
    destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- -> <-.
    split.
    - intros Hh; inversion Hh; subst.
      destruct (proj1 (IH ρ Hn _ _ eq_refl _) ltac:(eassumption)) as (hr & Hr & Hc).
      exists hr; split; [ assumption |]; eapply eval_selmc_snoc; eassumption.
    - intros (hr & Hr & Hc).
      destruct (eval_selmc_snoc_inv _ _ _ _ Hc) as (h1 & Hc1 & Hy).
      econstructor; [| eassumption ].
      apply (proj2 (IH ρ Hn _ _ eq_refl _)); eauto.
  Qed.

  (** A member of a module expression is its root's member, applied to the
      expression's arguments: [H.x] and [apps (member_ref R (pre ++ x)) args]
      evaluate alike, whatever the spine. *)
  Lemma eval_member_ref : forall ch H ρ r,
      ch <> nil ->
      ⟦ member_ref H ch ⟧ Θ ⍮ ρ ↘ r <->
      (let '(R, args, pre) := modexp_spine H in
       exists h f ns, ⟦ R ⟧ᵐ Θ ⍮ ρ ↘ h /\ h ·ₜ* (pre ++ ch) Θ ↘ f /\
                 ⟦ args ⟧* Θ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ↘ r).
  Proof.
    induction ch as [| x ch IH]; intros * Hch; [ contradiction |].
    destruct ch as [| y ch].
    - cbn [member_ref]; destruct (modexp_spine H) as [[R args] pre] eqn:E; split.
      + intros Hm; inversion Hm; subst.
        match goal with Hs : modexp_spine H = _ |- _ => rewrite E in Hs; injection Hs as <- <- <- end.
        do 3 eexists; repeat split; eassumption.
      + intros (h & f & ns & ? & ? & ? & ?); econstructor; eassumption.
    - change (member_ref H (x :: y :: ch)) with (member_ref (me_mem H x) (y :: ch)).
      rewrite (IH _ _ _ ltac:(discriminate)); cbn [modexp_spine].
      destruct (modexp_spine H) as [[R args] pre].
      rewrite <- app_assoc; reflexivity.
  Qed.

  Lemma modexp_spine_root_spine : forall H R args pre,
      modexp_spine H = (R, args, pre) -> modexp_spine R = (R, nil, nil).
  Proof.
    induction H as [| | H IH y | H IH N |]; intros * Hs; cbn in Hs; try (injection Hs as <- <- <-; reflexivity);
      destruct (modexp_spine H) as [[R' a'] p'] eqn:E; injection Hs as <- <- <-; eauto.
  Qed.

  Lemma eval_mem_spine : forall H x R args pre ρ r,
      modexp_spine H = (R, args, pre) ->
      ⟦ a_mem H x ⟧ Θ ⍮ ρ ↘ r <->
      exists h f ns, ⟦ R ⟧ᵐ Θ ⍮ ρ ↘ h /\ h ·ₜ* (pre ++ [x]) Θ ↘ f /\
                ⟦ args ⟧* Θ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ↘ r.
  Proof.
    intros * Hs; split.
    - intros Hm; inversion Hm; subst.
      match goal with Hs' : modexp_spine H = _ |- _ => rewrite Hs in Hs'; injection Hs' as <- <- <- end.
      do 3 eexists; repeat split; eassumption.
    - intros (h & f & ns & ? & ? & ? & ?); econstructor; eassumption.
  Qed.

  Lemma eval_mem_apps : forall H x R args pre ρ r,
      modexp_spine H = (R, args, pre) ->
      ⟦ a_mem H x ⟧ Θ ⍮ ρ ↘ r <-> ⟦ apps (member_ref R (pre ++ [x])) args ⟧ Θ ⍮ ρ ↘ r.
  Proof.
    intros * Hs.
    pose proof (modexp_spine_root_spine _ _ _ _ Hs) as HR.
    rewrite (eval_mem_spine _ _ _ _ _ _ _ Hs), eval_apps_exp.
    assert (Href : forall f, ⟦ member_ref R (pre ++ [x]) ⟧ Θ ⍮ ρ ↘ f <->
                        exists h, ⟦ R ⟧ᵐ Θ ⍮ ρ ↘ h /\ eval_selc Θ h (pre ++ [x]) f).
    { intros f; rewrite eval_member_ref by (destruct pre; discriminate).
      rewrite HR; cbn [app]; split.
      - intros (h & f' & ns & ? & ? & Hns & Ha); inversion Hns; subst; inversion Ha; subst; eauto.
      - intros (h & ? & ?); exists h, f, nil; repeat split; [ assumption | assumption | constructor | constructor ]. }
    split.
    - intros (h & f & ns & ? & ? & ? & ?); exists f, ns; repeat split; [ apply Href; eauto | assumption | assumption ].
    - intros (f & ns & Hf & ? & ?); apply Href in Hf as (h & ? & ?); exists h, f, ns; repeat split; assumption.
  Qed.

  (** Without arguments, a member is selection from the module's value. *)
  Lemma eval_mem_noargs : forall H x ρ r,
      me_noargs H ->
      ⟦ a_mem H x ⟧ Θ ⍮ ρ ↘ r <-> exists h, ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h /\ h ·ₜ x Θ ↘ r.
  Proof.
    intros * Hn.
    destruct (modexp_spine H) as [[R args] pre] eqn:Hs.
    assert (Hargs : args = nil).
    { clear -Hn Hs; revert R args pre Hs; induction H; intros; cbn in Hs, Hn;
        try (injection Hs as <- <- <-; reflexivity); [| contradiction ].
      destruct (modexp_spine H) as [[R' a'] p'] eqn:E; injection Hs as <- <- <-; eauto. }
    subst args.
    rewrite (eval_mem_spine _ _ _ _ _ _ _ Hs); split.
    - intros (hr & f & ns & Hr & Hc & Hns & Ha); inversion Hns; subst; inversion Ha; subst.
      assert (Hx1 : [x] <> nil) by discriminate.
      apply (eval_selc_app _ _ _ _ Hx1) in Hc as (h & Hh & Hx).
      exists h; split; [ apply (eval_modexp_noargs _ _ Hn _ _ Hs); eauto | inversion Hx; subst; [ assumption | match goal with H0 : eval_selc _ _ nil _ |- _ => inversion H0 end ] ].
    - intros (h & Hh & Hx).
      apply (eval_modexp_noargs _ _ Hn _ _ Hs) in Hh as (hr & Hr & Hc).
      exists hr, r, nil; repeat split; [ assumption | | constructor | constructor ].
      apply eval_selc_app; [ discriminate |]; exists h; split; [ assumption | constructor; assumption ].
  Qed.

  (** ** Generalized Types and Bodies

      A unit's member is generalized over its self slot, which becomes an
      [ℓₘ]-binder, and over the parameters, which become [Π]/[λ] binders.
      The [ℓₘ]-binder evaluates to the closure of the body before the
      member, as selection binds the self slot. *)

  Lemma eval_ctx_pi_self : forall Φ ρ A a,
      ⟦ A ⟧ Θ ⍮ ρ ↦ᵐ dm_body ρ nil Φ nil ↘ a <-> ⟦ ctx_pi (self_ent Φ :: nil) A ⟧ Θ ⍮ ρ ↘ a.
  Proof. intros; cbn; split; intros H; [ econstructor; exact H | inversion H; subst; assumption ]. Qed.

  Lemma eval_ctx_fn_self : forall Φ ρ M m,
      ⟦ M ⟧ Θ ⍮ ρ ↦ᵐ dm_body ρ nil Φ nil ↘ m <-> ⟦ ctx_fn (self_ent Φ :: nil) M ⟧ Θ ⍮ ρ ↘ m.
  Proof. intros; cbn; split; intros H; [ econstructor; exact H | inversion H; subst; assumption ]. Qed.
End Members.

Lemma ctx_pi_app : forall Ψ1 Ψ2 A, ctx_pi (Ψ1 ++ Ψ2) A = ctx_pi Ψ2 (ctx_pi Ψ1 A).
Proof. induction Ψ1 as [| [] Ψ1 IH]; intros; cbn; auto. Qed.

Lemma ctx_fn_app : forall Ψ1 Ψ2 M, ctx_fn (Ψ1 ++ Ψ2) M = ctx_fn Ψ2 (ctx_fn Ψ1 M).
Proof. induction Ψ1 as [| [] Ψ1 IH]; intros; cbn; auto. Qed.

(** The spine of a substituted module expression: the substituted root's spine,
    followed by the substituted arguments and the selections. *)
Lemma modexp_spine_sub_gen : forall H R args pre σ,
    modexp_spine H = (R, args, pre) ->
    modexp_spine H[σ]ᵐ =
      (let '(R', a', p') := modexp_spine R[σ]ᵐ in (R', a' ++ List.map (fun N => N[σ]) args, p' ++ pre)).
Proof.
  induction H as [| | H IH y | H IH N |]; intros * Hs; cbn in Hs.
  1,2,5: injection Hs as <- <- <-; destruct (modexp_spine _) as [[R' a'] p']; rewrite !app_nil_r; reflexivity.
  - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
    cbn [modexp_sub modexp_spine]; rewrite (IH _ _ _ _ eq_refl).
    destruct (modexp_spine R0[σ]ᵐ) as [[R' a'] p']; rewrite app_assoc; reflexivity.
  - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
    cbn [modexp_sub modexp_spine]; rewrite (IH _ _ _ _ eq_refl).
    destruct (modexp_spine R0[σ]ᵐ) as [[R' a'] p']; rewrite map_app, app_assoc; reflexivity.
Qed.

(** [H.x] and [apps (member_ref R (pre ++ x)) args] evaluate alike under any
    substitution. *)
Lemma eval_mem_apps_sub : forall {Θ} H x R args pre σ ρ r,
    modexp_spine H = (R, args, pre) ->
    ⟦ (a_mem H x)[σ] ⟧ Θ ⍮ ρ ↘ r <-> ⟦ (apps (member_ref R (pre ++ [x])) args)[σ] ⟧ Θ ⍮ ρ ↘ r.
Proof.
  intros * Hs.
  pose proof (modexp_spine_sub_gen _ _ _ _ σ Hs) as Hsσ.
  rewrite apps_sub, member_ref_sub.
  cbn [exp_sub].
  destruct (modexp_spine R[σ]ᵐ) as [[R' a'] p'] eqn:ER.
  rewrite (eval_mem_spine _ _ _ _ _ _ _ _ Hsσ), eval_apps_exp.
  split.
  - intros (h & f & ns & Hh & Hc & Hns & Ha).
    apply eval_exps_app_inv in Hns as (ms1 & ns2 & -> & Hms1 & Hns2).
    apply eval_apps_app in Ha as (g & Hg & Ha).
    exists g, ns2; repeat split; [| assumption | assumption ].
    apply eval_member_ref; [ destruct pre; discriminate |]; rewrite ER.
    exists h, f, ms1; repeat split; [ assumption | rewrite app_assoc; assumption | assumption | assumption ].
  - intros (g & ns2 & Hg & Hns2 & Ha).
    apply eval_member_ref in Hg; [| destruct pre; discriminate ]; rewrite ER in Hg.
    destruct Hg as (h & f & ms1 & Hh & Hc & Hms1 & Hg).
    exists h, f, (ms1 ++ ns2); repeat split; [ assumption | rewrite <- app_assoc; assumption | | ].
    + apply eval_exps_app; assumption.
    + apply eval_apps_app; eauto.
Qed.
