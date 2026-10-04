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
  Variables (Θ : gdeps) (Ξ : gstack).

  (** ** Lists of Arguments *)

  Lemma eval_exps_app : forall Ms Ns ρ ms ns,
      ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> ⟦ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns -> ⟦ Ms ++ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms ++ ns.
  Proof. induction 1; intros; cbn; [ assumption | econstructor; eauto ]. Qed.

  Lemma eval_exps_app_inv : forall Ms Ns ρ ls,
      ⟦ Ms ++ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ls -> exists ms ns, ls = ms ++ ns /\ ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms /\ ⟦ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns.
  Proof.
    induction Ms; intros * H; cbn in H.
    - exists nil, ls; repeat split; [ constructor | assumption ].
    - inversion H; subst. destruct (IHMs _ _ _ ltac:(eassumption)) as (ms1 & ns1 & -> & ? & ?).
      exists (m :: ms1), ns1; split; [ reflexivity | split; [ econstructor; eassumption | assumption ] ].
  Qed.

  Lemma eval_apps_app : forall f ms ns r,
      $*| f & ms ++ ns | Θ ⍮ Ξ ↘ r <-> exists g, $*| f & ms | Θ ⍮ Ξ ↘ g /\ $*| g & ns | Θ ⍮ Ξ ↘ r.
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

  (** ** Members of Global Modules

      A member of a global module applied to [args] is the member of the
      module with no argument, applied to [args]. *)

  Lemma eval_sel_global_apps : forall p x f args r,
      dm_global p nil ·ₜ x Θ ⍮ Ξ ↘ f -> $*| f & args | Θ ⍮ Ξ ↘ r -> dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r.
  Proof.
    intros * Hf Ha; inversion Hf; subst;
      match goal with Hn : eval_apps _ _ _ nil _ |- _ => inversion Hn; subst end;
      [ eapply eval_sel_global | eapply eval_sel_global_neut ]; eassumption.
  Qed.

  Lemma eval_sel_global_inv : forall p x args r,
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r ->
      exists f, dm_global p nil ·ₜ x Θ ⍮ Ξ ↘ f /\ $*| f & args | Θ ⍮ Ξ ↘ r.
  Proof.
    intros * H; inversion H; subst; eexists; split; try eassumption;
      [ eapply eval_sel_global | eapply eval_sel_global_neut ]; eauto; constructor.
  Qed.

  (** A chain of submodules of a global module, none of them an alias, is the
      global module at the path the chain extends it to. *)
  Lemma eval_mems_global : forall mems H mq ρ,
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global mq nil ->
      (forall m1 m2, mems = m1 ++ m2 -> m1 <> nil ->
         forall U r, gc_module Θ Ξ (qname_app mq m1) <> Some (mr_alias U r)) ->
      ⟦ me_mems H mems ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global (qname_app mq mems) nil.
  Proof.
    induction mems as [| y mems IH]; intros * HH Hna; cbn [me_mems].
    - rewrite qname_app_nil; exact HH.
    - replace (qname_app mq (y :: mems)) with (qname_app (qname_app mq (y :: nil)) mems)
        by (unfold qname_app; cbn; rewrite <- app_assoc; reflexivity).
      apply IH.
      + econstructor; [ exact HH |]; apply eval_selm_global.
        intros U r; apply (Hna (y :: nil) mems eq_refl ltac:(discriminate)).
      + intros m1 m2 -> Hm1 U r.
        replace (qname_app (qname_app mq (y :: nil)) m1) with (qname_app mq (y :: m1))
          by (unfold qname_app; cbn; rewrite <- app_assoc; reflexivity).
        apply (Hna (y :: m1) m2 eq_refl ltac:(discriminate)).
  Qed.

  Lemma eval_mems_inv : forall pre H ρ h,
      ⟦ me_mems H pre ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> exists h0, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h0 /\ h0 ·ₘ* pre Θ ⍮ Ξ ↘ h.
  Proof.
    induction pre as [| y pre IH]; intros * Hh; cbn [me_mems] in Hh.
    - exists h; split; [ exact Hh | constructor ].
    - destruct (IH _ _ _ Hh) as (h1 & Hh1 & Hc); inversion Hh1; subst.
      eexists; split; [ eassumption | econstructor; eassumption ].
  Qed.

  Lemma eval_mems_intro : forall pre H ρ h0 h,
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h0 -> h0 ·ₘ* pre Θ ⍮ Ξ ↘ h -> ⟦ me_mems H pre ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h.
  Proof.
    induction pre as [| y pre IH]; intros * Hh Hc; cbn [me_mems]; inversion Hc; subst; [ exact Hh |].
    eapply IH; [ econstructor; eassumption | eassumption ].
  Qed.

  Corollary eval_path_mod : forall p ρ,
      (forall m1 m2, q_chain p = m1 ++ m2 -> m1 <> nil ->
         forall U r, gc_module Θ Ξ (q_abs (q_unit p) m1) <> Some (mr_alias U r)) ->
      ⟦ qname_mod p ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global p nil.
  Proof.
    intros [fp ms] ρ Hna; unfold qname_mod; cbn [q_unit q_chain] in *.
    pose proof (eval_mems_global ms (me_unit fp) (q_abs fp nil) ρ ltac:(constructor) Hna) as H.
    exact H.
  Qed.

  (** [apps M args] evaluates by applying [M]'s value to the arguments'. *)
  Lemma eval_apps_exp : forall args M ρ r,
      ⟦ apps M args ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <->
      exists f ns, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ f /\ ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ⍮ Ξ ↘ r.
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
      h ·ₘ* (pre ++ ch) Θ ⍮ Ξ ↘ r <-> exists h1, h ·ₘ* pre Θ ⍮ Ξ ↘ h1 /\ h1 ·ₘ* ch Θ ⍮ Ξ ↘ r.
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
      h ·ₘ* pre Θ ⍮ Ξ ↘ h0 -> h0 ·ₘ y Θ ⍮ Ξ ↘ r -> h ·ₘ* (pre ++ [y]) Θ ⍮ Ξ ↘ r.
  Proof.
    intros; apply eval_selmc_app; exists h0; split; [ assumption | econstructor; [ eassumption | constructor ] ].
  Qed.

  Lemma eval_selmc_snoc_inv : forall pre y h r,
      h ·ₘ* (pre ++ [y]) Θ ⍮ Ξ ↘ r -> exists h0, h ·ₘ* pre Θ ⍮ Ξ ↘ h0 /\ h0 ·ₘ y Θ ⍮ Ξ ↘ r.
  Proof.
    intros * H; apply eval_selmc_app in H as (h0 & ? & Hy).
    inversion Hy; subst; match goal with H : eval_selmc _ _ _ nil _ |- _ => inversion H; subst end.
    eauto.
  Qed.

  Lemma eval_selc_app : forall pre h ch r,
      ch <> nil ->
      h ·ₜ* (pre ++ ch) Θ ⍮ Ξ ↘ r <-> exists h1, h ·ₘ* pre Θ ⍮ Ξ ↘ h1 /\ h1 ·ₜ* ch Θ ⍮ Ξ ↘ r.
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
      forall h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h <-> exists hr, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ hr /\ hr ·ₘ* pre Θ ⍮ Ξ ↘ h.
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
      ⟦ member_ref H ch ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <->
      (let '(R, args, pre) := modexp_spine H in
       exists h f ns, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h /\ h ·ₜ* (pre ++ ch) Θ ⍮ Ξ ↘ f /\
                 ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ⍮ Ξ ↘ r).
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
      ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <->
      exists h f ns, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h /\ h ·ₜ* (pre ++ [x]) Θ ⍮ Ξ ↘ f /\
                ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ⍮ Ξ ↘ r.
  Proof.
    intros * Hs; split.
    - intros Hm; inversion Hm; subst.
      match goal with Hs' : modexp_spine H = _ |- _ => rewrite Hs in Hs'; injection Hs' as <- <- <- end.
      do 3 eexists; repeat split; eassumption.
    - intros (h & f & ns & ? & ? & ? & ?); econstructor; eassumption.
  Qed.

  Lemma eval_mem_apps : forall H x R args pre ρ r,
      modexp_spine H = (R, args, pre) ->
      ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <-> ⟦ apps (member_ref R (pre ++ [x])) args ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r.
  Proof.
    intros * Hs.
    pose proof (modexp_spine_root_spine _ _ _ _ Hs) as HR.
    rewrite (eval_mem_spine _ _ _ _ _ _ _ Hs), eval_apps_exp.
    assert (Href : forall f, ⟦ member_ref R (pre ++ [x]) ⟧ Θ ⍮ Ξ ⍮ ρ ↘ f <->
                        exists h, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h /\ eval_selc Θ Ξ h (pre ++ [x]) f).
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
      ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <-> exists h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h /\ h ·ₜ x Θ ⍮ Ξ ↘ r.
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
      exists h; split; [ apply (eval_modexp_noargs _ _ Hn _ _ Hs); eauto | inversion Hx; subst; [ assumption | match goal with H0 : eval_selc _ _ _ nil _ |- _ => inversion H0 end ] ].
    - intros (h & Hh & Hx).
      apply (eval_modexp_noargs _ _ Hn _ _ Hs) in Hh as (hr & Hr & Hc).
      exists hr, r, nil; repeat split; [ assumption | | constructor | constructor ].
      apply eval_selc_app; [ discriminate |]; exists h; split; [ assumption | constructor; assumption ].
  Qed.

  (** ** Generalized Types and Bodies

      A unit's member is generalized over the body before it, which become
      [ℓ]/[ℓₘ] binders, and over the parameters, which become [Π]/[λ]
      binders.  The [ℓ]-binders evaluate exactly as the body does. *)

  Lemma eval_ctx_pi_body : forall Φ ρ ρ1 A a,
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ a -> ⟦ ctx_pi (body_ctx Φ) A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a.
  Proof.
    intros * Hb; revert A a; induction Hb; intros A0 a0 HA; cbn; [ assumption | | | eauto ].
    - apply IHHb; econstructor; eassumption.
    - apply IHHb; econstructor; eassumption.
  Qed.

  Lemma eval_ctx_fn_body : forall Φ ρ ρ1 M m,
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m -> ⟦ ctx_fn (body_ctx Φ) M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m.
  Proof.
    intros * Hb; revert M m; induction Hb; intros M0 m0 HM; cbn; [ assumption | | | eauto ].
    - apply IHHb; econstructor; eassumption.
    - apply IHHb; econstructor; eassumption.
  Qed.
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
Lemma eval_mem_apps_sub : forall {Θ Ξ} H x R args pre σ ρ r,
    modexp_spine H = (R, args, pre) ->
    ⟦ (a_mem H x)[σ] ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <-> ⟦ (apps (member_ref R (pre ++ [x])) args)[σ] ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r.
Proof.
  intros * Hs.
  pose proof (modexp_spine_sub_gen _ _ _ _ σ Hs) as Hsσ.
  rewrite apps_sub, member_ref_sub.
  cbn [exp_sub].
  destruct (modexp_spine R[σ]ᵐ) as [[R' a'] p'] eqn:ER.
  rewrite (eval_mem_spine _ _ _ _ _ _ _ _ _ Hsσ), eval_apps_exp.
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
