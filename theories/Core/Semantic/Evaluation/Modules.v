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
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
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

  (** Arguments applied in two groups. *)
  Lemma eval_app_args_app : forall Ms Ns f ρ r,
      eval_app_args Θ Ξ f (Ms ++ Ns) ρ r <-> exists g, eval_app_args Θ Ξ f Ms ρ g /\ eval_app_args Θ Ξ g Ns ρ r.
  Proof.
    induction Ms as [| M Ms IH]; intros; cbn; split.
    - intros H; exists f; split; [ constructor | assumption ].
    - intros (g & Hg & H); inversion Hg; subst; assumption.
    - intros H; inversion H; subst;
        (destruct (proj1 (IH _ _ _ _) ltac:(eassumption)) as (g' & ? & ?);
         exists g'; split; [ first [ eapply eval_app_args_evaluated; eassumption | eapply eval_app_args_proof; eassumption ] | assumption ]).
    - intros (g & Hg & H); inversion Hg; subst;
        [ eapply eval_app_args_evaluated | eapply eval_app_args_proof ]; try eassumption; apply IH; eauto.
  Qed.

  (** Where every function along the way takes arguments of an evaluated
      kind, the arguments are all evaluated and then applied. *)
  Lemma eval_app_args_evaluated_iff : forall (P : domain -> Prop),
      (forall f, P f -> evaluated_kind (arg_kind Θ Ξ f)) ->
      (forall f n g, P f -> $| f & n | Θ ⍮ Ξ ↘ g -> P g) ->
      forall Ns f ρ r, P f ->
      eval_app_args Θ Ξ f Ns ρ r <-> exists ns, ⟦ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| f & ns | Θ ⍮ Ξ ↘ r.
  Proof.
    intros P HP HPa; induction Ns as [| N Ns IH]; intros f ρ r Hf; split.
    - intros H; inversion H; subst; exists nil; split; constructor.
    - intros (ns & Hns & Ha); inversion Hns; subst; inversion Ha; subst; constructor.
    - intros H; inversion H; subst;
        [| exfalso; eapply evaluated_kind_not_propositional; [ exact (HP _ Hf) | eassumption ] ].
      match goal with Hg : $| f & ?n | _ ⍮ _ ↘ ?g, Hr : eval_app_args _ _ ?g _ _ _ |- _ =>
        apply (IH g) in Hr as (ns & ? & ?); [| eapply HPa; eassumption ] end.
      eexists; split; econstructor; eassumption.
    - intros (ns & Hns & Ha); inversion Hns; subst; inversion Ha; subst.
      eapply eval_app_args_evaluated; [ apply HP, Hf | eassumption | eassumption |].
      apply IH; [ eapply HPa; eassumption | eauto ].
  Qed.

  (** A type former, of an inductive type or of a record, takes arguments
      of an evaluated kind: its parameters ([arg_kind_ind_evaluated]). *)
  Lemma eval_app_args_ind : forall Ns p k vs ρ r,
      eval_app_args Θ Ξ (d_ind p k vs) Ns ρ r <-> exists ns, ⟦ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| d_ind p k vs & ns | Θ ⍮ Ξ ↘ r.
  Proof.
    intros; apply (eval_app_args_evaluated_iff (fun f => exists p k vs, f = d_ind p k vs));
      [ intros ? (? & ? & ? & ->); apply arg_kind_ind_evaluated
      | intros ? ? ? (? & ? & ? & ->) Ha; inversion Ha; subst; eauto
      | eauto ].
  Qed.

  Lemma eval_app_args_record : forall Ns p vs ρ r,
      eval_app_args Θ Ξ (d_record p vs) Ns ρ r <-> exists ns, ⟦ Ns ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| d_record p vs & ns | Θ ⍮ Ξ ↘ r.
  Proof.
    intros; apply (eval_app_args_evaluated_iff (fun f => exists p vs, f = d_record p vs));
      [ intros ? (? & ? & ->); apply arg_kind_record_evaluated
      | intros ? ? ? (? & ? & ->) Ha; inversion Ha; subst; eauto
      | eauto ].
  Qed.

  (** ** Members of Global Modules

      A relevant member of a global module applied to [args] is the member
      of the module with no argument, applied to [args].  A member tagged a
      proposition is kept as the selection of the member from the module at
      [args] ([eval_sel_global_proof]): it is not a value applied to the
      arguments. *)

  (** The value of the relevant term member [x] of the global module at
      [p], stored closed over the module's parameters, before any argument:
      the relevant cases of selection from a saturated global module,
      without the arguments. *)
  Inductive global_member_value (p : qname) (x : String.string) : domain -> Prop :=
  (** A term part ([gc_term]): its value in the empty environment *)
  | global_member_value_term : forall M f,
      gc_term Θ Ξ (qname_app p (x :: nil)) = Some M ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ f ->
      global_member_value p x f
  (** An opaque definition or axiom of an evaluated kind: a neutral at its
      closed type *)
  | global_member_value_neut : forall b pv κ A B a,
      gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv κ A B) ->
      evaluated_kind κ ->
      b = false \/ B = None ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
      global_member_value p x (⇑ a (d_glob (qname_app p (x :: nil))))
  (** The module of a member of a group of inductive types: its type former *)
  | global_member_value_indty : forall pq k D,
      gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
      ind_mlookup Θ Ξ (qname_app p (x :: nil)) = Some (pq, k, D) ->
      global_member_value p x (d_ind pq k nil)
  (** A record type: its type former *)
  | global_member_value_record : forall R,
      gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
      record_lookup Θ Ξ (qname_app p (x :: nil)) = Some R ->
      global_member_value p x (d_record (qname_app p (x :: nil)) nil).

  (** A member of a saturated global module is its stored value applied to
      the module's arguments. *)
  Lemma eval_sel_global_apps : forall p x f args r,
      module_saturated Θ Ξ p args ->
      global_member_value p x f -> $*| f & args | Θ ⍮ Ξ ↘ r -> dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r.
  Proof.
    intros * Hs Hf Ha; inversion Hf; subst;
      first [ eapply eval_sel_global; eassumption | eapply eval_sel_global_neut; eassumption
            | eapply eval_sel_global_ind; eassumption | eapply eval_sel_global_record; eassumption ].
  Qed.

  (** A member selected from a saturated global module: a relevant one, its
      stored value applied to the arguments, or one tagged a proposition,
      kept as its selection from the module, which has exactly its
      parameters. *)
  Lemma eval_sel_global_inv : forall p x args r,
      module_saturated Θ Ξ p args ->
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r ->
      (exists f, global_member_value p x f /\ $*| f & args | Θ ⍮ Ξ ↘ r) \/
      ((exists b pv A B, gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv ak_propositional A B)) /\
       exists T Φ, gc_loc Θ Ξ p = Some (T, Φ) /\ List.length args = List.length T /\
         r = ⋆ᵈ⟨member_proof x, global_proof_env p T args⟩).
  Proof.
    intros * Hs H; inversion H; subst;
      [ left; eexists; split; [ eapply global_member_value_term | ]; eassumption
      | left; eexists; split; [ eapply global_member_value_neut | ]; eassumption
      | right; split; [ do 4 eexists; eassumption | do 2 eexists; split; [ eassumption | split; [ eassumption | reflexivity ] ] ]
      | left; eexists; split; [ eapply global_member_value_indty |]; eassumption
      | exfalso; match goal with Hl : gc_loc _ _ _ = Some _ |- _ => specialize (Hs _ _ Hl) end; lia
      | left; eexists; split; [ eapply global_member_value_record | ]; eassumption ].
  Qed.

  (** A member of a global module lacking a parameter is its member
      closure. *)
  Lemma eval_sel_global_unsat_inv : forall p T Φ x args r,
      gc_loc Θ Ξ p = Some (T, Φ) -> List.length args < List.length T ->
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r -> r = d_member (dm_global p args) (x :: nil).
  Proof.
    intros * Hl Hlt H; inversion H; subst; try reflexivity;
      first [ match goal with Hs : module_saturated _ _ _ _ |- _ => specialize (Hs _ _ Hl) end; lia
            | (** a proof, at exactly the parameters *)
              match goal with Hl' : gc_loc _ _ _ = Some _ |- _ => rewrite Hl in Hl'; injection Hl' as <- <- end; lia ].
  Qed.

  (** Whether a global module at [args] is saturated is decided by its
      telescope. *)
  Lemma module_saturated_dec : forall p args,
      module_saturated Θ Ξ p args \/
      exists T Φ, gc_loc Θ Ξ p = Some (T, Φ) /\ List.length args < List.length T.
  Proof.
    intros p args; destruct (gc_loc Θ Ξ p) as [[T Φ] |] eqn:E.
    - destruct (PeanoNat.Nat.le_gt_cases (List.length T) (List.length args)) as [Hle | Hlt].
      + left; intros T' Φ' E'; rewrite E in E'; injection E' as <- <-; exact Hle.
      + right; exists T, Φ; split; [ reflexivity | exact Hlt ].
    - left; intros T' Φ' E'; rewrite E in E'; discriminate.
  Qed.

  (** A saturated global module stays saturated given more arguments. *)
  Lemma module_saturated_app : forall p args args',
      module_saturated Θ Ξ p args -> module_saturated Θ Ξ p (args ++ args').
  Proof. intros * Hs T Φ Hl; specialize (Hs _ _ Hl); rewrite List.length_app; lia. Qed.

  (** A chain of submodules of a global module, each a body module, an open
      frame or the module of an inductive type, is the global module at the
      path the chain extends it to. *)
  Lemma eval_mems_global : forall mems H mq ρ,
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global mq nil ->
      (forall m1 m2, mems = m1 ++ m2 -> m1 <> nil ->
         exists TΦ, gc_loc Θ Ξ (qname_app mq m1) = Some TΦ) ->
      ⟦ me_mems H mems ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global (qname_app mq mems) nil.
  Proof.
    induction mems as [| y mems IH]; intros * HH Hna; cbn [me_mems].
    - rewrite qname_app_nil; exact HH.
    - replace (qname_app mq (y :: mems)) with (qname_app (qname_app mq (y :: nil)) mems)
        by (unfold qname_app; cbn; rewrite <- app_assoc; reflexivity).
      apply IH.
      + econstructor; [ exact HH |].
        destruct (Hna (y :: nil) mems eq_refl ltac:(discriminate)) as (TΦ & Hl); eapply eval_selm_global; exact Hl.
      + intros m1 m2 -> Hm1.
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
         exists TΦ, gc_loc Θ Ξ (q_abs (q_unit p) m1) = Some TΦ) ->
      ⟦ qname_mod p ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global p nil.
  Proof.
    intros [fp ms] ρ Hna; unfold qname_mod; cbn [q_unit q_chain] in *.
    pose proof (eval_mems_global ms (me_unit fp) (q_abs fp nil) ρ ltac:(constructor) Hna) as H.
    exact H.
  Qed.

  (** [apps M args] evaluates by applying [M]'s value to the arguments,
      relevance-directed ([eval_app_args]). *)
  Lemma eval_apps_exp : forall args M ρ r,
      ⟦ apps M args ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <->
      exists f, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ f /\ eval_app_args Θ Ξ f args ρ r.
  Proof.
    induction args as [| N args IH]; intros; cbn; split.
    - intros H; exists r; split; [ assumption | constructor ].
    - intros (f & Hf & Ha); inversion Ha; subst; assumption.
    - intros H; apply IH in H as (f1 & Hf1 & Ha).
      inversion Hf1; subst; eexists; (split; [ eassumption |]);
        [ eapply eval_app_args_evaluated | eapply eval_app_args_proof ]; eassumption.
    - intros (f & Hf & Ha); inversion Ha; subst;
        apply IH; eexists; (split; [| eassumption ]); [ eapply eval_exp_app | eapply eval_exp_app_proof ]; eassumption.
  Qed.

  (** At a type former, the arguments are all evaluated, then applied. *)
  Corollary eval_apps_exp_ind : forall args p k ρ r,
      ⟦ apps (a_ind p k) args ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <->
      exists ns, ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| d_ind p k nil & ns | Θ ⍮ Ξ ↘ r.
  Proof.
    intros; rewrite eval_apps_exp; split.
    - intros (f & Hf & Ha); inversion Hf; subst; apply eval_app_args_ind in Ha; exact Ha.
    - intros H; exists (d_ind p k nil); split; [ constructor | apply eval_app_args_ind, H ].
  Qed.

  Corollary eval_apps_exp_record : forall args p ρ r,
      ⟦ apps (a_record p) args ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <->
      exists ns, ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns /\ $*| d_record p nil & ns | Θ ⍮ Ξ ↘ r.
  Proof.
    intros; rewrite eval_apps_exp; split.
    - intros (f & Hf & Ha); inversion Hf; subst; apply eval_app_args_record in Ha; exact Ha.
    - intros H; exists (d_record p nil); split; [ constructor | apply eval_app_args_record, H ].
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
      values of the expression's arguments, whatever the spine. *)
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

  (** [H.x] and [apps (member_ref R (pre ++ x)) args] evaluate alike where
      the member's value, and every value it is applied to the arguments
      along the way, takes arguments of an evaluated kind ([P]): the
      arguments of a module are evaluated, those of an application only at
      an argument of an evaluated kind. *)
  Lemma eval_mem_apps : forall (P : domain -> Prop),
      (forall f, P f -> evaluated_kind (arg_kind Θ Ξ f)) ->
      (forall f n g, P f -> $| f & n | Θ ⍮ Ξ ↘ g -> P g) ->
      forall H x R args pre ρ r,
      modexp_spine H = (R, args, pre) ->
      (forall f, ⟦ member_ref R (pre ++ [x]) ⟧ Θ ⍮ Ξ ⍮ ρ ↘ f -> P f) ->
      ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <-> ⟦ apps (member_ref R (pre ++ [x])) args ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r.
  Proof.
    intros P HP HPa * Hs HPf.
    pose proof (modexp_spine_root_spine _ _ _ _ Hs) as HR.
    rewrite (eval_mem_spine _ _ _ _ _ _ _ Hs), eval_apps_exp.
    assert (Href : forall f, ⟦ member_ref R (pre ++ [x]) ⟧ Θ ⍮ Ξ ⍮ ρ ↘ f <->
                        exists h, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h /\ h ·ₜ* (pre ++ [x]) Θ ⍮ Ξ ↘ f).
    { intros f; rewrite eval_member_ref by (destruct pre; discriminate).
      rewrite HR; cbn [app]; split.
      - intros (h & f' & ns & ? & ? & Hns & Ha); inversion Hns; subst; inversion Ha; subst; eauto.
      - intros (h & ? & ?); exists h, f, nil; repeat split; [ assumption | assumption | constructor | constructor ]. }
    split.
    - intros (h & f & ns & ? & ? & ? & ?).
      assert (Hf : ⟦ member_ref R (pre ++ [x]) ⟧ Θ ⍮ Ξ ⍮ ρ ↘ f) by (apply Href; eauto).
      exists f; split; [ exact Hf |].
      apply (eval_app_args_evaluated_iff P HP HPa _ _ _ _ (HPf _ Hf)); eauto.
    - intros (f & Hf & Ha).
      apply (eval_app_args_evaluated_iff P HP HPa _ _ _ _ (HPf _ Hf)) in Ha as (ns & ? & ?).
      apply Href in Hf as (h & ? & ?); exists h, f, ns; repeat split; assumption.
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
End Members.

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
