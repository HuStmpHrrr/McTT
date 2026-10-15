(** * A Module Expression Has the Kinds of its Value

    In a well-formed global context, the kinds read off a module expression
    in an environment ([skind]) are those of the module value it evaluates to
    ([dkind]), and selecting or applying a module value keeps the kinds of
    what is left ([kind_eval]).  A body evaluates to an environment with the
    kinds of the one the kinds read off it ([kenv]). *)

From Stdlib Require Import Lia List PeanoNat String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions GlobalModules.
From Mctt.Core.Semantic Require Import Evaluation Kinds KindsTyping.
Import Domain_Notations Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section KindsEval.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** *** Renaming by the Identity *)

  Lemma skind_id : forall ρ ρ', kren Θ Ξ wk_id ρ ρ' -> forall H ch k, skind Θ Ξ ρ H ch k <-> skind Θ Ξ ρ' H ch k.
  Proof.
    intros * K H ch k.
    rewrite <- (proj1 (kind_ren Θ Ξ) H wk_id ρ ρ' K), modexp_wk_id_ext by (intros x; reflexivity).
    reflexivity.
  Qed.

  Lemma ukind_id : forall ρ ρ', kren Θ Ξ wk_id ρ ρ' -> forall U ch k, ukind Θ Ξ ρ U ch k <-> ukind Θ Ξ ρ' U ch k.
  Proof.
    intros * K U ch k.
    rewrite <- (proj1 (proj2 (kind_ren Θ Ξ)) U wk_id ρ ρ' K), gunit_wk_id_ext by (intros x; reflexivity).
    reflexivity.
  Qed.

  Lemma kgens_id : forall ρ ρ', kren Θ Ξ wk_id ρ ρ' -> forall H its gs, kgens Θ Ξ ρ H its gs -> kgens Θ Ξ ρ' H its gs.
  Proof.
    intros * K H its gs; induction 1; constructor; auto; apply (skind_id _ _ K); assumption.
  Qed.

  (** *** Environments with the Same Kinds and Shape *)

  Definition is_modent (e : dentry) : bool :=
    match e with
    | de_mod _ => true
    | de_term _ => false
    end.

  (** Two environments with the same kinds, and modules at the same places. *)
  Definition kshape (ρ ρ' : env) : Prop :=
    kren Θ Ξ wk_id ρ ρ' /\ forall x, is_modent (env_entry ρ x) = is_modent (env_entry ρ' x).

  Lemma kshape_cons_term : forall ρ ρ' a a', kshape ρ ρ' -> kshape (de_term a :: ρ) (de_term a' :: ρ').
  Proof. intros * [K S]; split; intros [| x]; first [ apply kequiv_refl | apply K | reflexivity | apply S ]. Qed.

  Lemma kshape_cons_mod : forall ρ ρ' h h', kshape ρ ρ' -> kequiv Θ Ξ h h' -> kshape (de_mod h :: ρ) (de_mod h' :: ρ').
  Proof. intros * [K S] Hh; split; intros [| x]; first [ exact Hh | apply K | reflexivity | apply S ]. Qed.

  Lemma env_args_rev_args : forall args ρ, env_args ρ args = List.rev (List.map de_term args) ++ ρ.
  Proof.
    induction args as [| a args IH]; intros; [ reflexivity |].
    unfold env_args in *; cbn [List.fold_left List.map List.rev]; rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma kshape_terms : forall X Y ρ ρ', List.length X = List.length Y ->
      Forall (fun e => is_modent e = false) X -> Forall (fun e => is_modent e = false) Y ->
      kshape ρ ρ' -> kshape (X ++ ρ) (Y ++ ρ').
  Proof.
    induction X as [| e X IH]; intros [| e' Y] * Hl HX HY Hs; cbn in Hl; try discriminate; [ exact Hs |].
    inversion HX; inversion HY; subst.
    destruct e as [a | h], e' as [a' | h']; cbn in *; try discriminate.
    apply kshape_cons_term, IH; auto.
  Qed.

  Lemma kshape_args_pad : forall ρ args n, List.length args = n -> kshape (env_args ρ args) (kpad n ρ).
  Proof.
    intros * <-; rewrite env_args_rev_args; unfold kpad; apply kshape_terms.
    - rewrite length_rev, length_map, repeat_length; reflexivity.
    - apply Forall_rev, Forall_map, Forall_forall; reflexivity.
    - apply Forall_forall; intros e He; apply repeat_spec in He as ->; reflexivity.
    - split; [ intros x; apply kequiv_refl | reflexivity ].
  Qed.

  (** *** Global Modules *)

  Lemma dkind_global_args : forall p args args' ch k,
      dkind Θ Ξ (dm_global p args) ch k -> dkind Θ Ξ (dm_global p args') ch k.
  Proof. intros * Hk; inversion Hk; subst; solve [ econstructor; eassumption ]. Qed.

  Lemma dkind_global_snoc : forall p args y ch k,
      dkind Θ Ξ (dm_global (qname_app p (y :: nil)) args) ch k <-> dkind Θ Ξ (dm_global p args) (y :: ch) k.
  Proof.
    intros; split; intros Hk; inversion Hk; subst; rewrite ?qname_app_app in *; cbn [app] in *;
      solve [ econstructor; rewrite ?qname_app_app; cbn [app]; eassumption ].
  Qed.

  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma dkind_global_alias : forall p args y U r ch k,
      gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U r) ->
      dkind Θ Ξ (dm_global p args) (y :: ch) k <-> ukind Θ Ξ nil U (r ++ ch) k.
  Proof.
    intros * Ha.
    destruct (gc_module_alias_app _ _ Hg _ _ _ Ha ch) as [E1 E2].
    rewrite qname_app_app in E1, E2; cbn [app] in E1, E2.
    assert (E3 : gc_resolve Θ Ξ (qname_app p (y :: ch)) = None)
      by (destruct ch; [ eapply gc_module_alias_resolve; eassumption | apply E2; discriminate ]).
    split; intros Hk.
    - inversion Hk; subst; congruence.
    - eapply dk_global_alias; eassumption.
  Qed.

  (** *** Generated Entries *)

  Lemma eval_gens_prefix : forall gs Φ k ρ ρ2,
      ⟦ gens_append Φ k gs ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> exists ρm, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρm.
  Proof.
    induction gs as [| g gs IH]; intros * He; cbn [gens_append] in He; [ eauto |].
    destruct (ig_entry g) as [d E]; destruct (IH _ _ _ _ He) as [ρm Hm].
    inversion Hm; subst; eauto.
  Qed.

  Lemma kshape_gens : forall gs Φ k ρ ρm ρ2 σ,
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρm -> ⟦ gens_append Φ k gs ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> kshape ρm σ ->
      kshape ρ2 (kgens_env σ k gs).
  Proof.
    induction gs as [| g gs IH]; intros * Hm He Hs; cbn [gens_append kgens_env] in *.
    - rewrite <- (functional_eval_benv _ _ _ _ Hm He); exact Hs.
    - destruct g as [d pv A M | d pv E | d pv Δ p Ns]; cbn [ig_entry gentry_wk kentry] in He |- *;
        destruct (eval_gens_prefix _ _ _ _ _ He) as [ρm' Hm'];
        apply (IH _ _ _ _ _ _ Hm' He);
        inversion Hm'; subst;
        match goal with H1 : ⟦ Φ ⟧ᵇ _ ⍮ _ ⍮ ρ ↘ ?r |- _ => rewrite (functional_eval_benv _ _ _ _ H1 Hm) in * end.
      + apply kshape_cons_term; exact Hs.
      + apply kshape_cons_mod; [ exact Hs |].
        intros ch k0; rewrite !dkind_local_iff, gunit_wk_mk; cbn [tele_wk List.length moddef_wk wk_qn].
        apply ukind_id, Hs.
  Qed.

  Lemma items_upto_snoc : forall y its its1 it, items_upto y its = Some (its1, it) ->
      exists its0, its1 = its0 ++ it :: nil.
  Proof.
    induction its as [| it0 its IH]; intros * Hu; cbn in Hu; [ discriminate |].
    destruct (items_upto y its) as [[its1' it1] |] eqn:E.
    - injection Hu as <- <-; destruct (IH _ _ eq_refl) as [its0 ->]; exists (it0 :: its0); reflexivity.
    - destruct (String.eqb y (iitem_name it0)); [| discriminate ].
      injection Hu as <- <-; exists nil; reflexivity.
  Qed.

  Lemma gm_item_upto_snoc : forall Φ y Φ0 H its1 it, gm_item_upto Φ y = Some (Φ0, H, its1, it) ->
      exists its0, its1 = its0 ++ it :: nil.
  Proof.
    induction Φ as [| Φ IH x E | Φ IH H0 its]; intros * Hu; cbn in Hu; [ discriminate | |].
    - destruct (String.eqb y x); [ discriminate | eauto ].
    - destruct (items_upto y its) as [[its1' it1] |] eqn:E; [| eauto ].
      injection Hu as <- <- <- <-; eapply items_upto_snoc; exact E.
  Qed.

  Lemma gm_item_prefix_excl : forall Φ x r, gm_item_upto Φ x = Some r -> gm_prefix_upto Φ x = None.
  Proof.
    intros * Hi; destruct (gm_prefix_upto Φ x) eqn:E; [| reflexivity ].
    rewrite (gm_prefix_item_excl _ _ _ E) in Hi; discriminate.
  Qed.

  (** *** The Kinds of Values *)

  Theorem kind_eval :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> True) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> True) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> True) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> True) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ch k, dkind Θ Ξ h ch k <-> skind Θ Ξ ρ H ch k) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h ch k) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> True) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h (y :: ch) k) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> True) /\
    (forall h ch0 r, h ·ₘ* ch0 Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h (ch0 ++ ch) k) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> forall σ, kshape ρ σ -> exists σ', kenv Θ Ξ σ Φ σ' /\ kshape ρ' σ') /\
    (forall ρ nm A Bs m r, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall ρ nm A Bs gs vs r, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall ρ nm A Bs t v r, eval_ih Θ Ξ ρ nm A Bs t v r -> True) /\
    (forall p ups ρ t a, eval_shty Θ Ξ p ups ρ t a -> True) /\
    (forall ρm A ρ t v a, eval_ihty Θ Ξ ρm A ρ t v a -> True).
  Proof.
    apply eval_mut_ind; intros; try exact I.
    (* module expressions *)
    - rewrite skind_var_iff; reflexivity.
    - split; intros Hk; [ constructor; exact Hk | inversion Hk; subst; assumption ].
    - rewrite dkind_local_iff, skind_lit_iff; reflexivity.
    - rewrite skind_mem_iff; etransitivity; [ apply H1 | apply H0 ].
    - rewrite skind_app_iff; etransitivity; [ apply H2 | apply H0 ].
    (* application: the arguments of a module are no part of its kinds *)
    - split; apply dkind_global_args.
    - rewrite !dkind_local_iff; reflexivity.
    - rewrite !dkind_local_iff; reflexivity.
    - (* a saturated alias passes the argument to its target *)
      rewrite H0, H, dkind_local_iff, ukind_pad, ukind_alias_iff.
      apply skind_id, kshape_args_pad; assumption.
    - split; intros Hk.
      + constructor; apply H; apply H0; exact Hk.
      + inversion Hk; subst; apply H0, H; assumption.
    (* selection of a submodule *)
    - apply dkind_global_snoc.
    - rewrite H, dkind_local_iff; symmetry; apply dkind_global_alias; assumption.
    - split; intros Hk; [ inversion Hk; subst; assumption | constructor; exact Hk ].
    - (* a body's submodule: its closure over the environment of the body before it *)
      destruct (H _ (kshape_args_pad ρ args (List.length Δ) e)) as (σ & Hk & Hs).
      rewrite dkind_local_iff, (ukind_id _ _ (proj1 Hs)), dkind_local_iff.
      split; intros Hu.
      + eapply uk_mod; eassumption.
      + inversion Hu; subst;
          match goal with
          | H1 : gm_prefix_upto ?Φ ?y = Some _, H2 : gm_prefix_upto ?Φ ?y = Some _ |- _ =>
              rewrite H1 in H2; inversion H2; subst; clear H2
          | H1 : gm_prefix_upto ?Φ ?y = Some _, H2 : gm_item_upto ?Φ ?y = Some _ |- _ =>
              rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
          end.
        match goal with Hk1 : kenv _ _ _ _ ?r, Hu1 : ukind _ _ ?r _ _ _ |- ukind _ _ σ _ _ _ =>
          rewrite (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk _ Hk1); exact Hu1 end.
    - (* a module a local open declares: the target, or its member the item names *)
      destruct (H0 _ (kshape_args_pad ρ args (List.length Δ) e)) as (σ & Hk & Hs).
      rewrite H2, H1, (skind_id _ _ (proj1 Hs)), dkind_local_iff, (ukind_pad _ _ ρ Δ).
      replace (item_ch it nil ++ ch) with (item_ch it ch) by (destruct it as [[[] ?] ?]; reflexivity).
      split; intros Hu.
      + eapply uk_item; eassumption.
      + inversion Hu; subst; try prefix_item_excl;
          try match goal with Hp : gm_prefix_upto _ _ = Some _ |- _ =>
                rewrite (gm_item_prefix_excl _ _ _ e0) in Hp; discriminate Hp end.
        match goal with Hi : gm_item_upto _ _ = Some _ |- _ => rewrite e0 in Hi; inversion Hi; subst end.
        match goal with Hk1 : kenv _ _ _ _ ?r, Hs1 : skind _ _ ?r _ _ _ |- _ =>
          rewrite (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk _ Hk1); exact Hs1 end.
    - (* a saturated alias: selected from its target *)
      rewrite H0, H, dkind_local_iff, ukind_pad, ukind_alias_iff.
      apply skind_id, kshape_args_pad; assumption.
    - split; intros Hk; inversion Hk; subst; constructor; rewrite <- app_assoc in *; assumption.
    (* chains *)
    - reflexivity.
    - rewrite H0, H; reflexivity.
    (* bodies *)
    - exists σ; split; [ constructor | assumption ].
    - destruct (H _ H1) as (σ1 & Hk & Hs).
      exists (kbentry σ1 (ge_def b pv A (Some M)) :: σ1); split; [ constructor; exact Hk |].
      apply kshape_cons_term; exact Hs.
    - destruct (H _ H0) as (σ1 & Hk & Hs).
      exists (kbentry σ1 (ge_mod pm Uy) :: σ1); split; [ constructor; exact Hk |].
      apply kshape_cons_mod; [ exact Hs |].
      intros ch k; rewrite !dkind_local_iff; apply ukind_id, Hs.
    - destruct (H0 _ H2) as (σ1 & Hk & Hs).
      exists (kgens_env σ1 0 gs); split; [ econstructor; [ exact Hk | eapply kgens_id; [ apply Hs | eassumption ] ] |].
      eapply kshape_gens; [ constructor | exact e0 | exact Hs ].
  Qed.

  Corollary kind_eval_modexp : forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
      forall ch k, dkind Θ Ξ h ch k <-> skind Θ Ξ ρ H ch k.
  Proof. pose proof kind_eval as K; destruct_all; eauto. Qed.

  Corollary kind_eval_benv : forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
      forall σ, kshape ρ σ -> exists σ', kenv Θ Ξ σ Φ σ' /\ kshape ρ' σ'.
  Proof. pose proof kind_eval as K; destruct_all; eauto. Qed.

End KindsEval.
