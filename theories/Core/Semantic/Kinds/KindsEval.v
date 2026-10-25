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
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Syntactic.System.Global Require Import Modules.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping.
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

  (** The sort of an environment entry: a term ([0]), a module ([1]), or
      a term with a module part ([2]). *)
  Definition dentry_tag (e : dentry) : nat :=
    match e with
    | de_term _ => 0
    | de_mod _ => 1
    | de_dm _ _ => 2
    end.

  (** Two environments with the same kinds, and entries of the same sorts
      at the same places. *)
  Definition kshape (ρ ρ' : env) : Prop :=
    kren Θ Ξ wk_id ρ ρ' /\ forall x, dentry_tag (env_entry ρ x) = dentry_tag (env_entry ρ' x).

  Lemma kshape_cons_term : forall ρ ρ' a a', kshape ρ ρ' -> kshape (de_term a :: ρ) (de_term a' :: ρ').
  Proof. intros * [K S]; split; intros [| x]; first [ apply kequiv_refl | apply K | reflexivity | apply S ]. Qed.

  Lemma kshape_cons_mod : forall ρ ρ' h h', kshape ρ ρ' -> kequiv Θ Ξ h h' -> kshape (de_mod h :: ρ) (de_mod h' :: ρ').
  Proof. intros * [K S] Hh; split; intros [| x]; first [ exact Hh | apply K | reflexivity | apply S ]. Qed.

  (** A term with a module part, by the kinds of its module part. *)
  Lemma kshape_cons_dm : forall ρ ρ' a a' h h', kshape ρ ρ' -> kequiv Θ Ξ h h' ->
      kshape (de_dm a h :: ρ) (de_dm a' h' :: ρ').
  Proof. intros * [K S] Hh; split; intros [| x]; first [ exact Hh | apply K | reflexivity | apply S ]. Qed.

  Lemma env_args_rev_args : forall args ρ, env_args ρ args = List.rev (List.map de_term args) ++ ρ.
  Proof.
    induction args as [| a args IH]; intros; [ reflexivity |].
    unfold env_args in *; cbn [List.fold_left List.map List.rev]; rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma kshape_terms : forall X Y ρ ρ', List.length X = List.length Y ->
      Forall (fun e => dentry_tag e = 0) X -> Forall (fun e => dentry_tag e = 0) Y ->
      kshape ρ ρ' -> kshape (X ++ ρ) (Y ++ ρ').
  Proof.
    induction X as [| e X IH]; intros [| e' Y] * Hl HX HY Hs; cbn in Hl; try discriminate; [ exact Hs |].
    inversion HX; inversion HY; subst.
    destruct e as [a | h | a h], e' as [a' | h' | a' h']; cbn in *; try discriminate.
    apply kshape_cons_term, IH; auto.
  Qed.

  Lemma kshape_refl : forall ρ, kshape ρ ρ.
  Proof. intros ρ; split; [ intros x; apply kequiv_refl | reflexivity ]. Qed.

  (** An argument pushed under placeholders is one more placeholder. *)
  Lemma kshape_pad_push : forall m ρ n, kshape (kpad m (de_term n :: ρ)) (kpad (S m) ρ).
  Proof.
    intros; unfold kpad.
    replace (List.repeat (de_term d_true) m ++ de_term n :: ρ) with ((List.repeat (de_term d_true) m ++ de_term n :: nil) ++ ρ)
      by (rewrite <- app_assoc; reflexivity).
    replace (List.repeat (de_term d_true) (S m) ++ ρ) with ((List.repeat (de_term d_true) m ++ de_term d_true :: nil) ++ ρ)
      by (cbn [List.repeat]; rewrite List.repeat_cons, <- app_assoc; reflexivity).
    apply kshape_terms.
    - rewrite !length_app, !repeat_length; reflexivity.
    - apply Forall_app; split; [ apply Forall_forall; intros e He; apply repeat_spec in He as ->; reflexivity | repeat constructor ].
    - apply Forall_app; split; [ apply Forall_forall; intros e He; apply repeat_spec in He as ->; reflexivity | repeat constructor ].
    - apply kshape_refl.
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

  Lemma dkind_global_args : forall ch p args args' k,
      dkind Θ Ξ (dm_global p args) ch k -> dkind Θ Ξ (dm_global p args') ch k.
  Proof.
    induction ch as [| y ch IH]; intros * Hk; inversion Hk; subst;
      first [ eapply dkind_global_here_def; eassumption | eapply dkind_global_here_mod; eassumption
            | eapply dkind_global_here_dm; eassumption | eapply dkind_global_alias_dm; eassumption
            | eapply dkind_global_alias_case; eassumption | eapply dkind_global_step; [ eassumption | eassumption | eapply IH; eassumption ] ].
  Qed.

  (** A stored body is a module. *)
  Lemma dkind_global_loc : forall p args TΦ, gc_loc Θ Ξ p = Some TΦ -> dkind Θ Ξ (dm_global p args) nil mk_mod.
  Proof.
    intros * Hl; apply dkind_global_here_mod; unfold gc_loc in Hl; destruct (gc_frame Ξ p) eqn:Hf; [ right; eauto |].
    destruct TΦ; left; destruct (gc_body_module _ _ _ _ _ Hl); eauto.
  Qed.

  (** A stored submodule has the kinds of its parent's submodule closure:
      past the empty chain those of the longer chain, and at it a module. *)
  Lemma dkind_global_snoc : forall p args y ch k TΦ,
      gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ ->
      dkind Θ Ξ (dm_global (qname_app p (y :: nil)) args) ch k <-> dkind Θ Ξ (dm_member (dm_global p args) (y :: nil)) ch k.
  Proof.
    intros * Hl; destruct ch as [| c ch].
    - rewrite dkind_member_iff; cbn [app].
      pose proof (dkind_global_loc _ args _ Hl) as Hm.
      split.
      + intros Hk; pose proof (proj1 (@functional_kind Θ Ξ) _ _ _ Hk _ Hm) as ->.
        destruct (dm_path_cases Θ Ξ (qname_app p (y :: nil))) as [Hd | Hd].
        * right; repeat split; eapply dkind_global_here_dm; [ exact Hd | exact Hl ].
        * left; split; [ apply dkind_global_step; [ left; eexists; exact Hl | right; exact Hd | exact Hm ] | right; discriminate ].
      + intros [[Hk Hc] | (_ & -> & _)]; [| exact Hm ].
        inversion Hk; subst;
          first [ destruct Hc as [Hc | Hc]; exfalso; exact (Hc eq_refl)
                | exfalso; eapply gc_loc_not_alias; eassumption | assumption ].
    - rewrite dkind_member_cons_iff; cbn [app]; split; intros Hk.
      + apply dkind_global_step; [ left; eexists; exact Hl | left; discriminate | assumption ].
      + inversion Hk; subst; first [ exfalso; eapply gc_loc_not_alias; eassumption | assumption ].
  Qed.

  Lemma dm_of_cases : forall k, (k = mk_mod /\ dm_of k = mk_dm) \/ (k <> mk_mod /\ dm_of k = k).
  Proof. intros []; cbn; [ right | left | right ]; split; first [ reflexivity | discriminate ]. Qed.

  (** An alias submodule has the kinds of its parent's submodule closure:
      past the empty chain those of its unit, and at it a module. *)
  Lemma dkind_global_alias : forall p args y U ch k,
      gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U) ->
      ukind Θ Ξ nil U ch k <-> dkind Θ Ξ (dm_member (dm_global p args) (y :: nil)) ch k.
  Proof.
    intros * Ha.
    assert (Hst : (exists TΦ, gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ) \/
                  (exists b pv A B, gc_resolve Θ Ξ (qname_app p (y :: nil)) = Some (ge_def b pv A B)) -> False)
      by (intros [(? & Hl) | (? & ? & ? & ? & Hr)];
          [ exact (gc_loc_not_alias _ _ _ _ _ Hl Ha) | rewrite (gc_module_resolve _ _ _ _ Ha) in Hr; discriminate Hr ]).
    pose proof (proj1 (proj2 (@functional_kind Θ Ξ))) as Fu.
    pose proof (proj1 (proj2 (kind_nil_not_dm Θ Ξ))) as Nd.
    destruct ch as [| c ch].
    - rewrite dkind_member_iff; cbn [app]; split.
      + intros Hk; pose proof (Nd _ _ _ _ Hk eq_refl) as Hk'.
        destruct (dm_path_cases Θ Ξ (qname_app p (y :: nil))) as [Hd | Hd].
        * destruct (dm_of_cases k) as [(-> & _) | (Hm & Ek)].
          -- right; repeat split; change mk_dm with (dm_of mk_mod); eapply dkind_global_alias_dm; eassumption.
          -- left; split; [ rewrite <- Ek; eapply dkind_global_alias_dm; eassumption | right; exact Hk' ].
        * left; split; [ eapply dkind_global_alias_case; [ exact Ha | right; exact Hd | exact Hk ] | right; exact Hk' ].
      + intros [[Hk Hc] | (_ & -> & Hk)].
        * inversion Hk; subst;
            try (match goal with Ha' : gc_module _ _ _ = Some (mr_alias _) |- _ => rewrite Ha in Ha'; injection Ha' as <- end).
          -- exfalso; eapply gc_loc_not_alias; eassumption.
          -- assumption.
          -- match goal with Hk0 : ukind _ _ nil U nil ?k0 |- _ =>
               destruct (dm_of_cases k0) as [(-> & ->) | (_ & ->)]; [ destruct Hc as [Hc | Hc]; exfalso; exact (Hc eq_refl) | exact Hk0 ] end.
          -- exfalso; eapply Hst; eassumption.
        * inversion Hk; subst;
            try (match goal with Ha' : gc_module _ _ _ = Some (mr_alias _) |- _ => rewrite Ha in Ha'; injection Ha' as <- end).
          -- exfalso; eapply gc_loc_not_alias; eassumption.
          -- exfalso; eapply Nd; [ eassumption | reflexivity | reflexivity ].
          -- match goal with Hk0 : ukind _ _ nil U nil ?k0, Ek : dm_of ?k0 = mk_dm |- _ =>
               destruct (dm_of_cases k0) as [(-> & _) | (Hm & Ek')]; [ exact Hk0 |];
               rewrite Ek' in Ek; subst; exfalso; exact (Nd _ _ _ _ Hk0 eq_refl eq_refl) end.
          -- exfalso; eapply Hst; eassumption.
    - rewrite dkind_member_cons_iff; cbn [app]; split; intros Hk.
      + eapply dkind_global_alias_case; [ exact Ha | left; discriminate | exact Hk ].
      + inversion Hk; subst.
        * match goal with Ha' : gc_module _ _ _ = Some (mr_alias _) |- _ => rewrite Ha in Ha'; injection Ha' as <- end; assumption.
        * exfalso; eapply Hst; eassumption.
  Qed.

  (** *** Bodies Read Through Their Opens

      The environment a body makes is the one its expansion ([kbody])
      makes, and a submodule found in the expansion has the kinds the body
      gives the name: a written submodule its own, a module a local open
      declares those of what the item names in the open's target. *)

  Lemma kenv_gens : forall gs Φ k ρ ρ1, kenv Θ Ξ ρ Φ ρ1 -> kenv Θ Ξ ρ (gens_append Φ k gs) (kgens_env ρ1 k gs).
  Proof.
    induction gs as [| g gs IH]; intros * Hk; cbn [gens_append kgens_env]; [ exact Hk |].
    destruct (ig_entry g) as [d E] eqn:Eg.
    replace (kentry ρ1 k g) with (kbentry ρ1 (gentry_wk E (wk_shiftn k))) by (destruct g; cbn in Eg; injection Eg as <- <-; reflexivity).
    apply IH; constructor; exact Hk.
  Qed.

  Lemma kenv_kbody : forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> forall ρ1, kenv Θ Ξ ρ Φ ρ1 -> kenv Θ Ξ ρ Φx ρ1.
  Proof.
    induction 1 as [| ρ Φ Φx x E Hb IH | ρ Φ Φx ρ1 H its gs Hb IH Hk Hgs]; intros ρ2 Hk2.
    - exact Hk2.
    - inversion Hk2; subst; constructor; apply IH; assumption.
    - inversion Hk2; subst.
      match goal with Hk0 : kenv _ _ _ Φ ?r, Hg0 : kgens _ _ ?r _ _ ?g |- _ =>
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk _ (IH _ Hk0)) as <-;
        pose proof (functional_kgens _ _ _ _ _ Hgs Hg0) as <- end.
      apply kenv_gens; exact Hk.
  Qed.

  Lemma kenv_of_kbody : forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> exists ρ1, kenv Θ Ξ ρ Φ ρ1.
  Proof.
    induction 1 as [| ρ Φ Φx x E Hb IH | ρ Φ Φx ρ1 H its gs Hb IH Hk Hgs].
    - eexists; constructor.
    - destruct IH as (ρ1 & Hk); eexists; constructor; exact Hk.
    - destruct IH as (ρ2 & Hk2).
      pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk _ (kenv_kbody _ _ _ Hb _ Hk2)) as ->.
      eexists; econstructor; eassumption.
  Qed.

  Lemma ukind_gens_other : forall gs Φ k ρ sm y ch kk, existsb (String.eqb y) (map ig_name gs) = false ->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm (gens_append Φ k gs))) (y :: ch) kk <->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) kk.
  Proof.
    induction gs as [| g gs IH]; intros * Hn; cbn [gens_append]; [ reflexivity |].
    cbn [map existsb] in Hn; apply Bool.orb_false_iff in Hn as [Hy Hn].
    unfold ig_name in Hy; destruct (ig_entry g) as [d E] eqn:Eg; cbn [fst] in Hy.
    rewrite IH by exact Hn; apply ukind_body_ext_other.
    intros ->; rewrite String.eqb_refl in Hy; discriminate.
  Qed.

  Lemma kenv_eq_kbody : forall ρ Φ Φx ρ1 ρ1', kbody Θ Ξ ρ Φ Φx -> kenv Θ Ξ ρ Φ ρ1 -> kenv Θ Ξ ρ Φx ρ1' -> ρ1 = ρ1'.
  Proof.
    intros * Hb Hk Hk'; exact (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ (kenv_kbody _ _ _ Hb _ Hk) _ Hk').
  Qed.

  Lemma gm_prefix_name : forall Φ y Φ0 z E, gm_prefix_upto Φ y = Some (gm_ext Φ0 z E) -> z = y.
  Proof.
    induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hp; cbn in Hp; [ discriminate | |].
    - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as _ <- _; reflexivity | eauto ].
    - destruct (existsb _ _); [ discriminate | eauto ].
  Qed.

  (** The kinds a body gives a name its own entry declares. *)
  Lemma ukind_body_entry : forall ρ sm Φ y Φ' E ch k,
      gm_prefix_upto Φ y = Some (gm_ext Φ' y E) ->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k <->
      ((exists b pv A B, E = ge_def b pv A B) /\ ch = nil /\ k = mk_term) \/
      (exists pm U ρ1, E = ge_mod pm U /\ kenv Θ Ξ ρ Φ' ρ1 /\ ukind Θ Ξ ρ1 U ch k) \/
      (exists pv A M U ρ1 k0, E = ge_def_mod pv A M U /\ ch = nil /\ kenv Θ Ξ ρ Φ' ρ1 /\ ukind Θ Ξ ρ1 U nil k0 /\ k = dm_of k0) \/
      (exists pv A M U ρ1, E = ge_def_mod pv A M U /\ ch <> nil /\ kenv Θ Ξ ρ Φ' ρ1 /\ ukind Θ Ξ ρ1 U ch k).
  Proof.
    intros * Hp; split; intros Hu.
    - inversion Hu; subst;
        try (rewrite (gm_prefix_item_excl _ _ _ Hp) in *; discriminate);
        match goal with H2 : gm_prefix_upto _ _ = Some _ |- _ => rewrite Hp in H2; injection H2; intros; subst end.
      + left; repeat split; eauto.
      + right; left; do 3 eexists; repeat split; eassumption.
      + right; right; left; do 6 eexists; repeat split; eassumption.
      + right; right; right; do 5 eexists; repeat split; eassumption.
    - destruct Hu as [((b & pv & A & B & ->) & -> & ->) | [(pm & U & ρ1 & -> & Hk & Hu)
                     | [(pv & A & M & U & ρ1 & k0 & -> & -> & Hk & Hu & ->) | (pv & A & M & U & ρ1 & -> & Hc & Hk & Hu)]]].
      + eapply ukind_def; exact Hp.
      + eapply ukind_mod; [ exact Hp | exact Hk | exact Hu ].
      + eapply ukind_dm_here; [ exact Hp | exact Hk | exact Hu ].
      + eapply ukind_dm_step; [ exact Hp | exact Hc | exact Hk | exact Hu ].
  Qed.

  (** The kinds a body gives a name an open declares. *)
  Lemma ukind_body_item : forall ρ sm Φ y Φ0 H its1 it ρ0 ch k,
      gm_item_upto Φ y = Some (Φ0, H, its1, it) -> kenv Θ Ξ ρ Φ0 ρ0 ->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k <->
      match it with
      | (Some n, _, _) => (ch = nil /\ k = mk_term /\ skind Θ Ξ ρ0 H (n :: nil) mk_term) \/
                         (skind Θ Ξ ρ0 H (n :: nil) mk_mod /\ skind Θ Ξ ρ0 H (n :: ch) k) \/
                         (skind Θ Ξ ρ0 H (n :: nil) mk_dm /\ skind Θ Ξ ρ0 H (n :: ch) k)
      | (None, _, _) => skind Θ Ξ ρ0 H ch k
      end.
  Proof.
    intros * Hi Hk; split; intros Hu.
    - inversion Hu; subst;
        try match goal with H2 : gm_prefix_upto _ _ = Some _ |- _ => rewrite (gm_prefix_item_excl _ _ _ H2) in Hi; discriminate end;
        match goal with H2 : gm_item_upto _ _ = Some _ |- _ => rewrite Hi in H2; injection H2; intros; subst end;
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end;
        cbn [List.length kpad List.repeat app] in *; auto.
    - destruct it as [[[n |] d] pv].
      + destruct Hu as [(-> & -> & Hs) | [(Hs & Hs') | (Hs & Hs')]];
          [ eapply ukind_item_def | eapply ukind_item_mod | eapply ukind_item_dm ]; eassumption.
      + eapply ukind_item_self; eassumption.
  Qed.

  (** A body has the kinds of the body read through its opens. *)
  Lemma ukind_kbody : forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> forall sm ch k,
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) ch k <-> ukind Θ Ξ ρ (gu_mk nil (md_body sm Φx)) ch k.
  Proof.
    intros * Hb sm [| y ch] k; [ split; intros Hu; inversion Hu; subst; constructor |].
    revert y ch k; induction Hb as [| ρ Φ Φx x E Hb IH | ρ Φ Φx ρ0 H its gs Hb IH Hk Hgs]; intros y ch k.
    - reflexivity.
    - destruct (String.eqb_spec y x) as [-> | Hne];
        [| rewrite !ukind_body_ext_other by exact Hne; apply IH ].
      destruct (kenv_of_kbody _ _ _ Hb) as (ρ2 & Hk2).
      pose proof (kenv_kbody _ _ _ Hb _ Hk2) as Hk2x.
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?String.eqb_refl in *;
        try discriminate; match goal with Hp : Some _ = Some _ |- _ => injection Hp; intros; subst end.
      + eapply ukind_def; cbn; rewrite String.eqb_refl; reflexivity.
      + eapply ukind_mod; [ cbn; rewrite String.eqb_refl; reflexivity | exact Hk2x |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
      + eapply ukind_dm_here; [ cbn; rewrite String.eqb_refl; reflexivity | exact Hk2x |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
      + eapply ukind_dm_step; [ cbn; rewrite String.eqb_refl; reflexivity | assumption | exact Hk2x |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
      + eapply ukind_def; cbn; rewrite String.eqb_refl; reflexivity.
      + eapply ukind_mod; [ cbn; rewrite String.eqb_refl; reflexivity | exact Hk2 |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
      + eapply ukind_dm_here; [ cbn; rewrite String.eqb_refl; reflexivity | exact Hk2 |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
      + eapply ukind_dm_step; [ cbn; rewrite String.eqb_refl; reflexivity | assumption | exact Hk2 |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
    - (* an open *)
      destruct (items_upto y its) as [[its1 it] |] eqn:Ey.
      + destruct (kgens_prefix_some _ _ _ _ _ _ Hgs _ _ _ Ey) as (gs0 & g & Hg1 & Hpg).
        specialize (Hpg Φx 0); rewrite gens_append_snoc in Hpg.
        pose proof (gm_prefix_name _ _ _ _ _ Hpg) as Hy.
        destruct (kenv_of_kbody _ _ _ Hb) as (ρ2 & Hk2).
        pose proof (kenv_eq_kbody _ _ _ _ _ Hb Hk2 Hk) as <-.
        destruct (kgens_env_split gs0 ρ2 0) as (X & HX & Hl).
        pose proof (kenv_gens gs0 _ 0 _ _ Hk) as Hkx; rewrite HX in Hkx.
        assert (Hi : gm_item_upto (gm_open Φ H its) y = Some (Φ, H, its1, it)) by (cbn; rewrite Ey; reflexivity).
        rewrite Hy in Hpg.
        rewrite (ukind_body_item _ _ _ _ _ _ _ _ _ _ _ Hi Hk2), (ukind_body_entry _ _ _ _ _ _ _ _ Hpg).
        assert (Hsh : forall E0 ch0 k0,
                   ukind Θ Ξ (X ++ ρ2) (gu_mk nil (md_alias (modexp_wk E0 (wk_shiftn (0 + List.length gs0))))) ch0 k0 <->
                   skind Θ Ξ ρ2 E0 ch0 k0).
        { intros; rewrite ukind_alias_iff; cbn [Nat.add]; rewrite <- Hl.
          exact (proj1 (kind_ren Θ Ξ) _ (wk_shiftn (List.length X)) (X ++ ρ2) ρ2 (kren_shift_app Θ Ξ X ρ2) _ _). }
        pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ)))) as Fs.
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ))))) as Fk.
        inversion Hg1 as [| ? ? d pv ? ? Hn | ? ? n d pv ? ? Hs Hn | ? ? n d pv ? ? Hs Hn | ? ? n d pv ? ? Hs Hn]; subst;
          inversion Hn; subst; cbn [ig_entry snd gentry_wk] in Hpg |- *.
        * (* the open's target itself *)
          rewrite gunit_wk_mk; cbn [tele_wk List.length moddef_wk].
          split; [ intros Hu; right; left; do 3 eexists; split; [ reflexivity | split; [ exact Hkx | apply Hsh, Hu ] ] |].
          intros [((? & ? & ? & ? & ?) & _) | [(pm & U & ρ1 & [= <- <-] & Hk1 & Hu)
                 | [(? & ? & ? & ? & ? & ? & [=] & _) | (? & ? & ? & ? & ? & [=] & _)]]]; try discriminate.
          pose proof (Fk _ _ _ Hk1 _ Hkx) as ->; apply Hsh, Hu.
        * (* a term member: a definition *)
          split.
          -- intros [(-> & -> & _) | [(Hm & _) | (Hm & _)]]; [ left; split; [ do 4 eexists; reflexivity | split; reflexivity ] | |];
               pose proof (Fs _ _ _ _ Hs _ Hm); discriminate.
          -- intros [(_ & -> & ->) | [(? & ? & ? & [=] & _) | [(? & ? & ? & ? & ? & ? & [=] & _) | (? & ? & ? & ? & ? & [=] & _)]]];
               left; repeat split; exact Hs.
        * (* a module member: an alias of it *)
          rewrite gunit_wk_mk; cbn [tele_wk List.length moddef_wk].
          split.
          -- intros [(-> & -> & Ht) | [(_ & Hu) | (Hm & _)]];
               [ pose proof (Fs _ _ _ _ Hs _ Ht); discriminate | | pose proof (Fs _ _ _ _ Hs _ Hm); discriminate ].
             right; left; do 3 eexists; split; [ reflexivity | split; [ exact Hkx | apply (Hsh (me_mem H n)) ] ].
             apply skind_mem_iff; left; split; [ exact Hu |].
             destruct ch as [| c ch]; [ right; rewrite <- (Fs _ _ _ _ Hs _ Hu); discriminate | left; discriminate ].
          -- intros [((? & ? & ? & ? & ?) & _) | [(pm & U & ρ1 & [= <- <-] & Hk1 & Hu)
                    | [(? & ? & ? & ? & ? & ? & [=] & _) | (? & ? & ? & ? & ? & [=] & _)]]]; try discriminate.
             pose proof (Fk _ _ _ Hk1 _ Hkx) as ->.
             right; left; split; [ exact Hs |].
             destruct (proj1 (skind_mem_iff Θ Ξ _ _ _ _ _) (proj1 (Hsh (me_mem H n) ch k) Hu)) as [(Hu' & _) | (_ & _ & Hd)]; [ exact Hu' |].
             pose proof (Fs _ _ _ _ Hs _ Hd); discriminate.
        * (* a member with a term part and a module part: a definition with
             a module part, the alias of it *)
          rewrite gunit_wk_mk; cbn [tele_wk List.length moddef_wk].
          split.
          -- intros [(-> & -> & Ht) | [(Hm & _) | (_ & Hu)]];
               [ pose proof (Fs _ _ _ _ Hs _ Ht); discriminate | pose proof (Fs _ _ _ _ Hs _ Hm); discriminate |].
             destruct ch as [| c ch].
             ++ pose proof (Fs _ _ _ _ Hs _ Hu) as <-.
                right; right; left; do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; [ exact Hkx | split ] ] ];
                  [ apply (Hsh (me_mem H n)), skind_mem_dm, Hs | reflexivity ].
             ++ right; right; right; do 5 eexists; split; [ reflexivity | split; [ discriminate | split; [ exact Hkx |] ] ].
                apply (Hsh (me_mem H n)), skind_mem_cons_iff, Hu.
          -- intros [((? & ? & ? & ? & ?) & _) | [(? & ? & ? & [=] & _)
                    | [(pv' & A' & M' & U & ρ1 & k0 & [= <- <- <- <-] & -> & Hk1 & Hu & ->)
                      | (pv' & A' & M' & U & ρ1 & [= <- <- <- <-] & Hc & Hk1 & Hu)]]];
               try discriminate.
             ++ pose proof (Fk _ _ _ Hk1 _ Hkx) as ->.
                destruct (proj1 (skind_mem_iff Θ Ξ _ _ _ _ _) (proj1 (Hsh (me_mem H n) nil k0) Hu)) as [(Hu' & Hc) | (_ & -> & _)].
                ** pose proof (Fs _ _ _ _ Hs _ Hu') as <-.
                   destruct Hc as [Hc | Hc]; exfalso; exact (Hc eq_refl).
                ** right; right; split; exact Hs.
             ++ pose proof (Fk _ _ _ Hk1 _ Hkx) as ->.
                right; right; split; [ exact Hs |].
                destruct ch as [| c ch]; [ exfalso; exact (Hc eq_refl) |].
                apply skind_mem_cons_iff, (Hsh (me_mem H n)), Hu.
      + pose proof (items_upto_none_iff _ _ Ey) as Hn; rewrite <- (kgens_names _ _ _ _ _ _ Hgs) in Hn.
        rewrite ukind_body_open_other by exact Ey; rewrite ukind_gens_other by exact Hn; apply IH.
  Qed.

  (** The module part of a body's entry (of a submodule, or of a definition
      with a module part) has the kinds of the body's submodule closure at
      its name. *)
  Lemma ukind_kbody_mod : forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx ->
      forall y Φ' E U ρ1, gm_prefix_upto Φx y = Some (gm_ext Φ' y E) -> entry_unit E = Some U -> kenv Θ Ξ ρ Φ' ρ1 ->
      forall sm ch k, ukind Θ Ξ ρ1 U ch k <-> dkind Θ Ξ (dm_member (dm_local nil (md_body sm Φ) ρ) (y :: nil)) ch k.
  Proof.
    intros * Hb * Hp HE Hk1 sm ch k.
    pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ))))) as Fk.
    pose proof (proj1 (proj2 (kind_nil_not_dm Θ Ξ))) as Nd.
    destruct E as [| pm U0 | | pv A M U0 |]; cbn in HE; try discriminate; injection HE as ->.
    all: destruct ch as [| c ch].
    all: rewrite ?dkind_member_cons_iff, ?dkind_member_iff; cbn [app];
           rewrite ?dkind_local_iff, ?(ukind_kbody _ _ _ Hb), ?(ukind_body_entry _ _ _ _ _ _ _ _ Hp).
    - (* a submodule, itself: its unit, no member of anything *)
      split.
      + intros Hu; pose proof (Nd _ _ _ _ Hu eq_refl) as Hn.
        left; split; [ right; left; do 3 eexists; split; [ reflexivity | split; [ exact Hk1 | exact Hu ] ] | right; exact Hn ].
      + intros [[H0 _] | (_ & -> & H0)].
        * destruct H0 as [((? & ? & ? & ? & [=]) & _) | [(pm' & U' & ρ0 & [= <- <-] & Hk0 & Hu)
                         | [(? & ? & ? & ? & ? & ? & [=] & _) | (? & ? & ? & ? & ? & [=] & _)]]].
          pose proof (Fk _ _ _ Hk0 _ Hk1) as ->; exact Hu.
        * apply (ukind_kbody _ _ _ Hb), (ukind_body_entry _ _ _ _ _ _ _ _ Hp) in H0.
          destruct H0 as [((? & ? & ? & ? & [=]) & _) | [(pm' & U' & ρ0 & [= <- <-] & Hk0 & Hu)
                         | [(? & ? & ? & ? & ? & ? & [=] & _) | (? & ? & ? & ? & ? & [=] & _)]]].
          pose proof (Fk _ _ _ Hk0 _ Hk1) as ->; exfalso; exact (Nd _ _ _ _ Hu eq_refl eq_refl).
    - (* a submodule, past its name *)
      split.
      + intros Hu; right; left; do 3 eexists; split; [ reflexivity | split; [ exact Hk1 | exact Hu ] ].
      + intros [((? & ? & ? & ? & [=]) & _) | [(pm' & U' & ρ0 & [= <- <-] & Hk0 & Hu)
               | [(? & ? & ? & ? & ? & ? & [=] & _) | (? & ? & ? & ? & ? & [=] & _)]]].
        pose proof (Fk _ _ _ Hk0 _ Hk1) as ->; exact Hu.
    - (* a definition with a module part, itself: selected as a module *)
      split.
      + intros Hu; pose proof (Nd _ _ _ _ Hu eq_refl) as Hn.
        destruct (dm_of_cases k) as [(-> & _) | (Hm & Ek)].
        * right; split; [ reflexivity | split; [ reflexivity |] ].
          apply (ukind_kbody _ _ _ Hb), (ukind_body_entry _ _ _ _ _ _ _ _ Hp).
          right; right; left; do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; [ exact Hk1 | split; [ exact Hu | reflexivity ] ] ] ].
        * left; split; [| right; exact Hn ].
          right; right; left; do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; [ exact Hk1 | split; [ exact Hu | symmetry; exact Ek ] ] ] ].
      + intros [[H0 Hc] | (_ & -> & H0)].
        * destruct H0 as [((? & ? & ? & ? & [=]) & _) | [(? & ? & ? & [=] & _)
                         | [(pv' & A' & M' & U' & ρ0 & k0 & [= <- <- <- <-] & _ & Hk0 & Hu & ->) | (? & ? & ? & ? & ? & _ & Hn & _)]]].
          -- pose proof (Fk _ _ _ Hk0 _ Hk1) as ->.
             destruct (dm_of_cases k0) as [(-> & ->) | (_ & ->)]; [ destruct Hc as [Hc | Hc]; exfalso; exact (Hc eq_refl) | exact Hu ].
          -- exfalso; exact (Hn eq_refl).
        * apply (ukind_kbody _ _ _ Hb), (ukind_body_entry _ _ _ _ _ _ _ _ Hp) in H0.
          destruct H0 as [((? & ? & ? & ? & [=]) & _) | [(? & ? & ? & [=] & _)
                         | [(pv' & A' & M' & U' & ρ0 & k0 & [= <- <- <- <-] & _ & Hk0 & Hu & Ek) | (? & ? & ? & ? & ? & _ & Hn & _)]]].
          -- pose proof (Fk _ _ _ Hk0 _ Hk1) as ->.
             destruct (dm_of_cases k0) as [(-> & _) | (_ & Ek')]; [ exact Hu |].
             rewrite Ek' in Ek; subst; exfalso; exact (Nd _ _ _ _ Hu eq_refl eq_refl).
          -- exfalso; exact (Hn eq_refl).
    - (* a definition with a module part, past its name *)
      split.
      + intros Hu; right; right; right; do 5 eexists; split; [ reflexivity | split; [ discriminate | split; [ exact Hk1 | exact Hu ] ] ].
      + intros [((? & ? & ? & ? & [=]) & _) | [(? & ? & ? & [=] & _) | [(? & ? & ? & ? & ? & ? & _ & [=] & _)
               | (pv' & A' & M' & U' & ρ0 & [= <- <- <- <-] & _ & Hk0 & Hu)]]].
        pose proof (Fk _ _ _ Hk0 _ Hk1) as ->; exact Hu.
  Qed.

  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

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
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ch k, dkind Θ Ξ h ch k <-> ukind Θ Ξ ρ (gu_mk Δ D) ch k) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h ch k) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h ch k) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> True) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ (dm_member h (y :: nil)) ch k) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> True) /\
    (forall h ch0 r, h ·ₘ* ch0 Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ (dm_member h ch0) ch k) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> forall σ, kshape ρ σ -> exists σ', kenv Θ Ξ σ Φ σ' /\ kshape ρ' σ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall ρ p ups Bks gs vs r, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall ρ p ups Bks t v r, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> True) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> True) /\
    (forall ρm As ρ t v a, ⟦ihty v of t under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> True) /\
    (forall f m r, eval_proj Θ Ξ f m r -> True) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs -> True).
  Proof.
    apply eval_mut_ind; intros; try exact I.
    (* module expressions *)
    - rewrite skind_var_iff; reflexivity.
    - split; intros Hk; [ constructor; exact Hk | inversion Hk; subst; assumption ].
    - rewrite H, skind_lit_iff; reflexivity.
    - rewrite H1, dkind_member_iff, skind_mem_iff; cbn [app]; rewrite (H0 (y :: ch)), (H0 (y :: nil)); reflexivity.
    - rewrite skind_app_iff; etransitivity; [ apply H2 | apply H0 ].
    (* closures *)
    - apply dkind_local_iff.
    - apply dkind_local_iff.
    - rewrite H, ukind_alias_iff; reflexivity.
    (* application: the arguments of a module are no part of its kinds *)
    - split; apply dkind_global_args.
    - rewrite H, dkind_local_iff, (ukind_pad _ _ (ρ ↦ n)), (ukind_pad _ _ ρ (Δ ++ ce_ass A :: nil)), length_app, Nat.add_1_r.
      apply ukind_id, kshape_pad_push.
    - (* a submodule closure: its parent applied, then the chain *)
      rewrite H0, (dkind_member_iff Θ Ξ h'), (dkind_member_iff Θ Ξ h), (H (ch ++ ch0)), (H ch); reflexivity.
    - reflexivity.
    - rewrite H0, H; reflexivity.
    (* selection of a submodule *)
    - eapply dkind_global_snoc; exact e.
    - rewrite H0, H; apply dkind_global_alias; assumption.
    - reflexivity.
    - (* a body's submodule, found in the body read through its opens *)
      destruct (H _ (kshape_refl ρ)) as (σ & Hk & Hs).
      rewrite H0, (ukind_id _ _ (proj1 Hs)).
      eapply ukind_kbody_mod; eassumption.
    - (* a submodule closure: a longer chain *)
      rewrite (dkind_member_iff Θ Ξ h), (dkind_member_iff Θ Ξ (dm_member h ch)); cbn [app].
      rewrite !dkind_member_cons_iff, <- !app_assoc; reflexivity.
    (* chains *)
    - symmetry; apply dkind_member_nil.
    - rewrite H0; apply dkind_member_snoc; exact H.
    (* bodies *)
    - exists σ; split; [ constructor | assumption ].
    - destruct (H _ H1) as (σ1 & Hk & Hs).
      exists (kbentry σ1 (ge_def b pv A (Some M)) :: σ1); split; [ constructor; exact Hk |].
      apply kshape_cons_term; exact Hs.
    - destruct (H _ H1) as (σ1 & Hk & Hs).
      exists (kbentry σ1 (ge_mod pm (gu_mk Δy Dy)) :: σ1); split; [ constructor; exact Hk |].
      apply kshape_cons_mod; [ exact Hs |].
      intros ch k; rewrite H0, dkind_clo_iff; apply ukind_id, Hs.
    - (* a definition with a module part: a placeholder and its unit's
         closure *)
      match goal with Hρ : kshape ρ σ, IHΦ : forall σ0, kshape ρ σ0 -> _,
                      IHc : forall ch k, dkind _ _ h ch k <-> _ |- _ =>
        destruct (IHΦ _ Hρ) as (σ1 & Hk & Hs);
        exists (kbentry σ1 (ge_def_mod pv A M (gu_mk Δy Dy)) :: σ1); split; [ constructor; exact Hk |];
        apply kshape_cons_dm; [ exact Hs |];
        intros ch k; rewrite IHc, dkind_clo_iff; apply ukind_id, Hs end.
  Qed.

  Corollary kind_eval_modexp : forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
      forall ch k, dkind Θ Ξ h ch k <-> skind Θ Ξ ρ H ch k.
  Proof. pose proof kind_eval as K; destruct_all; eauto. Qed.

  Corollary kind_eval_close : forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h ->
      forall ch k, dkind Θ Ξ h ch k <-> ukind Θ Ξ ρ (gu_mk Δ D) ch k.
  Proof. pose proof kind_eval as K; destruct_all; eauto. Qed.

  Corollary kind_eval_appm : forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r ->
      forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h ch k.
  Proof. pose proof kind_eval as K; destruct_all; eauto. Qed.

  Corollary kind_eval_benv : forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
      forall σ, kshape ρ σ -> exists σ', kenv Θ Ξ σ Φ σ' /\ kshape ρ' σ'.
  Proof. pose proof kind_eval as K; destruct_all; eauto. Qed.

End KindsEval.
