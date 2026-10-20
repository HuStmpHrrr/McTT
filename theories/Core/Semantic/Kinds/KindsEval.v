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
      first [ eapply dk_global_here_def; eassumption | eapply dk_global_here_mod; eassumption
            | eapply dk_global_alias; eassumption | eapply dk_global_step; [ eassumption | eapply IH; eassumption ] ].
  Qed.

  Lemma dkind_global_snoc : forall p args y ch k TΦ,
      gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ ->
      dkind Θ Ξ (dm_global (qname_app p (y :: nil)) args) ch k <-> dkind Θ Ξ (dm_global p args) (y :: ch) k.
  Proof.
    intros * Hl; split; intros Hk; [ apply dk_global_step; [ left; eexists; exact Hl | assumption ] |].
    inversion Hk; subst; [ exfalso; eapply gc_loc_not_alias; eassumption | assumption ].
  Qed.

  Lemma dkind_global_alias : forall p args y U ch k,
      gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U) ->
      dkind Θ Ξ (dm_global p args) (y :: ch) k <-> ukind Θ Ξ nil U ch k.
  Proof.
    intros * Ha; split; intros Hk.
    - inversion Hk as [| | ? ? ? ? U' ? Ha' Hu' | ? ? ? ? ? Hn' _ | |]; subst;
        [ rewrite Ha in Ha'; injection Ha' as <-; exact Hu' |].
      exfalso; destruct Hn' as [(? & Hl) | (? & ? & ? & ? & Hr)];
        [ exact (gc_loc_not_alias _ _ _ _ _ Hl Ha) | rewrite (gc_module_resolve _ _ _ _ Ha) in Hr; discriminate Hr ].
    - eapply dk_global_alias; eassumption.
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
      (exists pm U ρ1, E = ge_mod pm U /\ kenv Θ Ξ ρ Φ' ρ1 /\ ukind Θ Ξ ρ1 U ch k).
  Proof.
    intros * Hp; split; intros Hu.
    - inversion Hu; subst;
        try (rewrite (gm_prefix_item_excl _ _ _ Hp) in *; discriminate);
        match goal with H2 : gm_prefix_upto _ _ = Some _ |- _ => rewrite Hp in H2; injection H2; intros; subst end.
      + left; repeat split; eauto.
      + right; do 3 eexists; repeat split; eassumption.
    - destruct Hu as [((b & pv & A & B & ->) & -> & ->) | (pm & U & ρ1 & -> & Hk & Hu)].
      + eapply uk_def; exact Hp.
      + eapply uk_mod; [ exact Hp | exact Hk | exact Hu ].
  Qed.

  (** The kinds a body gives a name an open declares. *)
  Lemma ukind_body_item : forall ρ sm Φ y Φ0 H its1 it ρ0 ch k,
      gm_item_upto Φ y = Some (Φ0, H, its1, it) -> kenv Θ Ξ ρ Φ0 ρ0 ->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k <->
      match it with
      | (Some n, _, _) => (ch = nil /\ k = mk_term /\ skind Θ Ξ ρ0 H (n :: nil) mk_term) \/
                         (skind Θ Ξ ρ0 H (n :: nil) mk_mod /\ skind Θ Ξ ρ0 H (n :: ch) k)
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
      + destruct Hu as [(-> & -> & Hs) | (Hs & Hs')]; [ eapply uk_item_def | eapply uk_item_mod ]; eassumption.
      + eapply uk_item_self; eassumption.
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
      + eapply uk_def; cbn; rewrite String.eqb_refl; reflexivity.
      + eapply uk_mod; [ cbn; rewrite String.eqb_refl; reflexivity | exact Hk2x |].
        match goal with Hk0 : kenv _ _ ?e ?Q ?r, Hk3 : kenv _ _ ?e ?Q ?r' |- _ =>
          assert_fails (constr_eq r r');
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk0 _ Hk3); subst end; assumption.
      + eapply uk_def; cbn; rewrite String.eqb_refl; reflexivity.
      + eapply uk_mod; [ cbn; rewrite String.eqb_refl; reflexivity | exact Hk2 |].
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
        assert (Hsh : forall E0 ch0 k0, ukind Θ Ξ (X ++ ρ2) (gu_mk nil (md_alias (modexp_wk E0 (wk_shiftn (0 + List.length gs0))))) ch0 k0 <->
                                   skind Θ Ξ ρ2 E0 ch0 k0).
        { intros; rewrite ukind_alias_iff; cbn [Nat.add]; rewrite <- Hl.
          exact (proj1 (kind_ren Θ Ξ) _ (wk_shiftn (List.length X)) (X ++ ρ2) ρ2 (kren_shift_app Θ Ξ X ρ2) _ _). }
        inversion Hg1 as [| ? ? d pv ? ? Hn | ? ? n d pv ? ? Hs Hn | ? ? n d pv ? ? Hs Hn]; subst;
          inversion Hn; subst; cbn [ig_entry snd gentry_wk] in Hpg |- *.
        * (* the open's target itself *)
          rewrite gunit_wk_mk; cbn [tele_wk List.length moddef_wk].
          split; [ intros Hu; right; do 3 eexists; split; [ reflexivity | split; [ exact Hkx | apply Hsh, Hu ] ] |].
          intros [((? & ? & ? & ? & ?) & _) | (pm & U & ρ1 & [= <- <-] & Hk1 & Hu)]; [ discriminate |].
          pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk1 _ Hkx) as ->; apply Hsh, Hu.
        * (* a term member: a definition *)
          split.
          -- intros [(-> & -> & _) | (Hm & _)]; [ left; split; [ do 4 eexists; reflexivity | split; reflexivity ] |].
             pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hs _ Hm); discriminate.
          -- intros [(_ & -> & ->) | (? & ? & ? & [=] & _)]; left; repeat split; exact Hs.
        * (* a module member: an alias of it *)
          rewrite gunit_wk_mk; cbn [tele_wk List.length moddef_wk].
          split.
          -- intros [(-> & -> & Ht) | (_ & Hu)];
               [ pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hs _ Ht); discriminate |].
             right; do 3 eexists; split; [ reflexivity | split; [ exact Hkx | apply (Hsh (me_mem H n)); apply skind_mem_iff, Hu ] ].
          -- intros [((? & ? & ? & ? & ?) & _) | (pm & U & ρ1 & [= <- <-] & Hk1 & Hu)]; [ discriminate |].
             pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk1 _ Hkx) as ->.
             right; split; [ exact Hs |]; apply skind_mem_iff, (proj1 (Hsh (me_mem H n) ch k) Hu).
      + pose proof (items_upto_none_iff _ _ Ey) as Hn; rewrite <- (kgens_names _ _ _ _ _ _ Hgs) in Hn.
        rewrite ukind_body_open_other by exact Ey; rewrite ukind_gens_other by exact Hn; apply IH.
  Qed.

  Lemma ukind_kbody_mod : forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx ->
      forall y Φ' pm U ρ1, gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm U)) -> kenv Θ Ξ ρ Φ' ρ1 ->
      forall sm ch k, ukind Θ Ξ ρ1 U ch k <-> ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k.
  Proof.
    intros * Hb * Hp Hk1 sm ch k; rewrite (ukind_kbody _ _ _ Hb), (ukind_body_entry _ _ _ _ _ _ _ _ Hp); split.
    - intros Hu; right; do 3 eexists; split; [ reflexivity | split; [ exact Hk1 | exact Hu ] ].
    - intros [((? & ? & ? & ? & ?) & _) | (pm' & U' & ρ1' & [= <- <-] & Hk1' & Hu)]; [ discriminate |].
      pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind Θ Ξ)))) _ _ _ Hk1' _ Hk1) as ->; exact Hu.
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
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h (y :: ch) k) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> True) /\
    (forall h ch0 r, h ·ₘ* ch0 Θ ⍮ Ξ ↘ r -> forall ch k, dkind Θ Ξ r ch k <-> dkind Θ Ξ h (ch0 ++ ch) k) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> forall σ, kshape ρ σ -> exists σ', kenv Θ Ξ σ Φ σ' /\ kshape ρ' σ') /\
    (forall ρ p Bks j m r, ⟦elim m at j of p Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall ρ p Bks gs vs r, ⟦ihs vs of gs under p Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall ρ p Bks t v r, ⟦ih v of t under p Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> True) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> True) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> True) /\
    (forall ρm As ρ t v a, ⟦ihty v of t under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> True).
  Proof.
    apply eval_mut_ind; intros; try exact I.
    (* module expressions *)
    - rewrite skind_var_iff; reflexivity.
    - split; intros Hk; [ constructor; exact Hk | inversion Hk; subst; assumption ].
    - rewrite H, skind_lit_iff; reflexivity.
    - rewrite skind_mem_iff; etransitivity; [ apply H1 | apply H0 ].
    - rewrite skind_app_iff; etransitivity; [ apply H2 | apply H0 ].
    (* closures *)
    - apply dkind_local_iff.
    - apply dkind_local_iff.
    - rewrite H, ukind_alias_iff; reflexivity.
    (* application: the arguments of a module are no part of its kinds *)
    - split; apply dkind_global_args.
    - rewrite H, dkind_local_iff, (ukind_pad _ _ (ρ ↦ n)), (ukind_pad _ _ ρ (Δ ++ ce_ass A :: nil)), length_app, Nat.add_1_r.
      apply ukind_id, kshape_pad_push.
    - split; intros Hk.
      + constructor; apply H; apply H0; exact Hk.
      + inversion Hk; subst; apply H0, H; assumption.
    - reflexivity.
    - rewrite H0, H; reflexivity.
    (* selection of a submodule *)
    - eapply dkind_global_snoc; exact e.
    - rewrite H0, H; symmetry; apply dkind_global_alias; assumption.
    - split; intros Hk; [ inversion Hk; subst; assumption | constructor; exact Hk ].
    - (* a body's submodule, found in the body read through its opens *)
      destruct (H _ (kshape_refl ρ)) as (σ & Hk & Hs).
      rewrite H0, (ukind_id _ _ (proj1 Hs)), dkind_local_iff.
      eapply ukind_kbody_mod; eassumption.
    - split; intros Hk; inversion Hk; subst; constructor; rewrite <- app_assoc in *; assumption.
    (* chains *)
    - reflexivity.
    - rewrite H0, H; reflexivity.
    (* bodies *)
    - exists σ; split; [ constructor | assumption ].
    - destruct (H _ H1) as (σ1 & Hk & Hs).
      exists (kbentry σ1 (ge_def b pv A (Some M)) :: σ1); split; [ constructor; exact Hk |].
      apply kshape_cons_term; exact Hs.
    - destruct (H _ H1) as (σ1 & Hk & Hs).
      exists (kbentry σ1 (ge_mod pm (gu_mk Δy Dy)) :: σ1); split; [ constructor; exact Hk |].
      apply kshape_cons_mod; [ exact Hs |].
      intros ch k; rewrite H0, dkind_clo_iff; apply ukind_id, Hs.
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
