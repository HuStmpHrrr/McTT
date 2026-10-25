(** * Kinds of Members Under Renaming and Evaluation

    The kind of a member ([dkind], [ukind], [skind]) is read off module
    values and the syntax of the units they close over.  It reads an
    environment only through the kinds of its module entries, so

    - a weakening of the syntax, in an environment whose module entries
      have the kinds of the original's at the renamed positions, has the
      same kinds ([kind_ren]);
    - a module expression has the kinds of its value ([kind_eval], in
      [KindsEval]). *)

From Stdlib Require Import Lia List PeanoNat String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Semantic Require Import Evaluation.
Import Domain_Notations Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** Whether a global path names a member with a term part and a module
    part is decided by its lookups. *)
Lemma dm_path_cases : forall Θ Ξ p, dm_path Θ Ξ p \/ ~ dm_path Θ Ξ p.
Proof.
  intros.
  destruct (ind_mlookup Θ Ξ p) as [r |] eqn:Ei; [ left; left; eauto |].
  destruct (record_lookup Θ Ξ p) as [R |] eqn:Er; [ left; right; left; eauto |].
  destruct (gc_entry Θ Ξ p) as [[| | | pv A M U |] |] eqn:Ee;
    try (right; intros [(r0 & H) | [(R0 & H) | (pv0 & A0 & M0 & U0 & H)]]; congruence).
  left; right; right; eauto.
Qed.

Section Kinds.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** Two module values with the same kinds at every chain. *)
  Definition kequiv (h h' : dmod) : Prop := forall ch k, dkind Θ Ξ h ch k <-> dkind Θ Ξ h' ch k.

  Lemma kequiv_refl : forall h, kequiv h h.
  Proof. intros h ch k; reflexivity. Qed.

  Lemma kequiv_sym : forall h h', kequiv h h' -> kequiv h' h.
  Proof. intros * H ch k; symmetry; apply H. Qed.

  Lemma kequiv_trans : forall h1 h2 h3, kequiv h1 h2 -> kequiv h2 h3 -> kequiv h1 h3.
  Proof. intros * H1 H2 ch k; split; intros H; [ apply H2, H1, H | apply H1, H2, H ]. Qed.

  (** [ρ] at the positions [φ] sends the indices of [ρ'] to has the kinds of
      [ρ']: the environment of a weakened term, against the original's. *)
  Definition kren (φ : wk) (ρ ρ' : env) : Prop := forall x, kequiv (env_mod ρ (φ x)) (env_mod ρ' x).

  Lemma kren_ext : forall φ ψ ρ ρ', wk_eq φ ψ -> kren φ ρ ρ' -> kren ψ ρ ρ'.
  Proof. intros * E H x; rewrite <- (E x); apply H. Qed.

  Lemma env_mod_cons_S : forall e ρ x, env_mod (e :: ρ) (S x) = env_mod ρ x.
  Proof. reflexivity. Qed.

  Lemma kren_q_term : forall φ ρ ρ' d d', kren φ ρ ρ' -> kren (wk_q φ) (de_term d :: ρ) (de_term d' :: ρ').
  Proof. intros * H [| x]; cbn [wk_q]; [ apply kequiv_refl | apply H ]. Qed.

  Lemma kren_q_mod : forall φ ρ ρ' h h', kren φ ρ ρ' -> kequiv h h' -> kren (wk_q φ) (de_mod h :: ρ) (de_mod h' :: ρ').
  Proof. intros * H Hh [| x]; cbn [wk_q]; [ exact Hh | apply H ]. Qed.

  Lemma kren_q_dm : forall φ ρ ρ' d d' h h', kren φ ρ ρ' -> kequiv h h' ->
      kren (wk_q φ) (de_dm d h :: ρ) (de_dm d' h' :: ρ').
  Proof. intros * H Hh [| x]; cbn [wk_q]; [ exact Hh | apply H ]. Qed.

  Lemma kren_pad : forall n φ ρ ρ', kren φ ρ ρ' -> kren (wk_qn n φ) (kpad n ρ) (kpad n ρ').
  Proof.
    induction n as [| n IH]; intros * H; [ exact H |].
    cbn [wk_qn]; apply kren_q_term; exact (IH _ _ _ H).
  Qed.

  (** An environment over another, read past its own entries. *)
  Lemma env_mod_app_shift : forall ρ0 ρ x, env_mod (ρ0 ++ ρ) (x + List.length ρ0) = env_mod ρ x.
  Proof.
    induction ρ0 as [| e ρ0 IH]; intros; cbn [List.length app]; [ rewrite Nat.add_0_r; reflexivity |].
    rewrite Nat.add_succ_r; apply IH.
  Qed.

  Lemma kren_shift_app : forall ρ0 ρ, kren (wk_shiftn (List.length ρ0)) (ρ0 ++ ρ) ρ.
  Proof. intros * x; cbn [wk_shiftn]; rewrite env_mod_app_shift; apply kequiv_refl. Qed.

  Lemma kren_comp : forall φ ψ ρ1 ρ2 ρ3, kren φ ρ1 ρ2 -> kren ψ ρ2 ρ3 -> kren (ψ ⊙ φ) ρ1 ρ3.
  Proof. intros * H1 H2 x; cbn [wk_compose]; eapply kequiv_trans; [ apply H1 | apply H2 ]. Qed.

  (** A unit's kinds are its definition's, under placeholders for its
      parameters. *)
  Lemma ukind_pad : forall ρ Δ D ch k,
      ukind Θ Ξ ρ (gu_mk Δ D) ch k <-> ukind Θ Ξ (kpad (List.length Δ) ρ) (gu_mk nil D) ch k.
  Proof.
    intros; split; intros H; inversion H; subst;
      first [ eapply ukind_self | eapply ukind_def; eassumption | eapply ukind_mod; eassumption | eapply ukind_dm_here; eassumption
            | eapply ukind_dm_step; eassumption | eapply ukind_item_def; eassumption | eapply ukind_item_mod; eassumption
            | eapply ukind_item_dm; eassumption | eapply ukind_item_self; eassumption | eapply ukind_alias; eassumption ].
  Qed.

  (** *** Lookups Past an Entry *)

  Lemma ukind_body_ext_other : forall ρ sm Φ x E y ch k, y <> x ->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm (gm_ext Φ x E))) (y :: ch) k <->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k.
  Proof.
    intros * Hne.
    assert (Ey : String.eqb y x = false) by (apply String.eqb_neq; exact Hne).
    split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ey in *;
      solve [ econstructor; try (cbn [gm_prefix_upto gm_item_upto]; rewrite ?Ey); eassumption ].
  Qed.

  Lemma ukind_body_open_other : forall ρ sm Φ H its y ch k, items_upto y its = None ->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm (gm_open Φ H its))) (y :: ch) k <->
      ukind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k.
  Proof.
    intros * Hn.
    assert (Ey : existsb (String.eqb y) (map iitem_name its) = false).
    { destruct (existsb _ _) eqn:E; [| reflexivity ].
      exfalso; clear - E Hn; induction its as [| it its IH]; cbn in *; [ discriminate |].
      destruct (items_upto y its) as [[] |]; [ discriminate |].
      apply Bool.orb_true_iff in E as [E | E]; [ rewrite E in Hn; discriminate | auto ]. }
    split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ey, ?Hn in *;
      solve [ econstructor; try (cbn [gm_prefix_upto gm_item_upto]; rewrite ?Ey, ?Hn); eassumption ].
  Qed.

  (** *** The Selections of a Module Expression *)

  Lemma skind_unit_iff : forall ρ ρ' fp ch k, skind Θ Ξ ρ (me_unit fp) ch k <-> skind Θ Ξ ρ' (me_unit fp) ch k.
  Proof. intros; split; intros H; inversion H; subst; constructor; assumption. Qed.

  Lemma skind_var_iff : forall ρ x ch k, skind Θ Ξ ρ (me_var x) ch k <-> dkind Θ Ξ (env_mod ρ x) ch k.
  Proof. intros; split; intros H; [ inversion H; subst; assumption | constructor; assumption ]. Qed.

  (** A selection: by the longer chain, but a member with a term part and
      a module part, selected as a module, is a module. *)
  Lemma skind_mem_iff : forall ρ H y ch k, skind Θ Ξ ρ (me_mem H y) ch k <->
      (skind Θ Ξ ρ H (y :: ch) k /\ (ch <> nil \/ k <> mk_dm)) \/
      (ch = nil /\ k = mk_mod /\ skind Θ Ξ ρ H (y :: nil) mk_dm).
  Proof.
    intros; split; intros Hk.
    - inversion Hk; subst; [ left; split; assumption | right; repeat split; assumption ].
    - destruct Hk as [[Hk Hc] | (-> & -> & Hk)]; [ apply skind_mem; assumption | apply skind_mem_dm; exact Hk ].
  Qed.

  (** Away from the empty chain, a selection is read by the longer chain. *)
  Lemma skind_mem_cons_iff : forall ρ H y c ch k, skind Θ Ξ ρ (me_mem H y) (c :: ch) k <-> skind Θ Ξ ρ H (y :: c :: ch) k.
  Proof.
    intros; rewrite skind_mem_iff; split; [ intros [[Hk _] | (? & _)]; [ exact Hk | discriminate ] |].
    intros Hk; left; split; [ exact Hk | left; discriminate ].
  Qed.

  (** A submodule closure: by the longer chain, but a member with a term
      part and a module part, selected as a module, is a module. *)
  Lemma dkind_member_iff : forall h ch0 ch k, dkind Θ Ξ (dm_member h ch0) ch k <->
      (dkind Θ Ξ h (ch0 ++ ch) k /\ (ch <> nil \/ k <> mk_dm)) \/
      (ch = nil /\ k = mk_mod /\ dkind Θ Ξ h ch0 mk_dm).
  Proof.
    intros; split; intros Hk.
    - inversion Hk; subst; [ left; split; assumption | right; repeat split; assumption ].
    - destruct Hk as [[Hk Hc] | (-> & -> & Hk)]; [ apply dkind_member; assumption | apply dkind_member_dm; exact Hk ].
  Qed.

  Lemma dkind_member_cons_iff : forall h ch0 c ch k, dkind Θ Ξ (dm_member h ch0) (c :: ch) k <-> dkind Θ Ξ h (ch0 ++ c :: ch) k.
  Proof.
    intros; rewrite dkind_member_iff; split; [ intros [[Hk _] | (? & _)]; [ exact Hk | discriminate ] |].
    intros Hk; left; split; [ exact Hk | left; discriminate ].
  Qed.

  (** At the empty chain, nothing is a member with a term part and a
      module part: a value, a unit and a module expression are what they
      are, not members of something. *)
  Lemma kind_nil_not_dm :
    (forall h ch k, dkind Θ Ξ h ch k -> ch = nil -> k <> mk_dm) /\
    (forall ρ U ch k, ukind Θ Ξ ρ U ch k -> ch = nil -> k <> mk_dm) /\
    (forall ρ H ch k, skind Θ Ξ ρ H ch k -> ch = nil -> k <> mk_dm) /\
    (forall ρ Φ ρ1, kenv Θ Ξ ρ Φ ρ1 -> True) /\
    (forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> True) /\
    (forall ρ H its gs, kgens Θ Ξ ρ H its gs -> True).
  Proof.
    apply kind_mut_ind; intros; try exact I; subst; try discriminate; try (intros Hd; discriminate Hd);
      try (match goal with H : ?l ++ nil = nil -> _ |- _ => rewrite List.app_nil_r in H end);
      try (match goal with H : (@nil ?T) <> nil \/ _ |- _ =>
             destruct H as [H | H]; [ exfalso; exact (H eq_refl) | exact H ] end);
      eauto.
  Qed.

  Corollary dkind_nil_not_dm : forall h k, dkind Θ Ξ h nil k -> k <> mk_dm.
  Proof. intros * Hk; exact (proj1 kind_nil_not_dm _ _ _ Hk eq_refl). Qed.

  (** The submodule closure at the empty chain is the module itself. *)
  Lemma dkind_member_nil : forall h ch k, dkind Θ Ξ (dm_member h nil) ch k <-> dkind Θ Ξ h ch k.
  Proof.
    intros; rewrite dkind_member_iff; cbn [app]; split.
    - intros [[Hk _] | (_ & _ & Hk)]; [ exact Hk | exfalso; exact (dkind_nil_not_dm _ _ Hk eq_refl) ].
    - intros Hk; left; split; [ exact Hk |].
      destruct ch as [| c ch]; [ right; exact (dkind_nil_not_dm _ _ Hk) | left; discriminate ].
  Qed.

  (** A submodule closure read through a selection that has the kinds of
      a one-name submodule closure. *)
  Lemma dkind_member_snoc : forall h h1 y,
      (forall ch k, dkind Θ Ξ h1 ch k <-> dkind Θ Ξ (dm_member h (y :: nil)) ch k) ->
      forall ch0 ch k, dkind Θ Ξ (dm_member h1 ch0) ch k <-> dkind Θ Ξ (dm_member h (y :: ch0)) ch k.
  Proof.
    intros * Hh1 [| c0 ch0] ch k; [ rewrite dkind_member_nil; apply Hh1 |].
    rewrite (dkind_member_iff h1), (dkind_member_iff h (y :: c0 :: ch0)), (Hh1 ((c0 :: ch0) ++ ch)), (Hh1 (c0 :: ch0)).
    cbn [app]; rewrite !dkind_member_cons_iff; reflexivity.
  Qed.

  Lemma skind_app_iff : forall ρ H N ch k, skind Θ Ξ ρ (me_app H N) ch k <-> skind Θ Ξ ρ H ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  Lemma skind_lit_iff : forall ρ U ch k, skind Θ Ξ ρ (me_lit U) ch k <-> ukind Θ Ξ ρ U ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  Lemma dkind_local_iff : forall Δ D ρ ch k, dkind Θ Ξ (dm_local Δ D ρ) ch k <-> ukind Θ Ξ ρ (gu_mk Δ D) ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  Lemma dkind_clo_iff : forall U ρ ch k, dkind Θ Ξ (dm_clo U ρ) ch k <-> ukind Θ Ξ ρ U ch k.
  Proof. intros [Δ D] *; apply dkind_local_iff. Qed.

  Lemma ukind_alias_iff : forall ρ E ch k, ukind Θ Ξ ρ (gu_mk nil (md_alias E)) ch k <-> skind Θ Ξ ρ E ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  (** *** Generated Entries Under a Renaming *)

  Definition kren_mod (H : modexp) : Prop :=
    forall φ ρ ρ', kren φ ρ ρ' -> forall ch k, skind Θ Ξ ρ (modexp_wk H φ) ch k <-> skind Θ Ξ ρ' H ch k.

  Lemma kgens_ren_fwd : forall H, kren_mod H -> forall φ ρ ρ', kren φ ρ ρ' ->
      forall its gs, kgens Θ Ξ ρ' H its gs -> kgens Θ Ξ ρ (modexp_wk H φ) its (List.map (fun g => igen_wk g φ) gs).
  Proof.
    intros H HH φ ρ ρ' Hφ; induction 1; cbn [List.map igen_wk exp_wk modexp_wk]; constructor; auto;
      apply (HH _ _ _ Hφ); assumption.
  Qed.

  Lemma kgens_ren_bwd : forall H, kren_mod H -> forall φ ρ ρ', kren φ ρ ρ' ->
      forall its gs0, kgens Θ Ξ ρ (modexp_wk H φ) its gs0 ->
      exists gs, kgens Θ Ξ ρ' H its gs /\ gs0 = List.map (fun g => igen_wk g φ) gs.
  Proof.
    intros H HH φ ρ ρ' Hφ its; induction its as [| [[[n |] d] pv] its IH]; intros gs0 Hg; inversion Hg; subst.
    - exists nil; split; [ constructor | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_def; [ apply (HH _ _ _ Hφ); eassumption | exact Hgs ] | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_mod; [ apply (HH _ _ _ Hφ); eassumption | exact Hgs ] | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_dm; [ apply (HH _ _ _ Hφ); eassumption | exact Hgs ] | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_self; exact Hgs | reflexivity ].
  Qed.

  Lemma kgens_alias_target : forall ρ H its gs, kgens Θ Ξ ρ H its gs ->
      forall d pv E, In (ig_alias d pv E) gs -> E = H \/ exists n, E = me_mem H n.
  Proof.
    induction 1; intros * Hin; cbn in Hin; try contradiction;
      destruct Hin as [Heq | Hin]; try discriminate; eauto.
    - injection Heq as <- <- <-; auto.
    - injection Heq as <- <- <-; eauto.
  Qed.

  (** A generated definition with a module part is of a member of the
      target. *)
  Lemma kgens_dm_target : forall ρ H its gs, kgens Θ Ξ ρ H its gs ->
      forall d pv A M E, In (ig_def_mod d pv A M E) gs -> exists n, E = me_mem H n.
  Proof.
    induction 1; intros * Hin; cbn in Hin; try contradiction;
      destruct Hin as [Heq | Hin]; try discriminate; eauto.
    injection Heq as <- <- <- <- <-; eauto.
  Qed.

  (** What an open generates: definitions, aliases and definitions with a
      module part. *)
  Lemma kgens_shape : forall ρ H its gs, kgens Θ Ξ ρ H its gs ->
      forall g, In g gs ->
      (exists d pv A M, g = ig_def d pv A M) \/ (exists d pv E, g = ig_alias d pv E) \/
      (exists d pv A M E, g = ig_def_mod d pv A M E).
  Proof.
    induction 1; intros g Hin; cbn in Hin; try contradiction; destruct Hin as [<- | Hin]; auto;
      first [ left; do 4 eexists; reflexivity | right; left; do 3 eexists; reflexivity
            | right; right; do 5 eexists; reflexivity ].
  Qed.

  (** The alias closures a generated item adds, after [k] items, on both
      sides of a renaming. *)
  Lemma kentry_alias_kequiv : forall H, kren_mod H -> forall φ ρ1 ρ1' A B E,
      kren φ ρ1 ρ1' -> List.length A = List.length B -> (E = H \/ exists n, E = me_mem H n) ->
      kequiv (dm_local nil (md_alias (modexp_wk (modexp_wk E φ) (wk_shiftn (List.length A)))) (A ++ ρ1))
             (dm_local nil (md_alias (modexp_wk E (wk_shiftn (List.length A)))) (B ++ ρ1')).
  Proof.
    intros H HH φ ρ1 ρ1' A B E Hφ Hl HE ch k.
    rewrite !dkind_local_iff, !ukind_alias_iff, !modexp_wk_wk.
    assert (H1 : kren (φ ⊙ wk_shiftn (List.length A)) (A ++ ρ1) ρ1').
    { intros x; cbn [wk_compose wk_shiftn]; rewrite env_mod_app_shift; apply Hφ. }
    assert (H2 : kren (wk_shiftn (List.length A)) (B ++ ρ1') ρ1') by (rewrite Hl; apply kren_shift_app).
    destruct HE as [-> | [n ->]].
    - rewrite (HH _ _ _ H1), (HH _ _ _ H2); reflexivity.
    - cbn [modexp_wk]; rewrite !skind_mem_iff, (HH _ _ _ H1), (HH _ _ _ H1), (HH _ _ _ H2), (HH _ _ _ H2); reflexivity.
  Qed.

  Lemma kgens_env_ren : forall H, kren_mod H -> forall φ ρ1 ρ1' its gs,
      kren φ ρ1 ρ1' -> kgens Θ Ξ ρ1' H its gs ->
      forall gs1 A B, List.length A = List.length B ->
      kren (wk_qn (List.length A) φ) (A ++ ρ1) (B ++ ρ1') ->
      (forall g, In g gs1 -> In g gs) ->
      kren (wk_qn (List.length A + List.length gs1) φ)
        (kgens_env (A ++ ρ1) (List.length A) (List.map (fun g => igen_wk g φ) gs1))
        (kgens_env (B ++ ρ1') (List.length A) gs1).
  Proof.
    intros H HH φ ρ1 ρ1' its gs Hφ Hg gs1; induction gs1 as [| g gs1 IH]; intros A B Hl HAB Hin;
      cbn [List.map kgens_env List.length]; [ rewrite Nat.add_0_r; exact HAB |].
    rewrite Nat.add_succ_r.
    destruct (kgens_shape _ _ _ _ Hg g (Hin g (or_introl eq_refl)))
      as [(d & pv & A0 & M & ->) | [(d & pv & E & ->) | (d & pv & A0 & M & E & ->)]];
      cbn [kentry igen_wk].
    - specialize (IH (de_term d_true :: A) (de_term d_true :: B)); cbn [List.length app] in IH.
      apply IH; [ congruence | cbn [wk_qn]; apply kren_q_term; exact HAB | intros; apply Hin; right; assumption ].
    - set (h := dm_local nil (md_alias (modexp_wk (modexp_wk E φ) (wk_shiftn (List.length A)))) (A ++ ρ1)).
      set (h' := dm_local nil (md_alias (modexp_wk E (wk_shiftn (List.length A)))) (B ++ ρ1')).
      specialize (IH (de_mod h :: A) (de_mod h' :: B)); cbn [List.length app] in IH.
      apply IH; [ congruence | cbn [wk_qn]; apply kren_q_mod; [ exact HAB |] | intros; apply Hin; right; assumption ].
      apply kentry_alias_kequiv with (H := H); [ exact HH | exact Hφ | exact Hl |].
      eapply kgens_alias_target; [ exact Hg | apply Hin; left; reflexivity ].
    - set (h := dm_local nil (md_alias (modexp_wk (modexp_wk E φ) (wk_shiftn (List.length A)))) (A ++ ρ1)).
      set (h' := dm_local nil (md_alias (modexp_wk E (wk_shiftn (List.length A)))) (B ++ ρ1')).
      specialize (IH (de_dm d_true h :: A) (de_dm d_true h' :: B)); cbn [List.length app] in IH.
      apply IH; [ congruence | cbn [wk_qn]; apply kren_q_dm; [ exact HAB |] | intros; apply Hin; right; assumption ].
      apply kentry_alias_kequiv with (H := H); [ exact HH | exact Hφ | exact Hl |].
      right; eapply kgens_dm_target; [ exact Hg | apply Hin; left; reflexivity ].
  Qed.

  (** *** A Weakening Has the Kinds of What It Weakens *)

  Definition kren_unit (U : gunit) : Prop :=
    forall φ ρ ρ', kren φ ρ ρ' -> forall ch k, ukind Θ Ξ ρ (gunit_wk U φ) ch k <-> ukind Θ Ξ ρ' U ch k.

  Definition kren_def (D : moddef) : Prop :=
    forall φ ρ ρ', kren φ ρ ρ' -> forall ch k,
      ukind Θ Ξ ρ (gu_mk nil (moddef_wk D φ)) ch k <-> ukind Θ Ξ ρ' (gu_mk nil D) ch k.

  (** A body read by kinds at a renamed environment, against the body
      renamed: the environments it makes, both ways, and its members. *)
  Record kren_body_at (Φ : gmod) (φ : wk) (ρ ρ' : env) : Prop := mk_kren_body_at
    { kren_body_at_fwd : forall ρ1', kenv Θ Ξ ρ' Φ ρ1' -> exists ρ1, kenv Θ Ξ ρ (gmod_wk Φ φ) ρ1 /\ kren (wk_qn (gm_binders Φ) φ) ρ1 ρ1'
    ; kren_body_at_bwd : forall ρ1, kenv Θ Ξ ρ (gmod_wk Φ φ) ρ1 -> exists ρ1', kenv Θ Ξ ρ' Φ ρ1' /\ kren (wk_qn (gm_binders Φ) φ) ρ1 ρ1'
    ; kren_body_at_kind : forall sm x ch k, ukind Θ Ξ ρ (gu_mk nil (md_body sm (gmod_wk Φ φ))) (x :: ch) k <->
        ukind Θ Ξ ρ' (gu_mk nil (md_body sm Φ)) (x :: ch) k }.

  Definition kren_body (Φ : gmod) : Prop :=
    forall φ ρ ρ', kren φ ρ ρ' -> kren_body_at Φ φ ρ ρ'.

  Definition kren_entry (E : gentry) : Prop :=
    match E with
    | ge_mod _ U | ge_def_mod _ _ _ U => kren_unit U
    | _ => True
    end.

  (** The generated entries an open makes, and their environment, on both
      sides of a renaming. *)
  Lemma kgens_env_ren0 : forall H, kren_mod H -> forall φ ρ1 ρ1' its gs,
      kren φ ρ1 ρ1' -> kgens Θ Ξ ρ1' H its gs ->
      kren (wk_qn (List.length gs) φ) (kgens_env ρ1 0 (List.map (fun g => igen_wk g φ) gs)) (kgens_env ρ1' 0 gs).
  Proof.
    intros * HH * Hφ Hg.
    exact (kgens_env_ren H HH φ ρ1 ρ1' its gs Hφ Hg gs nil nil eq_refl Hφ (fun g Hin => Hin)).
  Qed.

  #[local] Ltac kih :=
    match goal with IH : forall φ ρ ρ', kren φ ρ ρ' -> _, Hr : kren _ _ _ |- _ => apply IH; exact Hr end.

  Lemma kind_ren :
    (forall H, kren_mod H) /\ (forall U, kren_unit U) /\ (forall D, kren_def D) /\ (forall Φ, kren_body Φ).
  Proof.
    cut ((forall M : exp, True) /\ (forall H, kren_mod H) /\ (forall b : bnd, True) /\ (forall U, kren_unit U) /\
         (forall D, kren_def D) /\ (forall Φ, kren_body Φ) /\ (forall E, kren_entry E) /\ (forall e : centry, True));
      [ intros (_ & H1 & _ & H2 & H3 & H4 & _); auto |].
    apply (syn_mut_ind (fun _ => True) kren_mod (fun _ => True) kren_unit kren_def kren_body kren_entry (fun _ => True));
      intros; try exact I; unfold kren_mod, kren_unit, kren_def, kren_body, kren_entry in *.
    - (* a unit *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; apply skind_unit_iff.
    - (* a slot *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !skind_var_iff; apply Hφ.
    - (* a selection *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !skind_mem_iff;
        match goal with IH : forall φ ρ ρ', kren φ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hφ), (IH _ _ _ Hφ); reflexivity end.
    - (* an application *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !skind_app_iff; kih.
    - (* a literal *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !skind_lit_iff; kih.
    - (* a unit: its definition under its parameters *)
      intros φ ρ ρ' Hφ ch kk; rewrite gunit_wk_mk, (ukind_pad ρ (tele_wk Δ φ)), (ukind_pad ρ' Δ), length_tele_wk.
      match goal with IH : forall φ ρ ρ', kren φ ρ ρ' -> _ |- _ => apply IH end; apply kren_pad; exact Hφ.
    - (* a body *)
      intros φ ρ ρ' Hφ ch kk; cbn [moddef_wk].
      destruct ch as [| x ch].
      + split; intros Hk; inversion Hk; subst; constructor.
      + match goal with IH : forall φ ρ ρ', kren φ ρ ρ' -> _ |- _ => apply (IH _ _ _ Hφ) end.
    - (* an alias *)
      intros φ ρ ρ' Hφ ch kk; cbn [moddef_wk]; rewrite !ukind_alias_iff;
        match goal with IH : forall φ ρ ρ', kren φ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hφ); reflexivity end.
    - (* the empty body *)
      intros φ ρ ρ' Hφ; constructor.
      + intros ρ1' Hk; inversion Hk; subst; exists ρ; split; [ constructor | exact Hφ ].
      + intros ρ1 Hk; inversion Hk; subst; exists ρ'; split; [ constructor | exact Hφ ].
      + intros sm0 x ch kk; split; intros Hk; inversion Hk; subst; cbn in *; discriminate.
    - (* an entry *)
      intros φ ρ ρ' Hφ; destruct (H _ _ _ Hφ) as [IH1 IH2 IH3]; rename H0 into IHE.
      constructor.
      + intros ρb Hk; inversion Hk; subst; cbn [gmod_wk gm_binders wk_qn].
        destruct (IH1 _ ltac:(eassumption)) as (ρa & Hk1 & Hr1).
        eexists; split; [ apply ke_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_wk kbentry];
          try (apply kren_q_term; exact Hr1);
          try ((first [ apply kren_q_mod | apply kren_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dkind_clo_iff; apply IHE; exact Hr1 ]).
      + intros ρa Hk; cbn [gmod_wk] in Hk; inversion Hk; subst; cbn [gm_binders wk_qn].
        destruct (IH2 _ ltac:(eassumption)) as (ρb & Hk1 & Hr1).
        eexists; split; [ apply ke_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_wk kbentry];
          try (apply kren_q_term; exact Hr1);
          try ((first [ apply kren_q_mod | apply kren_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dkind_clo_iff; apply IHE; exact Hr1 ]).
      + intros sm0 y ch kk; cbn [gmod_wk].
        destruct (String.eqb_spec y x) as [-> | Hne];
          [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ Hne), ukind_body_ext_other by exact Hne; apply IH3 ].
        assert (Ex : String.eqb x x = true) by apply String.eqb_refl.
        split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto gmod_wk] in *; rewrite ?Ex in *;
          try discriminate.
        * destruct E as [b0 pv0 A0 B0 | | | |]; cbn in *; try congruence; eapply ukind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn [gentry_wk] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kenv _ _ _ (gmod_wk Φ φ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply ukind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_wk] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ (gmod_wk Φ φ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply ukind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_wk] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ (gmod_wk Φ φ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply ukind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [b0 pv0 A0 B0 | | | |]; cbn in *; try congruence; eapply ukind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kenv _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply ukind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply ukind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply ukind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
    - (* an open *)
      intros φ ρ ρ' Hφ; rename H0 into IHΦ, H1 into IHH; destruct (IHΦ _ _ _ Hφ) as [IH1 IH2 IH3].
      assert (Hcomp : forall n, wk_eq (wk_qn n (wk_qn (gm_binders Φ) φ)) (wk_qn (n + gm_binders Φ) φ))
        by (intros n x; apply (wk_qn_add n (gm_binders Φ) φ x)).
      constructor.
      + intros ρ2' Hk; inversion Hk; subst; cbn [gmod_wk gm_binders].
        destruct (IH1 _ ltac:(eassumption)) as (ρa & Hk1 & Hr1).
        match goal with Hg : kgens _ _ _ _ _ ?gs |- _ =>
          pose proof (kgens_ren_fwd _ IHH _ _ _ Hr1 _ _ Hg) as Hgw;
          pose proof (kgens_env_ren0 _ IHH _ _ _ _ _ Hr1 Hg) as Hre;
          pose proof (kgens_length _ _ _ _ _ _ Hg) as Hl end.
        eexists; split; [ apply ke_open; [ exact Hk1 | exact Hgw ] |].
        eapply kren_ext; [| exact Hre ]; rewrite Hl; apply Hcomp.
      + intros ρ2 Hk; cbn [gmod_wk] in Hk; inversion Hk; subst; cbn [gm_binders].
        destruct (IH2 _ ltac:(eassumption)) as (ρb & Hk1 & Hr1).
        match goal with Hg : kgens _ _ _ _ _ _ |- _ =>
          destruct (kgens_ren_bwd _ IHH _ _ _ Hr1 _ _ Hg) as (gs1 & Hg' & ->) end.
        pose proof (kgens_env_ren0 _ IHH _ _ _ _ _ Hr1 Hg') as Hre.
        pose proof (kgens_length _ _ _ _ _ _ Hg') as Hl.
        eexists; split; [ apply ke_open; [ exact Hk1 | exact Hg' ] |].
        eapply kren_ext; [| exact Hre ]; rewrite Hl; apply Hcomp.
      + intros sm0 y ch kk; cbn [gmod_wk].
        destruct (items_upto y its) as [[its1 it] |] eqn:Ey;
          [| rewrite (ukind_body_open_other _ _ _ _ _ _ _ _ Ey), ukind_body_open_other by exact Ey; apply IH3 ].
        assert (Hex : existsb (String.eqb y) (map iitem_name its) = true) by (eapply items_upto_some; exact Ey).
        split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto gmod_wk] in *; rewrite ?Ey, ?Hex in *;
          try discriminate.
        all: match goal with Hp : Some _ = Some (_, _, _, _) |- _ => injection Hp; intros; subst end.
        all: match goal with Hk1 : kenv _ _ ?e ?Q _, IH : forall r, kenv _ _ ?e ?Q r -> exists _, _ |- _ =>
               destruct (IH _ Hk1) as (ρ0 & Hk1' & Hr1) end.
        all: first [ eapply ukind_item_def; [ cbn; rewrite Ey; reflexivity | exact Hk1' |]; apply (IHH _ _ _ Hr1); assumption
                   | eapply ukind_item_mod; [ cbn; rewrite Ey; reflexivity | exact Hk1' | |]; apply (IHH _ _ _ Hr1); assumption
                   | eapply ukind_item_dm; [ cbn; rewrite Ey; reflexivity | exact Hk1' | |]; apply (IHH _ _ _ Hr1); assumption
                   | eapply ukind_item_self; [ cbn; rewrite Ey; reflexivity | exact Hk1' |]; apply (IHH _ _ _ Hr1); assumption ].
    - (* a submodule entry *) exact H.
    - (* a definition with a module part: its module part *) exact H1.
  Qed.


  (** *** A Substitution Has the Kinds of What It Substitutes

      As a renaming, a substitution that sends each slot to a module
      expression with the kinds of the original environment's entry there:
      terms are never looked at. *)

  Definition ksub (σ : sub) (ρ ρ' : env) : Prop :=
    forall x ch k, skind Θ Ξ ρ (sentry_modexp (σ x)) ch k <-> dkind Θ Ξ (env_mod ρ' x) ch k.

  Lemma ksub_q_term : forall σ ρ ρ' d d', ksub σ ρ ρ' -> ksub (sb_q σ) (de_term d :: ρ) (de_term d' :: ρ').
  Proof.
    intros * H [| x] ch k; rewrite ?sb_q_zero, ?sb_q_succ; cbn [sentry_modexp].
    - rewrite skind_var_iff; reflexivity.
    - rewrite <- sentry_modexp_wk, (proj1 kind_ren _ wk_shift (de_term d :: ρ) ρ (fun x => kequiv_refl _)).
      apply H.
  Qed.

  Lemma ksub_q_mod : forall σ ρ ρ' h h', ksub σ ρ ρ' -> kequiv h h' -> ksub (sb_q σ) (de_mod h :: ρ) (de_mod h' :: ρ').
  Proof.
    intros * H Hh [| x] ch k; rewrite ?sb_q_zero, ?sb_q_succ; cbn [sentry_modexp].
    - rewrite skind_var_iff; apply Hh.
    - rewrite <- sentry_modexp_wk, (proj1 kind_ren _ wk_shift (de_mod h :: ρ) ρ (fun x => kequiv_refl _)).
      apply H.
  Qed.

  Lemma ksub_q_dm : forall σ ρ ρ' d d' h h', ksub σ ρ ρ' -> kequiv h h' ->
      ksub (sb_q σ) (de_dm d h :: ρ) (de_dm d' h' :: ρ').
  Proof.
    intros * H Hh [| x] ch k; rewrite ?sb_q_zero, ?sb_q_succ; cbn [sentry_modexp].
    - rewrite skind_var_iff; apply Hh.
    - rewrite <- sentry_modexp_wk, (proj1 kind_ren _ wk_shift (de_dm d h :: ρ) ρ (fun x => kequiv_refl _)).
      apply H.
  Qed.

  Lemma ksub_pad : forall n σ ρ ρ', ksub σ ρ ρ' -> ksub (sb_qn n σ) (kpad n ρ) (kpad n ρ').
  Proof.
    induction n as [| n IH]; intros * H; [ exact H |].
    cbn [sb_qn kpad repeat app]; apply ksub_q_term; exact (IH _ _ _ H).
  Qed.

  Lemma ksub_ext : forall σ ψ ρ ρ', sb_eq σ ψ -> ksub σ ρ ρ' -> ksub ψ ρ ρ'.
  Proof. intros * E H x; rewrite <- (E x); apply H. Qed.

  Definition ksub_mod (H : modexp) : Prop :=
    forall σ ρ ρ', ksub σ ρ ρ' -> forall ch k, skind Θ Ξ ρ H[σ]ᵐ ch k <-> skind Θ Ξ ρ' H ch k.

  Definition ksub_unit (U : gunit) : Prop :=
    forall σ ρ ρ', ksub σ ρ ρ' -> forall ch k, ukind Θ Ξ ρ U[σ]ᵘ ch k <-> ukind Θ Ξ ρ' U ch k.

  Definition ksub_def (D : moddef) : Prop :=
    forall σ ρ ρ', ksub σ ρ ρ' -> forall ch k,
      ukind Θ Ξ ρ (gu_mk nil (moddef_sub D σ)) ch k <-> ukind Θ Ξ ρ' (gu_mk nil D) ch k.

  (** The same at a substituted environment, against the body
      substituted. *)
  Record ksub_body_at (Φ : gmod) (σ : sub) (ρ ρ' : env) : Prop := mk_ksub_body_at
    { ksub_body_at_fwd : forall ρ1', kenv Θ Ξ ρ' Φ ρ1' -> exists ρ1, kenv Θ Ξ ρ (gmod_sub Φ σ) ρ1 /\ ksub (sb_qn (gm_binders Φ) σ) ρ1 ρ1'
    ; ksub_body_at_bwd : forall ρ1, kenv Θ Ξ ρ (gmod_sub Φ σ) ρ1 -> exists ρ1', kenv Θ Ξ ρ' Φ ρ1' /\ ksub (sb_qn (gm_binders Φ) σ) ρ1 ρ1'
    ; ksub_body_at_kind : forall sm x ch k, ukind Θ Ξ ρ (gu_mk nil (md_body sm (gmod_sub Φ σ))) (x :: ch) k <->
        ukind Θ Ξ ρ' (gu_mk nil (md_body sm Φ)) (x :: ch) k }.

  Definition ksub_body (Φ : gmod) : Prop :=
    forall σ ρ ρ', ksub σ ρ ρ' -> ksub_body_at Φ σ ρ ρ'.

  Definition ksub_entry (E : gentry) : Prop :=
    match E with
    | ge_mod _ U | ge_def_mod _ _ _ U => ksub_unit U
    | _ => True
    end.

  Lemma kgens_sub_fwd : forall H, ksub_mod H -> forall σ ρ ρ', ksub σ ρ ρ' ->
      forall its gs, kgens Θ Ξ ρ' H its gs -> kgens Θ Ξ ρ H[σ]ᵐ its (List.map (fun g => igen_sub g σ) gs).
  Proof.
    intros H HH σ ρ ρ' Hσ; induction 1; cbn [List.map igen_sub exp_sub modexp_sub]; constructor; auto;
      apply (HH _ _ _ Hσ); assumption.
  Qed.

  Lemma kgens_sub_bwd : forall H, ksub_mod H -> forall σ ρ ρ', ksub σ ρ ρ' ->
      forall its gs0, kgens Θ Ξ ρ H[σ]ᵐ its gs0 ->
      exists gs, kgens Θ Ξ ρ' H its gs /\ gs0 = List.map (fun g => igen_sub g σ) gs.
  Proof.
    intros H HH σ ρ ρ' Hσ its; induction its as [| [[[n |] d] pv] its IH]; intros gs0 Hg; inversion Hg; subst.
    - exists nil; split; [ constructor | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_def; [ apply (HH _ _ _ Hσ); eassumption | exact Hgs ] | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_mod; [ apply (HH _ _ _ Hσ); eassumption | exact Hgs ] | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_dm; [ apply (HH _ _ _ Hσ); eassumption | exact Hgs ] | reflexivity ].
    - destruct (IH _ ltac:(eassumption)) as (gs1 & Hgs & ->).
      eexists; split; [ apply kgens_self; exact Hgs | reflexivity ].
  Qed.

  Lemma kentry_alias_ksub : forall H, ksub_mod H -> forall σ ρ1 ρ1' A B E,
      ksub σ ρ1 ρ1' -> List.length A = List.length B -> (E = H \/ exists n, E = me_mem H n) ->
      kequiv (dm_local nil (md_alias (modexp_wk E[σ]ᵐ (wk_shiftn (List.length A)))) (A ++ ρ1))
             (dm_local nil (md_alias (modexp_wk E (wk_shiftn (List.length A)))) (B ++ ρ1')).
  Proof.
    intros H HH σ ρ1 ρ1' A B E Hσ Hl HE ch k.
    rewrite !dkind_local_iff, !ukind_alias_iff.
    rewrite (proj1 kind_ren _ (wk_shiftn (List.length A)) (A ++ ρ1) ρ1 (kren_shift_app A ρ1)).
    rewrite Hl, (proj1 kind_ren _ (wk_shiftn (List.length B)) (B ++ ρ1') ρ1' (kren_shift_app B ρ1')).
    destruct HE as [-> | [n ->]]; [ rewrite (HH _ _ _ Hσ); reflexivity |].
    cbn [modexp_sub]; rewrite !skind_mem_iff, (HH _ _ _ Hσ), (HH _ _ _ Hσ); reflexivity.
  Qed.

  Lemma kgens_env_sub : forall H, ksub_mod H -> forall σ ρ1 ρ1' its gs,
      ksub σ ρ1 ρ1' -> kgens Θ Ξ ρ1' H its gs ->
      forall gs1 A B, List.length A = List.length B ->
      ksub (sb_qn (List.length A) σ) (A ++ ρ1) (B ++ ρ1') ->
      (forall g, In g gs1 -> In g gs) ->
      ksub (sb_qn (List.length A + List.length gs1) σ)
        (kgens_env (A ++ ρ1) (List.length A) (List.map (fun g => igen_sub g σ) gs1))
        (kgens_env (B ++ ρ1') (List.length A) gs1).
  Proof.
    intros H HH σ ρ1 ρ1' its gs Hσ Hg gs1; induction gs1 as [| g gs1 IH]; intros A B Hl HAB Hin;
      cbn [List.map kgens_env List.length]; [ rewrite Nat.add_0_r; exact HAB |].
    rewrite Nat.add_succ_r.
    destruct (kgens_shape _ _ _ _ Hg g (Hin g (or_introl eq_refl)))
      as [(d & pv & A0 & M & ->) | [(d & pv & E & ->) | (d & pv & A0 & M & E & ->)]];
      cbn [kentry igen_sub].
    - specialize (IH (de_term d_true :: A) (de_term d_true :: B)); cbn [List.length app] in IH.
      apply IH; [ congruence | cbn [sb_qn]; apply ksub_q_term; exact HAB | intros; apply Hin; right; assumption ].
    - set (h := dm_local nil (md_alias (modexp_wk E[σ]ᵐ (wk_shiftn (List.length A)))) (A ++ ρ1)).
      set (h' := dm_local nil (md_alias (modexp_wk E (wk_shiftn (List.length A)))) (B ++ ρ1')).
      specialize (IH (de_mod h :: A) (de_mod h' :: B)); cbn [List.length app] in IH.
      apply IH; [ congruence | cbn [sb_qn]; apply ksub_q_mod; [ exact HAB |] | intros; apply Hin; right; assumption ].
      apply kentry_alias_ksub with (H := H); [ exact HH | exact Hσ | exact Hl |].
      eapply kgens_alias_target; [ exact Hg | apply Hin; left; reflexivity ].
    - set (h := dm_local nil (md_alias (modexp_wk E[σ]ᵐ (wk_shiftn (List.length A)))) (A ++ ρ1)).
      set (h' := dm_local nil (md_alias (modexp_wk E (wk_shiftn (List.length A)))) (B ++ ρ1')).
      specialize (IH (de_dm d_true h :: A) (de_dm d_true h' :: B)); cbn [List.length app] in IH.
      apply IH; [ congruence | cbn [sb_qn]; apply ksub_q_dm; [ exact HAB |] | intros; apply Hin; right; assumption ].
      apply kentry_alias_ksub with (H := H); [ exact HH | exact Hσ | exact Hl |].
      right; eapply kgens_dm_target; [ exact Hg | apply Hin; left; reflexivity ].
  Qed.

  Lemma kgens_env_sub0 : forall H, ksub_mod H -> forall σ ρ1 ρ1' its gs,
      ksub σ ρ1 ρ1' -> kgens Θ Ξ ρ1' H its gs ->
      ksub (sb_qn (List.length gs) σ) (kgens_env ρ1 0 (List.map (fun g => igen_sub g σ) gs)) (kgens_env ρ1' 0 gs).
  Proof.
    intros * HH * Hσ Hg.
    exact (kgens_env_sub H HH σ ρ1 ρ1' its gs Hσ Hg gs nil nil eq_refl Hσ (fun g Hin => Hin)).
  Qed.

  #[local] Ltac ksih :=
    match goal with IH : forall σ ρ ρ', ksub σ ρ ρ' -> _, Hr : ksub _ _ _ |- _ => apply IH; exact Hr end.

  Lemma kind_sub :
    (forall H, ksub_mod H) /\ (forall U, ksub_unit U) /\ (forall D, ksub_def D) /\ (forall Φ, ksub_body Φ).
  Proof.
    cut ((forall M : exp, True) /\ (forall H, ksub_mod H) /\ (forall b : bnd, True) /\ (forall U, ksub_unit U) /\
         (forall D, ksub_def D) /\ (forall Φ, ksub_body Φ) /\ (forall E, ksub_entry E) /\ (forall e : centry, True));
      [ intros (_ & H1 & _ & H2 & H3 & H4 & _); auto |].
    apply (syn_mut_ind (fun _ => True) ksub_mod (fun _ => True) ksub_unit ksub_def ksub_body ksub_entry (fun _ => True));
      intros; try exact I; unfold ksub_mod, ksub_unit, ksub_def, ksub_body, ksub_entry in *.
    - (* a unit *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; apply skind_unit_iff.
    - (* a slot *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite skind_var_iff; apply Hσ.
    - (* a selection *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite !skind_mem_iff;
        match goal with IH : forall σ ρ ρ', ksub σ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hσ), (IH _ _ _ Hσ); reflexivity end.
    - (* an application *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite !skind_app_iff; ksih.
    - (* a literal *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite !skind_lit_iff; ksih.
    - (* a unit: its definition under its parameters *)
      intros σ ρ ρ' Hσ ch kk; rewrite gunit_sub_mk, (ukind_pad ρ (tele_sub Δ σ)), (ukind_pad ρ' Δ), length_tele_sub.
      match goal with IH : forall σ ρ ρ', ksub σ ρ ρ' -> _ |- _ => apply IH end; apply ksub_pad; exact Hσ.
    - (* a body *)
      intros σ ρ ρ' Hσ ch kk; cbn [moddef_sub].
      destruct ch as [| x ch].
      + split; intros Hk; inversion Hk; subst; constructor.
      + match goal with IH : forall σ ρ ρ', ksub σ ρ ρ' -> _ |- _ => apply (IH _ _ _ Hσ) end.
    - (* an alias *)
      intros σ ρ ρ' Hσ ch kk; cbn [moddef_sub]; rewrite !ukind_alias_iff;
        match goal with IH : forall σ ρ ρ', ksub σ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hσ); reflexivity end.
    - (* the empty body *)
      intros σ ρ ρ' Hσ; constructor.
      + intros ρ1' Hk; inversion Hk; subst; exists ρ; split; [ constructor | exact Hσ ].
      + intros ρ1 Hk; inversion Hk; subst; exists ρ'; split; [ constructor | exact Hσ ].
      + intros sm0 x ch kk; split; intros Hk; inversion Hk; subst; cbn in *; discriminate.
    - (* an entry *)
      intros σ ρ ρ' Hσ; destruct (H _ _ _ Hσ) as [IH1 IH2 IH3]; rename H0 into IHE.
      constructor.
      + intros ρb Hk; inversion Hk; subst; cbn [gmod_sub gm_binders sb_qn].
        destruct (IH1 _ ltac:(eassumption)) as (ρa & Hk1 & Hr1).
        eexists; split; [ apply ke_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_sub kbentry];
          try (apply ksub_q_term; exact Hr1);
          try ((first [ apply ksub_q_mod | apply ksub_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dkind_clo_iff; apply IHE; exact Hr1 ]).
      + intros ρa Hk; cbn [gmod_sub] in Hk; inversion Hk; subst; cbn [gm_binders sb_qn].
        destruct (IH2 _ ltac:(eassumption)) as (ρb & Hk1 & Hr1).
        eexists; split; [ apply ke_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_sub kbentry];
          try (apply ksub_q_term; exact Hr1);
          try ((first [ apply ksub_q_mod | apply ksub_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dkind_clo_iff; apply IHE; exact Hr1 ]).
      + intros sm0 y ch kk; cbn [gmod_sub].
        destruct (String.eqb_spec y x) as [-> | Hne];
          [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ Hne), ukind_body_ext_other by exact Hne; apply IH3 ].
        assert (Ex : String.eqb x x = true) by apply String.eqb_refl.
        split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto gmod_sub] in *; rewrite ?Ex in *;
          try discriminate.
        * destruct E as [b0 pv0 A0 B0 | | | |]; cbn in *; try congruence; eapply ukind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn [gentry_sub] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kenv _ _ _ (gmod_sub Φ σ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply ukind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_sub] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ (gmod_sub Φ σ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply ukind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_sub] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ (gmod_sub Φ σ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply ukind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [b0 pv0 A0 B0 | | | |]; cbn in *; try congruence; eapply ukind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kenv _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply ukind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply ukind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kenv _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply ukind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
    - (* an open *)
      intros σ ρ ρ' Hσ; rename H0 into IHΦ, H1 into IHH; destruct (IHΦ _ _ _ Hσ) as [IH1 IH2 IH3].
      assert (Hcomp : forall n, sb_eq (sb_qn n (sb_qn (gm_binders Φ) σ)) (sb_qn (n + gm_binders Φ) σ))
        by (intros n x; rewrite sb_qn_plus; reflexivity).
      constructor.
      + intros ρ2' Hk; inversion Hk; subst; cbn [gmod_sub gm_binders].
        destruct (IH1 _ ltac:(eassumption)) as (ρa & Hk1 & Hr1).
        match goal with Hg : kgens _ _ _ _ _ ?gs |- _ =>
          pose proof (kgens_sub_fwd _ IHH _ _ _ Hr1 _ _ Hg) as Hgw;
          pose proof (kgens_env_sub0 _ IHH _ _ _ _ _ Hr1 Hg) as Hre;
          pose proof (kgens_length _ _ _ _ _ _ Hg) as Hl end.
        eexists; split; [ apply ke_open; [ exact Hk1 | exact Hgw ] |].
        eapply ksub_ext; [| exact Hre ]; rewrite Hl; apply Hcomp.
      + intros ρ2 Hk; cbn [gmod_sub] in Hk; inversion Hk; subst; cbn [gm_binders].
        destruct (IH2 _ ltac:(eassumption)) as (ρb & Hk1 & Hr1).
        match goal with Hg : kgens _ _ _ _ _ _ |- _ =>
          destruct (kgens_sub_bwd _ IHH _ _ _ Hr1 _ _ Hg) as (gs1 & Hg' & ->) end.
        pose proof (kgens_env_sub0 _ IHH _ _ _ _ _ Hr1 Hg') as Hre.
        pose proof (kgens_length _ _ _ _ _ _ Hg') as Hl.
        eexists; split; [ apply ke_open; [ exact Hk1 | exact Hg' ] |].
        eapply ksub_ext; [| exact Hre ]; rewrite Hl; apply Hcomp.
      + intros sm0 y ch kk; cbn [gmod_sub].
        destruct (items_upto y its) as [[its1 it] |] eqn:Ey;
          [| rewrite (ukind_body_open_other _ _ _ _ _ _ _ _ Ey), ukind_body_open_other by exact Ey; apply IH3 ].
        assert (Hex : existsb (String.eqb y) (map iitem_name its) = true) by (eapply items_upto_some; exact Ey).
        split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto gmod_sub] in *; rewrite ?Ey, ?Hex in *;
          try discriminate.
        all: match goal with Hp : Some _ = Some (_, _, _, _) |- _ => injection Hp; intros; subst end.
        all: match goal with Hk1 : kenv _ _ ?e ?Q _, IH : forall r, kenv _ _ ?e ?Q r -> exists _, _ |- _ =>
               destruct (IH _ Hk1) as (ρ0 & Hk1' & Hr1) end.
        all: first [ eapply ukind_item_def; [ cbn; rewrite Ey; reflexivity | exact Hk1' |]; apply (IHH _ _ _ Hr1); assumption
                   | eapply ukind_item_mod; [ cbn; rewrite Ey; reflexivity | exact Hk1' | |]; apply (IHH _ _ _ Hr1); assumption
                   | eapply ukind_item_dm; [ cbn; rewrite Ey; reflexivity | exact Hk1' | |]; apply (IHH _ _ _ Hr1); assumption
                   | eapply ukind_item_self; [ cbn; rewrite Ey; reflexivity | exact Hk1' |]; apply (IHH _ _ _ Hr1); assumption ].
    - (* a submodule entry *) exact H.
    - (* a definition with a module part: its module part *) exact H1.
  Qed.

End Kinds.
