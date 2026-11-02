(** * Kinds of Members Under Renaming and Evaluation

    The kind of a member ([dmod_member_kind], [gunit_member_kind], [modexp_member_kind]) is read off module
    values and the syntax of the units they close over.  It reads an
    environment only through the kinds of its module entries, so

    - a weakening of the syntax, in an environment whose module entries
      have the kinds of the original's at the renamed positions, has the
      same kinds ([kind_rename]);
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
  Definition kinds_equiv (h h' : dmod) : Prop := forall ch k, dmod_member_kind Θ Ξ h ch k <-> dmod_member_kind Θ Ξ h' ch k.

  Lemma kinds_equiv_refl : forall h, kinds_equiv h h.
  Proof. intros h ch k; reflexivity. Qed.

  Lemma kinds_equiv_sym : forall h h', kinds_equiv h h' -> kinds_equiv h' h.
  Proof. intros * H ch k; symmetry; apply H. Qed.

  Lemma kinds_equiv_trans : forall h1 h2 h3, kinds_equiv h1 h2 -> kinds_equiv h2 h3 -> kinds_equiv h1 h3.
  Proof. intros * H1 H2 ch k; split; intros H; [ apply H2, H1, H | apply H1, H2, H ]. Qed.

  (** [ρ] at the positions [φ] sends the indices of [ρ'] to has the kinds of
      [ρ']: the environment of a weakened term, against the original's. *)
  Definition kinds_rename (φ : wk) (ρ ρ' : env) : Prop := forall x, kinds_equiv (env_mod ρ (φ x)) (env_mod ρ' x).

  Lemma kinds_rename_ext : forall φ ψ ρ ρ', wk_eq φ ψ -> kinds_rename φ ρ ρ' -> kinds_rename ψ ρ ρ'.
  Proof. intros * E H x; rewrite <- (E x); apply H. Qed.

  Lemma env_mod_cons_S : forall e ρ x, env_mod (e :: ρ) (S x) = env_mod ρ x.
  Proof. reflexivity. Qed.

  Lemma kinds_rename_q_term : forall φ ρ ρ' d d' t t', kinds_rename φ ρ ρ' -> kinds_rename (wk_q φ) (de_term d t :: ρ) (de_term d' t' :: ρ').
  Proof. intros * H [| x]; cbn [wk_q]; [ apply kinds_equiv_refl | apply H ]. Qed.

  Lemma kinds_rename_q_mod : forall φ ρ ρ' h h' U U', kinds_rename φ ρ ρ' -> kinds_equiv h h' ->
      kinds_rename (wk_q φ) (de_mod h U :: ρ) (de_mod h' U' :: ρ').
  Proof. intros * H Hh [| x]; cbn [wk_q]; [ exact Hh | apply H ]. Qed.

  Lemma kinds_rename_q_dm : forall φ ρ ρ' d d' t t' h h' U U', kinds_rename φ ρ ρ' -> kinds_equiv h h' ->
      kinds_rename (wk_q φ) (de_dm d t h U :: ρ) (de_dm d' t' h' U' :: ρ').
  Proof. intros * H Hh [| x]; cbn [wk_q]; [ exact Hh | apply H ]. Qed.

  Lemma kinds_rename_pad : forall n φ ρ ρ', kinds_rename φ ρ ρ' -> kinds_rename (wk_qn n φ) (kinds_pads n ρ) (kinds_pads n ρ').
  Proof.
    induction n as [| n IH]; intros * H; [ exact H |].
    cbn [wk_qn]; apply kinds_rename_q_term; exact (IH _ _ _ H).
  Qed.

  (** An environment over another, read past its own entries. *)
  Lemma env_mod_app_shift : forall ρ0 ρ x, env_mod (ρ0 ++ ρ) (x + List.length ρ0) = env_mod ρ x.
  Proof.
    induction ρ0 as [| e ρ0 IH]; intros; cbn [List.length app]; [ rewrite Nat.add_0_r; reflexivity |].
    rewrite Nat.add_succ_r; apply IH.
  Qed.

  Lemma kinds_rename_shift_app : forall ρ0 ρ, kinds_rename (wk_shiftn (List.length ρ0)) (ρ0 ++ ρ) ρ.
  Proof. intros * x; cbn [wk_shiftn]; rewrite env_mod_app_shift; apply kinds_equiv_refl. Qed.

  Lemma kinds_rename_comp : forall φ ψ ρ1 ρ2 ρ3, kinds_rename φ ρ1 ρ2 -> kinds_rename ψ ρ2 ρ3 -> kinds_rename (ψ ⊙ φ) ρ1 ρ3.
  Proof. intros * H1 H2 x; cbn [wk_compose]; eapply kinds_equiv_trans; [ apply H1 | apply H2 ]. Qed.

  (** A unit's kinds are its definition's, under placeholders for its
      parameters. *)
  Lemma gunit_member_kind_pad : forall ρ Δ D ch k,
      gunit_member_kind Θ Ξ ρ (gu_mk Δ D) ch k <-> gunit_member_kind Θ Ξ (kinds_pads (List.length Δ) ρ) (gu_mk nil D) ch k.
  Proof.
    intros; split; intros H; inversion H; subst;
      first [ eapply gunit_member_kind_self | eapply gunit_member_kind_def; eassumption | eapply gunit_member_kind_mod; eassumption | eapply gunit_member_kind_dm_here; eassumption
            | eapply gunit_member_kind_dm_step; eassumption | eapply gunit_member_kind_alias; eassumption ].
  Qed.

  (** *** Lookups Past an Entry *)

  Lemma gunit_member_kind_body_ext_other : forall ρ sm Φ x E y ch k, y <> x ->
      gunit_member_kind Θ Ξ ρ (gu_mk nil (md_body sm (gm_ext Φ x E))) (y :: ch) k <->
      gunit_member_kind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k.
  Proof.
    intros * Hne.
    assert (Ey : String.eqb y x = false) by (apply String.eqb_neq; exact Hne).
    split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ey in *;
      solve [ econstructor; try (cbn [gm_prefix_upto gm_item_upto]; rewrite ?Ey); eassumption ].
  Qed.

  Lemma gunit_member_kind_body_open_other : forall ρ sm Φ H its y ch k, items_upto y its = None ->
      gunit_member_kind Θ Ξ ρ (gu_mk nil (md_body sm (gm_open Φ H its))) (y :: ch) k <->
      gunit_member_kind Θ Ξ ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k.
  Proof.
    intros * Hn.
    assert (Ey : existsb (String.eqb y) (map import_item_name its) = false).
    { destruct (existsb _ _) eqn:E; [| reflexivity ].
      exfalso; clear - E Hn; induction its as [| it its IH]; cbn in *; [ discriminate |].
      destruct (items_upto y its) as [[] |]; [ discriminate |].
      apply Bool.orb_true_iff in E as [E | E]; [ rewrite E in Hn; discriminate | auto ]. }
    split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ey, ?Hn in *;
      solve [ econstructor; try (cbn [gm_prefix_upto gm_item_upto]; rewrite ?Ey, ?Hn); eassumption ].
  Qed.

  (** *** The Selections of a Module Expression *)

  Lemma modexp_member_kind_unit_iff : forall ρ ρ' fp ch k, modexp_member_kind Θ Ξ ρ (me_unit fp) ch k <-> modexp_member_kind Θ Ξ ρ' (me_unit fp) ch k.
  Proof. intros; split; intros H; inversion H; subst; constructor; assumption. Qed.

  Lemma modexp_member_kind_var_iff : forall ρ x ch k, modexp_member_kind Θ Ξ ρ (me_var x) ch k <-> dmod_member_kind Θ Ξ (env_mod ρ x) ch k.
  Proof. intros; split; intros H; [ inversion H; subst; assumption | constructor; assumption ]. Qed.

  (** A selection: by the longer chain, but a member with a term part and
      a module part, selected as a module, is a module. *)
  Lemma modexp_member_kind_mem_iff : forall ρ H y ch k, modexp_member_kind Θ Ξ ρ (me_mem H y) ch k <->
      (modexp_member_kind Θ Ξ ρ H (y :: ch) k /\ (ch <> nil \/ k <> member_kind_dm)) \/
      (ch = nil /\ k = member_kind_mod /\ modexp_member_kind Θ Ξ ρ H (y :: nil) member_kind_dm).
  Proof.
    intros; split; intros Hk.
    - inversion Hk; subst; [ left; split; assumption | right; repeat split; assumption ].
    - destruct Hk as [[Hk Hc] | (-> & -> & Hk)]; [ apply modexp_member_kind_mem; assumption | apply modexp_member_kind_mem_dm; exact Hk ].
  Qed.

  (** Away from the empty chain, a selection is read by the longer chain. *)
  Lemma modexp_member_kind_mem_cons_iff : forall ρ H y c ch k, modexp_member_kind Θ Ξ ρ (me_mem H y) (c :: ch) k <-> modexp_member_kind Θ Ξ ρ H (y :: c :: ch) k.
  Proof.
    intros; rewrite modexp_member_kind_mem_iff; split; [ intros [[Hk _] | (? & _)]; [ exact Hk | discriminate ] |].
    intros Hk; left; split; [ exact Hk | left; discriminate ].
  Qed.

  (** A submodule closure: by the longer chain, but a member with a term
      part and a module part, selected as a module, is a module. *)
  Lemma dmod_member_kind_member_iff : forall h ch0 ch k, dmod_member_kind Θ Ξ (dm_member h ch0) ch k <->
      (dmod_member_kind Θ Ξ h (ch0 ++ ch) k /\ (ch <> nil \/ k <> member_kind_dm)) \/
      (ch = nil /\ k = member_kind_mod /\ dmod_member_kind Θ Ξ h ch0 member_kind_dm).
  Proof.
    intros; split; intros Hk.
    - inversion Hk; subst; [ left; split; assumption | right; repeat split; assumption ].
    - destruct Hk as [[Hk Hc] | (-> & -> & Hk)]; [ apply dmod_member_kind_member; assumption | apply dmod_member_kind_member_dm; exact Hk ].
  Qed.

  Lemma dmod_member_kind_member_cons_iff : forall h ch0 c ch k, dmod_member_kind Θ Ξ (dm_member h ch0) (c :: ch) k <-> dmod_member_kind Θ Ξ h (ch0 ++ c :: ch) k.
  Proof.
    intros; rewrite dmod_member_kind_member_iff; split; [ intros [[Hk _] | (? & _)]; [ exact Hk | discriminate ] |].
    intros Hk; left; split; [ exact Hk | left; discriminate ].
  Qed.

  (** At the empty chain, nothing is a member with a term part and a
      module part: a value, a unit and a module expression are what they
      are, not members of something. *)
  Lemma kind_nil_not_dm :
    (forall h ch k, dmod_member_kind Θ Ξ h ch k -> ch = nil -> k <> member_kind_dm) /\
    (forall ρ U ch k, gunit_member_kind Θ Ξ ρ U ch k -> ch = nil -> k <> member_kind_dm) /\
    (forall ρ H ch k, modexp_member_kind Θ Ξ ρ H ch k -> ch = nil -> k <> member_kind_dm) /\
    (forall ρ Φ ρ1, kinds_env Θ Ξ ρ Φ ρ1 -> True).
  Proof.
    apply kind_mut_ind; intros; try exact I; subst; try discriminate; try (intros Hd; discriminate Hd);
      try (match goal with H : ?l ++ nil = nil -> _ |- _ => rewrite List.app_nil_r in H end);
      try (match goal with H : (@nil ?T) <> nil \/ _ |- _ =>
             destruct H as [H | H]; [ exfalso; exact (H eq_refl) | exact H ] end);
      eauto.
  Qed.

  Corollary dmod_member_kind_nil_not_dm : forall h k, dmod_member_kind Θ Ξ h nil k -> k <> member_kind_dm.
  Proof. intros * Hk; exact (proj1 kind_nil_not_dm _ _ _ Hk eq_refl). Qed.

  (** The submodule closure at the empty chain is the module itself. *)
  Lemma dmod_member_kind_member_nil : forall h ch k, dmod_member_kind Θ Ξ (dm_member h nil) ch k <-> dmod_member_kind Θ Ξ h ch k.
  Proof.
    intros; rewrite dmod_member_kind_member_iff; cbn [app]; split.
    - intros [[Hk _] | (_ & _ & Hk)]; [ exact Hk | exfalso; exact (dmod_member_kind_nil_not_dm _ _ Hk eq_refl) ].
    - intros Hk; left; split; [ exact Hk |].
      destruct ch as [| c ch]; [ right; exact (dmod_member_kind_nil_not_dm _ _ Hk) | left; discriminate ].
  Qed.

  (** A submodule closure read through a selection that has the kinds of
      a one-name submodule closure. *)
  Lemma dmod_member_kind_member_snoc : forall h h1 y,
      (forall ch k, dmod_member_kind Θ Ξ h1 ch k <-> dmod_member_kind Θ Ξ (dm_member h (y :: nil)) ch k) ->
      forall ch0 ch k, dmod_member_kind Θ Ξ (dm_member h1 ch0) ch k <-> dmod_member_kind Θ Ξ (dm_member h (y :: ch0)) ch k.
  Proof.
    intros * Hh1 [| c0 ch0] ch k; [ rewrite dmod_member_kind_member_nil; apply Hh1 |].
    rewrite (dmod_member_kind_member_iff h1), (dmod_member_kind_member_iff h (y :: c0 :: ch0)), (Hh1 ((c0 :: ch0) ++ ch)), (Hh1 (c0 :: ch0)).
    cbn [app]; rewrite !dmod_member_kind_member_cons_iff; reflexivity.
  Qed.

  Lemma modexp_member_kind_app_iff : forall ρ H N ch k, modexp_member_kind Θ Ξ ρ (me_app H N) ch k <-> modexp_member_kind Θ Ξ ρ H ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  Lemma modexp_member_kind_lit_iff : forall ρ U ch k, modexp_member_kind Θ Ξ ρ (me_lit U) ch k <-> gunit_member_kind Θ Ξ ρ U ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  Lemma dmod_member_kind_local_iff : forall Δ D ρ ch k, dmod_member_kind Θ Ξ (dm_local Δ D ρ) ch k <-> gunit_member_kind Θ Ξ ρ (gu_mk Δ D) ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  Lemma dmod_member_kind_clo_iff : forall U ρ ch k, dmod_member_kind Θ Ξ (dm_clo U ρ) ch k <-> gunit_member_kind Θ Ξ ρ U ch k.
  Proof. intros [Δ D] *; apply dmod_member_kind_local_iff. Qed.

  Lemma gunit_member_kind_alias_iff : forall ρ E ch k, gunit_member_kind Θ Ξ ρ (gu_mk nil (md_alias E)) ch k <-> modexp_member_kind Θ Ξ ρ E ch k.
  Proof. intros; split; intros Hk; [ inversion Hk; subst; assumption | constructor; assumption ]. Qed.

  (** A module named by its path has its kinds at every environment, and
      so does the closure of its alias: an inductive or a record type's
      module, as a body binds it ([kinds_body_entry]). *)
  Lemma modexp_member_kind_qname_mod : forall p ρ ρ' ch k,
      modexp_member_kind Θ Ξ ρ (qname_mod p) ch k <-> modexp_member_kind Θ Ξ ρ' (qname_mod p) ch k.
  Proof.
    intros [fp pre]; unfold qname_mod; cbn [q_unit q_chain].
    assert (Hg : forall ys E0, (forall ρ ρ' ch k, modexp_member_kind Θ Ξ ρ E0 ch k <-> modexp_member_kind Θ Ξ ρ' E0 ch k) ->
               forall ρ ρ' ch k, modexp_member_kind Θ Ξ ρ (me_mems E0 ys) ch k <-> modexp_member_kind Θ Ξ ρ' (me_mems E0 ys) ch k).
    { intros ys; induction ys as [| y ys IH]; intros E0 HE0; cbn [me_mems]; [ exact HE0 |].
      apply IH; intros ρ ρ' ch k; rewrite !modexp_member_kind_mem_iff, (HE0 ρ ρ'), (HE0 ρ ρ'); reflexivity. }
    apply Hg; intros; apply modexp_member_kind_unit_iff.
  Qed.

  Lemma kinds_equiv_qname_mod_clo : forall p ρ ρ',
      kinds_equiv (dm_clo (gu_mk nil (md_alias (qname_mod p))) ρ) (dm_clo (gu_mk nil (md_alias (qname_mod p))) ρ').
  Proof.
    intros * ch k; rewrite !dmod_member_kind_clo_iff, !gunit_member_kind_alias_iff; apply modexp_member_kind_qname_mod.
  Qed.

  (** *** Generated Entries Under a Renaming *)

  Definition kinds_rename_mod (H : modexp) : Prop :=
    forall φ ρ ρ', kinds_rename φ ρ ρ' -> forall ch k, modexp_member_kind Θ Ξ ρ (modexp_wk H φ) ch k <-> modexp_member_kind Θ Ξ ρ' H ch k.

  (** *** A Weakening Has the Kinds of What It Weakens *)

  Definition kinds_rename_unit (U : gunit) : Prop :=
    forall φ ρ ρ', kinds_rename φ ρ ρ' -> forall ch k, gunit_member_kind Θ Ξ ρ (gunit_wk U φ) ch k <-> gunit_member_kind Θ Ξ ρ' U ch k.

  Definition kinds_rename_def (D : moddef) : Prop :=
    forall φ ρ ρ', kinds_rename φ ρ ρ' -> forall ch k,
      gunit_member_kind Θ Ξ ρ (gu_mk nil (moddef_wk D φ)) ch k <-> gunit_member_kind Θ Ξ ρ' (gu_mk nil D) ch k.

  (** A body read by kinds at a renamed environment, against the body
      renamed: the environments it makes, both ways, and its members. *)
  Record kinds_rename_body_at (Φ : gmod) (φ : wk) (ρ ρ' : env) : Prop := mk_kinds_rename_body_at
    { kinds_rename_body_at_fwd : forall ρ1', kinds_env Θ Ξ ρ' Φ ρ1' -> exists ρ1, kinds_env Θ Ξ ρ (gmod_wk Φ φ) ρ1 /\ kinds_rename (wk_qn (gm_binders Φ) φ) ρ1 ρ1'
    ; kinds_rename_body_at_bwd : forall ρ1, kinds_env Θ Ξ ρ (gmod_wk Φ φ) ρ1 -> exists ρ1', kinds_env Θ Ξ ρ' Φ ρ1' /\ kinds_rename (wk_qn (gm_binders Φ) φ) ρ1 ρ1'
    ; kinds_rename_body_at_kind : forall sm x ch k, gunit_member_kind Θ Ξ ρ (gu_mk nil (md_body sm (gmod_wk Φ φ))) (x :: ch) k <->
        gunit_member_kind Θ Ξ ρ' (gu_mk nil (md_body sm Φ)) (x :: ch) k }.

  Definition kinds_rename_body (Φ : gmod) : Prop :=
    forall φ ρ ρ', kinds_rename φ ρ ρ' -> kinds_rename_body_at Φ φ ρ ρ'.

  Definition kinds_rename_entry (E : gentry) : Prop :=
    match E with
    | ge_mod _ U | ge_def_mod _ _ _ U => kinds_rename_unit U
    | _ => True
    end.

  #[local] Ltac kinds_rename_ih :=
    match goal with IH : forall φ ρ ρ', kinds_rename φ ρ ρ' -> _, Hr : kinds_rename _ _ _ |- _ => apply IH; exact Hr end.

  Lemma kind_rename :
    (forall H, kinds_rename_mod H) /\ (forall U, kinds_rename_unit U) /\ (forall D, kinds_rename_def D) /\ (forall Φ, kinds_rename_body Φ).
  Proof.
    cut ((forall M : exp, True) /\ (forall H, kinds_rename_mod H) /\ (forall b : binding, True) /\ (forall U, kinds_rename_unit U) /\
         (forall D, kinds_rename_def D) /\ (forall Φ, kinds_rename_body Φ) /\ (forall E, kinds_rename_entry E) /\ (forall e : centry, True));
      [ intros (_ & H1 & _ & H2 & H3 & H4 & _); auto |].
    apply (syn_mut_ind (fun _ => True) kinds_rename_mod (fun _ => True) kinds_rename_unit kinds_rename_def kinds_rename_body kinds_rename_entry (fun _ => True));
      intros; try exact I; unfold kinds_rename_mod, kinds_rename_unit, kinds_rename_def, kinds_rename_body, kinds_rename_entry in *.
    - (* a unit *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; apply modexp_member_kind_unit_iff.
    - (* a slot *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !modexp_member_kind_var_iff; apply Hφ.
    - (* a selection *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !modexp_member_kind_mem_iff;
        match goal with IH : forall φ ρ ρ', kinds_rename φ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hφ), (IH _ _ _ Hφ); reflexivity end.
    - (* an application *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !modexp_member_kind_app_iff; kinds_rename_ih.
    - (* a literal *)
      intros φ ρ ρ' Hφ ch kk; cbn [modexp_wk]; rewrite !modexp_member_kind_lit_iff; kinds_rename_ih.
    - (* a unit: its definition under its parameters *)
      intros φ ρ ρ' Hφ ch kk; rewrite gunit_wk_mk, (gunit_member_kind_pad ρ (tele_wk Δ φ)), (gunit_member_kind_pad ρ' Δ), length_tele_wk.
      match goal with IH : forall φ ρ ρ', kinds_rename φ ρ ρ' -> _ |- _ => apply IH end; apply kinds_rename_pad; exact Hφ.
    - (* a body *)
      intros φ ρ ρ' Hφ ch kk; cbn [moddef_wk].
      destruct ch as [| x ch].
      + split; intros Hk; inversion Hk; subst; constructor.
      + match goal with IH : forall φ ρ ρ', kinds_rename φ ρ ρ' -> _ |- _ => apply (IH _ _ _ Hφ) end.
    - (* an alias *)
      intros φ ρ ρ' Hφ ch kk; cbn [moddef_wk]; rewrite !gunit_member_kind_alias_iff;
        match goal with IH : forall φ ρ ρ', kinds_rename φ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hφ); reflexivity end.
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
        eexists; split; [ apply kinds_env_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_wk kinds_body_entry];
          try (apply kinds_rename_q_term; exact Hr1);
          try (apply kinds_rename_q_mod; [ exact Hr1 | apply kinds_equiv_qname_mod_clo ]);
          try ((first [ apply kinds_rename_q_mod | apply kinds_rename_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dmod_member_kind_clo_iff; apply IHE; exact Hr1 ]).
      + intros ρa Hk; cbn [gmod_wk] in Hk; inversion Hk; subst; cbn [gm_binders wk_qn].
        destruct (IH2 _ ltac:(eassumption)) as (ρb & Hk1 & Hr1).
        eexists; split; [ apply kinds_env_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_wk kinds_body_entry];
          try (apply kinds_rename_q_term; exact Hr1);
          try (apply kinds_rename_q_mod; [ exact Hr1 | apply kinds_equiv_qname_mod_clo ]);
          try ((first [ apply kinds_rename_q_mod | apply kinds_rename_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dmod_member_kind_clo_iff; apply IHE; exact Hr1 ]).
      + intros sm0 y ch kk; cbn [gmod_wk].
        destruct (String.eqb_spec y x) as [-> | Hne];
          [| rewrite (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ Hne), gunit_member_kind_body_ext_other by exact Hne; apply IH3 ].
        assert (Ex : String.eqb x x = true) by apply String.eqb_refl.
        split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto gmod_wk] in *; rewrite ?Ex in *;
          try discriminate.
        * destruct E as [b0 pv0 r0 A0 B0 | | | |]; cbn in *; try congruence;
            match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def _ _ _ _ _)) |- _ => injection Hp; intros; subst end;
            eapply gunit_member_kind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn [gentry_wk] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ (gmod_wk Φ φ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply gunit_member_kind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_wk] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ (gmod_wk Φ φ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_wk] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ (gmod_wk Φ φ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [b0 pv0 r0 A0 B0 | | | |]; cbn in *; try congruence;
            match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def _ _ _ _ _)) |- _ => injection Hp; intros; subst end;
            eapply gunit_member_kind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply gunit_member_kind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
    - (* an unexpanded open: kinds read no environment through it, and
         none of the names its items declare *)
      intros φ ρ ρ' Hφ; rename H0 into IHΦ; destruct (IHΦ _ _ _ Hφ) as [IH1 IH2 IH3].
      constructor; [ intros ρ2' Hk; inversion Hk | intros ρ2 Hk; cbn [gmod_wk] in Hk; inversion Hk |].
      intros sm0 y ch kk; cbn [gmod_wk].
      destruct (items_upto y its) as [[its1 it] |] eqn:Ey;
        [| rewrite (gunit_member_kind_body_open_other _ _ _ _ _ _ _ _ Ey), gunit_member_kind_body_open_other by exact Ey; apply IH3 ].
      assert (Hex : existsb (String.eqb y) (map import_item_name its) = true) by (eapply items_upto_some; exact Ey).
      split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gmod_wk] in *; rewrite ?Hex in *; discriminate.
    - (* a submodule entry *) exact H.
    - (* a definition with a module part: its module part *) exact H1.
  Qed.


  (** *** A Substitution Has the Kinds of What It Substitutes

      As a renaming, a substitution that sends each slot to a module
      expression with the kinds of the original environment's entry there:
      terms are never looked at. *)

  Definition kinds_sub (σ : sub) (ρ ρ' : env) : Prop :=
    forall x ch k, modexp_member_kind Θ Ξ ρ (sentry_modexp (σ x)) ch k <-> dmod_member_kind Θ Ξ (env_mod ρ' x) ch k.

  Lemma kinds_sub_q_term : forall σ ρ ρ' d d' t t', kinds_sub σ ρ ρ' -> kinds_sub (sb_q σ) (de_term d t :: ρ) (de_term d' t' :: ρ').
  Proof.
    intros * H [| x] ch k; rewrite ?sb_q_zero, ?sb_q_succ; cbn [sentry_modexp].
    - rewrite modexp_member_kind_var_iff; reflexivity.
    - rewrite <- sentry_modexp_wk, (proj1 kind_rename _ wk_shift (de_term d t :: ρ) ρ (fun x => kinds_equiv_refl _)).
      apply H.
  Qed.

  Lemma kinds_sub_q_mod : forall σ ρ ρ' h h' U U', kinds_sub σ ρ ρ' -> kinds_equiv h h' ->
      kinds_sub (sb_q σ) (de_mod h U :: ρ) (de_mod h' U' :: ρ').
  Proof.
    intros * H Hh [| x] ch k; rewrite ?sb_q_zero, ?sb_q_succ; cbn [sentry_modexp].
    - rewrite modexp_member_kind_var_iff; apply Hh.
    - rewrite <- sentry_modexp_wk, (proj1 kind_rename _ wk_shift (de_mod h U :: ρ) ρ (fun x => kinds_equiv_refl _)).
      apply H.
  Qed.

  Lemma kinds_sub_q_dm : forall σ ρ ρ' d d' t t' h h' U U', kinds_sub σ ρ ρ' -> kinds_equiv h h' ->
      kinds_sub (sb_q σ) (de_dm d t h U :: ρ) (de_dm d' t' h' U' :: ρ').
  Proof.
    intros * H Hh [| x] ch k; rewrite ?sb_q_zero, ?sb_q_succ; cbn [sentry_modexp].
    - rewrite modexp_member_kind_var_iff; apply Hh.
    - rewrite <- sentry_modexp_wk, (proj1 kind_rename _ wk_shift (de_dm d t h U :: ρ) ρ (fun x => kinds_equiv_refl _)).
      apply H.
  Qed.

  Lemma kinds_sub_pad : forall n σ ρ ρ', kinds_sub σ ρ ρ' -> kinds_sub (sb_qn n σ) (kinds_pads n ρ) (kinds_pads n ρ').
  Proof.
    induction n as [| n IH]; intros * H; [ exact H |].
    cbn [sb_qn kinds_pads repeat app]; apply kinds_sub_q_term; exact (IH _ _ _ H).
  Qed.

  Lemma kinds_sub_ext : forall σ ψ ρ ρ', sb_eq σ ψ -> kinds_sub σ ρ ρ' -> kinds_sub ψ ρ ρ'.
  Proof. intros * E H x; rewrite <- (E x); apply H. Qed.

  Definition kinds_sub_mod (H : modexp) : Prop :=
    forall σ ρ ρ', kinds_sub σ ρ ρ' -> forall ch k, modexp_member_kind Θ Ξ ρ H[σ]ᵐ ch k <-> modexp_member_kind Θ Ξ ρ' H ch k.

  Definition kinds_sub_unit (U : gunit) : Prop :=
    forall σ ρ ρ', kinds_sub σ ρ ρ' -> forall ch k, gunit_member_kind Θ Ξ ρ U[σ]ᵘ ch k <-> gunit_member_kind Θ Ξ ρ' U ch k.

  Definition kinds_sub_def (D : moddef) : Prop :=
    forall σ ρ ρ', kinds_sub σ ρ ρ' -> forall ch k,
      gunit_member_kind Θ Ξ ρ (gu_mk nil (moddef_sub D σ)) ch k <-> gunit_member_kind Θ Ξ ρ' (gu_mk nil D) ch k.

  (** The same at a substituted environment, against the body
      substituted. *)
  Record kinds_sub_body_at (Φ : gmod) (σ : sub) (ρ ρ' : env) : Prop := mk_kinds_sub_body_at
    { kinds_sub_body_at_fwd : forall ρ1', kinds_env Θ Ξ ρ' Φ ρ1' -> exists ρ1, kinds_env Θ Ξ ρ (gmod_sub Φ σ) ρ1 /\ kinds_sub (sb_qn (gm_binders Φ) σ) ρ1 ρ1'
    ; kinds_sub_body_at_bwd : forall ρ1, kinds_env Θ Ξ ρ (gmod_sub Φ σ) ρ1 -> exists ρ1', kinds_env Θ Ξ ρ' Φ ρ1' /\ kinds_sub (sb_qn (gm_binders Φ) σ) ρ1 ρ1'
    ; kinds_sub_body_at_kind : forall sm x ch k, gunit_member_kind Θ Ξ ρ (gu_mk nil (md_body sm (gmod_sub Φ σ))) (x :: ch) k <->
        gunit_member_kind Θ Ξ ρ' (gu_mk nil (md_body sm Φ)) (x :: ch) k }.

  Definition kinds_sub_body (Φ : gmod) : Prop :=
    forall σ ρ ρ', kinds_sub σ ρ ρ' -> kinds_sub_body_at Φ σ ρ ρ'.

  Definition kinds_sub_entry (E : gentry) : Prop :=
    match E with
    | ge_mod _ U | ge_def_mod _ _ _ U => kinds_sub_unit U
    | _ => True
    end.

  #[local] Ltac kinds_sub_ih :=
    match goal with IH : forall σ ρ ρ', kinds_sub σ ρ ρ' -> _, Hr : kinds_sub _ _ _ |- _ => apply IH; exact Hr end.

  Lemma kind_sub :
    (forall H, kinds_sub_mod H) /\ (forall U, kinds_sub_unit U) /\ (forall D, kinds_sub_def D) /\ (forall Φ, kinds_sub_body Φ).
  Proof.
    cut ((forall M : exp, True) /\ (forall H, kinds_sub_mod H) /\ (forall b : binding, True) /\ (forall U, kinds_sub_unit U) /\
         (forall D, kinds_sub_def D) /\ (forall Φ, kinds_sub_body Φ) /\ (forall E, kinds_sub_entry E) /\ (forall e : centry, True));
      [ intros (_ & H1 & _ & H2 & H3 & H4 & _); auto |].
    apply (syn_mut_ind (fun _ => True) kinds_sub_mod (fun _ => True) kinds_sub_unit kinds_sub_def kinds_sub_body kinds_sub_entry (fun _ => True));
      intros; try exact I; unfold kinds_sub_mod, kinds_sub_unit, kinds_sub_def, kinds_sub_body, kinds_sub_entry in *.
    - (* a unit *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; apply modexp_member_kind_unit_iff.
    - (* a slot *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite modexp_member_kind_var_iff; apply Hσ.
    - (* a selection *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite !modexp_member_kind_mem_iff;
        match goal with IH : forall σ ρ ρ', kinds_sub σ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hσ), (IH _ _ _ Hσ); reflexivity end.
    - (* an application *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite !modexp_member_kind_app_iff; kinds_sub_ih.
    - (* a literal *)
      intros σ ρ ρ' Hσ ch kk; cbn [modexp_sub]; rewrite !modexp_member_kind_lit_iff; kinds_sub_ih.
    - (* a unit: its definition under its parameters *)
      intros σ ρ ρ' Hσ ch kk; rewrite gunit_sub_mk, (gunit_member_kind_pad ρ (tele_sub Δ σ)), (gunit_member_kind_pad ρ' Δ), length_tele_sub.
      match goal with IH : forall σ ρ ρ', kinds_sub σ ρ ρ' -> _ |- _ => apply IH end; apply kinds_sub_pad; exact Hσ.
    - (* a body *)
      intros σ ρ ρ' Hσ ch kk; cbn [moddef_sub].
      destruct ch as [| x ch].
      + split; intros Hk; inversion Hk; subst; constructor.
      + match goal with IH : forall σ ρ ρ', kinds_sub σ ρ ρ' -> _ |- _ => apply (IH _ _ _ Hσ) end.
    - (* an alias *)
      intros σ ρ ρ' Hσ ch kk; cbn [moddef_sub]; rewrite !gunit_member_kind_alias_iff;
        match goal with IH : forall σ ρ ρ', kinds_sub σ ρ ρ' -> _ |- _ => rewrite (IH _ _ _ Hσ); reflexivity end.
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
        eexists; split; [ apply kinds_env_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_sub kinds_body_entry];
          try (apply kinds_sub_q_term; exact Hr1);
          try (apply kinds_sub_q_mod; [ exact Hr1 | apply kinds_equiv_qname_mod_clo ]);
          try ((first [ apply kinds_sub_q_mod | apply kinds_sub_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dmod_member_kind_clo_iff; apply IHE; exact Hr1 ]).
      + intros ρa Hk; cbn [gmod_sub] in Hk; inversion Hk; subst; cbn [gm_binders sb_qn].
        destruct (IH2 _ ltac:(eassumption)) as (ρb & Hk1 & Hr1).
        eexists; split; [ apply kinds_env_ext; exact Hk1 |].
        destruct E as [b pv A B | pm U | pv D Φd | pv Δa pa Nsa | pr Rr Φr]; cbn [gentry_sub kinds_body_entry];
          try (apply kinds_sub_q_term; exact Hr1);
          try (apply kinds_sub_q_mod; [ exact Hr1 | apply kinds_equiv_qname_mod_clo ]);
          try ((first [ apply kinds_sub_q_mod | apply kinds_sub_q_dm ]);
               [ exact Hr1 | intros ch0 k0; rewrite !dmod_member_kind_clo_iff; apply IHE; exact Hr1 ]).
      + intros sm0 y ch kk; cbn [gmod_sub].
        destruct (String.eqb_spec y x) as [-> | Hne];
          [| rewrite (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ Hne), gunit_member_kind_body_ext_other by exact Hne; apply IH3 ].
        assert (Ex : String.eqb x x = true) by apply String.eqb_refl.
        split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gm_item_upto gmod_sub] in *; rewrite ?Ex in *;
          try discriminate.
        * destruct E as [b0 pv0 r0 A0 B0 | | | |]; cbn in *; try congruence;
            match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def _ _ _ _ _)) |- _ => injection Hp; intros; subst end;
            eapply gunit_member_kind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn [gentry_sub] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ (gmod_sub Φ σ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply gunit_member_kind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_sub] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ (gmod_sub Φ σ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn [gentry_sub] in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ (gmod_sub Φ σ) _ |- _ => destruct (IH2 _ Hk1) as (ρb & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [b0 pv0 r0 A0 B0 | | | |]; cbn in *; try congruence;
            match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def _ _ _ _ _)) |- _ => injection Hp; intros; subst end;
            eapply gunit_member_kind_def; cbn; rewrite Ex; reflexivity.
        * destruct E as [| pm0 U0 | | |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_mod _ _)) |- _ => injection Hp as <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply gunit_member_kind_mod; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_here; [ cbn; rewrite Ex; reflexivity | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
        * destruct E as [| | | pv0 A0 M0 U0 |]; cbn in *; try congruence.
          match goal with Hp : Some _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- _ => injection Hp as <- <- <- <- <- end.
          match goal with Hk1 : kinds_env _ _ _ Φ _ |- _ => destruct (IH1 _ Hk1) as (ρa & Hk1' & Hr1) end.
          eapply gunit_member_kind_dm_step; [ cbn; rewrite Ex; reflexivity | assumption | exact Hk1' |].
          apply (IHE _ _ _ Hr1); assumption.
    - (* an unexpanded open: kinds read no environment through it, and
         none of the names its items declare *)
      intros σ ρ ρ' Hσ; rename H0 into IHΦ; destruct (IHΦ _ _ _ Hσ) as [IH1 IH2 IH3].
      constructor; [ intros ρ2' Hk; inversion Hk | intros ρ2 Hk; cbn [gmod_sub] in Hk; inversion Hk |].
      intros sm0 y ch kk; cbn [gmod_sub].
      destruct (items_upto y its) as [[its1 it] |] eqn:Ey;
        [| rewrite (gunit_member_kind_body_open_other _ _ _ _ _ _ _ _ Ey), gunit_member_kind_body_open_other by exact Ey; apply IH3 ].
      assert (Hex : existsb (String.eqb y) (map import_item_name its) = true) by (eapply items_upto_some; exact Ey).
      split; intros Hk; inversion Hk; subst; cbn [gm_prefix_upto gmod_sub] in *; rewrite ?Hex in *; discriminate.
    - (* a submodule entry *) exact H.
    - (* a definition with a module part: its module part *) exact H1.
  Qed.

End Kinds.
