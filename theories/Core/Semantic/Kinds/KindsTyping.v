(** * The Kinds of Typed Members

    The kinds evaluation reads off module values ([dmod_member_kind], [gunit_member_kind],
    [modexp_member_kind]) are read in an environment whose module entries have the kinds
    of the units their context's slots hold ([kinds_match]); the entries the
    kinds read off an open are those it generates, with the types left out
    ([generated_item_erase], [kinds_match_gens]). *)

From Stdlib Require Import Lia List PeanoNat String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic.Kinds Require Import Kinds.
Import Domain_Notations Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Generated Entries *)

Lemma gens_append_app : forall gs1 gs2 Φ k,
    gens_append Φ k (gs1 ++ gs2) = gens_append (gens_append Φ k gs1) (k + List.length gs1) gs2.
Proof.
  induction gs1 as [| g gs1 IH]; intros; cbn [app gens_append List.length]; [ rewrite Nat.add_0_r; reflexivity |].
  destruct (generated_item_entry g) as [d E]; rewrite IH, Nat.add_succ_r; reflexivity.
Qed.

Lemma gens_append_snoc : forall gs g Φ k,
    gens_append Φ k (gs ++ g :: nil) =
    gm_ext (gens_append Φ k gs) (generated_item_name g) (gentry_wk (snd (generated_item_entry g)) (wk_shiftn (k + List.length gs))).
Proof.
  intros; rewrite gens_append_app; cbn [gens_append]; unfold generated_item_name; destruct (generated_item_entry g); reflexivity.
Qed.

Lemma items_upto_none_iff : forall x its, items_upto x its = None -> existsb (String.eqb x) (map import_item_name its) = false.
Proof.
  induction its as [| it its IH]; intros H; cbn in *; [ reflexivity |].
  destruct (items_upto x its) as [[] |]; [ discriminate |].
  destruct (String.eqb x (import_item_name it)); [ discriminate |]; cbn; auto.
Qed.

(** Past the names an open declares, the generated entries are skipped. *)
Lemma gens_prefix_none : forall gs Φ k y, existsb (String.eqb y) (map generated_item_name gs) = false ->
    gm_prefix_upto (gens_append Φ k gs) y = gm_prefix_upto Φ y.
Proof.
  induction gs as [| g gs IH]; intros * Hn; cbn [gens_append]; [ reflexivity |].
  cbn [map existsb] in Hn; apply Bool.orb_false_iff in Hn as [Hy Hn].
  unfold generated_item_name in Hy; destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [fst] in Hy.
  rewrite IH by exact Hn; cbn [gm_prefix_upto]; rewrite Hy; reflexivity.
Qed.

(** The entry generated for the last item declaring [y]. *)
Lemma gens_prefix_some : forall Θ Ξ Γ H its gs, items_gen Θ Ξ Γ H its gs ->
    forall y its1 it, items_upto y its = Some (its1, it) ->
    exists its0 gs0 g, its1 = its0 ++ it :: nil /\ items_gen Θ Ξ Γ H its0 gs0 /\
      items_gen Θ Ξ Γ H (it :: nil) (g :: nil) /\
      (exists R Rg, its = its1 ++ R /\ gs = gs0 ++ g :: Rg) /\
      forall Φ k, gm_prefix_upto (gens_append Φ k gs) y = Some (gens_append Φ k (gs0 ++ g :: nil)).
Proof.
  intros * Hg; induction Hg as [| | | | ]; intros y its1 it0 Hu; cbn [items_upto] in Hu; try discriminate.
  all: destruct (items_upto y its) as [[its1' it1] |] eqn:Eu.
  all: try (injection Hu as <- <-;
            destruct (IHHg _ _ _ Eu) as (its0 & gs0 & g0 & -> & Hg0 & Hg1 & (Rits & Rg & -> & ->) & Hp);
            eexists (_ :: its0), (_ :: gs0), g0; split; [ reflexivity |]; split; [ econstructor; eassumption |];
            split; [ exact Hg1 |]; split; [ exists Rits, Rg; split; reflexivity |];
            intros Φ kk; cbn [gens_append app]; apply Hp).
  all: match type of Hu with context [String.eqb ?a ?b] => destruct (String.eqb a b) eqn:Ey end; [| discriminate ]; injection Hu as <- <-.
  all: pose proof (items_upto_none_iff _ _ Eu) as Hn; rewrite <- (items_gen_names _ _ _ _ _ _ Hg) in Hn.
  all: eexists nil, nil, _; split; [ reflexivity |]; split; [ constructor |].
  all: split; [ solve [ econstructor; eauto using items_gen_nil ] |].
  all: split; [ eexists _, _; split; reflexivity |].
  all: intros Φ kk; cbn [gens_append app generated_item_entry]; rewrite gens_prefix_none by exact Hn;
         cbn [gm_prefix_upto import_item_name] in *; rewrite Ey; reflexivity.
Qed.

Lemma app_length_inv : forall {A} (l1 l2 l3 l4 : list A),
    List.length l1 = List.length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  induction l1 as [| a l1 IH]; intros l2 [| b l3] l4 Hl E; cbn in *; try discriminate.
  - split; [ reflexivity | exact E ].
  - injection E as -> E; injection Hl as Hl; destruct (IH _ _ _ Hl E) as [-> ->]; split; reflexivity.
Qed.

(** ** Matching Environments

    An environment matches a context when its module entries have the kinds
    of the units the context's slots hold. *)

Section Match.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition kinds_match (Γ : ctx) (ρ : env) : Prop :=
    forall x U, Γ ∋ #x ≔ₘ U -> kinds_equiv Θ Ξ (env_mod ρ x) (dm_clo U ρ).

  Lemma gunit_member_kind_shift : forall d ρ U ch k,
      gunit_member_kind Θ Ξ (d :: ρ) (gunit_expand (gunit_wk U wk_shift)) ch k <-> gunit_member_kind Θ Ξ ρ (gunit_expand U) ch k.
  Proof.
    intros; apply (proj1 (proj2 (kind_rename Θ Ξ)) U wk_shift (d :: ρ) ρ).
    intros x; apply kinds_equiv_refl.
  Qed.

  Lemma kinds_match_nil : forall ρ, kinds_match nil ρ.
  Proof. intros ρ x U Hl; inversion Hl. Qed.

  Lemma kinds_match_cons_term : forall Γ ρ e d, kinds_match Γ ρ -> (forall U, e <> ce_mod U) ->
      (forall A M U, e <> ce_dm A M U) -> kinds_match (e :: Γ) (d :: ρ).
  Proof.
    intros * HΓ He Hd x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity | exfalso; eapply Hd; reflexivity |].
    eapply kinds_equiv_trans; [ apply HΓ; eassumption |].
    intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_shift; reflexivity.
  Qed.

  (** A definition with a module part, matched by its module part. *)
  Lemma kinds_match_cons_dm : forall Γ ρ A M U d t h V, kinds_match Γ ρ -> kinds_equiv Θ Ξ h (dm_clo U ρ) ->
      kinds_match (ce_dm A M U :: Γ) (de_dm d t h V :: ρ).
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kinds_equiv_trans; [ exact Hh |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_shift; reflexivity.
    - eapply kinds_equiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_shift; reflexivity.
  Qed.

  Lemma kinds_match_cons_mod : forall Γ ρ U h V, kinds_match Γ ρ -> kinds_equiv Θ Ξ h (dm_clo U ρ) ->
      kinds_match (ce_mod U :: Γ) (de_mod h V :: ρ).
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kinds_equiv_trans; [ exact Hh |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_shift; reflexivity.
    - eapply kinds_equiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_shift; reflexivity.
  Qed.

  (** The same, for an environment read past its first entry. *)
  Lemma gunit_member_kind_drop : forall ρ U ch k,
      gunit_member_kind Θ Ξ ρ (gunit_expand (gunit_wk U wk_shift)) ch k <-> gunit_member_kind Θ Ξ ρ↯ (gunit_expand U) ch k.
  Proof.
    intros; apply (proj1 (proj2 (kind_rename Θ Ξ)) U wk_shift ρ ρ↯).
    intros x; cbn [wk_shift]; rewrite env_mod_drop; apply kinds_equiv_refl.
  Qed.

  Lemma kinds_match_drop_term : forall Γ ρ e, kinds_match Γ ρ↯ -> (forall U, e <> ce_mod U) ->
      (forall A M U, e <> ce_dm A M U) -> kinds_match (e :: Γ) ρ.
  Proof.
    intros * HΓ He Hd x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity | exfalso; eapply Hd; reflexivity |].
    rewrite <- env_mod_drop; eapply kinds_equiv_trans; [ apply HΓ; eassumption |].
    intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_drop; reflexivity.
  Qed.

  Lemma kinds_match_drop_mod : forall Γ ρ U, kinds_match Γ ρ↯ -> kinds_equiv Θ Ξ (env_mod ρ 0) (dm_clo U ρ↯) ->
      kinds_match (ce_mod U :: Γ) ρ.
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kinds_equiv_trans; [ exact Hh |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_drop; reflexivity.
    - rewrite <- env_mod_drop; eapply kinds_equiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_drop; reflexivity.
  Qed.

  (** The same, for a definition with a module part. *)
  Lemma kinds_match_drop_dm : forall Γ ρ A M U, kinds_match Γ ρ↯ -> kinds_equiv Θ Ξ (env_mod ρ 0) (dm_clo U ρ↯) ->
      kinds_match (ce_dm A M U :: Γ) ρ.
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kinds_equiv_trans; [ exact Hh |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_drop; reflexivity.
    - rewrite <- env_mod_drop; eapply kinds_equiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dmod_member_kind_clo_iff, gunit_member_kind_drop; reflexivity.
  Qed.

  Lemma kinds_match_kinds_pads : forall Δ Γ ρ, tele_ass Δ -> kinds_match Γ ρ -> kinds_match (Δ ++ Γ) (kinds_pads (List.length Δ) ρ).
  Proof.
    induction 1 as [| e Δ [A ->] HΔ IH]; intros HΓ; cbn [app List.length]; [ exact HΓ |].
    unfold kinds_pads in *; cbn [List.repeat app].
    apply kinds_match_cons_term; [ auto | discriminate | discriminate ].
  Qed.

  (** The same, for the arguments of a unit, at any types. *)
  Lemma kinds_match_env_args : forall Δ Γ ρ vts, tele_ass Δ -> kinds_match Γ ρ -> List.length vts = List.length Δ ->
      kinds_match (Δ ++ Γ) (env_extend_typed ρ vts).
  Proof.
    induction Δ as [| e Δ IH]; intros * HΔ HΓ Hl.
    - destruct vts; [ exact HΓ | discriminate ].
    - inversion HΔ as [| ? ? [A ->] HΔ']; subst.
      destruct (List.exists_last (l := vts) ltac:(destruct vts; [ discriminate | discriminate ])) as (vts' & c & ->).
      rewrite length_app in Hl; cbn in Hl.
      unfold env_extend_typed; rewrite fold_left_app; cbn [fold_left app].
      apply kinds_match_cons_term; [ apply IH; [ exact HΔ' | exact HΓ | lia ] | discriminate | discriminate ].
  Qed.

  Lemma kinds_match_ext : forall Φ y E Γ ρ1, kinds_match (body_ctx Φ ++ Γ) ρ1 ->
      kinds_match (body_ctx (gm_ext Φ y E) ++ Γ) (kinds_body_entry ρ1 y E :: ρ1).
  Proof.
    intros * H; destruct E as [b pv ra A [M |] | pm U | pv pq k D Φd | pv A M U | pv pr Rr Φr]; cbn [body_ctx kinds_body_entry app];
      first [ apply kinds_match_cons_mod; [ exact H | apply kinds_equiv_refl ]
            | apply kinds_match_cons_dm; [ exact H | apply kinds_equiv_refl ]
            | apply kinds_match_cons_term; [ exact H | discriminate | discriminate ] ].
  Qed.

End Match.
