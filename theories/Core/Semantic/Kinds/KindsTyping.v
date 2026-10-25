(** * The Kinds of Typed Members

    The kinds evaluation reads off module values ([dkind], [ukind],
    [skind]) are read in an environment whose module entries have the kinds
    of the units their context's slots hold ([kmatch]); the entries the
    kinds read off an open are those it generates, with the types left out
    ([ig_erase], [kmatch_gens]). *)

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

(** A generated item without its type, as kinds read it ([kgens]). *)
Definition ig_erase (g : igen) : igen :=
  match g with
  | ig_def d pv _ M => ig_def d pv a_True M
  | ig_def_mod d pv _ M E => ig_def_mod d pv a_True M E
  | _ => g
  end.

Lemma gens_append_app : forall gs1 gs2 Φ k,
    gens_append Φ k (gs1 ++ gs2) = gens_append (gens_append Φ k gs1) (k + List.length gs1) gs2.
Proof.
  induction gs1 as [| g gs1 IH]; intros; cbn [app gens_append List.length]; [ rewrite Nat.add_0_r; reflexivity |].
  destruct (ig_entry g) as [d E]; rewrite IH, Nat.add_succ_r; reflexivity.
Qed.

Lemma gens_append_snoc : forall gs g Φ k,
    gens_append Φ k (gs ++ g :: nil) =
    gm_ext (gens_append Φ k gs) (ig_name g) (gentry_wk (snd (ig_entry g)) (wk_shiftn (k + List.length gs))).
Proof.
  intros; rewrite gens_append_app; cbn [gens_append]; unfold ig_name; destruct (ig_entry g); reflexivity.
Qed.

Lemma items_upto_none_iff : forall x its, items_upto x its = None -> existsb (String.eqb x) (map iitem_name its) = false.
Proof.
  induction its as [| it its IH]; intros H; cbn in *; [ reflexivity |].
  destruct (items_upto x its) as [[] |]; [ discriminate |].
  destruct (String.eqb x (iitem_name it)); [ discriminate |]; cbn; auto.
Qed.

(** Past the names an open declares, the generated entries are skipped. *)
Lemma gens_prefix_none : forall gs Φ k y, existsb (String.eqb y) (map ig_name gs) = false ->
    gm_prefix_upto (gens_append Φ k gs) y = gm_prefix_upto Φ y.
Proof.
  induction gs as [| g gs IH]; intros * Hn; cbn [gens_append]; [ reflexivity |].
  cbn [map existsb] in Hn; apply Bool.orb_false_iff in Hn as [Hy Hn].
  unfold ig_name in Hy; destruct (ig_entry g) as [d E] eqn:Eg; cbn [fst] in Hy.
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
  all: split; [ solve [ econstructor; eauto using ign_nil ] |].
  all: split; [ eexists _, _; split; reflexivity |].
  all: intros Φ kk; cbn [gens_append app ig_entry]; rewrite gens_prefix_none by exact Hn;
         cbn [gm_prefix_upto iitem_name] in *; rewrite Ey; reflexivity.
Qed.

(** The same for the items kinds read. *)
Lemma kgens_names : forall Θ Ξ ρ H its gs, kgens Θ Ξ ρ H its gs -> List.map ig_name gs = List.map iitem_name its.
Proof. induction 1; cbn; f_equal; auto. Qed.

Lemma kgens_prefix_some : forall Θ Ξ ρ H its gs, kgens Θ Ξ ρ H its gs ->
    forall y its1 it, items_upto y its = Some (its1, it) ->
    exists gs0 g, kgens Θ Ξ ρ H (it :: nil) (g :: nil) /\
      forall Φ k, gm_prefix_upto (gens_append Φ k gs) y = Some (gens_append Φ k (gs0 ++ g :: nil)).
Proof.
  intros * Hg; induction Hg as [| | | | ]; intros y its1 it0 Hu; cbn [items_upto] in Hu; try discriminate.
  all: destruct (items_upto y its) as [[its1' it1] |] eqn:Eu.
  all: try (injection Hu as <- <-;
            destruct (IHHg _ _ _ Eu) as (gs0 & g0 & Hg1 & Hp);
            match goal with |- exists _ _, _ /\ forall _ _, gm_prefix_upto (gens_append _ _ (?g :: _)) _ = _ =>
              exists (g :: gs0), g0 end; split; [ exact Hg1 |];
            intros Φ k; cbn [gens_append app ig_entry]; apply Hp).
  all: match type of Hu with context [String.eqb ?a ?b] => destruct (String.eqb a b) eqn:Ey end; [| discriminate ]; injection Hu as <- <-.
  all: pose proof (items_upto_none_iff _ _ Eu) as Hn; rewrite <- (kgens_names _ _ _ _ _ _ Hg) in Hn.
  all: eexists nil, _; split; [ solve [ econstructor; eauto using kg_nil ] |].
  all: intros Φ k; cbn [gens_append app ig_entry]; rewrite gens_prefix_none by exact Hn;
         cbn [gm_prefix_upto iitem_name] in *; rewrite Ey; reflexivity.
Qed.

Lemma app_length_inv : forall {A} (l1 l2 l3 l4 : list A),
    List.length l1 = List.length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  induction l1 as [| a l1 IH]; intros l2 [| b l3] l4 Hl E; cbn in *; try discriminate.
  - split; [ reflexivity | exact E ].
  - injection E as -> E; injection Hl as Hl; destruct (IH _ _ _ Hl E) as [-> ->]; split; reflexivity.
Qed.

Lemma kgens_app_inv : forall Θ Ξ ρ H its1 its2 gs, kgens Θ Ξ ρ H (its1 ++ its2) gs ->
    exists gs1 gs2, gs = gs1 ++ gs2 /\ kgens Θ Ξ ρ H its1 gs1 /\ kgens Θ Ξ ρ H its2 gs2.
Proof.
  induction its1 as [| it its1 IH]; intros * Hg; cbn [app] in Hg.
  - exists nil, gs; split; [ reflexivity |]; split; [ constructor | exact Hg ].
  - inversion Hg; subst;
      match goal with Hr : kgens _ _ _ _ (its1 ++ its2) _ |- _ =>
        destruct (IH _ _ Hr) as (gs1 & gs2 & -> & H1 & H2) end;
      eexists (_ :: gs1), gs2; (split; [ reflexivity |]); (split; [| exact H2 ]); econstructor; eassumption.
Qed.

(** ** Matching Environments

    An environment matches a context when its module entries have the kinds
    of the units the context's slots hold. *)

Section Match.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition kmatch (Γ : ctx) (ρ : env) : Prop :=
    forall x U, Γ ∋ #x ≔ₘ U -> kequiv Θ Ξ (env_mod ρ x) (dm_clo U ρ).

  Lemma ukind_shift : forall d ρ U ch k, ukind Θ Ξ (d :: ρ) (gunit_wk U wk_shift) ch k <-> ukind Θ Ξ ρ U ch k.
  Proof.
    intros; apply (proj1 (proj2 (kind_ren Θ Ξ)) U wk_shift (d :: ρ) ρ).
    intros x; apply kequiv_refl.
  Qed.

  Lemma kmatch_nil : forall ρ, kmatch nil ρ.
  Proof. intros ρ x U Hl; inversion Hl. Qed.

  Lemma kmatch_cons_term : forall Γ ρ e d, kmatch Γ ρ -> (forall U, e <> ce_mod U) ->
      (forall A M U, e <> ce_dm A M U) -> kmatch (e :: Γ) (d :: ρ).
  Proof.
    intros * HΓ He Hd x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity | exfalso; eapply Hd; reflexivity |].
    eapply kequiv_trans; [ apply HΓ; eassumption |].
    intros ch k; rewrite !dkind_clo_iff, ukind_shift; reflexivity.
  Qed.

  (** A definition with a module part, matched by its module part. *)
  Lemma kmatch_cons_dm : forall Γ ρ A M U d h, kmatch Γ ρ -> kequiv Θ Ξ h (dm_clo U ρ) ->
      kmatch (ce_dm A M U :: Γ) (de_dm d h :: ρ).
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kequiv_trans; [ exact Hh |].
      intros ch k; rewrite !dkind_clo_iff, ukind_shift; reflexivity.
    - eapply kequiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dkind_clo_iff, ukind_shift; reflexivity.
  Qed.

  Lemma kmatch_cons_mod : forall Γ ρ U h, kmatch Γ ρ -> kequiv Θ Ξ h (dm_clo U ρ) ->
      kmatch (ce_mod U :: Γ) (de_mod h :: ρ).
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kequiv_trans; [ exact Hh |].
      intros ch k; rewrite !dkind_clo_iff, ukind_shift; reflexivity.
    - eapply kequiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dkind_clo_iff, ukind_shift; reflexivity.
  Qed.

  (** The same, for an environment read past its first entry. *)
  Lemma ukind_drop : forall ρ U ch k, ukind Θ Ξ ρ (gunit_wk U wk_shift) ch k <-> ukind Θ Ξ ρ↯ U ch k.
  Proof.
    intros; apply (proj1 (proj2 (kind_ren Θ Ξ)) U wk_shift ρ ρ↯).
    intros x; cbn [wk_shift]; rewrite env_mod_drop; apply kequiv_refl.
  Qed.

  Lemma kmatch_drop_term : forall Γ ρ e, kmatch Γ ρ↯ -> (forall U, e <> ce_mod U) ->
      (forall A M U, e <> ce_dm A M U) -> kmatch (e :: Γ) ρ.
  Proof.
    intros * HΓ He Hd x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity | exfalso; eapply Hd; reflexivity |].
    rewrite <- env_mod_drop; eapply kequiv_trans; [ apply HΓ; eassumption |].
    intros ch k; rewrite !dkind_clo_iff, ukind_drop; reflexivity.
  Qed.

  Lemma kmatch_drop_mod : forall Γ ρ U, kmatch Γ ρ↯ -> kequiv Θ Ξ (env_mod ρ 0) (dm_clo U ρ↯) ->
      kmatch (ce_mod U :: Γ) ρ.
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kequiv_trans; [ exact Hh |].
      intros ch k; rewrite !dkind_clo_iff, ukind_drop; reflexivity.
    - rewrite <- env_mod_drop; eapply kequiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dkind_clo_iff, ukind_drop; reflexivity.
  Qed.

  (** The same, for a definition with a module part. *)
  Lemma kmatch_drop_dm : forall Γ ρ A M U, kmatch Γ ρ↯ -> kequiv Θ Ξ (env_mod ρ 0) (dm_clo U ρ↯) ->
      kmatch (ce_dm A M U :: Γ) ρ.
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kequiv_trans; [ exact Hh |].
      intros ch k; rewrite !dkind_clo_iff, ukind_drop; reflexivity.
    - rewrite <- env_mod_drop; eapply kequiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dkind_clo_iff, ukind_drop; reflexivity.
  Qed.

  Lemma kmatch_kpad : forall Δ Γ ρ, tele_ass Δ -> kmatch Γ ρ -> kmatch (Δ ++ Γ) (kpad (List.length Δ) ρ).
  Proof.
    induction 1 as [| e Δ [A ->] HΔ IH]; intros HΓ; cbn [app List.length]; [ exact HΓ |].
    unfold kpad in *; cbn [List.repeat app].
    apply kmatch_cons_term; [ auto | discriminate | discriminate ].
  Qed.

  (** The same, for the arguments of a unit. *)
  Lemma kmatch_env_args : forall Δ Γ ρ args, tele_ass Δ -> kmatch Γ ρ -> List.length args = List.length Δ ->
      kmatch (Δ ++ Γ) (env_args ρ args).
  Proof.
    induction Δ as [| e Δ IH]; intros * HΔ HΓ Hl.
    - destruct args; [ exact HΓ | discriminate ].
    - inversion HΔ as [| ? ? [A ->] HΔ']; subst.
      destruct (List.exists_last (l := args) ltac:(destruct args; [ discriminate | discriminate ])) as (args' & c & ->).
      rewrite length_app in Hl; cbn in Hl.
      unfold env_args; rewrite fold_left_app; cbn [fold_left app].
      apply kmatch_cons_term; [ apply IH; [ exact HΔ' | exact HΓ | lia ] | discriminate | discriminate ].
  Qed.

  Lemma kmatch_ext : forall Φ y E Γ ρ1, kmatch (body_ctx Φ ++ Γ) ρ1 ->
      kmatch (body_ctx (gm_ext Φ y E) ++ Γ) (kbentry ρ1 E :: ρ1).
  Proof.
    intros * H; destruct E as [b pv A [M |] | pm U | pv pq k D Φd | pv A M U | pv pr Rr Φr]; cbn [body_ctx kbentry app];
      first [ apply kmatch_cons_mod; [ exact H | apply kequiv_refl ]
            | apply kmatch_cons_dm; [ exact H | apply kequiv_refl ]
            | apply kmatch_cons_term; [ exact H | discriminate | discriminate ] ].
  Qed.

  Lemma kentry_erase : forall ρ k g,
      kentry ρ k (ig_erase g) = kbentry ρ (gentry_wk (snd (ig_entry g)) (wk_shiftn k)).
  Proof. intros ρ k []; reflexivity. Qed.

  Lemma kmatch_gens : forall gs Φ k Γ ρ1, kmatch (body_ctx Φ ++ Γ) ρ1 ->
      kmatch (body_ctx (gens_append Φ k gs) ++ Γ) (kgens_env ρ1 k (map ig_erase gs)).
  Proof.
    induction gs as [| g gs IH]; intros * H; cbn [gens_append map kgens_env]; [ exact H |].
    rewrite kentry_erase.
    destruct (ig_entry g) as [d E] eqn:Eg; cbn [snd].
    apply IH, kmatch_ext, H.
  Qed.

  Lemma kgens_env_app : forall gs1 gs2 ρ k,
      kgens_env ρ k (gs1 ++ gs2) = kgens_env (kgens_env ρ k gs1) (k + List.length gs1) gs2.
  Proof.
    induction gs1 as [| g gs1 IH]; intros; cbn [app kgens_env List.length]; [ rewrite Nat.add_0_r; reflexivity |].
    rewrite IH, Nat.add_succ_r; reflexivity.
  Qed.

  Lemma kgens_env_split : forall gs ρ k, exists X, kgens_env ρ k gs = X ++ ρ /\ List.length X = List.length gs.
  Proof.
    induction gs as [| g gs IH]; intros; cbn [kgens_env]; [ exists nil; auto |].
    destruct (IH (kentry ρ k g :: ρ) (S k)) as (X & -> & Hl).
    exists (X ++ kentry ρ k g :: nil); rewrite <- app_assoc, length_app; cbn; split; [ reflexivity | lia ].
  Qed.

End Match.
