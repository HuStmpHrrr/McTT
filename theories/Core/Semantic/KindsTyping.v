(** * The Kinds of Typed Members

    The kinds evaluation reads off module values ([dkind], [ukind],
    [skind]) are those typing gives ([member_type]), in an environment whose
    module entries have the kinds of the units their context's slots hold
    ([kmatch]).  In particular, the entries the kinds read off an open are
    those typing generates for it, with the types left out ([member_kind]). *)

From Stdlib Require Import Lia List PeanoNat String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Semantic Require Import Evaluation Kinds.
Import Domain_Notations Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Generated Entries *)

(** A generated item without its type, as kinds read it ([kgens]). *)
Definition ig_erase (g : igen) : igen :=
  match g with
  | ig_def d pv _ M => ig_def d pv a_True M
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
Lemma gens_prefix_some : forall Θ Ξ io Γ H its gs, items_gen Θ Ξ io Γ H its gs ->
    forall y its1 it, items_upto y its = Some (its1, it) ->
    exists its0 gs0 g, its1 = its0 ++ it :: nil /\ items_gen Θ Ξ io Γ H its0 gs0 /\
      items_gen Θ Ξ io Γ H (it :: nil) (g :: nil) /\
      (exists R Rg, its = its1 ++ R /\ gs = gs0 ++ g :: Rg) /\
      forall Φ k, gm_prefix_upto (gens_append Φ k gs) y = Some (gens_append Φ k (gs0 ++ g :: nil)).
Proof.
  intros * Hg; induction Hg as [| | | | | ]; intros y its1 it0 Hu; cbn [items_upto] in Hu; try discriminate;
    match type of Hu with
    | match items_upto ?y ?its with _ => _ end = _ =>
        destruct (items_upto y its) as [[its1' it1] |] eqn:Eu
    end.
  all: try (injection Hu as <- <-;
            destruct (IHHg _ _ _ Eu) as (its0 & gs0 & g & -> & Hg0 & Hg1 & (R & Rg & -> & ->) & Hp);
            eexists (_ :: its0), (_ :: gs0), g; split; [ reflexivity |]; split; [ econstructor; eassumption |];
            split; [ exact Hg1 |]; split; [ exists R, Rg; split; reflexivity |];
            intros Φ k; cbn [gens_append app]; apply Hp).
  all: destruct (String.eqb _ _) eqn:Ey; [| discriminate ]; injection Hu as <- <-.
  all: pose proof (items_upto_none_iff _ _ Eu) as Hn; rewrite <- (items_gen_names _ _ _ _ _ _ _ Hg) in Hn.
  all: eexists nil, nil, _; split; [ reflexivity |]; split; [ constructor |].
  all: split; [ solve [ econstructor; eauto using ign_nil ] |].
  all: split; [ eexists _, _; split; reflexivity |].
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
    forall x U, Γ ∋ #x ⇒ₘ U -> kequiv Θ Ξ (env_mod ρ x) (dm_local ρ U nil).

  Lemma ukind_shift : forall d ρ U ch k, ukind Θ Ξ (d :: ρ) (gunit_wk U wk_shift) ch k <-> ukind Θ Ξ ρ U ch k.
  Proof.
    intros; apply (proj1 (proj2 (kind_ren Θ Ξ)) U wk_shift (d :: ρ) ρ).
    intros x; apply kequiv_refl.
  Qed.

  Lemma kmatch_nil : forall ρ, kmatch nil ρ.
  Proof. intros ρ x U Hl; inversion Hl. Qed.

  Lemma kmatch_cons_term : forall Γ ρ e d, kmatch Γ ρ -> (forall U, e <> ce_mod U) -> kmatch (e :: Γ) (d :: ρ).
  Proof.
    intros * HΓ He x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity |].
    eapply kequiv_trans; [ apply HΓ; eassumption |].
    intros ch k; rewrite !dkind_local_iff, ukind_shift; reflexivity.
  Qed.

  Lemma kmatch_cons_mod : forall Γ ρ U h, kmatch Γ ρ -> kequiv Θ Ξ h (dm_local ρ U nil) ->
      kmatch (ce_mod U :: Γ) (de_mod h :: ρ).
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kequiv_trans; [ exact Hh |].
      intros ch k; rewrite !dkind_local_iff, ukind_shift; reflexivity.
    - eapply kequiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dkind_local_iff, ukind_shift; reflexivity.
  Qed.

  (** The same, for an environment read past its first entry. *)
  Lemma ukind_drop : forall ρ U ch k, ukind Θ Ξ ρ (gunit_wk U wk_shift) ch k <-> ukind Θ Ξ ρ↯ U ch k.
  Proof.
    intros; apply (proj1 (proj2 (kind_ren Θ Ξ)) U wk_shift ρ ρ↯).
    intros x; cbn [wk_shift]; rewrite env_mod_drop; apply kequiv_refl.
  Qed.

  Lemma kmatch_drop_term : forall Γ ρ e, kmatch Γ ρ↯ -> (forall U, e <> ce_mod U) -> kmatch (e :: Γ) ρ.
  Proof.
    intros * HΓ He x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity |].
    rewrite <- env_mod_drop; eapply kequiv_trans; [ apply HΓ; eassumption |].
    intros ch k; rewrite !dkind_local_iff, ukind_drop; reflexivity.
  Qed.

  Lemma kmatch_drop_mod : forall Γ ρ U, kmatch Γ ρ↯ -> kequiv Θ Ξ (env_mod ρ 0) (dm_local ρ↯ U nil) ->
      kmatch (ce_mod U :: Γ) ρ.
  Proof.
    intros * HΓ Hh x U' Hl; inversion Hl; subst.
    - eapply kequiv_trans; [ exact Hh |].
      intros ch k; rewrite !dkind_local_iff, ukind_drop; reflexivity.
    - rewrite <- env_mod_drop; eapply kequiv_trans; [ apply HΓ; eassumption |].
      intros ch k; rewrite !dkind_local_iff, ukind_drop; reflexivity.
  Qed.

  Lemma kmatch_kpad : forall Δ Γ ρ, tele_ass Δ -> kmatch Γ ρ -> kmatch (Δ ++ Γ) (kpad (List.length Δ) ρ).
  Proof.
    induction 1 as [| e Δ [A ->] HΔ IH]; intros HΓ; cbn [app List.length]; [ exact HΓ |].
    unfold kpad in *; cbn [List.repeat app].
    apply kmatch_cons_term; [ auto | discriminate ].
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
      apply kmatch_cons_term; [ apply IH; [ exact HΔ' | exact HΓ | lia ] | discriminate ].
  Qed.

  Lemma kmatch_ext : forall Φ y E Γ ρ1, kmatch (body_ctx Φ ++ Γ) ρ1 ->
      kmatch (body_ctx (gm_ext Φ y E) ++ Γ) (kbentry ρ1 E :: ρ1).
  Proof.
    intros * H; destruct E as [b pv A [M |] | pm U | pv D Φd | pv Δ p Ns]; cbn [body_ctx kbentry app];
      first [ apply kmatch_cons_mod; [ exact H | apply kequiv_refl ]
            | apply kmatch_cons_term; [ exact H | discriminate ] ].
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

  (** *** Typed Members Have Their Kinds *)

  (** What the entries of an expanded body tell of the raw body's lookups. *)
  Definition body_looks (Γ : ctx) (Φ Φx : gmod) (ρ : env) : Prop :=
    forall x Φ' E, gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
      (forall b pv A B, E = ge_def b pv A B -> ukind Θ Ξ ρ (gu_mk nil (md_body Φ)) (x :: nil) mk_term) /\
      (forall pm Uy, E = ge_mod pm Uy -> exists ρ', kmatch (body_ctx Φ' ++ Γ) ρ' /\
         forall ch k, ukind Θ Ξ ρ' Uy ch k -> ukind Θ Ξ ρ (gu_mk nil (md_body Φ)) (x :: ch) k).

  Lemma mres_kind_gen : forall Δ R, mres_kind (mres_gen Δ R) = mres_kind R.
  Proof. intros ? []; reflexivity. Qed.

  Lemma mres_kind_app : forall R N R', mres_app R N = Some R' -> mres_kind R' = mres_kind R.
  Proof.
    intros [A | T | T] N R' H; cbn in H.
    - destruct (pi_view A) as [[] |]; [ injection H as <-; reflexivity | discriminate ].
    - destruct (tele_inst T N); cbn in H; [ injection H as <-; reflexivity | discriminate ].
    - destruct (tele_inst T N); cbn in H; [ injection H as <-; reflexivity | discriminate ].
  Qed.

  Theorem member_kind :
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R ->
       forall ρ, kmatch Γ ρ -> skind Θ Ξ ρ H ch (mres_kind R)) /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R ->
       forall ρ, kmatch Γ ρ -> ukind Θ Ξ ρ U ch (mres_kind R)) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
       forall ρ, kmatch Γ ρ -> exists ρ1, kenv Θ Ξ ρ Φ ρ1 /\ kmatch (body_ctx Φx ++ Γ) ρ1 /\ body_looks Γ Φ Φx ρ) /\
    (forall io Γ H its gs, items_gen Θ Ξ io Γ H its gs -> io = None ->
       forall ρ, kmatch Γ ρ -> kgens Θ Ξ ρ H its (map ig_erase gs)).
  Proof.
    apply member_type_both_ind; intros.
    - (* a definition of a unit *)
      constructor; eapply dk_global_def; eassumption.
    - (* a module of a unit *)
      constructor; eapply dk_global_mod; eassumption.
    - (* the module of an inductive type *)
      constructor; eapply dk_global_mod; eassumption.
    - (* an alias of a unit *)
      constructor; eapply dk_global_alias; [ eassumption |]; auto using kmatch_nil.
    - (* a slot *)
      constructor; match goal with Hm : kmatch _ _, Hl : _ ∋ #_ ⇒ₘ _ |- _ => apply (Hm _ _ Hl) end.
      apply dkind_local_iff; auto.
    - (* a literal *)
      constructor; auto.
    - (* a selection *)
      constructor; auto.
    - (* an application *)
      constructor; erewrite mres_kind_app by eassumption; auto.
    - (* a body itself *)
      constructor.
    - (* a definition of a body *)
      apply ukind_pad.
      match goal with IH : forall ρ, kmatch (_ ++ _) ρ -> _, Hp : gm_prefix_upto _ _ = _,
                      Ht : tele_ass _, Hm : kmatch _ ρ |- _ =>
        destruct (IH _ (kmatch_kpad _ _ _ Ht Hm)) as (ρ1 & _ & _ & HL);
        exact (proj1 (HL _ _ _ Hp) _ _ _ _ eq_refl) end.
    - (* a module of a body *)
      rewrite mres_kind_gen; apply ukind_pad.
      match goal with IH : forall ρ, kmatch (_ ++ _) ρ -> _, Hp : gm_prefix_upto _ _ = _,
                      Ht : tele_ass _, Hm : kmatch _ ρ |- _ =>
        destruct (IH _ (kmatch_kpad _ _ _ Ht Hm)) as (ρ1 & _ & _ & HL);
        destruct (proj2 (HL _ _ _ Hp) _ _ eq_refl) as (ρ' & Hm' & Hl) end.
      apply Hl; auto.
    - (* an alias *)
      rewrite mres_kind_gen; constructor; apply H, kmatch_kpad; assumption.
    - (* the empty body *)
      exists ρ; split; [ constructor |]; split; [ exact H |].
      intros x Φ' E Hp; discriminate Hp.
    - (* an entry *)
      destruct (H _ H0) as (ρ1 & Hk & Hm & HL).
      exists (kbentry ρ1 E :: ρ1); split; [ constructor; exact Hk |]; split; [ apply kmatch_ext, Hm |].
      intros y Φ' E' Hp; cbn [gm_prefix_upto] in Hp.
      destruct (String.eqb_spec y x) as [-> | Hne].
      + injection Hp as <- <-.
        assert (Ex : String.eqb x x = true) by apply String.eqb_refl.
        split.
        * intros * ->; eapply uk_def; cbn [gm_prefix_upto]; rewrite Ex; reflexivity.
        * intros * ->; exists ρ1; split; [ exact Hm |].
          intros ch k Hu; eapply uk_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk | exact Hu ].
      + destruct (HL _ _ _ Hp) as [HL1 HL2]; split.
        * intros; apply ukind_body_ext_other; [ exact Hne |]; eauto.
        * intros * HE; destruct (HL2 _ _ HE) as (ρ' & Hm' & Hl); exists ρ'; split; [ exact Hm' |].
          intros; apply ukind_body_ext_other; [ exact Hne |]; auto.
    - (* an open *)
      match goal with
      | IHΦ : forall ρ, kmatch ?Γ ρ -> exists _, kenv _ _ ρ Φ _ /\ _, Hm0 : kmatch ?Γ ρ |- _ =>
          destruct (IHΦ _ Hm0) as (ρ1 & Hk & Hm & HL)
      end.
      match goal with
      | IHg : None = None -> forall ρ, kmatch _ ρ -> kgens _ _ ρ _ _ _ |- _ =>
          pose proof (IHg eq_refl _ Hm) as Hg
      end.
      match goal with Hig : items_gen _ _ _ _ _ _ _ |- _ => rename Hig into i end.
      exists (kgens_env ρ1 0 (map ig_erase gs)); split; [ econstructor; [ exact Hk | exact Hg ] |].
      split; [ apply kmatch_gens, Hm |].
      intros y Φ' E Hp.
      destruct (items_upto y its) as [[its1 it] |] eqn:Ey.
      + (* a name the open declares *)
        destruct (gens_prefix_some _ _ _ _ _ _ _ i _ _ _ Ey) as (its0 & gs0 & g & -> & Hg0 & Hg1 & Hrest & Hgp).
        rewrite Hgp, gens_append_snoc in Hp; injection Hp as <- Hn HE; subst E.
        assert (Hu : forall ch k, skind Θ Ξ ρ1 H (item_ch it ch) k ->
                       ukind Θ Ξ ρ (gu_mk nil (md_body (gm_open Φ H its))) (y :: ch) k)
          by (intros ch k Hs; eapply uk_item; [ cbn [gm_item_upto]; rewrite Ey; reflexivity | exact Hk | exact Hs ]).
        inversion Hg1 as [| ? ? ? ? ? ? ? Hn0 | ? ? ? ? ? ? ? Hmt Hn0 | ? ? ? ? ? ? ? ? Hmt Hn0
                         | ? ? ? ? ? ? ? ? ? ? ? ? Hmt Hq Hi Hn0 | ? ? ? ? ? ? ? ? Hmt Hio Hn0 ]; subst; cbn [ig_entry snd gentry_wk].
        * (* the target itself *)
          split; [ intros; discriminate |].
          intros pm Uy [= <- <-].
          exists (kgens_env ρ1 0 (map ig_erase gs0)); split; [ apply kmatch_gens, Hm |].
          intros ch k Hk'; apply Hu; cbn [item_ch].
          cbn [gunit_wk moddef_wk wk_qn] in Hk'; apply ukind_alias_iff in Hk'.
          destruct (kgens_env_split (map ig_erase gs0) ρ1 0) as (X & EX & HX).
          rewrite EX in Hk'; rewrite length_map in HX.
          apply (proj1 (kind_ren Θ Ξ) H (wk_shiftn (List.length gs0)) (X ++ ρ1) ρ1); [| exact Hk' ].
          rewrite <- HX; apply kren_shift_app.
        * (* a definition *)
          split; [| intros; discriminate ].
          intros; apply Hu; cbn [item_ch].
          (* its generated entry, as the kinds read it *)
          destruct Hrest as (Rr & Rg & Eits & Egs); rewrite Eits, <- app_assoc in Hg; cbn [app] in Hg.
          destruct (kgens_app_inv _ _ _ _ _ _ _ Hg) as (ga & gb & Egb & Hga & Hgb).
          rewrite Egs, map_app in Egb.
          apply app_length_inv in Egb as [_ <-];
            [| rewrite length_map, (kgens_length _ _ _ _ _ _ Hga), (items_gen_length _ _ _ _ _ _ _ Hg0); reflexivity ].
          cbn [map ig_erase] in Hgb; inversion Hgb; subst; assumption.
        * (* a module *)
          split; [ intros; discriminate |].
          intros pm Uy [= <- <-].
          exists (kgens_env ρ1 0 (map ig_erase gs0)); split; [ apply kmatch_gens, Hm |].
          intros ch k Hk'; apply Hu; cbn [item_ch].
          cbn [gunit_wk moddef_wk wk_qn] in Hk'; apply ukind_alias_iff in Hk'.
          destruct (kgens_env_split (map ig_erase gs0) ρ1 0) as (X & EX & HX).
          rewrite EX in Hk'; rewrite length_map in HX.
          apply (proj1 (kind_ren Θ Ξ) (me_mem H n) (wk_shiftn (List.length gs0)) (X ++ ρ1) ρ1) in Hk';
            [| rewrite <- HX; apply kren_shift_app ].
          apply skind_mem_iff; exact Hk'.
      + (* a name before the open *)
        pose proof (items_upto_none_iff _ _ Ey) as Hn.
        rewrite <- (items_gen_names _ _ _ _ _ _ _ i) in Hn.
        rewrite gens_prefix_none in Hp by exact Hn.
        destruct (HL _ _ _ Hp) as [HL1 HL2]; split.
        * intros; apply ukind_body_open_other; [ exact Ey |]; eauto.
        * intros * HE; destruct (HL2 _ _ HE) as (ρ' & Hm' & Hl); exists ρ'; split; [| intros; apply ukind_body_open_other; [ exact Ey | auto ] ].
          (* the context before the open is a suffix of the one after *)
          exact Hm'.
    - (* no items *)
      constructor.
    - (* the target itself *)
      cbn [map ig_erase]; constructor; auto.
    - (* a definition *)
      cbn [map ig_erase]; constructor; [| auto ].
      replace mk_term with (mres_kind (mr_term A)) by reflexivity; auto.
    - (* a module *)
      cbn [map ig_erase]; constructor; [| auto ].
      replace mk_mod with (mres_kind (mr_mod T)) by reflexivity; auto.
    - (* an inductive type: none generated locally *)
      discriminate.
    - discriminate.
  Qed.

End Match.
