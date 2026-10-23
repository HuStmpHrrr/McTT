(** * The Access Fill: Skeletons, the Identity, Functionality

    What a module expression denotes reads a context through its skeleton
    only ([ctx_skeleton]): its module slots and their units, and which of
    its other binders hold terms ([mdenote_skeleton_all]).  So an
    access-free term ([access_free_exp]), read in skeleton contexts, has
    no access the fill could rewrite, and every fill of it is the term
    itself ([fill_access_free_all]); and the fill is functional
    ([fill_functional_all]).  The same for a whole command
    ([fill_cmd_access_free], [fill_cmd_functional]) is in
    [System.Command], with [fill_cmd]. *)

From Stdlib Require Import List String Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy AccessFill.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
From Mctt.Algorithmic.Typing Require Import Definitions Functional.
Import Syntax_Notations.

(** ** Skeletons *)

Lemma ctx_skeleton_app : forall Δ Γ, ctx_skeleton (Δ ++ Γ) = ctx_skeleton Δ ++ ctx_skeleton Γ.
Proof. intros; apply List.map_app. Qed.

(** Contexts of one skeleton extended by one prefix have one skeleton. *)
Lemma ctx_skeleton_app_eq : forall Δ Γ Γ',
    ctx_skeleton Γ = ctx_skeleton Γ' -> ctx_skeleton (Δ ++ Γ) = ctx_skeleton (Δ ++ Γ').
Proof. intros * E; rewrite !ctx_skeleton_app, E; reflexivity. Qed.

(** A module slot is read off the skeleton. *)
Lemma lookup_mod_skeleton : forall Γ x U, Γ ∋ #x ≔ₘ U -> forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> Γ' ∋ #x ≔ₘ U.
Proof.
  induction 1 as [Γ U | Γ n U e _ IH]; intros [| e' Γ'] E; cbn in E; try discriminate; injection E as Ee E.
  - destruct e'; cbn in Ee; try discriminate; injection Ee as <-; constructor.
  - constructor; apply IH; assumption.
Qed.

(** Whether a binder holds a term is read off the skeleton. *)
Lemma lookup_term_skeleton : forall Γ x A, Γ ∋ #x : A ->
    forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> exists A', Γ' ∋ #x : A'.
Proof.
  induction 1 as [Γ A | Γ A M | Γ n A e _ IH]; intros [| e' Γ'] E; cbn in E; try discriminate; injection E as Ee E.
  1,2: destruct e'; cbn in Ee; try discriminate; eexists; constructor.
  destruct (IH _ E) as [A' HA']; eexists; constructor; exact HA'.
Qed.

(** What a module expression, a unit and an entry denote, a body's
    expansion and an open's items, are read off the skeleton. *)
Lemma mdenote_skeleton_all : forall Θ Ξ,
    (forall Γ H R, mdenote Θ Ξ Γ H R ->
       forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> mdenote Θ Ξ Γ' H R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R ->
       forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> udenote Θ Ξ Γ' o U R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R ->
       forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> edenote Θ Ξ Γ' o E R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
       forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> body_xp Θ Ξ Γ' Φ Φx) /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs ->
       forall Γ', ctx_skeleton Γ = ctx_skeleton Γ' -> items_gen Θ Ξ g Γ' H its gs).
Proof.
  intros Θ Ξ; apply mdenote_all_ind; intros; econstructor; eauto using lookup_mod_skeleton, ctx_skeleton_app_eq.
Qed.

(** Holes are their own skeleton. *)
Lemma ctx_skeleton_holes : forall n, ctx_skeleton (ctx_holes n) = ctx_holes n.
Proof. induction n as [| n IH]; cbn; [ reflexivity | f_equal; exact IH ]. Qed.

(** A telescope of assumptions has a hole per entry for skeleton. *)
Lemma ctx_skeleton_ass : forall Δ, tele_ass Δ -> ctx_skeleton Δ = ctx_holes (List.length Δ).
Proof. induction 1 as [| e Δ [A ->] _ IH]; cbn; [ reflexivity | f_equal; exact IH ]. Qed.

(** A term binder in front of contexts of one skeleton. *)
Lemma ctx_skeleton_cons_term : forall A Γ Γ',
    ctx_skeleton Γ = ctx_skeleton Γ' -> ctx_skeleton (ce_ass A :: Γ) = ctx_skeleton (ce_hole :: Γ').
Proof. intros * E; cbn; f_equal; exact E. Qed.

Lemma ctx_skeleton_cons_def : forall A M Γ Γ',
    ctx_skeleton Γ = ctx_skeleton Γ' -> ctx_skeleton (ce_def A M :: Γ) = ctx_skeleton (ce_hole :: Γ').
Proof. intros * E; cbn; f_equal; exact E. Qed.

(** A module slot in front of contexts of one skeleton. *)
Lemma ctx_skeleton_cons_mod : forall U Γ Γ',
    ctx_skeleton Γ = ctx_skeleton Γ' -> ctx_skeleton (ce_mod U :: Γ) = ctx_skeleton (ce_mod U :: Γ').
Proof. intros * E; cbn; f_equal; exact E. Qed.

(** Assumptions in front of a context, and as many holes. *)
Lemma ctx_skeleton_ass_app : forall Δ n Γ Γ',
    tele_ass Δ -> List.length Δ = n -> ctx_skeleton Γ = ctx_skeleton Γ' ->
    ctx_skeleton (Δ ++ Γ) = ctx_skeleton (ctx_holes n ++ Γ').
Proof. intros * HΔ <- E; rewrite !ctx_skeleton_app, ctx_skeleton_ass, ctx_skeleton_holes, E by exact HΔ; reflexivity. Qed.

(** Holes in front of contexts of one skeleton. *)
Lemma ctx_skeleton_holes_app : forall n Γ Γ',
    ctx_skeleton Γ = ctx_skeleton Γ' -> ctx_skeleton (ctx_holes n ++ Γ) = ctx_skeleton (ctx_holes n ++ Γ').
Proof. intros; apply ctx_skeleton_app_eq; assumption. Qed.


(** ** The Fill of an Access-Free Command Is Itself *)

(** Give the induction hypothesis [IH] the derivation [Hp] about [X], when
    what it then says is not trivial: [Hp] is the other derivation's, not
    the hypothesis's own. *)
Ltac feed_nontrivial IH X Hp :=
  let T := type of (IH X Hp) in
  lazymatch T with
  | ?a = ?a => fail
  | ?a = ?a /\ _ => fail
  | _ => specialize (IH X Hp)
  end.

Ltac feed_nontrivial2 IH X Y Hp :=
  let T := type of (IH X Y Hp) in
  lazymatch T with
  | ?a = ?a => fail
  | ?a = ?a /\ _ => fail
  | _ => specialize (IH X Y Hp)
  end.

(** One step towards two fills of one part being one: use an equation, or
    the functionality of what the fill reads, or give an induction
    hypothesis the other fill of its part. *)
Ltac fill_functional_step Hg :=
  first
    [ match goal with
      | E : _ /\ _ |- _ => destruct E
      | E : read_module _ = read_module _ |- _ => injection E as E
      | E : read_term _ = read_term _ |- _ => injection E as E
      | E : read_module _ = read_term _ |- _ => discriminate E
      | E : read_term _ = read_module _ |- _ => discriminate E
      | E : nf_indty _ _ _ = nf_indty _ _ _ |- _ => injection E as E
      | E : nf_record _ _ = nf_record _ _ |- _ => injection E as E
      | E : ?x = _ |- _ => is_var x; subst x
      | E : _ = ?x |- _ => is_var x; subst x
      | H1 : ?f = Some ?a, H2 : ?f = Some ?b |- _ =>
          assert_fails constr_eq a b; assert (a = b) by congruence; clear H2
      | H1 : _ ⊢a ?M ⟹ ?W1, H2 : _ ⊢a ?M ⟹ ?W2 |- _ =>
          assert_fails constr_eq W1 W2;
          assert (W1 = W2) by (refine (@functional_alg_type_infer _ _ _ _ _ _ H1 H2); exact Hg); clear H2
      | H1 : body_xp _ _ ?G ?F ?X1, H2 : body_xp _ _ ?G ?F ?X2 |- _ =>
          assert_fails constr_eq X1 X2;
          assert (X1 = X2) by exact (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ H1 _ H2);
          clear H2
      | E : ?a = ?b -> _, E' : ?a = ?b |- _ => specialize (E E')
      end
    | match goal with
      | IH : forall _, fill_exp _ _ _ _ _ -> _, Hp : fill_exp _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, elim_group _ _ _ _ _ _ -> _, Hp : elim_group _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_exps _ _ _ _ _ -> _, Hp : fill_exps _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_fvals _ _ _ _ _ -> _, Hp : fill_fvals _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _ _, fill_blocks _ _ _ _ _ _ _ _ _ _ -> _, Hp : fill_blocks _ _ _ _ _ _ ?Y _ _ ?X |- _ =>
          feed_nontrivial2 IH Y X Hp
      | IH : forall _, fill_brs _ _ _ _ _ _ _ _ _ _ -> _, Hp : fill_brs _ _ _ _ _ _ _ _ _ ?X |- _ =>
          feed_nontrivial IH X Hp
      | IH : forall _, fill_oexp _ _ _ _ _ -> _, Hp : fill_oexp _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_read _ _ _ _ _ -> _, Hp : fill_read _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _ _, fill_mod _ _ _ _ _ _ -> _, Hp : fill_mod _ _ _ _ ?X ?Y |- _ => feed_nontrivial2 IH X Y Hp
      | IH : forall _, fill_unit _ _ _ _ _ -> _, Hp : fill_unit _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_def _ _ _ _ _ -> _, Hp : fill_def _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_tele _ _ _ _ _ -> _, Hp : fill_tele _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_body _ _ _ _ _ -> _, Hp : fill_body _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      end ].

(** Invert each access-free hypothesis about a term that is no variable. *)
Ltac inv_access_free :=
  repeat match goal with
    | Hp : ?T |- _ =>
        match T with
        | access_free_exp _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_exps _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_fvals _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_blocks _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_brs _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_oexp _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_mod _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_unit _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_def _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_tele _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        | access_free_body _ _ _ ?X => tryif is_var X then fail else (inversion Hp; subst; clear Hp)
        end
    end.

(** Give each induction hypothesis the access-free hypothesis about its
    part. *)
Ltac feed_ih :=
  repeat match goal with
    | Hp : ?T, IH : forall _ : ctx, _ |- _ =>
        match T with
        | access_free_exp _ _ ?G _ => specialize (IH G Hp)
        | access_free_exps _ _ ?G _ => specialize (IH G Hp)
        | access_free_fvals _ _ ?G _ => specialize (IH G Hp)
        | access_free_oexp _ _ ?G _ => specialize (IH G Hp)
        | access_free_mod _ _ ?G _ => specialize (IH G Hp)
        | access_free_unit _ _ ?G _ => specialize (IH G Hp)
        | access_free_def _ _ ?G _ => specialize (IH G Hp)
        | access_free_tele _ _ ?G _ => specialize (IH G Hp)
        | access_free_body _ _ ?G _ => specialize (IH G Hp)
        end
    end.

(** Two contexts of one skeleton, with one binder or one prefix more. *)
Ltac skeleton_tac :=
  first [ assumption
        | apply ctx_skeleton_cons_term; assumption
        | apply ctx_skeleton_cons_def; assumption
        | apply ctx_skeleton_cons_mod; assumption
        | apply ctx_skeleton_app_eq; assumption ].

(** Discharge the skeleton premise of each fed hypothesis, and use what it
    says. *)
Ltac close_ih :=
  repeat match goal with
    | E : ctx_skeleton _ = ctx_skeleton _ -> _ |- _ => specialize (E ltac:(skeleton_tac))
    | E : _ /\ _ |- _ => destruct E
    | E : read_module _ = read_module _ |- _ => injection E as E
    | E : ?x = _ |- _ => is_var x; subst x
    end.

Section Identity.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** The block contexts of a group filed in a well-formed global context
      are assumptions. *)
  Lemma elim_ctx_skeletons : forall p D j Mj Us gs As Γ Γ',
      ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> ctx_skeleton Γ = ctx_skeleton Γ' ->
      ctx_skeleton (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) = ctx_skeleton (ctx_holes (im_nn Mj) ++ Γ') /\
      ctx_skeleton (elim_mctx p D j Mj Us ++ Γ) = ctx_skeleton (ctx_holes (S (im_nn Mj)) ++ Γ') /\
      ctx_skeleton (elim_bctx p D Mj gs As Us ++ Γ) =
        ctx_skeleton (ctx_holes (im_nn Mj + List.length gs + cargs_nrec gs) ++ Γ').
  Proof.
    intros * Hl Hj E.
    destruct (decl_of_lookup _ _ _ _ _ (wf_ctx_empty _ _ Hg) Hl) as [_ Hc].
    repeat split; apply ctx_skeleton_ass_app; try exact E.
    - apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption.
    - apply length_tele_sub.
    - eapply elim_mctx_ass; eassumption.
    - apply length_elim_mctx.
    - eapply elim_bctx_ass; eassumption.
    - rewrite length_elim_bctx; lia.
  Qed.

  (** Each part of the fill, of a part with no access read in a context of
      the same skeleton, is the part itself; a module expression reads as
      itself, a module. *)
  Lemma fill_access_free_all :
    (forall Γ M M', fill_exp Θ Ξ Γ M M' ->
       forall Γ', access_free_exp Θ Ξ Γ' M -> ctx_skeleton Γ = ctx_skeleton Γ' -> M' = M) /\
    (forall Γ oq M p, elim_group Θ Ξ Γ oq M p -> True) /\
    (forall Γ Ms Ms', fill_exps Θ Ξ Γ Ms Ms' ->
       forall Γ', access_free_exps Θ Ξ Γ' Ms -> ctx_skeleton Γ = ctx_skeleton Γ' -> Ms' = Ms) /\
    (forall Γ fs fs', fill_fvals Θ Ξ Γ fs fs' ->
       forall Γ', access_free_fvals Θ Ξ Γ' fs -> ctx_skeleton Γ = ctx_skeleton Γ' -> fs' = fs) /\
    (forall Γ p D Us As j Bks Bks', fill_blocks Θ Ξ Γ p D Us As j Bks Bks' ->
       ind_lookup Θ Ξ p = Some D ->
       forall Γ', access_free_blocks Θ Ξ Γ' Bks -> ctx_skeleton Γ = ctx_skeleton Γ' -> Bks' = Bks) /\
    (forall Γ p D Mj Us As Bs Bs', fill_brs Θ Ξ Γ p D Mj Us As Bs Bs' ->
       ind_lookup Θ Ξ p = Some D -> forall j, ind_member D j = Some Mj ->
       forall Γ', access_free_brs Θ Ξ Γ' Bs -> ctx_skeleton Γ = ctx_skeleton Γ' -> Bs' = Bs) /\
    (forall Γ oM oM', fill_oexp Θ Ξ Γ oM oM' ->
       forall Γ', access_free_oexp Θ Ξ Γ' oM -> ctx_skeleton Γ = ctx_skeleton Γ' -> oM' = oM) /\
    (forall Γ H r, fill_read Θ Ξ Γ H r ->
       forall Γ', access_free_mod Θ Ξ Γ' H -> ctx_skeleton Γ = ctx_skeleton Γ' -> r = read_module H) /\
    (forall Γ H H' op, fill_mod Θ Ξ Γ H H' op ->
       forall Γ', access_free_mod Θ Ξ Γ' H -> ctx_skeleton Γ = ctx_skeleton Γ' -> H' = H /\ op = None) /\
    (forall Γ U U', fill_unit Θ Ξ Γ U U' ->
       forall Γ', access_free_unit Θ Ξ Γ' U -> ctx_skeleton Γ = ctx_skeleton Γ' -> U' = U) /\
    (forall Γ D D', fill_def Θ Ξ Γ D D' ->
       forall Γ', access_free_def Θ Ξ Γ' D -> ctx_skeleton Γ = ctx_skeleton Γ' -> D' = D) /\
    (forall Γ Δ Δ', fill_tele Θ Ξ Γ Δ Δ' ->
       forall Γ', access_free_tele Θ Ξ Γ' Δ -> ctx_skeleton Γ = ctx_skeleton Γ' -> Δ' = Δ) /\
    (forall Γ Φ Φ', fill_body Θ Ξ Γ Φ Φ' ->
       forall Γ', access_free_body Θ Ξ Γ' Φ -> ctx_skeleton Γ = ctx_skeleton Γ' -> Φ' = Φ).
  Proof.
    apply fill_mut_ind; intros; try exact I; inv_access_free; feed_ih; close_ih; try reflexivity; try discriminate.
    all: try (split; reflexivity).
    (** A term binder or a term member read as a term, where the
        access-free skeleton says it holds none *)
    all: try solve [ exfalso; match goal with
      | Hl : ?G ∋ #?k : _, Hn : forall A, ~ ?G' ∋ #?k : A, E : ctx_skeleton ?G = ctx_skeleton ?G' |- _ =>
          destruct (lookup_term_skeleton _ _ _ Hl _ E) as [? ?]; eapply Hn; eassumption
      | Hm : mdenote _ _ ?G ?H _, Hn : forall A oM, ~ mdenote _ _ ?G' ?H _, E : ctx_skeleton ?G = ctx_skeleton ?G' |- _ =>
          eapply Hn, (proj1 (mdenote_skeleton_all Θ Ξ)); [ exact Hm | exact E ]
      end ].
    (** A body's entries: the two expansions are one *)
    all: try match goal with
      | Hb : body_xp _ _ ?G ?F ?X, Hb' : body_xp _ _ ?G' ?F ?X', E : ctx_skeleton ?G = ctx_skeleton ?G' |- _ =>
          assert (X' = X) as -> by
            exact (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hb' _
                     (proj1 (proj2 (proj2 (proj2 (mdenote_skeleton_all Θ Ξ)))) _ _ _ Hb _ E))
      end; close_ih; try reflexivity.
    (** An eliminator's blocks and branches, in their contexts' skeletons *)
    - rewrite (H2 e0 Γ' H13 H4); reflexivity.
    - destruct (elim_ctx_skeletons p D j Mj Us nil nil Γ Γ' H3 e H5) as (E1 & E2 & _).
      replace (S (im_nn Mj) - 1) with (im_nn Mj) in H, H11 by lia.
      rewrite (H E1), (H0 E2), (H1 H3 j e Γ' H14 H5), (H2 H3 Γ' H15 H5); reflexivity.
    - destruct (elim_ctx_skeletons p D j Mj Us gs As Γ Γ' H1 H2 H4) as (_ & _ & E3).
      rewrite (H E3), (H0 H1 j H2 Γ' H11 H4); reflexivity.
  Qed.

  (** A record's fields with no access, over contexts of one skeleton. *)
  Lemma fill_fields_access_free : forall Γ fs fs', fill_fields Θ Ξ Γ fs fs' ->
      forall Γ', access_free_fields Θ Ξ Γ' fs -> ctx_skeleton Γ = ctx_skeleton Γ' -> fs' = fs.
  Proof.
    induction 1 as [| Γ f T T' fs fs' HT _ IH]; intros Γ' Hp E; [ reflexivity |].
    rewrite (proj1 fill_access_free_all _ _ _ HT Γ' (Hp 0 f T eq_refl) E).
    rewrite (IH (ce_hole :: Γ')); [ reflexivity | | apply ctx_skeleton_cons_term; exact E ].
    intros j g U Hj; specialize (Hp (S j) g U Hj).
    replace (ctx_holes j ++ ce_hole :: Γ') with (ctx_holes (S j) ++ Γ'); [ exact Hp |].
    clear; unfold ctx_holes; induction j as [| j IHj]; cbn; [ reflexivity | f_equal; exact IHj ].
  Qed.

  (** ** The Fill Is Functional

      The fill reads its contexts through lookups, [mdenote], [body_xp]
      and [⊢a], all functional.  An eliminator's blocks read the motives
      of the filled blocks, which the motives' own fills fix first. *)
  Lemma fill_functional_all :
    (forall Γ M M1, fill_exp Θ Ξ Γ M M1 -> forall M2, fill_exp Θ Ξ Γ M M2 -> M1 = M2) /\
    (forall Γ oq M p, elim_group Θ Ξ Γ oq M p -> forall p', elim_group Θ Ξ Γ oq M p' -> p = p') /\
    (forall Γ Ms Ms1, fill_exps Θ Ξ Γ Ms Ms1 -> forall Ms2, fill_exps Θ Ξ Γ Ms Ms2 -> Ms1 = Ms2) /\
    (forall Γ fs fs1, fill_fvals Θ Ξ Γ fs fs1 -> forall fs2, fill_fvals Θ Ξ Γ fs fs2 -> fs1 = fs2) /\
    (forall Γ p D Us As j Bks Bks1, fill_blocks Θ Ξ Γ p D Us As j Bks Bks1 ->
       forall As' Bks2, fill_blocks Θ Ξ Γ p D Us As' j Bks Bks2 ->
       blocks_motives Bks1 = blocks_motives Bks2 /\ (As = As' -> Bks1 = Bks2)) /\
    (forall Γ p D Mj Us As Bs Bs1, fill_brs Θ Ξ Γ p D Mj Us As Bs Bs1 ->
       forall Bs2, fill_brs Θ Ξ Γ p D Mj Us As Bs Bs2 -> Bs1 = Bs2) /\
    (forall Γ oM oM1, fill_oexp Θ Ξ Γ oM oM1 -> forall oM2, fill_oexp Θ Ξ Γ oM oM2 -> oM1 = oM2) /\
    (forall Γ H r1, fill_read Θ Ξ Γ H r1 -> forall r2, fill_read Θ Ξ Γ H r2 -> r1 = r2) /\
    (forall Γ H H1 op1, fill_mod Θ Ξ Γ H H1 op1 -> forall H2 op2, fill_mod Θ Ξ Γ H H2 op2 -> H1 = H2 /\ op1 = op2) /\
    (forall Γ U U1, fill_unit Θ Ξ Γ U U1 -> forall U2, fill_unit Θ Ξ Γ U U2 -> U1 = U2) /\
    (forall Γ D D1, fill_def Θ Ξ Γ D D1 -> forall D2, fill_def Θ Ξ Γ D D2 -> D1 = D2) /\
    (forall Γ Δ Δ1, fill_tele Θ Ξ Γ Δ Δ1 -> forall Δ2, fill_tele Θ Ξ Γ Δ Δ2 -> Δ1 = Δ2) /\
    (forall Γ Φ Φ1, fill_body Θ Ξ Γ Φ Φ1 -> forall Φ2, fill_body Θ Ξ Γ Φ Φ2 -> Φ1 = Φ2).
  Proof.
    apply fill_mut_ind; intros;
      lazymatch goal with Hl : _ |- _ => inversion Hl; subst; clear Hl end;
      try discriminate;
      repeat fill_functional_step Hg;
      try reflexivity; try (split; reflexivity);
      (** A binder or a member read as a module and as a term *)
      try solve [ exfalso; match goal with
        | Hn : forall A, ~ ?G ∋ #?k : A, Hl : ?G ∋ #?k : _ |- _ => eapply Hn; exact Hl
        | Hn : forall A oM, ~ mdenote _ _ ?G ?E _, Hm : mdenote _ _ ?G ?E _ |- _ => eapply Hn; exact Hm
        end ].
    (** A block: its motive first, then, at one set of motives, its
        branches *)
    split; [ cbn; f_equal; exact H0 | intros <-; rewrite (H1 _ H20), (H2 eq_refl); reflexivity ].
  Qed.

  (** A record's fields have one fill. *)
  Lemma fill_fields_functional : forall Γ fs fs1, fill_fields Θ Ξ Γ fs fs1 ->
      forall fs2, fill_fields Θ Ξ Γ fs fs2 -> fs1 = fs2.
  Proof.
    induction 1 as [| Γ f T T1 fs fs1 HT _ IH]; intros fs2 H2; inversion H2; subst; [ reflexivity |].
    pose proof (proj1 fill_functional_all _ _ _ HT _ H5) as <-.
    rewrite (IH _ H6); reflexivity.
  Qed.
End Identity.
