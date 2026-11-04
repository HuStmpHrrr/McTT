(** * The Typed Fill Is Functional

    The fill reads its contexts through lookups, [mdenote], [body_xp],
    [elim_target] and [⊢a], all functional, so a term, a command and a
    unit's parameters have one fill each ([fill_functional_all],
    [fill_cmd_functional], [fill_params_functional]).  An eliminator's
    blocks read the motives of the filled blocks, which the motives' own
    fills fix first. *)

From Stdlib Require Import List String Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy Translations.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
From Mctt.Core.TypedElab Require Import ElimTarget Fill.
From Mctt.Algorithmic.Typing Require Import Definitions Functional.
Import Syntax_Notations.

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

Ltac feed_nontrivial3 IH X Y Z Hp :=
  let T := type of (IH X Y Z Hp) in
  lazymatch T with
  | ?a = ?a => fail
  | ?a = ?a /\ _ => fail
  | _ => specialize (IH X Y Z Hp)
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
      | E : elim_target_one _ _ = elim_target_one _ _ |- _ => injection E as E
      | E : (_, _) = (_, _) |- _ => injection E as E
      | E : ?x = _ |- _ => is_var x; subst x
      | E : _ = ?x |- _ => is_var x; subst x
      | H1 : ?f = Some ?a, H2 : ?f = Some ?b |- _ =>
          assert_fails constr_eq a b; assert (a = b) by congruence; clear H2
      | H1 : ?f = elim_target_one ?a ?b, H2 : ?f = elim_target_one ?c ?d |- _ =>
          assert_fails constr_eq (a, b) (c, d);
          assert (elim_target_one a b = elim_target_one c d) by congruence; clear H2
      | H1 : _ ⊢a ?M ⟹ ?W1, H2 : _ ⊢a ?M ⟹ ?W2 |- _ =>
          assert_fails constr_eq W1 W2;
          assert (W1 = W2) by (refine (@functional_alg_type_infer _ _ _ _ _ _ H1 H2); exact Hg); clear H2
      | H1 : body_xp _ _ ?G ?F ?X1, H2 : body_xp _ _ ?G ?F ?X2 |- _ =>
          assert_fails constr_eq X1 X2;
          assert (X1 = X2) by exact (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ H1 _ H2);
          clear H2
      (** The entries an open generates, stored with it *)
      | H1 : items_gen _ _ ?G ?H ?its ?X1, H2 : items_gen _ _ ?G ?H ?its ?X2 |- _ =>
          assert_fails constr_eq X1 X2;
          assert (X1 = X2) by exact (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ _ H1 _ H2);
          clear H2
      | E : ?a = ?b -> _, E' : ?a = ?b |- _ => specialize (E E')
      end
    | match goal with
      | IH : forall _, fill_exp _ _ _ _ _ _ -> _, Hp : fill_exp _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_field_vals _ _ _ _ _ _ -> _, Hp : fill_field_vals _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _ _ _, fill_blocks _ _ _ _ _ _ _ _ _ _ _ _ -> _, Hp : fill_blocks _ _ _ ?R _ _ _ _ ?Y _ _ ?X |- _ =>
          feed_nontrivial3 IH Y R X Hp
      | IH : forall _, fill_scrutinee_type _ _ _ _ _ _ _ _ _ _ _ -> _, Hp : fill_scrutinee_type _ _ _ _ _ _ _ _ _ _ ?X |- _ =>
          feed_nontrivial IH X Hp
      | IH : forall _, fill_brs _ _ _ _ _ _ _ _ _ _ _ _ -> _, Hp : fill_brs _ _ _ _ _ _ _ _ _ _ _ ?X |- _ =>
          feed_nontrivial IH X Hp
      | IH : forall _, fill_optional_exp _ _ _ _ _ _ -> _, Hp : fill_optional_exp _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_read _ _ _ _ _ _ -> _, Hp : fill_read _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _ _, fill_mod _ _ _ _ _ _ _ -> _, Hp : fill_mod _ _ _ _ _ ?X ?Y |- _ => feed_nontrivial2 IH X Y Hp
      | IH : forall _, fill_unit _ _ _ _ _ _ -> _, Hp : fill_unit _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_def _ _ _ _ _ _ -> _, Hp : fill_def _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_tele _ _ _ _ _ _ -> _, Hp : fill_tele _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      | IH : forall _, fill_body _ _ _ _ _ _ -> _, Hp : fill_body _ _ _ _ _ ?X |- _ => feed_nontrivial IH X Hp
      end ].

Section Functional.
  Variables (Θ : gdeps) (Ξ : gstack) (B : builtins).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** Each part of the fill has one fill. *)
  Lemma fill_functional_all :
    (forall Γ M M1, fill_exp Θ Ξ B Γ M M1 -> forall M2, fill_exp Θ Ξ B Γ M M2 -> M1 = M2) /\
    (forall Γ fs fs1, fill_field_vals Θ Ξ B Γ fs fs1 -> forall fs2, fill_field_vals Θ Ξ B Γ fs fs2 -> fs1 = fs2) /\
    (forall r Γ p D Us As j Bks Bks1, fill_blocks Θ Ξ B r Γ p D Us As j Bks Bks1 ->
       forall As' r' Bks2, fill_blocks Θ Ξ B r' Γ p D Us As' j Bks Bks2 ->
       blocks_motives Bks1 = blocks_motives Bks2 /\ (r = r' -> As = As' -> Bks1 = Bks2)) /\
    (forall Γ p D j Mj Us Z Z1, fill_scrutinee_type Θ Ξ B Γ p D j Mj Us Z Z1 ->
       forall Z2, fill_scrutinee_type Θ Ξ B Γ p D j Mj Us Z Z2 -> Z1 = Z2) /\
    (forall r Γ p D Mj Us As Bs Bs1, fill_brs Θ Ξ B r Γ p D Mj Us As Bs Bs1 ->
       forall Bs2, fill_brs Θ Ξ B r Γ p D Mj Us As Bs Bs2 -> Bs1 = Bs2) /\
    (forall Γ oM oM1, fill_optional_exp Θ Ξ B Γ oM oM1 -> forall oM2, fill_optional_exp Θ Ξ B Γ oM oM2 -> oM1 = oM2) /\
    (forall Γ H r1, fill_read Θ Ξ B Γ H r1 -> forall r2, fill_read Θ Ξ B Γ H r2 -> r1 = r2) /\
    (forall Γ H H1 op1, fill_mod Θ Ξ B Γ H H1 op1 -> forall H2 op2, fill_mod Θ Ξ B Γ H H2 op2 -> H1 = H2 /\ op1 = op2) /\
    (forall Γ U U1, fill_unit Θ Ξ B Γ U U1 -> forall U2, fill_unit Θ Ξ B Γ U U2 -> U1 = U2) /\
    (forall Γ D D1, fill_def Θ Ξ B Γ D D1 -> forall D2, fill_def Θ Ξ B Γ D D2 -> D1 = D2) /\
    (forall Γ Δ Δ1, fill_tele Θ Ξ B Γ Δ Δ1 -> forall Δ2, fill_tele Θ Ξ B Γ Δ Δ2 -> Δ1 = Δ2) /\
    (forall Γ Φ Φ1, fill_body Θ Ξ B Γ Φ Φ1 -> forall Φ2, fill_body Θ Ξ B Γ Φ Φ2 -> Φ1 = Φ2).
  Proof.
    apply fill_mut_ind; intros;
      lazymatch goal with Hl : _ |- _ => inversion Hl; subst; clear Hl end;
      try discriminate;
      repeat fill_functional_step Hg;
      try reflexivity; try (split; reflexivity);
      (** A binder or a member read as a module and as a term; an
          annotation written and omitted *)
      try solve [ exfalso; match goal with
        | Hn : ~ term_binder ?G ?k, Hl : term_binder ?G ?k |- _ => exact (Hn Hl)
        | Hn : forall r A oM, ~ mdenote _ _ ?G ?E _, Hm : mdenote _ _ ?G ?E _ |- _ => eapply Hn; exact Hm
        | Hn : ?a <> ?a |- _ => exact (Hn eq_refl)
        end ].
    (** An eliminator: the blocks' motives are filled alike at any
        relevance, so the motive of the member infers one sort, and the
        blocks are filled at one relevance. *)
    - match goal with
      | Emot : blocks_motives ?L1 = blocks_motives ?L2,
        Hm1 : nth_error ?L1 ?m = Some ?b1, Hm2 : nth_error ?L2 ?m = Some ?b2,
        Hw1 : _ ⊢a eb_motive ?b1 ⟹ ?W1, Hw2 : _ ⊢a eb_motive ?b2 ⟹ ?W2 |- _ =>
          assert (Emb : eb_motive b1 = eb_motive b2)
            by (unfold blocks_motives in Emot; pose proof (List.map_nth_error eb_motive _ _ Hm1) as E1;
                pose proof (List.map_nth_error eb_motive _ _ Hm2) as E2; rewrite Emot in E1; congruence);
          rewrite Emb in Hw1;
          assert (W1 = W2) as <- by (refine (@functional_alg_type_infer _ _ _ _ _ _ Hw1 Hw2); exact Hg)
      end.
      repeat match goal with E : ?a = ?a -> _ |- _ => specialize (E eq_refl) end.
      repeat match goal with E : blocks_motives ?L1 = blocks_motives ?L2 -> _, E' : blocks_motives ?L1 = blocks_motives ?L2 |- _ =>
        specialize (E E') end.
      subst; reflexivity.
    (** A block: its motive first, then, at one relevance and one set of
        motives, its branches *)
    - split; [ cbn; f_equal; assumption | intros <- <-; f_equal; f_equal; [ auto |] ].
      match goal with IH : _ = _ -> _ = _ -> _ = _ |- _ => apply IH; reflexivity end.
  Qed.

  (** Named types have one fill. *)
  Lemma fill_fields_functional : forall Γ fs fs1, fill_fields Θ Ξ B Γ fs fs1 ->
      forall fs2, fill_fields Θ Ξ B Γ fs fs2 -> fs1 = fs2.
  Proof.
    induction 1 as [| Γ f T T1 fs fs1 HT _ IH]; intros fs2 H2; inversion H2; subst; [ reflexivity |].
    pose proof (proj1 fill_functional_all _ _ _ HT _ H5) as <-.
    rewrite (IH _ H6); reflexivity.
  Qed.

  (** Two fills of a group's members, in groups of one set of uniform
      parameters, agree on the members' parameters and sorts. *)
  Lemma fill_raw_members_heads_functional : forall R1 R2 ms ms1 ms2, raw_decl_uparams R1 = raw_decl_uparams R2 ->
      Forall2 (fill_raw_member Θ Ξ B R1) ms ms1 -> Forall2 (fill_raw_member Θ Ξ B R2) ms ms2 ->
      Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) ms1 ms2.
  Proof.
    pose proof fill_functional_all as (Fe & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ft & _).
    intros * Eu H1; revert ms2; induction H1 as [| Mr M1 ms ms1 [_ Hn1 Hs1 _] _ IH]; intros ms2 H2;
      inversion H2 as [| ? M2 ? ms2' [_ Hn2 Hs2 _] H2']; subst; constructor; [| exact (IH _ H2') ].
    rewrite Eu in Hn1, Hs1; split; [ exact (Ft _ _ _ Hn1 _ Hn2) | exact (Fe _ _ _ Hs1 _ Hs2) ].
  Qed.

  (** A constructor's arguments have one fill. *)
  Lemma fill_raw_cons_functional : forall Γ (cs : list (string * list (string * surface_exp))) (cs1 cs2 : list (string * list (string * exp))),
      Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields Θ Ξ B Γ (snd rc) (snd rc')) cs cs1 ->
      Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields Θ Ξ B Γ (snd rc) (snd rc')) cs cs2 -> cs1 = cs2.
  Proof.
    intros * H1; revert cs2; induction H1 as [| [c args] [c1 a1] cs cs1 [Ef1 Ht1] _ IH]; intros cs2 H2;
      inversion H2 as [| ? [c2 a2] ? cs2' [Ef2 Ht2] H2']; subst; [ reflexivity |].
    cbn in *; subst.
    rewrite (IH _ H2'), (fill_fields_functional _ _ _ Ht1 _ Ht2); reflexivity.
  Qed.

  (** A group's members have one fill, in groups that agree on the
      uniform parameters and the members' parameters and sorts. *)
  Lemma fill_raw_members_functional : forall R1 R2 ms ms1 ms2, raw_decl_uparams R1 = raw_decl_uparams R2 ->
      Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) (raw_decl_members R1) (raw_decl_members R2) ->
      Forall2 (fill_raw_member Θ Ξ B R1) ms ms1 -> Forall2 (fill_raw_member Θ Ξ B R2) ms ms2 ->
      Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) ms1 ms2 -> ms1 = ms2.
  Proof.
    intros * Eu Hh H1; revert ms2; induction H1 as [| Mr M1 ms ms1 [En1 _ _ Ec1] _ IH]; intros ms2 H2 Hh0;
      inversion H2 as [| ? M2 ? ms2' [En2 _ _ Ec2] H2']; subst; [ reflexivity |].
    inversion Hh0 as [| ? ? ? ? [Enp Ens] Hh0']; subst.
    rewrite (raw_member_args_ctx_heads_eq Ξ R1 R2 M1 M2 Eu Hh Enp) in Ec1.
    rewrite (raw_member_parts_eq M2 M1 (eq_trans En1 (eq_sym En2)) Enp Ens (fill_raw_cons_functional _ _ _ _ Ec1 Ec2)),
      (IH _ H2' Hh0'); reflexivity.
  Qed.

  (** A group has one fill. *)
  Lemma fill_raw_decl_functional : forall R R1 R2, fill_raw_decl Θ Ξ B R R1 -> fill_raw_decl Θ Ξ B R R2 -> R1 = R2.
  Proof.
    pose proof fill_functional_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ft & _).
    intros R R1 R2 [Hu1 Hr1 Hm1] [Hu2 Hr2 Hm2].
    pose proof (Ft _ _ _ Hu1 _ Hu2) as Eu.
    pose proof (fill_raw_members_heads_functional _ _ _ _ _ Eu Hm1 Hm2) as Hh.
    apply (raw_decl_parts_eq R2 R1); [ exact Eu | exact (fill_raw_members_functional _ _ _ _ _ Eu Hh Hm1 Hm2 Hh) | congruence ].
  Qed.

  (** The heads of functions have one fill. *)
  Lemma fill_raw_fun_heads_functional : forall Γ fs hs1 hs2,
      Forall2 (fill_raw_fun_head Θ Ξ B Γ) fs hs1 -> Forall2 (fill_raw_fun_head Θ Ξ B Γ) fs hs2 -> hs1 = hs2.
  Proof.
    pose proof fill_functional_all as (Fe & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ft & _).
    intros * H1; revert hs2; induction H1 as [| f [n1 p1 s1] fs hs1 [En1 Ep1 Es1] _ IH]; intros hs2 H2;
      inversion H2 as [| ? [n2 p2] ? hs2' [En2 Ep2 Es2] H2']; subst; [ reflexivity |].
    cbn in *; pose proof (Ft _ _ _ Ep1 _ Ep2) as <-; pose proof (Fe _ _ _ Es1 _ Es2) as <-.
    rewrite (IH _ H2'); subst; reflexivity.
  Qed.

  (** A function of a mutual definition is its head, its result and its
      clauses. *)
  Lemma raw_fun_head_parts_eq : forall f f',
      raw_fun_head_of f' = raw_fun_head_of f -> raw_fun_res f' = raw_fun_res f -> raw_fun_clauses f' = raw_fun_clauses f -> f' = f.
  Proof. intros [] []; cbn; intros E; injection E; intros; subst; reflexivity. Qed.

  (** The bodies of functions have one fill: first their results, which fix
      the motives, then their clauses. *)
  Lemma fill_raw_fun_bodies_functional : forall Γ pq D Us As1 As2 (l : list (surface_raw_fun * raw_fun_head * nat)) fs1 fs2,
      Forall2 (fun fhm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ As1 (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f') l fs1 ->
      Forall2 (fun fhm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ As2 (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f') l fs2 ->
      Forall2 (fun f1 f2 => raw_fun_nparams f1 = raw_fun_nparams f2 /\ raw_fun_res f1 = raw_fun_res f2) fs1 fs2 /\
      (As1 = As2 -> fs1 = fs2).
  Proof.
    pose proof fill_functional_all as (Fe & _ & _ & _ & Fb & _).
    intros Γ pq D Us As1 As2 l fs1 fs2 H1; revert fs2; induction H1 as [| [[f h] m] f1 l fs1 [Eh1 Hm1 Hr1 Hc1] _ IH];
      intros fs2 H2; inversion H2 as [| ? f2 ? fs2' [Eh2 _ Hr2 Hc2] H2']; subst; [ split; [ constructor | reflexivity ] |].
    cbn [fst snd] in *.
    destruct (ind_member D m) as [Mm |] eqn:Hj; [| contradiction ].
    pose proof (Fe _ _ _ (Hr1 Mm eq_refl) _ (Hr2 Mm eq_refl)) as Er.
    destruct (IH _ H2') as [Hrs IHe].
    assert (Ep : raw_fun_nparams f1 = raw_fun_nparams f2)
      by (apply (f_equal raw_fun_head_nparams) in Eh1, Eh2; cbn in Eh1, Eh2; congruence).
    split; [ constructor; [ split; [ exact Ep | exact Er ] | exact Hrs ] |].
    intros <-; pose proof (Fb _ _ _ _ _ _ _ _ _ (Hc1 Mm eq_refl) _ (Hc2 Mm eq_refl)) as Ec.
    rewrite (raw_fun_head_parts_eq f1 f2 (eq_trans Eh2 (eq_sym Eh1)) (eq_sym Er) (eq_sym Ec)), (IHe eq_refl); reflexivity.
  Qed.

  (** A command has one fill. *)
  Theorem fill_cmd_functional : forall c its1 its2, fill_cmd Θ Ξ B c its1 -> fill_cmd Θ Ξ B c its2 -> its1 = its2.
  Proof.
    pose proof fill_functional_all as (Fe & _ & _ & _ & _ & Fo & _ & Fm & _ & _ & Ft & _).
    intros c c1 c2 H1 H2.
    inversion H1; subst; inversion H2; subst;
      try solve [ exfalso; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end ].
    (** Two fills of one kind: part by part, in order *)
    all: repeat match goal with
      | Ha : fill_tele _ _ _ ?G ?D ?X, Hb : fill_tele _ _ _ ?G ?D ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (Ft _ _ _ Ha _ Hb); subst X
      | Ha : fill_exp _ _ _ ?G ?D ?X, Hb : fill_exp _ _ _ ?G ?D ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (Fe _ _ _ Ha _ Hb); subst X
      | Ha : fill_optional_exp _ _ _ ?G ?D ?X, Hb : fill_optional_exp _ _ _ ?G ?D ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (Fo _ _ _ Ha _ Hb); subst X
      | Ha : fill_mod _ _ _ ?G ?D ?X _, Hb : fill_mod _ _ _ ?G ?D ?Y _ |- _ =>
          assert_fails constr_eq X Y; destruct (Fm _ _ _ _ Ha _ _ Hb) as [? _]; subst X
      | Ha : fill_fields _ _ _ ?G ?D ?X, Hb : fill_fields _ _ _ ?G ?D ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (fill_fields_functional _ _ _ Ha _ Hb); subst X
      | Ha : fill_raw_decl _ _ _ ?R ?X, Hb : fill_raw_decl _ _ _ ?R ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (fill_raw_decl_functional _ _ _ Ha Hb); subst X
      | Ha : _ ⊢a ?M ⟹ ?W1, Hb : _ ⊢a ?M ⟹ ?W2 |- _ =>
          assert_fails constr_eq W1 W2;
          assert (W1 = W2) by (refine (@functional_alg_type_infer _ _ _ _ _ _ Ha Hb); exact Hg); subst W1
      | Ha : Forall2 (fill_raw_fun_head _ _ _ ?G) ?F ?X, Hb : Forall2 (fill_raw_fun_head _ _ _ ?G) ?F ?Y |- _ =>
          assert_fails constr_eq X Y; pose proof (fill_raw_fun_heads_functional _ _ _ _ Ha Hb) as E;
          injection E as <- <-
      | Ha : mdef_group _ _ ?G ?f ?F ?p ?m ?P ?D ?U ?M, Hb : mdef_group _ _ ?G ?f ?F ?p' ?m' ?P' ?D' ?U' ?M' |- _ =>
          assert_fails constr_eq p p'; destruct (mdef_group_functional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha Hb)
            as (<- & <- & <- & <- & <- & <-)
      end; try reflexivity.
    (** A mutual definition's bodies: their results, then their motives,
        then their clauses *)
    lazymatch goal with
    | Ha : Forall2 _ ?l (?a :: ?x), Hb : Forall2 _ ?l (?b :: ?y) |- _ =>
        destruct (fill_raw_fun_bodies_functional _ _ _ _ _ _ _ _ _ Ha Hb) as [Hrs He];
        rewrite (He (mdef_blocks_motives_eq _ _ _ _ _ Hrs)) in *; reflexivity
    end.
  Qed.

  (** A unit's parameter telescope has one fill. *)
  Theorem fill_params_functional : forall Δ Δ1 Δ2, fill_params Θ Ξ B Δ Δ1 -> fill_params Θ Ξ B Δ Δ2 -> Δ1 = Δ2.
  Proof.
    pose proof fill_functional_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ft & _).
    intros * H1 H2; exact (Ft _ _ _ H1 _ H2).
  Qed.
End Functional.

(** ** The Shape of a Filled Command *)

(** Whether a written command has terms to fill: all but a load, whose
    fill is the load. *)
Definition surface_cmd_terms (c : surface_cmd) : bool :=
  match c with
  | surface_cmd_load _ => false
  | _ => true
  end.

(** A command without terms is filled to the load it is. *)
Lemma fill_cmd_no_terms : forall Θ Ξ B c its, surface_cmd_terms c = false -> fill_cmd Θ Ξ B c its ->
    exists fp, c = surface_cmd_load fp /\ its = ci_core (core_cmd_load fp) :: nil.
Proof. intros * Ht H; destruct H; cbn in Ht; try discriminate; eauto. Qed.

(** A command with terms is filled to a core command that is neither a
    load nor a close, then the rest. *)
Lemma fill_cmd_head : forall Θ Ξ B c its, surface_cmd_terms c = true -> fill_cmd Θ Ξ B c its ->
    exists c0 its', its = ci_core c0 :: its' /\ (forall fp, c0 <> core_cmd_load fp) /\ (forall x pv, c0 <> core_cmd_close x pv).
Proof. intros * Ht H; destruct H; cbn in Ht; try discriminate; eexists _, _; (split; [ reflexivity | split; intros; discriminate ]). Qed.
