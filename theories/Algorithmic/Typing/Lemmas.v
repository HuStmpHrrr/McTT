From Stdlib Require Import Wf_nat.
From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Semantic Require Import Consequences.
From Mctt.Core.Syntactic Require Import CoreInversions Corollaries Fresh LevelEq.
From Mctt.Core.Syntactic Require Levels.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Core.Syntactic.System Require Import GlobalModules MemberWf.
From Mctt.Core.Semantic Require Import MemberWf Avoid.
Import Domain_Notations Fixed_Notations Wk_Notations.

Lemma me_noargs_spine : forall H R args pre, me_noargs H -> modexp_spine H = (R, args, pre) -> args = nil.
Proof.
  induction H as [| | H IH y | H IH N | ]; intros * Hn Hs; cbn in *; try (injection Hs; intros; subst; reflexivity).
  - destruct (modexp_spine H) as [[R0 args0] pre0]; injection Hs; intros; subst; eauto.
  - contradiction.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma functional_alg_type_infer : forall {Γ A A' M},
    Γ ⊢a M ⟹ A ->
    Γ ⊢a M ⟹ A' ->
    A = A'.
Proof.
  intros * HM1 HM2. gen A'.
  induction HM1; intros;
    inversion_clear HM2;
    functional_nbe_rewrite_clear;
    f_equiv;
    try reflexivity;
    intuition.
  (** A global against another rule for members: a chain from a unit has no
      argument, and a global's member type is its resolved type. *)
  all: try solve [ exfalso; match goal with
    | Hp : mod_qname ?H = Some _, Hs : modexp_spine ?H = (_, ?args, _), Ha : ?args = nil -> False |- _ =>
        rewrite (mod_qname_spine _ _ Hp) in Hs; injection Hs; intros; subst; contradiction end ].
  all: try solve [ match goal with
    | Hp : mod_qname ?H = Some _, Hm : member_type _ _ _ ?H _ (mr_term ?A1), Hr : gc_resolve _ _ _ = Some (ge_def _ _ ?A2 _) |- _ =>
        pose proof (mt_glob_type _ _ _ _ _ _ _ _ _ _ _ Hp Hm Hr); subst; functional_nbe_rewrite_clear; reflexivity end ].
  (** An unannotated [let]: the body's type, then the type of the rest. *)
  4:{ assert (A = A0) as <- by eauto. assert (C = C0) as <- by eauto.
      functional_nbe_rewrite_clear. reflexivity. }
  (** Module [let]s and members. *)
  4:{ assert (C = C0) as <- by eauto. functional_nbe_rewrite_clear. reflexivity. }
  4:{ match goal with
      | H1 : member_type _ _ _ ?H ?c (mr_term ?A1), H2 : member_type _ _ _ ?H ?c (mr_term ?A2) |- _ =>
          tryif constr_eq A1 A2 then fail
          else pose proof (proj1 (member_type_functional _ _) _ _ _ _ H1 _ H2) as E; injection E as E; subst A2
      end.
      functional_nbe_rewrite_clear. reflexivity. }
  4,5: exfalso; match goal with Hn : me_noargs ?H, Hs : modexp_spine ?H = _, Ha : _ = nil -> False |- _ =>
         apply Ha, (me_noargs_spine _ _ _ _ Hn Hs) end.
  4:{ match goal with Hs1 : modexp_spine ?H = _, Hs2 : modexp_spine ?H = _ |- _ =>
        rewrite Hs1 in Hs2; injection Hs2; intros; subst end; eauto. }
  (** [Π]: the two parts infer the same universes, so the two universes the
      side conditions normalise are the same. *)
  - assert (UA = UA0) as <- by intuition.
    assert (UB = UB0) as <- by intuition.
    assert (u = u0) as <- by (eapply is_univ_nf_functional; eassumption).
    assert (v = v0) as <- by (eapply is_univ_nf_functional; eassumption).
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (Πⁿ A B = Πⁿ A0 B0) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (C = C0) as <- by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (A = A0) as <- by mauto using ctx_lookup_functional.
    functional_nbe_rewrite_clear.
    reflexivity.
  (** Globals are resolved by a function, so both derivations read the same
      type. *)
  - assert (A = A0) as <- by congruence.
    functional_nbe_rewrite_clear.
    reflexivity.
Qed.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

End Fixed_GCtx.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (?Γ ⊢a ?M ⟹ ?A1), H2 : (?Γ ⊢a ?M ⟹ ?A2) |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2 using functional_alg_type_infer] | tactic_error A2 A1]; clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Universe Normal Forms as Types

    The universe a type infers is a universe normal form [u]; as a term it is
    [unf_tm u], which is a small universe at a level term or a large one.
    The declarative rules ask for a large universe, which a small one is below
    ([wf_subtyp_small_large]): this is the cumulativity the algorithmic layer
    relies on. *)
Lemma wf_exp_unf_large : forall {Γ A} {u : unf},
    Γ ⊢ A : unf_tm u ->
    Γ ⊢ A : Typeω@(unf_large u).
Proof.
  intros * HA; destruct u as [L | n]; cbn in *; [| exact HA ].
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of (fst L) (la_to_list (snd L))⟩ : Typeω@k) as [k Hk]
    by (gen_presups; eauto 2).
  assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_subtyp'; [ exact HA | apply wf_subtyp_small_large; [ assumption |] ].
  eapply wf_univ_lvl_inversion; exact Hk.
Qed.

Lemma wf_exp_unf_large_ge : forall {Γ A} {u : unf} {i : nat},
    unf_le u (unl i) ->
    Γ ⊢ A : unf_tm u ->
    Γ ⊢ A : Typeω@i.
Proof.
  intros * Hle HA; apply wf_exp_unf_large in HA.
  destruct u; cbn in *; (eapply lift_exp_ge; [| exact HA ]); lia.
Qed.

(** The universe of a [Π] ([unf_pi_tm]).  Two small universes join in the
    small tier when the codomain's level does not mention the bound variable:
    that level is the weakening of its un-weakening, which is a level of [Γ]
    ([level_nf_strengthen]); both parts are moved up to the join.  Otherwise
    the [Π] is at the large join. *)
Lemma wf_pi_unf_pi : forall {Γ A B} {u v : unf},
    Γ ⊢ A : unf_tm u ->
    Γ ▹ A ⊢ B : unf_tm v ->
    Γ ⊢ Π A B : unf_pi_tm u v.
Proof.
  intros * HA HB.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HAl : Γ ⊢ A : Typeω@(unf_large u)) by (apply wf_exp_unf_large; exact HA).
  assert (HBl : Γ ▹ A ⊢ B : Typeω@(unf_large v)) by (apply wf_exp_unf_large; exact HB).
  assert (HΓA : ⊢ Γ ▹ A) by mauto 2.
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [unf_pi_tm unf_max unf_tm unf_large fst snd] in *.
  - destruct (la_freshb 0 ys) eqn:Hf.
    + (** The small join. *)
      apply (proj2 (proj2 nf_freshb_iff)) in Hf.
      assert (HLB : lvl_exp_of d (la_to_list ys) = (lvl_exp_of d (la_to_list (la_unwk 0 ys)))[↑]ʷ)
        by exact (nf_fresh_unwk 0 (nf_lvl d ys) Hf).
      set (LA := lvl_exp_of c (la_to_list xs)) in *.
      set (LBs := lvl_exp_of d (la_to_list (la_unwk 0 ys))) in *.
      assert (HLA : Γ ⊢ LA : Level)
        by (assert (exists k, Γ ⊢ Type⟨LA⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto 2);
            eapply wf_univ_lvl_inversion; exact Hk).
      rewrite HLB in HB.
      assert (HLBl : Γ ▹ A ⊢ LBs[↑]ʷ : Level)
        by (assert (exists k, Γ ▹ A ⊢ Type⟨LBs[↑]ʷ⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto 2);
            eapply wf_univ_lvl_inversion; exact Hk).
      assert (HLBs : Γ ⊢ LBs : Level)
        by exact (level_nf_strengthen Γ A (nf_lvl d (la_unwk 0 ys)) HΓA HLBl).
      assert (Ht : Γ ⊢ maxl LA LBs : Level) by mauto 3.
      assert (Hw : Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
      apply wf_pi_small; [ exact Ht | |].
      * eapply wf_exp_subtyp'; [ exact HA |].
        apply wf_subtyp_suniv; [ assumption | assumption | assumption | apply lvl_sub_maxl_l; assumption ].
      * eapply wf_exp_subtyp'; [ exact HB |].
        assert (Hsub : Γ ⊢ Type⟨LBs⟩ ⊆ Type⟨maxl LA LBs⟩)
          by (apply wf_subtyp_suniv; [ assumption | assumption | assumption | apply lvl_sub_maxl_r; assumption ]).
        exact (wk_preserves_subtyp _ _ _ _ _ _ _ Hsub Hw).
    + apply wf_pi; assumption.
  - destruct xs; cbn [unf_tm]; (apply wf_pi; [ eapply lift_exp_ge; [| exact HAl ]; lia | assumption ]).
  - destruct ys; cbn [unf_tm]; (apply wf_pi; [ assumption | eapply lift_exp_ge; [| exact HBl ]; lia ]).
  - apply wf_pi; [ eapply lift_exp_ge; [| exact HAl ]; lia | eapply lift_exp_ge; [| exact HBl ]; lia ].
Qed.

(** The universe of a [Π] is a type. *)
Lemma wf_unf_pi_tm : forall {Γ A B} {u v : unf},
    Γ ⊢ A : unf_tm u ->
    Γ ▹ A ⊢ B : unf_tm v ->
    exists k, Γ ⊢ unf_pi_tm u v : Typeω@k.
Proof.
  intros * HA HB.
  pose proof (wf_pi_unf_pi HA HB) as H.
  gen_presups; eauto 2.
Qed.

(** A small universe at a literal level reads back as itself. *)
Lemma nbe_ty_suniv_lit : forall {Γ n W},
    nbe_ty_f Γ Type@n W ->
    W = Typeⁿ@n.
Proof.
  intros * Hn.
  dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst.
  match goal with H : eval_exp _ _ (a_llit _) _ _ |- _ => inversion H; subst end.
  dir_inversion_by_head read_typ; subst.
  match goal with H : Rnf ⇓ Levelᵈ (dlvl_lit n) in _ ↘ _ |- _ =>
    pose proof (read_nf_dlvl_lit n (length Γ)) as Hk;
    assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption) end.
  reflexivity.
Qed.



(** A premise [⟹ UA] with [is_univ_nf UA u] is sound as a typing at
    [unf_tm u], while the declarative rules ask for a large universe: such a
    hypothesis is lifted to [Typeω@(unf_large u)] ([wf_exp_unf_large]).
    [is_univ_nf_eq] turns the side condition into the shape of [UA]. *)
#[local] Tactic Notation "lift_univ_at" constr(Δ) constr(A) constr(u) :=
  repeat match goal with Hi : is_univ_nf ?UA u |- _ =>
    assert_fails (constr_eq UA (univ_nf u));
    rewrite (is_univ_nf_eq _ _ Hi) in * end;
  assert (wf_exp gc_deps gc_stack Δ (unf_tm u) A)
    by (rewrite <- nf_to_exp_univ_nf; mauto 2);
  assert (wf_exp gc_deps gc_stack Δ (a_typ (unf_large u)) A)
    by (apply wf_exp_unf_large; eassumption).

Lemma alg_type_sound :
  (forall {Γ A M}, Γ ⊢a M ⟸ A -> ⊢ Γ -> forall i, Γ ⊢ A : Typeω@i -> Γ ⊢ M : A) /\
    (forall {Γ A M}, Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A) /\
    (forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ) /\
    (forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) /\
    (forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H).
Proof.
  (** Every premise that asks for a type is [⟹ univ_nf u], so its soundness
      is a typing at [unf_tm u]. *)
  apply alg_type_mut_ind; intros; simpl_univ_nf;
    cbn [unf_tm] in *; try mautosolve 4.
  (** The cases below are dispatched on the shape of the goal rather than by
      position: a new rule would silently renumber positional selectors. *)
  all: lazymatch goal with
  (** An unannotated [let]: the type its body infers is a type. *)
  | |- _ ⊢ ℓ ≔ _ in _ : _ =>
      assert (HM : Γ ⊢ M : A) by eauto;
      assert (exists i, Γ ⊢ (A : exp) : Typeω@i) as [i HA] by (gen_presups; eauto 2);
      assert (⊢ Γ ▸ (A : exp) ≔ M) by mauto 3;
      assert (Γ ▸ (A : exp) ≔ M ⊢ B : C) by eauto;
      assert (exists j, Γ ▸ (A : exp) ≔ M ⊢ C : Typeω@j) as [j HCj] by (gen_presups; eauto 2);
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_def _ _ _ _ _ _ HA HM)) as HCs;
      assert (Γ ⊢ C[Id,,M] ≈ D : Typeω@j) as <- by mauto 3 using soundness_ty';
      eapply wf_let; [ exact HA | exact HM | eassumption | solve_let_ann ]
  (** A module [let]. *)
  | |- _ ⊢ ℓₘ _ in _ : _ =>
      assert (HU : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) by eauto;
      assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
      assert (Γ ▹ₘ U ⊢ B : C) by eauto;
      assert (exists j, Γ ▹ₘ U ⊢ C : Typeω@j) as [j HCj] by (gen_presups; eauto 2);
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_mod _ _ _ _ HU)) as HCs;
      assert (Γ ⊢ C[Id ,,ₘ me_lit U] ≈ D : Typeω@j) as <- by mauto 3 using soundness_ty';
      eapply wf_let_mod; eauto
  (** A member of an applied module: its root's member, applied. *)
  | Hs : modexp_spine _ = (_, _, _) |- _ ⊢ a_mem _ _ : _ =>
      assert (Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A) by eauto;
      assert (exists j, Γ ⊢ A : Typeω@j) as [j] by (gen_presups; eauto 2);
      eapply wf_mem_app; eauto
  (** A member, at the normal form of its canonical type. *)
  | Hmt : member_type _ _ _ _ _ (mr_term _) |- _ ⊢ a_mem _ _ : _ =>
      assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) by eauto;
      destruct (proj1 member_wf _ _ _ _ Hmt HH ltac:(intros; discriminate))
        as ([i HA] & HMu & _); cbn [mres_ty] in *;
      destruct (HMu eq_refl) as (M & HMe & HMt);
      assert (Γ ⊢ A ≈ B : Typeω@i) as <- by mauto 3 using soundness_ty';
      eapply wf_mem; [ eassumption | exact HH | exact Hmt | exact HA | exact HMe | exact HMt ]
  (** An extension by an assumption, a definition or a module. *)
  | |- wf_ext_eq _ _ _ (_ ▹ _) _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      lift_univ_at (Ψ ++ Γ) A u;
      eapply wf_ext_eq_ass; [ eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto ]
  | |- wf_ext_eq _ _ _ (_ ▸ _ ≔ _) _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      lift_univ_at (Ψ ++ Γ) A u;
      assert (Ψ ++ Γ ⊢ M : A) by eauto;
      eapply wf_ext_eq_def;
        [ eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto
        | eapply wf_exp_eq_refl; eauto | eauto | eauto ]
  | |- wf_ext_eq _ _ _ (_ ▹ₘ _) _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      eapply wf_ext_eq_mod; eauto
  (** A unit that is an alias. *)
  | |- wf_unit_eq _ _ _ _ _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      eapply wf_unit_eq_alias; eauto
  (** A module expression applied. *)
  | Hmt : member_type _ _ _ _ nil (mr_mod _) |- wf_modexp_eq _ _ _ _ _ =>
      assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) by eauto;
      destruct (proj1 member_wf _ _ _ _ Hmt HH ltac:(intros; discriminate)) as ([i HA] & _);
      cbn [mres_ty] in HA;
      match goal with Hv : tele_view _ = Some _ |- _ =>
        destruct (tele_view_wf _ _ _ _ _ HA Hv) as (_ & HB & _) end;
      assert (Γ ⊢ N : B) by eauto;
      eapply wf_me_app; eauto using wf_exp_eq_refl
  | _ => idtac
  end.
  (** The join of two levels is one application deeper than [mautosolve 4]
      reaches: both arguments are checked against [Level]. *)
  all: try solve [ apply wf_maxl; mauto 4 ].
  (** A small universe: its level is a level, and the universe above is the
      normal form of [Type⟨succl M⟩]. *)
  all: try match goal with
    | Hn : nbe_ty_f _ (a_univ (succl ?M)) ?W |- _ ⊢ a_univ ?M : _ =>
        assert (Γ ⊢ M : Level) by mauto 3;
        assert (Γ ⊢ Type⟨succl M⟩ : Typeω@0) by (apply wf_univ_large_tm; mauto 3);
        assert (Γ ⊢ Type⟨succl M⟩ ≈ W : Typeω@0) as <- by mauto 3 using soundness_ty';
        apply wf_univ; assumption
    end.
  - assert (Γ ⊢ M : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Typeω@i) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Typeω@(max i j)) by mauto 3 using lift_exp_max_right.
    assert (Γ ⊢ B : Typeω@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Γ ⊢ A ⊆ B) by mauto 2 using alg_subtyping_sound.
    mauto 3.
  - assert (Γ ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ Γ ▹ ℕ) by mauto 2.
    lift_univ_at (Γ ▹ ℕ) A u.
    assert (⊢ Γ ▹ ℕ ▹ A) by mauto 3.
    assert (Γ ⊢ M : ℕ) by mauto 2.
    assert (Γ ⊢ A[Id,,zero] : Typeω@(unf_large u)) by mauto 3.
    assert (Γ ▹ ℕ ▹ A ⊢ A[Wk ⨟ Wk,,succ #1] : Typeω@(unf_large u)) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Typeω@(unf_large u)) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert (Γ ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ Γ ▹ ⊥) by mauto 2.
    lift_univ_at (Γ ▹ ⊥) A u.
    assert (Γ ⊢ M : ⊥) by mauto 2.
    assert (Γ ⊢ A[Id,,M] : Typeω@(unf_large u)) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Typeω@(unf_large u)) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  (** A [Π] is at the normal form of the join of the universes of its
      parts. *)
  - lift_univ_at Γ A u.
    assert (⊢ Γ ▹ A) by mauto 3.
    match goal with HB : is_univ_nf ?UB v |- _ => rewrite (is_univ_nf_eq _ _ HB) in * end.
    assert (HB' : Γ ▹ A ⊢ B : unf_tm v) by (rewrite <- nf_to_exp_univ_nf; mauto 2).
    match goal with HA : Γ ⊢ A : unf_tm u |- _ => pose proof (wf_pi_unf_pi HA HB') as HPi end.
    assert (exists k, Γ ⊢ unf_pi_tm u v : Typeω@k) as [k Hk] by (gen_presups; eauto 2).
    assert (Γ ⊢ unf_pi_tm u v ≈ W : Typeω@k) by (eapply soundness_ty'; eassumption).
    eapply wf_exp_subtyp'; [ exact HPi | eapply wf_subtyp_refl'; eassumption ].
  (** [λ]: the annotation is a type, so the function is of the [Π] of its
      normal form and the body's type. *)
  - lift_univ_at Γ A u.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ⊢ A ≈ C : Typeω@(unf_large u)) by mauto 2 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 2.
    assert (exists j, Γ ▹ A ⊢ B : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ Π A B ≈ Π C B : Typeω@(max (unf_large u) j)) as <- by mauto 3.
    mauto 3.
  - assert (Γ ⊢ M : Π A B) by mauto 2.
    assert (exists i, Γ ⊢ Π A B : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Typeω@i /\ Γ ▹ (A : exp) ⊢ B : Typeω@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 2.
    assert (Γ ⊢ B[Id,,N] ≈ C : Typeω@i) as <- by mauto 4 using soundness_ty'.
    mauto 3.
  - lift_univ_at Γ A u.
    assert (Γ ⊢ M : A) by mauto 2.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 2.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3.
    assert (Γ ⊢ C[Id,,M] ≈ D : Typeω@j) as <- by mauto 3 using soundness_ty'.
    mauto 3.
  - assert (Γ ⊢ #x : A) by mauto 2.
    assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 2.
    assert (Γ ⊢ A ≈ B : Typeω@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
  (** The resolution premise of [wf_mem_glob] is the same function call, so
      the declarative rule applies directly; [soundness_ty'] relates the
      inferred normal form to the declarative type. *)
  - assert (Γ ⊢ a_mem H x : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 3 using wf_glob_typ.
    assert (Γ ⊢ A ≈ C : Typeω@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 alg_type_sound); eassumption.
Qed.

Lemma alg_type_infer_sound : forall {Γ A M},
    Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 (proj2 alg_type_sound)); eassumption.
Qed.

Lemma alg_ext_sound : forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
Proof. intros; eapply (proj1 (proj2 (proj2 alg_type_sound))); eassumption. Qed.

Lemma alg_unit_sound : forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 alg_type_sound)))); eassumption. Qed.

Lemma alg_modexp_sound : forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros; eapply (proj2 (proj2 (proj2 (proj2 alg_type_sound)))); eassumption. Qed.

(** The same after soundness, where the typing comes from the derivation
    rather than from an induction hypothesis. *)
#[local] Tactic Notation "lift_univ_sound" constr(Δ) constr(A) constr(u) :=
  repeat match goal with Hi : is_univ_nf ?UA u |- _ =>
    assert_fails (constr_eq UA (univ_nf u));
    rewrite (is_univ_nf_eq _ _ Hi) in * end;
  assert (wf_exp gc_deps gc_stack Δ (unf_tm u) A)
    by (rewrite <- nf_to_exp_univ_nf; mauto 3 using alg_type_infer_sound);
  assert (wf_exp gc_deps gc_stack Δ (a_typ (unf_large u)) A)
    by (apply wf_exp_unf_large; eassumption).

Lemma alg_type_infer_normal : forall {Γ A A' M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A' ->
    A = A'.
Proof.
  intros * ? Hinfer Hnbe. gen A'.
  assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (symmetry; eapply nbe_ty_suniv_lit; eassumption);
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  (** A small universe infers the normal form of [Type⟨succl M⟩], which
      normalises to itself. *)
  - assert (Γ ⊢ M : Level) by (eapply alg_type_check_sound; mauto 3).
    assert (Γ ⊢ Type⟨succl M⟩ : Typeω@0) by (apply wf_univ_large_tm; mauto 3).
    eapply idempotent_nbe_ty; eassumption.
  - assert (Γ ⊢ ℕ : Typeω@0) by mauto 3.
    assert (Γ ⊢ M : ℕ) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ℕ) by mauto 3.
    lift_univ_sound (Γ ▹ ℕ) A u.
    f_equiv; mautosolve 4.
  - assert (Γ ⊢ ⊥ : Typeω@0) by mauto 3.
    assert (Γ ⊢ M : ⊥) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ⊥) by mauto 3.
    lift_univ_sound (Γ ▹ ⊥) A u.
    f_equiv; mautosolve 4.
  (** [Π]: the universe it infers is a normal form, which normalises to
      itself. *)
  - lift_univ_sound Γ A u.
    assert (⊢ Γ ▹ A) by mauto 3.
    lift_univ_sound (Γ ▹ A) B v.
    match goal with HA : Γ ⊢ A : unf_tm u, HB : Γ ▹ A ⊢ B : unf_tm v |- _ =>
      destruct (wf_unf_pi_tm HA HB) as [k Hk] end.
    eapply idempotent_nbe_ty; eassumption.
  - lift_univ_sound Γ A u.
    assert (Γ ⊢ A ≈ C : Typeω@(unf_large u)) by mauto 3 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (⊨ Γ ▹ (C : exp) ≈ Γ ▹ A) by mauto 3.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    assert (initial_env_f (Γ ▹ (C : exp)) (ρ ↦ ⇑! a (length Γ))) by mauto 3.
    assert (nbe_ty_f Γ A C) by mauto 3.
    assert (nbe_ty_f Γ C A0) by mauto 3.
    replace A0 with C by mauto 3.
    assert (nbe_ty_f (Γ ▹ (C : exp)) B B') by mauto 3.
    assert (nbe_ty_f (Γ ▹ A) B B') by mauto 4 using ctxeq_nbe_ty_eq'; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ M : Πⁿ A B) by mauto 3 using alg_type_infer_sound.
    assert (exists i, Γ ⊢ Π A B : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Typeω@i /\ Γ ▹ (A : exp) ⊢ B : Typeω@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 3 using alg_type_check_sound.
    assert (Γ ⊢ B[Id,,N] : Typeω@i) by mauto 3; (f_equiv; mautosolve 4).
  - lift_univ_sound Γ A u.
    assert (Γ ⊢ M : A) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
    assert (exists i, Γ ⊢ (A : exp) : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (⊢ Γ ▸ (A : exp) ≔ M) by mauto 2.
    assert (Γ ▸ (A : exp) ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▸ (A : exp) ≔ M ⊢ C : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3; (f_equiv; mautosolve 4).
  - assert (HU : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
    assert (Γ ▹ₘ U ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ₘ U ⊢ C : Typeω@j) as [j HCj] by (gen_presups; eauto 2).
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_mod _ _ _ _ HU)); (f_equiv; mautosolve 4).
  - match goal with Hm : member_type _ _ _ _ _ (mr_term _) |- _ => rename Hm into Hmt end.
    destruct (proj1 member_wf _ _ _ _ Hmt ltac:(eapply alg_modexp_sound; eassumption) ltac:(intros; discriminate))
      as ([i HA] & _); cbn [mres_ty] in HA.
    (f_equiv; mautosolve 4).
  - eapply IHHinfer; [ assumption | mauto 3 using alg_type_infer_sound | assumption ].
  - assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 2; (f_equiv; mautosolve 4).
  (** A global infers the normal form of a type of the ambient context, so
      [idempotent_nbe_ty] closes it; that it is a type is [wf_glob_typ]. *)
  - assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 3 using wf_glob_typ.
    (f_equiv; mautosolve 4).
Qed.

Hint Resolve alg_type_infer_normal : mctt.

(** A type checked against a large universe infers a universe at an index
    below it: with the small tier that index need not be a large one. *)
Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i).
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [ contradiction | |].
  - exists Typeωⁿ@i0, (unl i0); split; [ exact Hinfer | split; [ constructor | cbn; assumption ] ].
  - exists (univⁿ c xs), (uns (c, xs)); split; [ exact Hinfer | split; [ constructor | exact I ] ].
Qed.

Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M A B i},
    ⊢ Γ ->
    Γ ⊢ Π A B : Typeω@i ->
    Γ ⊢a M ⟸ Π A B ->
    exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Typeω@i /\ Γ ▹ A ⊢a B' ⊆ B.
Proof.
  intros * ? ? Hcheck.
  assert (Γ ⊢ A : Typeω@i /\ Γ ▹ A ⊢ B : Typeω@i) as [] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' C Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  inversion Hnbe1; subst.
  functional_initial_env_rewrite_clear.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  simpl in *.
  assert (Γ ⊢ M : Πⁿ A0 B0) by mauto 3 using alg_type_infer_sound.
  assert (exists j, Γ ⊢ Π A0 B0 : Typeω@j) as [j] by (gen_presups; eauto 2).
  assert (Γ ⊢ A0 : Typeω@j /\ Γ ▹ (A0 : exp) ⊢ B0 : Typeω@j) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty_f Γ A A0) by mauto 3.
  assert (Γ ⊢ A ≈ A0 : Typeω@i) by mauto 3 using soundness_ty'.
  repeat split; mauto 3.
  assert (initial_env_f (Γ ▹ A) (ρ ↦ ⇑! a (length Γ))) by mauto 3.
  assert (nbe_ty_f (Γ ▹ A) B B') by mauto 3.
  assert (initial_env_f (Γ ▹ (A0 : exp)) (ρ ↦ ⇑! a0 (length Γ))) by mauto 3.
  assert (nbe_ty_f (Γ ▹ (A0 : exp)) B0 B0) by mauto 3.
  assert (⊨ Γ ▹ (A0 : exp) ≈ Γ ▹ A) by mauto 3.
  assert (nbe_ty_f (Γ ▹ A) B0 B0) by mauto 4 using ctxeq_nbe_ty_eq'.
  mauto 3.
Qed.

Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.

Lemma alg_type_check_subtyp : forall {Γ A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊢a M ⟸ A'.
Proof.
  intros * [] **.
  assert (Γ0 ⊢a B ⊆ A') by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

Hint Resolve alg_type_check_subtyp : mctt.

Corollary alg_type_check_conv : forall {Γ i A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ≈ A' : Typeω@i ->
    Γ ⊢a M ⟸ A'.
Proof.
  mauto 3.
Qed.

Hint Resolve alg_type_check_conv : mctt.

Lemma nbe_ty_pi_inv : forall Γ B C W, nbe_ty_f Γ (Π B C) W ->
    exists B' C', W = Πⁿ B' C' /\ nbe_ty_f Γ B B'.
Proof.
  intros * Hnbe.
  inversion Hnbe; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  do 2 eexists; split; [ reflexivity | econstructor; eassumption ].
Qed.

(** ** Unannotated Definitions

    The number of unannotated [let]s in a term, the measure of the outer
    induction of completeness: the body of an unannotated [let] is checked in
    a context refined to the type its definiens infers, by a derivation which
    is not a subderivation, but whose subject has fewer of them. *)
Fixpoint exp_lets (M : exp) : nat :=
  match M with
  | a_succ M | a_succl M | a_univ M => exp_lets M
  | a_maxl M N => exp_lets M + exp_lets N
  | a_natrec A MZ MS M => exp_lets A + exp_lets MZ + exp_lets MS + exp_lets M
  | a_exfalso A M => exp_lets A + exp_lets M
  | a_pi A B => exp_lets A + exp_lets B
  | a_fn A M => exp_lets A + exp_lets M
  | a_app M N => exp_lets M + exp_lets N
  | a_let b B => bnd_lets b + exp_lets B
  | a_mem H _ => modexp_lets H
  | _ => 0
  end
with modexp_lets (H : modexp) : nat :=
  match H with
  | me_mem H _ => modexp_lets H
  | me_app H N => modexp_lets H + exp_lets N
  | me_lit U => gunit_lets U
  | _ => 0
  end
with bnd_lets (b : bnd) : nat :=
  match b with
  | b_def (Some A) M => exp_lets A + exp_lets M
  | b_def None M => S (exp_lets M)
  | b_mod U => gunit_lets U
  end
with gunit_lets (U : gunit) : nat :=
  match U with
  | gu_mk Δ D =>
      (fix tele_lets (Δ : list centry) : nat :=
         match Δ with
         | nil => 0
         | e :: Δ' => centry_lets e + tele_lets Δ'
         end) Δ + moddef_lets D
  end
with moddef_lets (D : moddef) : nat :=
  match D with
  | md_body Φ => gmod_lets Φ
  | md_alias E => modexp_lets E
  end
with gmod_lets (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ E => gmod_lets Φ + gentry_lets E
  | gm_open Φ H _ => gmod_lets Φ + modexp_lets H
  end
with gentry_lets (E : gentry) : nat :=
  match E with
  | ge_def _ _ A B => exp_lets A + match B with Some M => exp_lets M | None => 0 end
  | ge_mod _ U => gunit_lets U
  end
with centry_lets (e : centry) : nat :=
  match e with
  | ce_ass A => exp_lets A
  | ce_def A M => exp_lets A + exp_lets M
  | ce_mod U => gunit_lets U
  end.

Fixpoint ctx_lets (Γ : ctx) : nat :=
  match Γ with
  | nil => 0
  | e :: Γ' => centry_lets e + ctx_lets Γ'
  end.

Lemma gunit_lets_mk : forall Δ D, gunit_lets (gu_mk Δ D) = ctx_lets Δ + moddef_lets D.
Proof. intros; cbn; f_equal; induction Δ; cbn; congruence. Qed.

Lemma ctx_lets_app : forall Ψ Γ, ctx_lets (Ψ ++ Γ) = ctx_lets Ψ + ctx_lets Γ.
Proof. induction Ψ; intros; cbn; [| rewrite IHΨ ]; lia. Qed.

Lemma body_ctx_lets : forall Φ, ctx_lets (body_ctx Φ) <= gmod_lets Φ.
Proof.
  induction Φ as [| Φ IH x [b pv A [M |] | pm U] | Φ IH c its ]; cbn; rewrite ?ctx_lets_app; [ lia .. |].
  enough (ctx_lets (List.repeat (ce_ass a_nat) (List.length its)) = 0) by lia.
  induction (List.length its); cbn; auto.
Qed.

Lemma exp_lets_apps : forall M args,
    exp_lets (apps M args) = exp_lets M + List.fold_right (fun N n => exp_lets N + n) 0 args.
Proof. intros M args; revert M; induction args; intros; cbn; [ lia | rewrite IHargs; cbn; lia ]. Qed.

Lemma exp_lets_member_ref : forall ch H, ch <> nil -> exp_lets (member_ref H ch) = modexp_lets H.
Proof.
  induction ch as [| y ch IH]; intros H Hch; [ congruence |].
  destruct ch as [| z ch]; [ reflexivity |].
  change (member_ref H (y :: z :: ch)) with (member_ref (me_mem H y) (z :: ch)).
  rewrite IH by discriminate; reflexivity.
Qed.

Lemma exp_lets_spine : forall H R args pre x,
    modexp_spine H = (R, args, pre) ->
    exp_lets (apps (member_ref R (pre ++ x :: nil)) args) = modexp_lets H.
Proof.
  intros; rewrite exp_lets_apps, exp_lets_member_ref by (destruct pre; discriminate).
  match goal with Hs : modexp_spine _ = _ |- _ => revert R args pre Hs end.
  induction H as [| | H IH y | H IH N | ]; intros R args pre Hs; cbn in Hs |- *;
    try (injection Hs as <- <- <-; cbn; lia).
  - destruct (modexp_spine H) as [[R0 args0] pre0]; injection Hs as <- <- <-; eauto.
  - destruct (modexp_spine H) as [[R0 args0] pre0]; injection Hs as <- <- <-.
    rewrite List.fold_right_app; cbn.
    specialize (IH _ _ _ eq_refl).
    enough (forall l k, List.fold_right (fun N n => exp_lets N + n) k l
                   = List.fold_right (fun N n => exp_lets N + n) 0 l + k) as E by (rewrite E; lia).
    induction l; intros; cbn; [ lia | rewrite IHl; lia ].
Qed.

Ltac lets_bound :=
  repeat match goal with
         | Hs : modexp_spine ?H = (?R, ?args, ?pre)
           |- context [exp_lets (apps (member_ref ?R (?pre ++ ?x :: nil)) ?args)] =>
             rewrite (exp_lets_spine H R args pre x Hs)
         end;
  repeat first
    [ progress rewrite ?gunit_lets_mk, ?ctx_lets_app in *
    | progress cbn [exp_lets modexp_lets bnd_lets moddef_lets gmod_lets
                    gentry_lets centry_lets ctx_lets] in * ];
  repeat match goal with
         | Φ : gmod |- _ =>
             lazymatch goal with
             | _ : ctx_lets (body_ctx Φ) <= gmod_lets Φ |- _ => fail
             | _ => pose proof (body_ctx_lets Φ)
             end
         end;
  lia.

(** A term that infers a universe checks against every universe above it: the
    algorithmic counterpart of the universe subtyping rules, against a large
    universe and against a small one at a literal level. *)
Lemma alg_type_check_typ_of : forall Γ A UA (u : unf) i,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    unf_le u (unl i) ->
    Γ ⊢a A ⟸ Typeω@i.
Proof.
  intros * HΓ Hi Hu Hle.
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in *.
  apply alg_subtyping_complete.
  destruct u as [L | j]; cbn [unf_tm unf_le] in *.
  - apply wf_subtyp_small_large; [ assumption |].
    assert (exists k, Γ ⊢ Type⟨lvl_exp_of (fst L) (la_to_list (snd L))⟩ : Typeω@k) as [k Hk]
      by (gen_presups; eauto 2).
    eapply wf_univ_lvl_inversion; exact Hk.
  - apply wf_subtyp_ge; [ assumption | lia ].
Qed.

Lemma alg_type_check_suniv : forall Γ A UA (u : unf) m,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    unf_le u (unf_lit m) ->
    Γ ⊢a A ⟸ Type@m.
Proof.
  intros * HΓ Hi Hu Hle.
  destruct u as [[c xs] | j]; cbn [unf_le unf_lit] in Hle; [| contradiction ].
  (** A level below a literal has no atom. *)
  assert (xs = la_nil) as -> by exact (lvl_le_lit_closed (c, xs) m Hle).
  assert (c <= m) by (apply lvl_le_real in Hle; exact Hle).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf.
  apply alg_subtyping_complete.
  cbn [unf_tm fst snd la_to_list lvl_exp_of].
  apply wf_subtyp_suniv_le; [ assumption | lia ].
Qed.

(** A type checked against a small universe at a literal level infers a
    universe below it. *)
Lemma alg_type_check_suniv_implies_alg_type_infer_univ : forall {Γ A n},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type@n ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unf_lit n).
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  apply nbe_ty_suniv_lit in Hnbe2 as ->.
  inversion Hnfsub; subst; [ contradiction |].
  exists (univⁿ c xs), (uns (c, xs)); split; [ exact Hinfer | split; [ constructor | assumption ] ].
Qed.

(** The same at a level term: the inferred universe is small, at a canonical
    level below the one [Type⟨t⟩] normalizes to. *)
Lemma alg_type_check_suniv_tm_implies_alg_type_infer_univ : forall {Γ A t},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L') /\ lvl_le L L'.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' B' Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  pose proof Hnbe2 as Hn.
  inversion Hn; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  destruct L as [d ys]; unfold nf_univ_of in *; cbn [fst snd] in *.
  inversion Hnfsub; subst; [ contradiction |].
  exists (c, xs), (d, ys); split; [ exact Hinfer | split; [ exact Hnbe2 | assumption ] ].
Qed.

(** ** Completeness of the [Π] Rule

    A [Π] whose parts infer universes checks against every type its
    universe ([unf_pi_tm]) is below. *)
Lemma alg_pi_check_of_infer : forall Γ A B UA UB (u v : unf) T k,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹ A ⊢a B ⟹ UB ->
    is_univ_nf UA u ->
    is_univ_nf UB v ->
    Γ ⊢ T : Typeω@k ->
    Γ ⊢ unf_pi_tm u v ⊆ T ->
    Γ ⊢a Π A B ⟸ T.
Proof.
  intros * HΓ HAi HBi Hu Hv HT Hsub.
  assert (HA : Γ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu); eapply alg_type_infer_sound; eassumption).
  assert (⊢ Γ ▹ A) by (eapply wf_ctx_extend, wf_exp_unf_large; exact HA).
  assert (HB : Γ ▹ A ⊢ B : unf_tm v)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hv); eapply alg_type_infer_sound; eassumption).
  destruct (wf_unf_pi_tm HA HB) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW HeqW]].
  econstructor; [ eapply ati_pi; eassumption |].
  apply alg_subtyping_complete.
  etransitivity; [| exact Hsub ].
  eapply wf_subtyp_refl'; symmetry; exact HeqW.
Qed.

(** The universe a [Π] infers is a universe normal form: [unf_pi_tm] is a
    universe term, which reads back as one. *)
Lemma nbe_ty_unf_pi_tm_univ : forall Γ (u v : unf) W,
    nbe_ty_f Γ (unf_pi_tm u v) W ->
    exists w, is_univ_nf W w.
Proof.
  intros * Hn.
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [unf_pi_tm unf_max unf_tm fst snd] in Hn;
    [ destruct (la_freshb 0 ys) | destruct xs | destruct ys |];
    cbn [unf_tm] in Hn;
    dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst;
    dir_inversion_by_head read_typ; subst;
    eexists; first [ constructor | match goal with |- is_univ_nf (nf_univ_of ?L) _ => destruct L; constructor end ].
Qed.

(** A [Π] whose parts infer universes infers one. *)
Lemma alg_pi_infer_univ : forall Γ A B UA UB (u v : unf),
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹ A ⊢a B ⟹ UB ->
    is_univ_nf UA u ->
    is_univ_nf UB v ->
    exists W w, Γ ⊢a Π A B ⟹ W /\ is_univ_nf W w /\ nbe_ty_f Γ (unf_pi_tm u v) W.
Proof.
  intros * HΓ HAi HBi Hu Hv.
  assert (HA : Γ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu); eapply alg_type_infer_sound; eassumption).
  assert (⊢ Γ ▹ A) by (eapply wf_ctx_extend, wf_exp_unf_large; exact HA).
  assert (HB : Γ ▹ A ⊢ B : unf_tm v)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hv); eapply alg_type_infer_sound; eassumption).
  destruct (wf_unf_pi_tm HA HB) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW _]].
  destruct (nbe_ty_unf_pi_tm_univ _ _ _ _ HW) as [w Hw].
  exists W, w; split; [ eapply ati_pi; eassumption | split; assumption ].
Qed.

(** The universe of a [Π] of two types below a large universe is below it. *)
Lemma unf_pi_tm_large : forall Γ (u v : unf) i k,
    ⊢ Γ ->
    Γ ⊢ unf_pi_tm u v : Typeω@k ->
    unf_le u (unl i) ->
    unf_le v (unl i) ->
    Γ ⊢ unf_pi_tm u v ⊆ Typeω@i.
Proof.
  intros * HΓ Hk Hu Hv.
  destruct u as [[c xs] | i1], v as [[d ys] | j1]; cbn [unf_pi_tm unf_le fst snd] in *.
  - destruct (la_freshb 0 ys).
    + apply wf_subtyp_small_large; [ exact HΓ | eapply wf_univ_lvl_inversion; exact Hk ].
    + apply wf_subtyp_ge; [ exact HΓ | lia ].
  - destruct xs; cbn [unf_max unf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - destruct ys; cbn [unf_max unf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - cbn [unf_max unf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia ].
Qed.

(** The small [Π] at a level term.  The codomain's universe is below the
    normal form of the weakened level, which is fresh ([nbe_ty_wk_fresh]), so
    the codomain's level is fresh too ([lvl_le_la_fresh]) and the [Π] is in
    the small tier, at a level below [L]: the domain's is below [L] in [Γ],
    and the codomain's below [L[↑]ʷ] in [Γ ▹ A], which strengthens. *)
Lemma alg_pi_small_complete : forall Γ L A B,
    Γ ⊢ L : Level ->
    Γ ⊢ A : Type⟨L⟩ ->
    Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a A ⟸ Type⟨L⟩ ->
    Γ ▹ A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π A B ⟸ Type⟨L⟩.
Proof.
  intros * HL HA HB HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (HΓA : ⊢ Γ ▹ A) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓ HAc) as (LA & Lt & HAi & HnL & HLA).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓA HBc) as (LB & L' & HBi & HnL' & HLB).
  assert (HfL' : la_fresh 0 (snd L'))
    by exact (nbe_ty_wk_fresh _ _ Γ A Type⟨L⟩ _ HnL').
  pose proof (lvl_le_la_fresh 0 _ _ HLB HfL') as HfLB.
  destruct LA as [c xs], LB as [d ys], Lt as [e zs], L' as [f ws]; cbn [fst snd] in *.
  eapply (alg_pi_check_of_infer _ _ _ _ _ (uns (c, xs)) (uns (d, ys)) _ 0);
    [ exact HΓ | exact HAi | exact HBi | constructor | constructor | apply wf_univ_large_tm; assumption |].
  cbn [unf_pi_tm fst snd].
  assert (Hfb : la_freshb 0 ys = true) by (apply (proj2 (proj2 nf_freshb_iff)); exact HfLB).
  rewrite Hfb.
  (** The levels and their atoms. *)
  assert (HAi' : Γ ⊢ A : Type⟨lvl_exp_of c (la_to_list xs)⟩) by (eapply alg_type_infer_sound in HAi; eassumption).
  assert (HBi' : Γ ▹ A ⊢ B : Type⟨lvl_exp_of d (la_to_list ys)⟩) by (eapply alg_type_infer_sound in HBi; eassumption).
  assert (HLAe : Γ ⊢ lvl_exp_of c (la_to_list xs) : Level)
    by (assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (la_to_list xs)⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto 2);
        eapply wf_univ_lvl_inversion; exact Hk).
  assert (HLBe : Γ ▹ A ⊢ lvl_exp_of d (la_to_list ys) : Level)
    by (assert (exists k, Γ ▹ A ⊢ Type⟨lvl_exp_of d (la_to_list ys)⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto 2);
        eapply wf_univ_lvl_inversion; exact Hk).
  assert (HTt : Γ ⊢ Type⟨L⟩ ≈ (nf_univ_of (e, zs) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ apply wf_univ_large_tm; assumption | exact HnL ]).
  assert (HTt' : Γ ▹ A ⊢ Type⟨L[↑]ʷ⟩ ≈ (nf_univ_of (f, ws) : exp) : Typeω@0).
  { eapply soundness_ty'; [| exact HnL' ].
    apply wf_univ_large_tm; [ assumption |].
    eapply (wk_preserves_exp _ _ _ _ Level); [ exact HL | mauto 2 ]. }
  cbn [nf_to_exp nf_univ_of fst snd] in HTt, HTt'.
  apply exp_eq_suniv_tm_inj in HTt, HTt'.
  assert (HLt : Γ ⊢ lvl_exp_of e (la_to_list zs) : Level) by (gen_presups; assumption).
  assert (HL't : Γ ▹ A ⊢ lvl_exp_of f (la_to_list ws) : Level) by (gen_presups; assumption).
  assert (HLBeq : lvl_exp_of d (la_to_list ys) = (lvl_exp_of d (la_to_list (la_unwk 0 ys)))[↑]ʷ)
    by exact (nf_fresh_unwk 0 (nf_lvl d ys) HfLB).
  set (LAe := lvl_exp_of c (la_to_list xs)) in *.
  set (LBs := lvl_exp_of d (la_to_list (la_unwk 0 ys))) in *.
  assert (HLBl : Γ ▹ A ⊢ LBs[↑]ʷ : Level) by (rewrite <- HLBeq; exact HLBe).
  assert (HLBs : Γ ⊢ LBs : Level) by exact (level_nf_strengthen Γ A (nf_lvl d (la_unwk 0 ys)) HΓA HLBl).
  apply wf_subtyp_suniv; [ exact HΓ | mauto 3 | exact HL |].
  apply lvl_sub_maxl_lub; [ exact HLAe | exact HLBs | exact HL | |].
  - (** The domain's level is below [L]. *)
    unfold lvl_sub.
    pose proof (lvl_exp_of_le c xs e zs HΓ (lvl_exp_of_la_wf _ _ HLAe) (lvl_exp_of_la_wf _ _ HLt) HLA) as Hle.
    transitivity (maxl LAe (lvl_exp_of e (la_to_list zs)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt ] |].
    transitivity (lvl_exp_of e (la_to_list zs)); [ exact Hle | symmetry; exact HTt ].
  - (** The codomain's, below [L[↑]ʷ] in [Γ ▹ A], strengthened. *)
    unfold lvl_sub.
    pose proof (lvl_exp_of_le d ys f ws HΓA (lvl_exp_of_la_wf _ _ HLBe) (lvl_exp_of_la_wf _ _ HL't) HLB) as Hle.
    rewrite HLBeq in Hle.
    assert (Hlong : Γ ▹ A ⊢ maxl LBs[↑]ʷ L[↑]ʷ ≈ L[↑]ʷ : Level).
    { transitivity (maxl LBs[↑]ʷ (lvl_exp_of f (la_to_list ws)));
        [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt' ] |].
      transitivity (lvl_exp_of f (la_to_list ws)); [ exact Hle | symmetry; exact HTt' ]. }
    exact (exp_eq_strengthen nil Γ A (maxl LBs L) L Level ltac:(constructor) HΓA ltac:(mauto 3) HL Hlong).
Qed.

(** Completeness, for terms and for the module judgments at once, since a
    unit's body holds terms and a term may hold a unit.  The global context is
    an index of the judgments, so it is fixed for the induction, as in
    [subtyp_spec]. *)
Lemma alg_type_complete_lets : forall n,
  (forall Θ Ξ Γ, wf_ctx Θ Ξ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     (ctx_lets Ψ <= n -> Γ ⊢aˣ Ψ) /\ (ctx_lets Ψ' <= n -> Γ ⊢aˣ Ψ')) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack ->
     (modexp_lets H <= n -> Γ ⊢aᵐ H) /\ (modexp_lets H' <= n -> Γ ⊢aᵐ H')).
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind.
  apply syntactic_wf_mut_ind; intros; try exact I; subst; destruct_let_ann;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with IH : user_exp ?M -> _ |- _ => specialize (IH (user_exp_all M)) end;
    try match goal with Hue : user_exp _ |- _ => clear Hue end;
    try match goal with |- (_ <= n -> _) /\ (_ <= n -> _) => split; intros end;
    repeat match goal with
           | IH : _ <= n -> _ |- _ => specialize (IH ltac:(lets_bound))
           | IH : (_ <= n -> ?P) /\ ?Q |- _ =>
               let H' := fresh in
               assert (H' : P /\ Q) by (split; [ apply (proj1 IH); lets_bound | exact (proj2 IH) ]);
               clear IH; rename H' into IH
           | IH : ?P /\ (_ <= n -> ?Q) |- _ =>
               let H' := fresh in
               assert (H' : P /\ Q) by (split; [ exact (proj1 IH) | apply (proj2 IH); lets_bound ]);
               clear IH; rename H' into IH
           end.
  (** Only the unannotated [let] needs the outer induction. *)
  all: try (lazymatch goal with |- _ ⊢a ℓ ≔ _ in _ ⟸ _ => fail | _ => clear IHn end).
  all: match goal with |- _ ⊢a _ ⟸ _ =>
         gen_presups;
         (** A universe, [ℕ], [⊤] and [⊥] infer their own universe. *)
         try solve [ eapply alg_type_check_suniv;
                     [ assumption | mauto 3 | constructor | cbn; apply lvl_le_lit; lia ]
                   | eapply alg_type_check_typ_of;
                     [ assumption | mauto 3 | constructor | cbn; first [ exact I | lia ] ] ];
         (** A small universe at a level term infers the normal form of the
             universe above it. *)
         try match goal with
           | |- _ ⊢a a_univ ?M ⟸ a_univ (succl ?M) =>
               assert (HSU : Γ ⊢ Type⟨succl M⟩ : Typeω@0) by (apply wf_univ_large_tm; mauto 3);
               destruct (soundness_ty HSU) as [W [HW HWe]];
               econstructor; [ eapply ati_suniv; eassumption |];
               apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe
           end;
         mauto 4 using alg_subtyping_complete, alg_type_check_subtyp | _ => idtac end.
  (** An unannotated [let].  The definiens infers [A'], a subtype of the [A]
      of the derivation, so the body's derivation is moved to [Γ ▸ A' ≔ M] by
      refinement.  That derivation is no subderivation, but its subject has
      fewer unannotated [let]s, which is what the outer induction is for. *)
  13:{ match goal with Hc : Γ ⊢a M ⟸ A |- _ => inversion Hc as [? A' ? ? HMi HMs]; subst end.
      assert (Γ ⊢ M : A') by mauto 3 using alg_type_infer_sound.
      assert (exists k, Γ ⊢ A' : Typeω@k) as [k HA'] by (gen_presups; eauto 2).
      assert (Γ ⊢ A' : Typeω@(max i k)) by mauto 3 using lift_exp_max_right.
      assert (Γ ⊢ A : Typeω@(max i k)) by mauto 3 using lift_exp_max_left.
      assert (Γ ⊢ A' ⊆ A) by mauto 3 using alg_subtyping_sound.
      assert (Γ ▸ A' ≔ M ⊢s Id : Γ ▸ A ≔ M) by (eapply wf_sub_id_extend_def; mauto 3).
      assert (HB' : Γ ▸ A' ≔ M ⊢ B : C) by mauto 3.
      assert (HBa : Γ ▸ A' ≔ M ⊢a B ⟸ C).
      { destruct (IHn (exp_lets B) ltac:(lets_bound)) as (_ & IHt & _).
        eapply IHt; [ exact HB' | reflexivity | reflexivity | apply user_exp_all | lia ]. }
      clear IHn.
      inversion HBa as [? C' ? ? HBi HBs]; subst.
      assert (⊢ Γ ▸ A' ≔ M) by mauto 3.
      assert (Γ ▸ A' ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
      assert (exists k, Γ ▸ A' ≔ M ⊢ C' : Typeω@k) as [k1] by (gen_presups; eauto 2).
      assert (exists k, Γ ▸ A ≔ M ⊢ C : Typeω@k) as [k2] by (gen_presups; eauto 2).
      assert (Γ ▸ A' ≔ M ⊢ C : Typeω@k2) by mauto 3.
      assert (Γ ▸ A' ≔ M ⊢ C' ⊆ C)
        by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
      assert (Γ ⊢s Id,,M : Γ ▸ A' ≔ M) by (eapply wf_sub_single_def; eassumption).
      assert (Γ ⊢ C'[Id,,M] : Typeω@k1) by mauto 3.
      assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Typeω@k1) as [W []]
        by (eapply soundness_ty; mauto 3).
      assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
      assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
      econstructor; [ eapply ati_let_infer; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A module [let], through its body. *)
  14:{ destruct H0 as [HUa _].
       inversion H4 as [? C' ? ? HBi HBs]; subst.
       assert (Γ ▹ₘ U ⊢ B : C') by mauto 3 using alg_type_infer_sound.
       assert (exists k, Γ ▹ₘ U ⊢ C' : Typeω@k) as [k HCk] by (gen_presups; eauto 2).
       pose proof (wf_sub_single_mod _ _ _ _ H) as Hσ.
       pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCk Hσ) as HC'σ.
       destruct (soundness_ty HC'σ) as [W [HW HWe]].
       assert (Γ ▹ₘ U ⊢ C' ⊆ C)
         by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
       assert (Γ ⊢ C'[Id ,,ₘ me_lit U] ⊆ C[Id ,,ₘ me_lit U]) by mauto 3.
       assert (Γ ⊢ W ⊆ C[Id ,,ₘ me_lit U]) by (transitivity C'[Id ,,ₘ me_lit U]; mauto 3).
       econstructor; [ eapply ati_let_mod; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A member, at the normal form of its canonical type. *)
  14:{ destruct H2 as [Hm _].
       destruct (soundness_ty H4) as [W [HW HWe]].
       econstructor; [ eapply ati_mem; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A member of an applied module, as its root's member applied. *)
  14:{ destruct H1 as [Hm _].
       inversion H7 as [? A' ? ? Hi Hs]; subst.
       econstructor; [ eapply ati_mem_app; eauto | exact Hs ]. }
  (** The level forms: each infers [Level], which is its own normal form. *)
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists UA u, Γ ▹ ℕ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Typeω@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Typeω@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists UA u, Γ ▹ ⊥ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Typeω@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Typeω@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  (** [Π], at either tier: the join of the two indices is below the universe
      of the rule's conclusion. *)
  - assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (exists UB v, Γ ▹ A ⊢a B ⟹ UB /\ is_univ_nf UB v /\ unf_le v (unl i))
        as [UB [v [? []]]] by mauto 3.
    assert (HAu : Γ ⊢ A : unf_tm u)
      by (rewrite <- nf_to_exp_univ_nf; match goal with Hu : is_univ_nf ?UA u |- _ => rewrite <- (is_univ_nf_eq _ _ Hu) end;
          eapply alg_type_infer_sound; eassumption).
    assert (HBv : Γ ▹ A ⊢ B : unf_tm v)
      by (rewrite <- nf_to_exp_univ_nf; match goal with Hv : is_univ_nf ?UB v |- _ => rewrite <- (is_univ_nf_eq _ _ Hv) end;
          eapply alg_type_infer_sound; eassumption).
    destruct (wf_unf_pi_tm HAu HBv) as [k Hk].
    eapply (alg_pi_check_of_infer _ _ _ _ _ u v _ (S i)); try eassumption; [ mauto 3 |].
    eapply unf_pi_tm_large; eassumption.
  (** The small [Π], at a level term. *)
  - eapply alg_pi_small_complete; eassumption.
  - assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (Γ ▹ A ⊢a M ⟸ B) by mauto 3.
    assert (exists B', Γ ▹ A ⊢a M ⟹ B' /\ Γ ▹ A ⊢a B' ⊆ B) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i) as [W []] by mauto 3 using soundness_ty.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ▹ A ⊢ M : B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B' : Typeω@j) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert (Γ ⊢a M ⟸ Π A B) by mauto 2.
    assert (Γ ⊢a N ⟸ A) by mauto 2.
    assert (exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Typeω@i /\ Γ ▹ A ⊢a B' ⊆ B) as [A' [B' [? []]]] by mauto 3.
    assert (Γ ⊢ M : Πⁿ A' B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ⊢ Π A' B' : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A' : Typeω@j /\ Γ ▹ (A' : exp) ⊢ B' : Typeω@j) as [] by mauto 3.
    assert (Γ ⊢ N : A') by mauto 3.
    assert (Γ ⊢ B'[Id,,N] : Typeω@j) by mauto 3.
    assert (exists W, nbe_ty_f Γ B'[Id,,N] W /\ Γ ⊢ B'[Id,,N] ≈ W : Typeω@j) as [W []] by (eapply soundness_ty; mauto 3).
    assert (Γ ▹ A ⊢ B' : Typeω@j) by mauto 4.
    assert (Γ ▹ A ⊢ B' ⊆ B) by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ B'[Id,,N] ⊆ B[Id,,N]) by mauto 3.
    assert (Γ ⊢ W ⊆ B[Id,,N]) by (transitivity B'[Id,,N]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢a B ⟸ C) by mauto 2.
    assert (exists C', Γ ▸ A ≔ M ⊢a B ⟹ C' /\ Γ ▸ A ≔ M ⊢a C' ⊆ C) as [C' []]
        by (inversion_clear_by_head alg_type_check; firstorder).
    assert (Γ ▸ A ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
    assert (exists k, Γ ▸ A ≔ M ⊢ C' : Typeω@k) as [k] by (gen_presups; eauto 2).
    assert (exists k', Γ ▸ A ≔ M ⊢ C : Typeω@k') as [k'] by (gen_presups; eauto 2).
    assert (Γ ▸ A ≔ M ⊢ C' ⊆ C)
      by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ C'[Id,,M] : Typeω@k) by mauto 3.
    assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Typeω@k) as [W []]
        by (eapply soundness_ty; mauto 3).
    assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
    assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  (** Resolution is the same function call in both systems. *)
  - assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 3 using wf_glob_typ.
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i) as [W []]
        by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.

  (** Extensions. *)
  - constructor.
  - constructor.
  - destruct H0 as [Hl _].
    pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ H2) as [UA [u [Hj [Hu _]]]].
    econstructor; eauto.
  - destruct H0 as [_ Hr].
    pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' H6) as [UA [u [Hj' [Hu _]]]].
    econstructor; eauto.
  - destruct H0 as [Hl _].
    pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ H2) as [UA [u [Hj [Hu _]]]].
    econstructor; eauto.
  - destruct H0 as [_ Hr].
    pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' H10) as [UA [u [Hj' [Hu _]]]].
    econstructor; eauto.
  - destruct H0 as [Hl _]; destruct H2 as [HU _]; econstructor; eauto.
  - destruct H0 as [_ Hr]; destruct H4 as [HU' _]; econstructor; eauto.
  (** Units. *)
  - destruct H0 as [Hl _]; destruct (body_shape_refl _ _ H4) as (Hs1 & Hs2 & Hn).
    eapply aunit_body; eauto.
  - destruct H0 as [_ Hr]; destruct (body_shape_refl _ _ H4) as (Hs1 & Hs2 & Hn).
    eapply aunit_body; eauto.
    rewrite <- Hn; assumption.
  - destruct H0 as [Hl _]; destruct H4 as [HE _]; econstructor; eauto.
  - destruct H0 as [_ Hr]; destruct H6 as [HE' _]; econstructor; eauto.
  - destruct H0; assumption.
  - destruct H0; assumption.
  - destruct H0 as [H01 _]; assumption.
  - destruct H2 as [_ H22]; assumption.
  (** Module expressions. *)
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
Qed.

Lemma alg_type_complete_all :
  (forall Θ Ξ Γ, wf_ctx Θ Ξ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aˣ Ψ /\ Γ ⊢aˣ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵘ U /\ Γ ⊢aᵘ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵐ H /\ Γ ⊢aᵐ H').
Proof.
  repeat split; intros; try exact I.
  - eapply (alg_type_complete_lets (exp_lets M)); eauto.
  - eapply (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (gunit_lets U + gunit_lets U'))))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (gunit_lets U + gunit_lets U'))))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (modexp_lets H + modexp_lets H'))))))) _ _ _ _ _ H0 H1 H2)); lia.
  - eapply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (modexp_lets H + modexp_lets H'))))))) _ _ _ _ _ H0 H1 H2)); lia.
Qed.

Lemma alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    Γ ⊢a M ⟸ A.
Proof.
  intros * Hue HM; exact (proj1 (proj2 alg_type_complete_all) _ _ _ _ _ HM eq_refl eq_refl Hue).
Qed.

Lemma alg_ext_complete : forall {Γ Ψ}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Γ ⊢aˣ Ψ.
Proof. intros * HΨ; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all)))) _ _ _ _ _ HΨ eq_refl eq_refl)). Qed.

Lemma alg_unit_complete : forall {Γ U}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ⊢aᵘ U.
Proof. intros * HU; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all))))) _ _ _ _ _ HU eq_refl eq_refl)). Qed.

Lemma alg_modexp_complete : forall {Γ H}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> Γ ⊢aᵐ H.
Proof. intros * HH; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all))))) _ _ _ _ _ HH eq_refl eq_refl)). Qed.



Hint Resolve alg_type_check_complete : mctt.

Corollary alg_type_infer_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    exists B, Γ ⊢a M ⟹ B /\ Γ ⊢a B ⊆ A.
Proof.
  intros.
  assert (Γ ⊢a M ⟸ A) as Hcheck by mauto 4 using alg_type_check_complete.
  inversion_clear Hcheck.
  firstorder.
Qed.

Hint Resolve alg_type_infer_complete : mctt.

Corollary alg_type_infer_large_typ_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i).
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

Hint Resolve alg_type_infer_large_typ_complete : mctt.

(** Completeness at a small universe, with the old precise shape: the
    inferred universe is a small universe at a literal level below [n] (an
    atom is never below a literal, [lvl_le_lit_closed]).  The large tier's
    statement is [alg_type_infer_large_typ_complete]. *)
Corollary alg_type_infer_typ_complete : forall {Γ n A},
    user_exp A ->
    Γ ⊢ A : Type@n ->
    exists m, Γ ⊢a A ⟹ Typeⁿ@m /\ m <= n.
Proof.
  intros * HA HAn.
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_implies_alg_type_infer_univ ltac:(eassumption)
              (alg_type_check_complete HA HAn)) as (UA & u & Hinf & Hu & Hle).
  destruct u as [[c xs] | i]; cbn in Hle; [| contradiction].
  inversion Hu; subst.
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs; cbn in Hxs; subst xs.
  exists c; split; [ exact Hinf |].
  rewrite lvl_le_correct in Hle; specialize (Hle (fun _ => 0)); unfold lvl_ev, lvl_lit in Hle; cbn in Hle; lia.
Qed.

(** The same at a level term [t]: the inferred universe is small, at a
    canonical level below the normal form of [t]. *)
Corollary alg_type_infer_typ_complete_tm : forall {Γ t A},
    user_exp A ->
    Γ ⊢ A : Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_f Γ t Level (nf_lvl_of L') /\ lvl_le L L'.
Proof.
  intros * HA HAt.
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ ltac:(eassumption)
              (alg_type_check_complete HA HAt)) as (L & L' & Hinf & Hn & Hle).
  exists L, L'; split; [ exact Hinf | split; [ exact (nbe_ty_univ_level Hn) | exact Hle ] ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve alg_type_infer_normal : mctt.
#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.
#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.
#[export]
Hint Resolve alg_type_check_subtyp : mctt.
#[export]
Hint Resolve alg_type_check_conv : mctt.
#[export]
Hint Resolve alg_type_check_complete : mctt.
#[export]
Hint Resolve alg_type_infer_complete : mctt.
#[export]
Hint Resolve alg_type_infer_large_typ_complete : mctt.
