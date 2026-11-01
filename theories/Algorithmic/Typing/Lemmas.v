From Stdlib Require Import Wf_nat PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Typing Require Export Functional.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Completeness.Modules Require Import ValidUnit.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic Require Import CoreInversions Corollaries Fresh.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.Inductives Require Import IndCong IndConv.
From Mctt.Core.Syntactic.Levels Require Levels.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Core.Syntactic.System.Global Require Import Modules Paths DescTyping LookupSound MemberWf.
From Mctt.Core.Semantic Require Import MemberWf Avoid.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
Import Domain_Notations Fixed_Notations Wk_Notations.

(** The universe premise of a [Π] rule, as its two cases: a large universe,
    or a small one at a level. *)
#[local]
Ltac destruct_univ :=
  repeat match goal with
         | HU : wf_is_univ _ _ _ ?U |- _ => is_var U; inversion HU; subst; clear HU
         end;
  repeat match goal with
         | H : context [exp_wk (a_typ ?i) ?φ] |- _ => change (exp_wk (a_typ i) φ) with (a_typ i) in H
         | H : context [exp_wk (a_univ ?L) ?φ] |- _ => change (exp_wk (a_univ L) φ) with (a_univ (exp_wk L φ)) in H
         | |- context [exp_wk (a_typ ?i) ?φ] => change (exp_wk (a_typ i) φ) with (a_typ i)
         | |- context [exp_wk (a_univ ?L) ?φ] => change (exp_wk (a_univ L) φ) with (a_univ (exp_wk L φ))
         end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

End Fixed_GCtx.

(** The global context is well formed: a hypothesis says so, or a
    judgment in one of its contexts presupposes it. *)
Ltac gctx_wf_tac :=
  lazymatch goal with
  | |- wf_gstack ?T ?X =>
      first [ assumption
            | match goal with H : wf_ctx T X _ |- _ => exact (ctx_wf_gctx _ _ _ H) end
            | match goal with H : wf_exp T X _ _ _ |- _ => exact (ctx_wf_gctx _ _ _ (presup_exp_ctx H)) end
            | match goal with H : wf_modexp_eq T X _ _ _ |- _ => exact (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx H)) end
            | match goal with H : exists i, wf_exp T X _ _ _ |- _ =>
                let i := fresh "i" in let Hi := fresh "Hi" in
                destruct H as [i Hi]; exact (ctx_wf_gctx _ _ _ (presup_exp_ctx Hi)) end
            | match goal with H : wf_type T X _ _ |- _ =>
                let Hi := fresh "Hi" in
                destruct H as [? ? Hi]; exact (ctx_wf_gctx _ _ _ (presup_exp_ctx Hi)) end
            | solve [ mauto 3 ] ]
  end.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (?Γ ⊢a ?M ⟹ ?A1), H2 : (?Γ ⊢a ?M ⟹ ?A2) |- _ =>
      clean replace A2 with A1
        by first [ solve [ eapply functional_alg_type_infer; [| exact H1 | exact H2 ]; gctx_wf_tac ]
                 | solve [ eapply functional_alg_type_infer; [| exact H2 | exact H1 ]; gctx_wf_tac ]
                 | solve [ mauto 2 using functional_alg_type_infer ]
                 | tactic_error A2 A1 ];
      clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Moving Levels Up the Sorts

    A level of a sort is a level of every larger sort ([wf_subtyp_level]). *)
Lemma wf_exp_level_up : forall {Γ M m n},
    m <= n ->
    Γ ⊢ M : Level@m ->
    Γ ⊢ M : Level@n.
Proof.
  intros * Hmn HM; assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_level; assumption ].
Qed.

Lemma wf_exp_eq_level_up : forall {Γ M M' m n},
    m <= n ->
    Γ ⊢ M ≈ M' : Level@m ->
    Γ ⊢ M ≈ M' : Level@n.
Proof.
  intros * Hmn HM; assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_eq_subtyp'; [ exact HM | apply wf_subtyp_level; assumption ].
Qed.

(** ** Universe Normal Forms as Types

    A universe normal form, as a term, is a universe. *)
Lemma univ_term_universe_nf_tm : forall u, univ_term (universe_nf_tm u).
Proof. intros [L | n]; constructor. Qed.

(** A goal [exists k, Γ ⊢ U : Typeω@k] at a universe [U] that a hypothesis
    (or a presupposition of one) types a term at: a universe is of a large
    one ([univ_term_typed_large]), as a proposition is not. *)
Ltac univ_large :=
  let univ_term_tac := first [ apply univ_term_universe_nf_tm | constructor ] in
  lazymatch goal with
  | |- exists _, wf_exp _ _ ?Γ _ ?U =>
      first [ match goal with H : wf_exp _ _ Γ _ _ |- _ => refine (univ_term_typed_large _ H); univ_term_tac end
            | gen_presups;
              match goal with H : wf_exp _ _ Γ _ _ |- _ => refine (univ_term_typed_large _ H); univ_term_tac end ]
  end.

(**

    The universe a type infers is a universe normal form [u]; as a term it is
    [universe_nf_tm u], which is a small universe at a level term or a large one.
    The declarative rules ask for a large universe, which a small one is below
    ([wf_subtyp_small_large]): this is the cumulativity the algorithmic layer
    relies on. *)
Lemma wf_exp_universe_nf_large_index : forall {Γ A} {u : universe_nf},
    Γ ⊢ A : universe_nf_tm u ->
    Γ ⊢ A : Typeω@(universe_nf_large_index u).
Proof.
  intros * HA; destruct u as [L | n]; cbn in *; [| exact HA ].
  destruct (presup_exp_typ HA) as [Sk _ Hk].
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct (wf_univ_lvl_inversion Hk) as [n Hn].
  eapply wf_exp_subtyp'; [ exact HA | eapply wf_subtyp_small_large; eassumption ].
Qed.

(** The normal form of a type is its own normal form. *)
Lemma nbe_ty_self : forall {Γ i A B},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B B.
Proof.
  intros * HA Hn.
  assert (Γ ⊢ A ≈ B : Typeω@i) by (eapply soundness_ty'; eassumption).
  assert (HB : Γ ⊢ B : Typeω@i) by (gen_presups; assumption).
  destruct (soundness_ty HB) as (C & HC & _).
  assert (B = C) as <- by (exact (idempotent_nbe_ty HA Hn HC)).
  exact HC.
Qed.

(** A universe normal form whose level is a canonical level of a sort its
    level term has, each atom a level of its own sort: what the normal form
    of a universe is ([univ_nf_well_scoped]). *)
Definition universe_nf_well_scoped (Γ : ctx) (u : universe_nf) : Prop :=
  match u with
  | universe_small L => exists n, Γ ⊢ lvl_exp_of (fst L) (List.map atom_exp (snd L)) : Level@n /\
                    fst (fst L) <= n /\ @level_atoms_well_scoped gc_deps gc_stack n Γ (snd L)
  | universe_large _ => True
  end.

Lemma universe_nf_well_scoped_of_nbe : forall {Γ u i},
    Γ ⊢ universe_nf_tm u : Typeω@i ->
    nbe_ty_f Γ (universe_nf_tm u) (universe_nf_to_nf u) ->
    universe_nf_well_scoped Γ u.
Proof.
  intros * Hu Hn; destruct u as [[c xs] | j]; cbn in *; [| exact I ].
  exact (univ_nf_well_scoped Hu Hn).
Qed.

(** The domain of a [Π] the algorithm counts in the universe [u]: a type
    of [u], or a proposition, where [u] (the least small universe,
    [is_sort_nf_prop]) is a type. *)
Definition pi_domain_ok (Γ : ctx) (A : typ) (u : universe_nf) : Prop :=
  Γ ⊢ A : universe_nf_tm u \/ (Γ ⊢ A : Propₘ /\ exists k, Γ ⊢ universe_nf_tm u : Typeω@k).

(** A type of a sort normal form [UA] ([is_sort_nf]) is of its sort, a large
    universe or [Prop]. *)
Lemma sort_typed_of_is_sort_nf : forall {Γ A} {UA : nf} {r u},
    Γ ⊢ A : UA -> is_sort_nf UA r u -> Γ ⊢ A : relevance_sort r Typeω@(universe_nf_large_index u).
Proof.
  intros * HA Hs; destruct Hs as [W u' Hu |]; cbn [relevance_sort]; [| exact HA ].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA.
  exact (wf_exp_universe_nf_large_index HA).
Qed.

(** The sort above is a sort. *)
Lemma type_sort_relevance_universe : forall r i, type_sort (relevance_sort r Typeω@i).
Proof. intros; apply type_sort_relevance; constructor. Qed.

(** It is a type of the next universe. *)
Lemma relevance_sort_universe_typed : forall Γ r i, ⊢ Γ -> Γ ⊢ relevance_sort r Typeω@i : Typeω@(S i).
Proof. intros * HΓ; destruct r; cbn [relevance_sort]; [ apply wf_typ, HΓ | eapply wf_prop_large; exact HΓ ]. Qed.

(** A type of a sort normal form is a [Π] domain at its universe. *)
Lemma pi_domain_ok_of_is_sort_nf : forall {Γ A} {UA : nf} {r u},
    Γ ⊢ A : UA -> is_sort_nf UA r u -> pi_domain_ok Γ A u.
Proof.
  intros * HA Hs; destruct Hs as [W u' Hu |].
  - left; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA; exact HA.
  - right; split; [ exact HA |].
    assert (⊢ Γ) by (gen_presups; assumption).
    exists 0; cbn; eapply (wf_univ_large_tm (n := 0)); [ assumption | apply wf_llit; [ cbn; lia | assumption ] ].
Qed.

(** The universe of a [Π] ([universe_nf_pi_tm]).  Two small universes join in the
    small tier, the codomain's level bounded under the binder
    ([lvl_bound]): the bound, weakened back, is above the codomain's level
    ([lvl_bound_above]) and mentions no bound variable, so it is the weakening
    of a level of [Γ] ([level_nf_strengthen]); both parts are moved up to the
    join.  Otherwise the [Π] is at the large join. *)
Lemma wf_pi_universe_nf_pi : forall {Γ A B} {u v : universe_nf},
    pi_domain_ok Γ A u ->
    Γ ▹ A ⊢ B : universe_nf_tm v ->
    universe_nf_well_scoped (Γ ▹ A) v ->
    Γ ⊢ Π A B : universe_nf_pi_tm u v.
Proof.
  intros * HA HB Hv.
  assert (⊢ Γ) by (destruct HA as [HA | [HA _]]; gen_presups; assumption).
  assert (HAl : Γ ⊢ A : Typeω@(universe_nf_large_index u) \/ Γ ⊢ A : Propₘ)
    by (destruct HA as [HA | [HA _]]; [ left; apply wf_exp_universe_nf_large_index; exact HA | right; exact HA ]).
  assert (HBl : Γ ▹ A ⊢ B : Typeω@(universe_nf_large_index v)) by (apply wf_exp_universe_nf_large_index; exact HB).
  assert (HΓA : ⊢ Γ ▹ A) by (destruct HAl as [HA0 | HA0]; (eapply wf_ctx_extend; [ exact HA0 | constructor ])).
  (** The domain's universe is a type. *)
  assert (HUk : exists k, Γ ⊢ universe_nf_tm u : Typeω@k)
    by (destruct HA as [HA | [_ HA]]; [ exact (univ_term_typed_large (univ_term_universe_nf_tm _) HA) | exact HA ]).
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [universe_nf_pi_tm universe_nf_max universe_nf_tm universe_nf_large_index fst snd] in *.
  - (** The small join. *)
    destruct Hv as (nB & HLB0 & Hd & Hys); cbn [fst snd] in *.
    unfold lvl_bound; cbn [fst snd].
    set (LA := lvl_exp_of c (List.map atom_exp xs)) in *.
    set (cb := ordinal_max d (level_atoms_open_bound 0 ys)) in *.
    set (fp := level_atoms_fresh_part 0 ys) in *.
    set (LBs := lvl_exp_of cb (List.map atom_exp (List.map (map_level_atom (ne_unwk 0)) fp))).
    assert (exists nA, Γ ⊢ LA : Level@nA) as [nA HLA0]
      by (destruct HUk as [k Hk]; eapply wf_univ_lvl_inversion; exact Hk).
    set (N := S (Nat.max nA nB)).
    assert (Hcb : fst cb <= N)
      by (subst cb N; apply ordinal_max_fst_le;
          [ lia | eapply Nat.le_trans; [ apply level_atoms_open_bound_fst; eapply level_atoms_well_scoped_sorts; exact Hys | lia ] ]).
    assert (HysN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹ A) ys) by (eapply level_atoms_well_scoped_mono; [| exact Hys ]; lia).
    assert (HfpN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹ A) fp) by (apply level_atoms_well_scoped_fresh_part; exact HysN).
    assert (HLB : Γ ▹ A ⊢ lvl_exp_of d (List.map atom_exp ys) : Level@N) by (eapply wf_exp_level_up; [| exact HLB0 ]; lia).
    (** The bound, weakened back, is the level of its fresh atoms. *)
    assert (Hfresh : lvl_exp_of cb (List.map atom_exp fp) = LBs[↑]ʷ)
      by exact (nf_fresh_unwk 0 (nf_lvl cb fp) (level_atoms_fresh_part_fresh 0 ys)).
    assert (HLBl : Γ ▹ A ⊢ LBs[↑]ʷ : Level@N)
      by (rewrite <- Hfresh; apply lvl_exp_of_wf; [ exact Hcb | exact HΓA | apply level_atoms_well_scoped_wf; exact HfpN ]).
    assert (Habove : Γ ▹ A ⊢ maxl (lvl_exp_of d (List.map atom_exp ys)) LBs[↑]ʷ ≈ LBs[↑]ʷ : Level@N).
    { rewrite <- Hfresh.
      apply lvl_exp_of_le; [ lia | exact Hcb | exact HΓA | exact HysN | exact HfpN |].
      exact (lvl_bound_above 0 (d, ys)). }
    assert (HLA : Γ ⊢ LA : Level@N) by (eapply wf_exp_level_up; [| exact HLA0 ]; lia).
    assert (HLBs : Γ ⊢ LBs : Level@N).
    { refine (level_nf_strengthen Γ A _ (nf_lvl cb (List.map (map_level_atom (ne_unwk 0)) fp)) _ HΓA HLBl).
      (* PENDING design: a level whose atoms hold proofs need not strengthen (level_nf_strengthen asks nf_proof_free). *)
      admit. }
    assert (Ht : Γ ⊢ maxl LA LBs : Level@N) by mauto 3.
    assert (Hw : Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
    eapply wf_pi_lvl_at_domain; [ exact Ht | |].
    + destruct HA as [HA | [HA _]]; [ left | right; exact HA ].
      eapply wf_exp_subtyp'; [ exact HA |].
      eapply wf_subtyp_suniv; [ assumption | exact HLA | exact Ht | apply lvl_sub_maxl_l; assumption ].
    + eapply wf_exp_subtyp'; [ exact HB |].
      assert (Hsub : Γ ⊢ Type⟨LBs⟩ ⊆ Type⟨maxl LA LBs⟩)
        by (eapply wf_subtyp_suniv; [ assumption | exact HLBs | exact Ht | apply lvl_sub_maxl_r; assumption ]).
      etransitivity; [| exact (wk_preserves_subtyp _ _ _ _ _ _ _ Hsub Hw) ].
      eapply wf_subtyp_suniv; [ exact HΓA | exact HLB | exact HLBl | exact Habove ].
  (** A large join: the domain lifted to it, of the universe or a proposition. *)
  - destruct xs; cbn [universe_nf_tm];
      (apply wf_pi_at_domain; [ destruct HAl as [HAl | HAl]; [ left; eapply lift_exp_ge; [| exact HAl ]; lia | right; exact HAl ]
                              | assumption ]).
  - destruct ys; cbn [universe_nf_tm];
      (apply wf_pi_at_domain; [ exact HAl | eapply lift_exp_ge; [| exact HBl ]; lia ]).
  - apply wf_pi_at_domain; [ destruct HAl as [HAl | HAl]; [ left; eapply lift_exp_ge; [| exact HAl ]; lia | right; exact HAl ]
                           | eapply lift_exp_ge; [| exact HBl ]; lia ].
Admitted. (* PENDING design: level_nf_strengthen at a level whose atoms hold proofs *)

(** The universe of a [Π] is a type. *)
Lemma wf_universe_nf_pi_tm : forall {Γ A B} {u v : universe_nf},
    pi_domain_ok Γ A u ->
    Γ ▹ A ⊢ B : universe_nf_tm v ->
    universe_nf_well_scoped (Γ ▹ A) v ->
    exists k, Γ ⊢ universe_nf_pi_tm u v : Typeω@k.
Proof.
  intros * HA HB Hv.
  refine (univ_term_typed_large _ (wf_pi_universe_nf_pi HA HB Hv)).
  destruct u as [[] |], v as [[] |]; cbn; constructor.
Qed.

(** A premise [⟹ UA] with [is_univ_nf UA u] is sound as a typing at
    [universe_nf_tm u], while the declarative rules ask for a large universe: such a
    hypothesis is lifted to [Typeω@(universe_nf_large_index u)] ([wf_exp_universe_nf_large_index]).
    [is_univ_nf_eq] turns the side condition into the shape of [UA]. *)
#[local] Tactic Notation "lift_univ_at" constr(Δ) constr(A) constr(u) :=
  repeat match goal with Hi : is_univ_nf ?UA u |- _ =>
    assert_fails (constr_eq UA (universe_nf_to_nf u));
    rewrite (is_univ_nf_eq _ _ Hi) in * end;
  assert (Δ ⊢ A : universe_nf_tm u)
    by (rewrite <- nf_to_exp_univ_nf; mauto 2);
  assert (Δ ⊢ A : a_typ (universe_nf_large_index u))
    by (apply wf_exp_universe_nf_large_index; eassumption).

(** Terms with, position by position, the normal forms of terms at the
    instances of a telescope are, position by position, equal to them. *)
Lemma nfs_agree_sound : forall Δ Γ0 Γ σ σ' Ms Rs,
    tele_ass Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ ≈ σ' : Γ0 ->
    List.length Ms = List.length Δ -> List.length Rs = List.length Δ ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N : T) ->
    (forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ σ' Rs) j = Some T -> Γ ⊢ N : T) ->
    nfs_agree Γ Ms Rs (tele_insts Δ σ Ms) ->
    forall j N R T, List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
      List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N ≈ R : T.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ HMl HRl HMs HRs Hag j N R T HN HR HT.
  - destruct Ms; [ destruct j; discriminate | discriminate ].
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in HMl, HRl; cbn in HMl, HRl.
    destruct Ms as [| M0 Ms]; [ cbn in HMl; lia |]; destruct Rs as [| R0 Rs]; [ cbn in HRl; lia |].
    rewrite tele_insts_snoc in HMs, HRs, Hag, HT.
    rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [S0 HS0 HA0]].
    inversion Hag as [| ? ? ? W ? ? ? HMW HRW Hag']; subst.
    assert (HM0 : Γ ⊢ M0 : A0[σ]) by (apply (HMs 0); reflexivity).
    assert (HR0' : Γ ⊢ R0 : A0[σ']) by (apply (HRs 0); reflexivity).
    assert (HAA : Γ ⊢ A0[σ] ≈ A0[σ'] : S0) by (eapply sub_eq_preserves_sort; [ exact HA0 | exact HS0 | exact Hσ ]).
    assert (HR0 : Γ ⊢ R0 : A0[σ]) by (exact (exp_conv_sort HS0 ltac:(symmetry; exact HAA) HR0')).
    assert (HMR : Γ ⊢ M0 ≈ R0 : A0[σ])
      by (etransitivity; [ eapply soundness'; eassumption | symmetry; eapply soundness'; eassumption ]).
    destruct j as [| j]; cbn in HN, HR, HT.
    + injection HN as <-; injection HR as <-; injection HT as <-; exact HMR.
    + eapply (IH _ _ _ _ Ms Rs); [ exact Hass | exact HΔ | | cbn in HMl; lia | cbn in HRl; lia | | | exact Hag' | exact HN | exact HR | exact HT ].
      * eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | exact HS0 | exact HM0 | exact HR0' | exact HMR ].
      * intros j' N' T' HN' HT'; apply (HMs (S j')); [ exact HN' | exact HT' ].
      * intros j' N' T' HN' HT'; apply (HRs (S j')); [ exact HN' | exact HT' ].
Qed.

(** The eliminator: its uniform parameters are typed, and the uniform
    arguments of its member's type at them are equal to those of the type
    its scrutinee infers ([nfs_agree_sound]), so the scrutinee is of the
    member's type ([mty_params_conv]); the blocks are typed at the uniform
    parameters, by the induction hypotheses.  The eliminator is of the
    motive's instance, before that is normalised. *)
Lemma alg_elim_typed : forall Γ M pc k Rs p D oq m Mm Dq Mk bm Bks Us Ns r i,
    ⊢ Γ -> Γ ⊢ M : apps (a_ind pc k) (List.map nf_to_exp Rs) ->
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
    List.nth_error Bks m = Some bm -> List.length Bks = ind_nblk D ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ T : Srt -> Γ ⊢ U : T) ->
    nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
    Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
    blocks_binder_count_ok D Bks ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list -> forall Srt, type_sort Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Typeω@i : Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Z : Typeω@i) ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z
         (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (elim_mctx p D j Mj Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ relevance_sort r Typeω@i : Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : relevance_sort r Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       ⊢ (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ elim_branch_type p D j Mj c gs (eb_motive b) Us : Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ B : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
    Γ ⊢ a_elim r oq Us m Bks M : (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros * HΓ HM Hl Hg Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag -> HBnm HZt HZc HAt HBn HBa HBt.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgw; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsuf.
  pose proof (block_member_not_rview _ _ _ _ _ Hsuf HBl Hm Hb) as Hnr.
  (** The uniform parameters. *)
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T).
  { eapply tele_insts_typed_all; [ exact (decl_closed_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ) | apply wf_sub_id, HΓ |].
    intros j U X HU HX (SX & HSX & HXt); exact (HUs _ _ _ HU HX HΓ _ HSX HXt). }
  (** The scrutinee, of the member's type. *)
  destruct (presup_exp_typ HM) as [Skk _ Hkk].
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk Hkk HRl) as HRt.
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq HUl HUt) as [HPl HPt].
  destruct (params_typed_split _ _ Dq Hcq _ _ _ _ Hk HRl HRt) as [HRu _].
  assert (HRl' : List.length (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HRl; lia).
  assert (HPR : forall j N R X, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some X -> Γ ⊢ N ≈ R : X).
  { intros j N R X HN HR HX.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    eapply (nfs_agree_sound (ind_uparams Dq) Γ Γ Id Id); [ exact (decl_closed_ass _ Hcq) | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓ)
           | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite HPl; reflexivity | rewrite HRl'; reflexivity
           | exact HPt | exact HRu | exact Hag | exact HN | | exact HX ].
    rewrite List.nth_error_firstn; destruct (Nat.ltb_spec j (ind_nu Dq)); [ exact HR | lia ]. }
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq Hk HUl HUt HRl HRt HPR) as [HNl HNt [iE HE]].
  assert (HM' : Γ ⊢ M : ind_mty p D m Us (List.skipn (ind_nu Dq) (List.map nf_to_exp Rs))) by (eapply wf_conv'; [ exact HM | exact HE ]).
  clear HPR HRu HPt HRt Hkk Skk HE Hag HUs HRl' HPl HM.
  set (Ns := List.skipn (ind_nu Dq) (List.map nf_to_exp Rs)) in *.
  (** The blocks. *)
  assert (HUt' : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ Γ)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  assert (HBmot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : relevance_sort r Typeω@i)
    by (intros j Mj b Hj Hb0;
        exact (HAt _ _ _ Hj Hb0 (HUt' _ _ Hj) _ (type_sort_universe _) (relevance_sort_universe_typed _ r i (HUt' _ _ Hj)))).
  assert (HAs : motives_typed gc_deps gc_stack Γ p D Us (blocks_motives Bks) r i).
  { intros j Mj Hj Hjr; destruct (blocks_nth _ _ _ _ Hsuf HBl Hj Hjr) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0); exact (HBmot _ _ _ Hj Hb0). }
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUt) as Hσ.
  assert (HBts : blocks_typed gc_deps gc_stack Γ p D Us Bks r i).
  { constructor; [ exact HBl | exact HBnm | | exact HBmot | | exact HBn | | exact HBa | ].
    - intros j Mj b Z Hj Hb0 HZ.
      pose proof (HUt' _ _ Hj) as HC; unfold elim_mctx in HC; cbn [List.app] in HC.
      destruct (ctx_decomp HC) as [HΨ [SH HSH HH]].
      pose proof (HZt _ _ _ _ Hj Hb0 HZ HΨ _ (type_sort_universe _) (wf_typ _ _ _ _ HΨ)) as HZi.
      destruct (HZc _ _ _ _ Hj Hb0 HZ) as (W & HZW & HHW).
      (** The member's type is of a universe, as [Z] is: they have one
          normal form ([exp_eq_of_nbe_ty_same]). *)
      assert (exists jH, (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list
                ⊢ ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)) : Typeω@jH)
        as [jH HH'].
      { destruct HSH as [jH |]; [ exists jH; exact HH |].
        exfalso.
        destruct (exp_eq_of_nbe_ty_same (or_introl HZi) (or_intror HH) HZW HHW) as [HE | HE].
        - exact (typ_prop_absurd (presup_exp_eq_right HE) HH).
        - exact (typ_prop_absurd HZi (presup_exp_eq_left HE)). }
      clear HH HSH SH; rename HH' into HH.
      assert (HZH : (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list
                      ⊢ Z ≈ ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))
                      : Typeω@(max i jH)).
      { etransitivity; [ eapply lift_exp_eq_max_left; eapply soundness_ty'; eassumption
                       | symmetry; eapply lift_exp_eq_max_right; eapply soundness_ty'; eassumption ]. }
      unfold elim_mctx.
      assert (Hext : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ tele_sub (im_nparams Mj) (sb_of_list Id Us)
                                                ≈ tele_sub (im_nparams Mj) (sb_of_list Id Us))
        by (apply ctx_ext_refl; [ apply tele_ass_sub; exact (decl_closed_nparams_ass _ Hc _ _ Hj) | exact HΨ ]).
      eapply wf_ext_eq_ass_eq; [ exact Hext | eapply lift_exp_max_left; exact HZi | constructor | exact HZH
                               | eapply lift_exp_max_right; exact HH | eapply lift_exp_max_right; exact HH ].
    - intros j Mj Hj; apply ctx_ext_refl; [ exact (elim_mctx_ass _ _ _ _ _ Hc Hj) | exact (HUt' _ _ Hj) ].
    - intros j Mj c gs Hj Hcon; apply ctx_ext_refl; [ exact (elim_bctx_ass _ _ _ _ _ _ _ _ Hc Hj) | eapply elim_bctx_wf; eassumption ].
    - intros j Mj b c gs n B Hj Hb0 Hcon Hin.
      pose proof (wf_branch_type_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs Hl Hj (block_member_not_rview _ _ _ _ _ Hsuf HBl Hj Hb0)
                    HΓ HUl HUt HUt' HAs Hcon) as Hbs.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HBmot _ _ _ Hj Hb0) Hbs) as HBty.
      rewrite relevance_sort_sub in HBty; cbn [exp_sub] in HBty.
      eapply HBt; [ exact Hj | exact Hb0 | exact Hcon | exact Hin | eapply elim_bctx_wf; eassumption
                  | exact (type_sort_relevance_universe r i) | exact HBty ]. }
  exact (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hg Hm Hb HBts HUl HUt HNl HNt HM').
Qed.

(** The eliminator is of the normal form of the motive's instance. *)
Lemma alg_elim_sound : forall Γ M pc k Rs p D oq m Mm Dq Mk bm Bks Us Ns r i T,
    ⊢ Γ -> Γ ⊢ M : apps (a_ind pc k) (List.map nf_to_exp Rs) ->
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
    List.nth_error Bks m = Some bm -> List.length Bks = ind_nblk D ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ T : Srt -> Γ ⊢ U : T) ->
    nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
    Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
    blocks_binder_count_ok D Bks ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list -> forall Srt, type_sort Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Typeω@i : Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Z : Typeω@i) ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z
         (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (elim_mctx p D j Mj Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ relevance_sort r Typeω@i : Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : relevance_sort r Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       ⊢ (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ elim_branch_type p D j Mj c gs (eb_motive b) Us : Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ B : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
    nbe_ty_f Γ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] T ->
    Γ ⊢ a_elim r oq Us m Bks M : T /\ exists Srt, type_sort Srt /\ Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : Srt.
Proof.
  intros * HΓ HM Hl Hg Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag HNs HBnm HZt HZc HAt HBn HBa HBt HT.
  pose proof (alg_elim_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ HM Hl Hg Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag HNs
                HBnm HZt HZc HAt HBn HBa HBt) as Hel.
  destruct (presup_exp_typ Hel) as [Sj HSj Hj].
  split; [ exact (exp_conv_sort HSj (soundness_ty_at_sort HSj Hj HT) Hel) | exists Sj; split; assumption ].
Qed.

(** What a checked body is: the body, read in an extension [Ψ] of [Γ0], is
    its expansion, which extends [Ψ], and the targets of its opens are
    well-formed modules where they stand. *)
Record alg_body_ok (Γ0 Ψ Γ : ctx) (Φ Φx : gmod) : Prop := mk_alg_body_ok
  { (** The body's expansion is [Φx] *)
    alg_body_ok_xp : body_xp gc_deps gc_stack Γ Φ Φx
    (** The expansion extends [Ψ] over [Γ0] *)
  ; alg_body_ok_ext : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φx ++ Ψ ≈ body_ctx Φx ++ Ψ
    (** The targets of the opens are modules where they stand *)
  ; alg_body_ok_opens : forall k Ψo H, List.nth_error (body_opens Φ Φx) k = Some (Ψo, H) -> gc_deps ⍮ gc_stack ⍮ Ψo ++ Γ ⊢ᵐ H ≈ H
    (** The term parts of the expansion are of the sorts at their tags *)
  ; alg_body_ok_tags : exists L, body_tags Γ Φx L }.

Definition alg_body_sound (Γ : ctx) (Φ Φx : gmod) : Prop :=
  forall Γ0 Ψ, Γ = Ψ ++ Γ0 -> ⊢ Γ0 -> gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ Ψ ≈ Ψ -> alg_body_ok Γ0 Ψ Γ Φ Φx.

Lemma alg_body_nil_sound : forall Γ, alg_body_sound Γ gm_nil gm_nil.
Proof.
  intros Γ Γ0 Ψ -> HΓ0 HΨ; constructor; [ constructor | exact HΨ | | exists 0; apply body_tags_nil ].
  intros [| k] * Hk; discriminate.
Qed.

(** A definition, of the sort at its tag. *)
Lemma alg_body_def_sound : forall Γ Φ Φx x b pv r A M i,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : relevance_sort r Typeω@i) ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ M : A) ->
    alg_body_sound Γ (gm_ext Φ x (ge_def b pv r A (Some M))) (gm_ext Φx x (ge_def b pv r A (Some M))).
Proof.
  intros * IH HA HM Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HA HC); specialize (HM HC).
  constructor; [ constructor; exact Hbx | | exact Ho |].
  - rewrite List.app_assoc in HA, HM; cbn [body_ctx List.app].
    eapply wf_ext_eq_def_same; [ exact HX | exact HA | apply type_sort_relevance_universe | exact HA | exact HM | exact HM ].
  - exists (max L i); apply body_tags_ext; [ exact (body_tags_mono _ _ _ _ HL (Nat.le_max_l L i)) |].
    intros A' M' HE; cbn [entry_tm entry_relevance] in HE |- *; injection HE as <- <-.
    exact (relevance_sort_lift _ _ _ _ _ HA (Nat.le_max_r L i)).
Qed.

Lemma alg_body_mod_sound : forall Γ Φ Φx x pm U,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵘ U ≈ U) ->
    alg_body_sound Γ (gm_ext Φ x (ge_mod pm U)) (gm_ext Φx x (ge_mod pm U)).
Proof.
  intros * IH HU Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HU HC); rewrite List.app_assoc in HU.
  constructor; [ constructor; exact Hbx | | exact Ho |].
  - cbn [body_ctx List.app]; apply wf_ext_eq_mod; [ exact HX | exact HU | exact HU ].
  - exists L; apply body_tags_ext; [ exact HL | intros * [=] ].
Qed.

(** A definition with a module part: as a definition and as a submodule. *)
Lemma alg_body_dm_sound : forall Γ Φ Φx x pv A M U i,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : Typeω@i) ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ M : A) ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵘ U ≈ U) ->
    alg_body_sound Γ (gm_ext Φ x (ge_def_mod pv A M U)) (gm_ext Φx x (ge_def_mod pv A M U)).
Proof.
  intros * IH HA HM HU Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HA HC); specialize (HM HC); specialize (HU HC).
  constructor; [ constructor; exact Hbx | | exact Ho |].
  - rewrite List.app_assoc in HA, HM, HU; cbn [body_ctx List.app].
    eapply wf_ext_eq_dm; [ exact HX | exact HA | apply wf_exp_eq_refl; exact HA | exact HM | apply wf_exp_eq_refl; exact HM
                         | exact HA | exact HM | exact HU | exact HU ].
  - exists (max L i); apply body_tags_ext; [ exact (body_tags_mono _ _ _ _ HL (Nat.le_max_l L i)) |].
    intros A' M' HE; cbn [entry_tm entry_relevance relevance_sort] in HE |- *; injection HE as <- <-.
    eapply lift_exp_ge; [| exact HA ]; lia.
Qed.

Lemma alg_body_open_sound : forall Γ Φ Φx H R Rm its gs,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵐ H ≈ H) ->
    mdenote gc_deps gc_stack (body_ctx Φx ++ Γ) H R ->
    mdesc_mod R = Some Rm ->
    items_gen gc_deps gc_stack (body_ctx Φx ++ Γ) H its gs ->
    items_ok its ->
    alg_body_sound Γ (gm_open Φ H its) (gens_append Φx 0 gs).
Proof.
  intros * IH HH HR HRm Hg Hok Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HH HC).
  pose proof (gens_ext_wf _ _ _ _ _ _ Hg HH HX) as HXg.
  constructor; [ econstructor; eassumption | exact HXg | |].
  - cbn [body_opens]; rewrite <- (items_gen_length _ _ _ _ _ _ Hg), gm_dropn_gens_append.
    intros [| k] * Hk; cbn in Hk; [ injection Hk as <- <-; exact HH | exact (Ho _ _ _ Hk) ].
  - pose proof (ext_eq_ctx_left _ _ _ _ _ HXg) as HCg; rewrite <- List.app_assoc in HCg.
    exact (body_tags_gens _ _ _ _ Hg _ _ eq_refl HH Φx nil L eq_refl HCg HL).
Qed.

(** A body: its parameters, relevant at a level, its expansion, the
    targets of its opens, and its definitions at the sorts of their tags,
    filled in ([wf_gm_fill]), so it is a unit ([unit_full_body]). *)
Lemma alg_unit_body_sound : forall Γ Δ Φ Φx,
    (⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ /\ exists l, params_relevant gc_deps gc_stack Γ Δ l) ->
    tele_ass Δ -> alg_body_sound (Δ ++ Γ) Φ Φx ->
    body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ.
Proof.
  intros * HΔ Ht HB Hs Hsx Hn HΓ.
  destruct (HΔ HΓ) as [HΔe [l Hl]].
  destruct (HB _ _ eq_refl HΓ HΔe) as [Hbx HX Ho [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  (** The sort of each name: its entry's tag, at [L]. *)
  set (es := fun y => relevance_sort match gm_prefix_upto Φx y with
                                      | Some (gm_ext _ _ E) => entry_relevance E
                                      | _ => relevant
                                      end Typeω@L).
  apply unit_eq_of_full; apply (unit_full_body _ _ _ _ _ _ Hbx HC Ho Ht Hs Hsx Hn l Hl es).
  - intros y; apply type_sort_relevance_universe.
  - intros * Hp HE; exists L; unfold es; cbv beta; rewrite Hp; reflexivity.
  - intros * Hp HE Hf; unfold es; cbv beta; rewrite Hp.
    pose proof (HL _ _ _ _ _ Hp HE) as HA.
    pose proof (wf_gm_fill _ _ _ _ _ (presup_exp_ctx HA) Hf) as Hσ.
    pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA (type_sort_relevance_universe _ _) Hσ) as HAσ.
    exact HAσ.
Qed.

(** A tuple whose annotation normalises to a record type at [Rs], its
    fields checked at their types at [Rs]: of that normal form. *)
Lemma alg_tuple_sound : forall Γ T (fs : list (String.string * exp)) p Rs R i,
    ⊢ Γ -> Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_record p Rs) -> record_lookup gc_deps gc_stack p = Some R ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))] : Srt ->
       Γ ⊢ M : U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))]) ->
    Γ ⊢ a_tuple T fs : nf_record p Rs.
Proof.
  intros * HΓ HT Hn Hl Hfs HMs.
  assert (HTR : Γ ⊢ T ≈ nf_record p Rs : Typeω@i) by (eapply soundness_ty'; eassumption).
  cbn [nf_to_exp] in HTR |- *.
  assert (HRa : Γ ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) by (gen_presups; assumption).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) as HRt.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt _]].
  pose proof (tuple_fields_typed_seq _ _ _ _ _ Hrt Hl HRl Hfs HRt
                ltac:(intros * Hk Hfk (S' & HS' & Hi'); exact (HMs _ _ _ _ Hk Hfk HΓ _ HS' Hi'))) as HFt.
  eapply wf_conv'; [ eapply wf_tuple; [ exact HT | exact HTR | exact Hrt | exact Hl | exact HRl | exact HRt | exact Hfs | exact HFt ]
                   | exact HTR ].
Qed.

(** A projection of an element of a record type at [Rs]: of its field's
    type at [Rs] and the projections before it, which is a type. *)
Lemma alg_proj_typed : forall Γ M p Rs R f k U,
    ⊢ Γ -> Γ ⊢ M : nf_record p Rs -> record_lookup gc_deps gc_stack p = Some R ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    exists m, Γ ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] : relevance_sort (record_field_rel R k) Typeω@m /\
      Γ ⊢ a_proj f M : U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)].
Proof.
  intros * HΓ HM Hl Hfk; cbn [nf_to_exp] in HM.
  (** A record type is of a large universe, never a proposition. *)
  assert (exists i, Γ ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) as [i HRa]
    by (destruct (presup_exp_typ HM) as [SR HSR HRS]; destruct HSR as [iR |];
        [ exists iR; exact HRS | exfalso; exact (typ_prop_record_absurd HRS) ]).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) as HRt.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt _]].
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl HRl HRt) as [m Hm].
  destruct (record_proj_cong_at _ _ _ M M p R _ m k f U (wf_exp_eq_refl HM) Hrt Hl HRl HRt Hm Hfk) as [HUU Hpp].
  exists m; split; gen_presups; assumption.
Qed.

(** So it is of the normal form of that type. *)
Lemma alg_proj_sound : forall Γ M p Rs R f k U W,
    ⊢ Γ -> Γ ⊢ M : nf_record p Rs -> record_lookup gc_deps gc_stack p = Some R ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    nbe_ty_f Γ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] W ->
    Γ ⊢ a_proj f M : W.
Proof.
  intros * HΓ HM Hl Hfk Hn.
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ HM Hl Hfk) as (m & HUt & Hp).
  pose proof (type_sort_relevance_universe (record_field_rel R k) m) as HS.
  exact (exp_conv_sort HS (soundness_ty_at_sort HS HUt Hn) Hp).
Qed.

(** A type whose type [UB] normalises to a universe normal form [v] is of
    [v], whose level's atoms are of the sorts they carry: [UB] is of a
    large universe, as a universe normal form is no proposition's normal
    form ([nbe_ty_prop_not_univ_pi]). *)
Lemma typed_at_univ_nf : forall Δ B (UB UB' : nf) v,
    Δ ⊢ B : UB -> nbe_ty_f Δ UB UB' -> is_univ_nf UB' v ->
    Δ ⊢ B : universe_nf_tm v /\ universe_nf_well_scoped Δ v.
Proof.
  intros * HBU HnB Hv.
  assert (exists k, Δ ⊢ (UB : exp) : Typeω@k) as [kB HUB].
  { destruct (presup_exp_typ HBU) as [SB HSB HUB0]; destruct HSB as [kB |]; [ exists kB; exact HUB0 |].
    exfalso; pose proof (nbe_ty_prop_not_univ_pi _ _ _ HUB0 HnB) as Hnu.
    rewrite (is_univ_nf_eq _ _ Hv) in Hnu; destruct v as [[] |]; cbn in Hnu; exact Hnu. }
  assert (HUBe : Δ ⊢ (UB : exp) ≈ UB' : Typeω@kB) by (eapply soundness_ty'; eassumption).
  pose proof (nbe_ty_self HUB HnB) as HnB'.
  rewrite (is_univ_nf_eq _ _ Hv) in HUBe, HnB'.
  assert (HB' : Δ ⊢ B : universe_nf_tm v) by (rewrite <- nf_to_exp_univ_nf; eapply wf_conv'; [ exact HBU | exact HUBe ]).
  split; [ exact HB' |].
  eapply universe_nf_well_scoped_of_nbe; [ rewrite <- nf_to_exp_univ_nf; gen_presups; eassumption
                                         | rewrite <- nf_to_exp_univ_nf; exact HnB' ].
Qed.

(** The parts of a typed [Π] of the sort [r]: the domain of a sort, the
    codomain of the sort at [r] at a large universe (a small universe is
    below every large one). *)
Lemma wf_pi_parts_large : forall Γ r A B C,
    Γ ⊢ a_pi r A B : C ->
    exists Sd k, type_sort Sd /\ Γ ⊢ A : Sd /\ Γ ▹ A ⊢ B : relevance_sort r Typeω@k.
Proof.
  intros * H.
  destruct (wf_pi_inversion_at H) as [U SA HU HA HD HB _].
  assert (HΓA : ⊢ Γ ▹ A) by (gen_presups; assumption).
  inversion HU as [? ? ? i HΓ | ? ? ? n L HL]; subst; destruct HD; destruct r; cbn [relevance_sort exp_wk] in HB.
  - exists Typeω@i, i; repeat split; [ constructor | exact HA | exact HB ].
  - exists Typeω@i, 0; repeat split; [ constructor | exact HA | exact HB ].
  - exists Propₘ, i; repeat split; [ constructor | exact HA | exact HB ].
  - exists Propₘ, 0; repeat split; [ constructor | exact HA | exact HB ].
  - assert (HL1 : Γ ▹ A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ Level@n); [ exact HL | mauto 2 ]).
    exists Typeω@0, 0; repeat split; [ constructor | exact (wf_exp_suniv_large HL HA) | exact (wf_exp_suniv_large HL1 HB) ].
  - exists Typeω@0, 0; repeat split; [ constructor | exact (wf_exp_suniv_large HL HA) | exact HB ].
  - assert (HL1 : Γ ▹ A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ Level@n); [ exact HL | mauto 2 ]).
    exists Propₘ, 0; repeat split; [ constructor | exact HA | exact (wf_exp_suniv_large HL1 HB) ].
  - exists Propₘ, 0; repeat split; [ constructor | exact HA | exact HB ].
Qed.

(** A type of a sort, of the relevance [r] its value says, is of the sort
    [r] names ([typed_at_sort_of_initial_relevance]). *)
Lemma typed_at_relevance_of_nbe : forall {Γ A S r},
    type_sort S -> Γ ⊢ A : S -> nbe_ty_relevance Γ A r ->
    exists k : nat, Γ ⊢ A : relevance_sort r Typeω@k.
Proof.
  intros * HS HA (ρ & a & Hρ & Ha & <-).
  exact (typed_at_sort_of_initial_relevance HS HA Hρ Ha).
Qed.

(** Conversely, a type of the sort [r] names is of the relevance [r]: its
    value at the initial environment is of the sort's relevance
    ([typed_at_sort_of_initial_relevance]), and no type is of both sorts
    ([typ_prop_absurd]). *)
Lemma nbe_ty_relevance_of_typed : forall {Γ A r} {i : nat},
    Γ ⊢ A : relevance_sort r Typeω@i -> nbe_ty_relevance Γ A r.
Proof.
  intros * HA.
  pose proof (type_sort_relevance_universe r i) as HS.
  destruct (nbe_ty_exists_sort HS HA) as [W [ρ a Hρ Ha _]].
  exists ρ, a; split; [ exact Hρ | split; [ exact Ha |] ].
  destruct (typed_at_sort_of_initial_relevance HS HA Hρ Ha) as [k Hk].
  destruct r, (domain_relevance a); cbn [relevance_sort] in *; [ reflexivity | | | reflexivity ];
    exfalso; eapply typ_prop_absurd; eassumption.
Qed.

Lemma alg_type_sound :
  (forall {Γ A M}, Γ ⊢a M ⟸ A -> ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ A : Srt -> Γ ⊢ M : A) /\
    (forall {Γ A M}, Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A) /\
    (forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ) /\
    (forall {Γ Δ}, Γ ⊢aᵖ Δ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ /\ exists l, params_relevant gc_deps gc_stack Γ Δ l) /\
    (forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) /\
    (forall {Γ Φ Φx}, Γ ⊢aᵇ Φ ⇝ Φx -> alg_body_sound Γ Φ Φx) /\
    (forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H).
Proof.
  apply alg_type_mut_ind; intros.
  (** ** Checking: by the inferred type, below the checked one *)
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : ?A, HG : ⊢ ?G, Hs : ?G ⊢a ?A ⊆ ?B, HS : type_sort ?S, HB : ?G ⊢ ?B : ?S |- _ =>
        pose proof (IH HG) as HM; destruct (presup_exp_typ HM) as [SA HSA HA];
        eapply wf_exp_subtyp; [ exact HM | exact HB | exact HS | exact (alg_subtyping_sound_sort _ _ _ _ _ HSA HS Hs HA HB) ]
    end.
  (** ** Inference *)
  (** The universes, the levels and [Prop] *)
  - apply wf_typ; assumption.
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : _, Hn : nbe_ty_f _ (a_univ (succl ?M)) ?W, HG : ⊢ ?G |- _ =>
        pose proof (IH HG) as HMl; cbn [nf_to_exp] in HMl;
        assert (HSU : G ⊢ Type⟨succl M⟩ : Typeω@0) by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; exact HMl ]);
        eapply wf_conv'; [ eapply wf_univ; exact HMl | eapply soundness_ty'; [ exact HSU | exact Hn ] ]
    end.
  - apply wf_level; assumption.
  - apply wf_llit; [ lia | assumption ].
  - match goal with IH : ⊢ ?G -> ?G ⊢ ?M : _, HG : ⊢ ?G |- _ => pose proof (IH HG) as HMl end.
    cbn [nf_to_exp] in *; apply wf_succl; assumption.
  - match goal with
    | HM : ⊢ ?G -> ?G ⊢ ?M : _, HN : ⊢ ?G -> ?G ⊢ ?N : _, HG : ⊢ ?G |- ?G ⊢ maxl ?M ?N : _ =>
        pose proof (HM HG) as HMl; pose proof (HN HG) as HNl; cbn [nf_to_exp] in HMl, HNl |- *;
        match type of HMl with _ ⊢ _ : Level@?m => match type of HNl with _ ⊢ _ : Level@?n =>
          apply wf_maxl; [ apply (wf_exp_level_up (m := m)); [ lia | exact HMl ]
                         | apply (wf_exp_level_up (m := n)); [ lia | exact HNl ] ] end end
    end.
  - apply wf_prop; assumption.
  (** The propositions [⊤], [⊥], the proof [⋆] and the introduction of [⊤] *)
  - apply wf_True; assumption.
  - apply wf_true; assumption.
  - apply wf_tt; assumption.
  - apply wf_False; assumption.
  (** Ex falso: the target at its sort, the proof at [⊥] *)
  - match goal with
    | IHC : ⊢ ?G -> ?G ⊢ ?C : (nf_to_exp ?UC), Hs : is_sort_nf ?UC ?r ?u, IHM : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ⊥ : Srt -> ?G ⊢ ?M : ⊥,
      Hn : nbe_ty_f ?G ?C ?W, HG : ⊢ ?G |- _ =>
        pose proof (sort_typed_of_is_sort_nf (IHC HG) Hs) as HCs;
        pose proof (type_sort_relevance_universe r (universe_nf_large_index u)) as HS;
        pose proof (IHM HG _ type_sort_prop (wf_False _ _ _ HG)) as HM0;
        exact (exp_conv_sort HS (soundness_ty_at_sort HS HCs Hn) (wf_absurd _ _ _ _ _ _ HCs HS HM0))
    end.
  (** A conjunction of propositions *)
  - match goal with
    | IHP : ⊢ ?G -> ?G ⊢ ?P : (nf_to_exp Propⁿ), IHQ : ⊢ ?G ▹ ?P -> ?G ▹ ?P ⊢ ?Q : (nf_to_exp Propⁿ), HG : ⊢ ?G |- _ =>
        pose proof (IHP HG) as HP; cbn [nf_to_exp] in HP;
        assert (HGP : ⊢ G ▹ P) by (eapply wf_ctx_extend; [ exact HP | constructor ]);
        pose proof (IHQ HGP) as HQ; cbn [nf_to_exp] in HQ;
        apply wf_and; assumption
    end.
  (** A proof of a conjunction: at its annotation, normalised *)
  - match goal with
    | IHT : ⊢ ?G -> ?G ⊢ ?T : (nf_to_exp Propⁿ), HnT : nbe_ty_f ?G ?T (Σₚⁿ ?P ?Q),
      IHM : ⊢ ?G -> forall Srt, _ -> ?G ⊢ (nf_to_exp ?P) : Srt -> ?G ⊢ ?M : _,
      IHN : ⊢ ?G -> forall Srt, _ -> ?G ⊢ (nf_to_exp ?Q)[Id,,?M] : Srt -> ?G ⊢ ?N : _, HG : ⊢ ?G |- _ =>
        pose proof (IHT HG) as HT; cbn [nf_to_exp] in HT;
        pose proof (soundness_ty_at_sort type_sort_prop HT HnT) as HTe; cbn [nf_to_exp] in HTe;
        assert (HPQ : G ⊢ Σₚ (nf_to_exp P) (nf_to_exp Q) : Propₘ) by (gen_presups; assumption);
        destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
        pose proof (IHM HG _ type_sort_prop HP) as HM;
        assert (HQM : G ⊢ (nf_to_exp Q)[Id,,M] : Propₘ)
          by (exact (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ HP type_sort_prop HM)));
        pose proof (IHN HG _ type_sort_prop HQM) as HN;
        cbn [nf_to_exp];
        exact (exp_conv_sort type_sort_prop HTe (wf_conj _ _ _ _ _ _ _ _ HT HTe HP HQ HM HN))
    end.
  (** The components of a proof of a conjunction *)
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp (Σₚⁿ ?P ?Q)), HG : ⊢ ?G |- _ =>
        pose proof (IH HG) as HM; cbn [nf_to_exp] in HM;
        assert (HPQ : G ⊢ Σₚ (nf_to_exp P) (nf_to_exp Q) : Propₘ)
          by (let S0 := fresh "S0" in let H00 := fresh "H00" in
              destruct (presup_exp_typ HM) as [S0 _ H00]; exact (prop_former_typed H00 ltac:(eauto 6)));
        destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
        eapply wf_left; eassumption
    end.
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp (Σₚⁿ ?P ?Q)), Hn : nbe_ty_f ?G (nf_to_exp ?Q)[Id,,a_left ?M] ?W, HG : ⊢ ?G |- _ =>
        pose proof (IH HG) as HM; cbn [nf_to_exp] in HM;
        assert (HPQ : G ⊢ Σₚ (nf_to_exp P) (nf_to_exp Q) : Propₘ)
          by (let S0 := fresh "S0" in let H00 := fresh "H00" in
              destruct (presup_exp_typ HM) as [S0 _ H00]; exact (prop_former_typed H00 ltac:(eauto 6)));
        destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
        assert (HL : G ⊢ a_left M : nf_to_exp P) by (eapply wf_left; eassumption);
        assert (HQL : G ⊢ (nf_to_exp Q)[Id,,a_left M] : Propₘ)
          by (exact (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ HP type_sort_prop HL)));
        exact (exp_conv_sort type_sort_prop (soundness_ty_at_sort type_sort_prop HQL Hn)
                 (wf_right _ _ _ _ _ _ HP HQ HM HQL))
    end.
  (** The placeholder type and its element *)
  - apply wf_placeholder_type; assumption.
  - apply wf_placeholder; assumption.
  (** The type former, a constructor and the eliminator *)
  - match goal with Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, HΓ : ⊢ ?G |- _ =>
      destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc];
      destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ) as [j Hj];
      eapply wf_conv'; [ eapply wf_ind; eassumption | eapply soundness_ty'; eassumption ] end.
  - match goal with Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hcon : ind_con _ _ = Some ?gs,
                    HΓ : ⊢ ?G |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) Hl Hk Hcon HΓ) as [j Hj];
      eapply wf_conv'; [ eapply wf_con_closed; eassumption | eapply soundness_ty'; eassumption ] end.
  - match goal with
    | HM : ⊢ ?G -> ?G ⊢ ?M : _, HΓ : ⊢ ?G, Hg : elim_grp ?D ?oq ?p ?m |- ?G ⊢ a_elim ?r ?oq _ ?m _ ?M : _ =>
        eapply proj1; eapply (alg_elim_sound G M _ _ _ p D oq m); first [ exact HΓ | exact (HM HΓ) | eassumption ]
    end.
  (** A [Π]: the domain of either sort, counted in its universe, the
      codomain at the normal form of its universe, whose level's atoms are
      of the sorts they carry; at the normal form of the join *)
  - match goal with
    | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?rA ?u, IHB : ⊢ ?G ▹ ?A -> ?G ▹ ?A ⊢ ?B : (nf_to_exp ?UB),
      HnB : nbe_ty_f (?G ▹ ?A) (nf_to_exp ?UB) ?UB', Hv : is_univ_nf ?UB' ?v,
      HnW : nbe_ty_f ?G (universe_nf_pi_tm ?u ?v) ?W, HG : ⊢ ?G |- _ =>
        pose proof (IHA HG) as HA0;
        pose proof (pi_domain_ok_of_is_sort_nf HA0 Hs) as HAd;
        pose proof (sort_typed_of_is_sort_nf HA0 Hs) as HAs;
        assert (HGA : ⊢ G ▹ A) by (eapply wf_ctx_extend; [ exact HAs | apply type_sort_relevance_universe ]);
        destruct (typed_at_univ_nf _ _ _ _ _ (IHB HGA) HnB Hv) as [HB' Hvw];
        pose proof (wf_pi_universe_nf_pi HAd HB' Hvw) as HPi;
        destruct (wf_universe_nf_pi_tm HAd HB' Hvw) as [k Hk];
        eapply wf_exp_subtyp'; [ exact HPi | eapply wf_subtyp_refl'; eapply soundness_ty'; eassumption ]
    end.
  (** A [∀]: over a type of either sort, into propositions *)
  - match goal with
    | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?rA ?u, IHB : ⊢ ?G ▹ ?A -> ?G ▹ ?A ⊢ ?B : (nf_to_exp Propⁿ), HG : ⊢ ?G |- _ =>
        pose proof (sort_typed_of_is_sort_nf (IHA HG) Hs) as HAs;
        assert (HGA : ⊢ G ▹ A) by (eapply wf_ctx_extend; [ exact HAs | apply type_sort_relevance_universe ]);
        pose proof (IHB HGA) as HB; cbn [nf_to_exp] in HB |- *;
        exact (wf_all_sort _ _ _ _ (type_sort_relevance_universe _ _) HAs HB)
    end.
  (** [λ]: the annotation of either sort, the body at its type of the sort
      [r]; the function is of the [Π] of the annotation's normal form *)
  - match goal with
    | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?rA ?u, IHM : ⊢ ?G ▹ ?A -> ?G ▹ ?A ⊢ ?M : (nf_to_exp ?B),
      Hr : nbe_ty_relevance (?G ▹ ?A) (nf_to_exp ?B) ?r, Hn : nbe_ty_f ?G ?A ?C, HG : ⊢ ?G |- _ =>
        pose proof (sort_typed_of_is_sort_nf (IHA HG) Hs) as HAs;
        pose proof (type_sort_relevance_universe rA (universe_nf_large_index u)) as HSA;
        assert (HGA : ⊢ G ▹ A) by (eapply wf_ctx_extend; [ exact HAs | exact HSA ]);
        pose proof (IHM HGA) as HM;
        let SB := fresh "SB" in let HSB := fresh "HSB" in let HB0 := fresh "HB0" in let kB := fresh "kB" in
        let HBs := fresh "HBs" in
        destruct (presup_exp_typ HM) as [SB HSB HB0];
        destruct (typed_at_relevance_of_nbe HSB HB0 Hr) as [kB HBs];
        pose proof (soundness_ty_at_sort HSA HAs Hn) as HAC;
        assert (Hfn : G ⊢ λ A M : a_pi r A B) by (eapply wf_fn; [ exact HAs | exact HSA | exact HBs | exact HM ]);
        cbn [nf_to_exp];
        destruct r; cbn [relevance_sort] in HBs |- *;
        [ destruct (pi_cong_sort HSA HAs HAC (wf_exp_eq_refl HBs)) as [k Hk];
          eapply wf_conv'; [ exact Hfn | exact Hk ]
        | exact (exp_conv_sort type_sort_prop (all_cong_sort HSA HAs HAC (wf_exp_eq_refl HBs)) Hfn) ]
    end.
  (** An application: at the codomain instantiated, normalised *)
  - match goal with
    | IHM : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp (nf_pi ?r ?A ?B)), IHN : ⊢ ?G -> forall Srt, _ -> ?G ⊢ (nf_to_exp ?A) : Srt -> ?G ⊢ ?N : _,
      Hn : nbe_ty_f ?G (nf_to_exp ?B)[Id,,?N] ?C, HG : ⊢ ?G |- _ =>
        pose proof (IHM HG) as HM; cbn [nf_to_exp] in HM;
        assert (exists Spi, G ⊢ a_pi r (nf_to_exp A) (nf_to_exp B) : Spi) as [Spi HPi]
          by (let S00 := fresh "S00" in let H00 := fresh "H00" in destruct (presup_exp_typ HM) as [S00 _ H00]; eauto);
        destruct (wf_pi_parts_large _ _ _ _ _ HPi) as (SA & iU & HSA & HA & HBr);
        pose proof (IHN HG _ HSA HA) as HN;
        pose proof (type_sort_relevance_universe r iU) as HSB;
        assert (HBN : G ⊢ (nf_to_exp B)[Id,,N] : relevance_sort r Typeω@iU)
          by (exact (sub_preserves_sort _ _ _ _ _ _ _ HBr HSB (wf_sub_single _ _ _ _ _ _ HA HSA HN)));
        exact (exp_conv_sort HSB (soundness_ty_at_sort HSB HBN Hn) (wf_app _ _ _ _ _ _ _ _ _ _ HA HSA HBr HM HN))
    end.
  (** A local definition: its type of the sort [r], an annotation checked
      against, without one a type of a universe; the body's type, of a
      sort, instantiated, normalised *)
  - match goal with Ha : alg_let_ann _ _ |- _ => destruct Ha as [-> | ->] end; simpl_let_guards.
    + (** Without an annotation *)
      match goal with
      | Hr : nbe_ty_relevance ?G (nf_to_exp ?W) relevant,
        IHM : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp ?W), IHB : ⊢ ?G ▸ (nf_to_exp ?W) ≔ ?M -> _ ⊢ ?B : (nf_to_exp ?C),
        Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id,,?M] ?D, HG : ⊢ ?G |- _ =>
          pose proof (IHM HG) as HM;
          let SW := fresh "SW" in let HSW := fresh "HSW" in let HW0 := fresh "HW0" in let kW := fresh "kW" in
          let HAs := fresh "HAs" in
          destruct (presup_exp_typ HM) as [SW HSW HW0];
          destruct (typed_at_relevance_of_nbe HSW HW0 Hr) as [kW HAs]; cbn [relevance_sort] in HAs;
          assert (HGd : ⊢ G ▸ (nf_to_exp W) ≔ M) by (eapply wf_ctx_extend_def; [ exact HAs | constructor | exact HM ]);
          pose proof (IHB HGd) as HB;
          destruct (presup_exp_typ HB) as [SC HSC HC];
          pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_def _ _ _ _ _ _ HAs (type_sort_universe _) HM)) as HCs;
          exact (exp_conv_sort HSC (soundness_ty_at_sort HSC HCs Hn)
                   (wf_let _ _ _ _ _ _ _ _ _ HAs (type_sort_universe _) HM HB ltac:(left; split; [ reflexivity | eexists; reflexivity ])))
      end.
    + (** With one *)
      match goal with
      | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u,
        IHM : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ?A : Srt -> ?G ⊢ ?M : ?A, IHB : ⊢ ?G ▸ ?A ≔ ?M -> _ ⊢ ?B : (nf_to_exp ?C),
        Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id,,?M] ?D, HG : ⊢ ?G |- _ =>
          pose proof (sort_typed_of_is_sort_nf (IHA HG) Hs) as HAs;
          pose proof (type_sort_relevance_universe r (universe_nf_large_index u)) as HSA;
          pose proof (IHM HG _ HSA HAs) as HM;
          assert (HGd : ⊢ G ▸ A ≔ M) by (eapply wf_ctx_extend_def; [ exact HAs | exact HSA | exact HM ]);
          pose proof (IHB HGd) as HB;
          destruct (presup_exp_typ HB) as [SC HSC HC];
          pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_def _ _ _ _ _ _ HAs HSA HM)) as HCs;
          exact (exp_conv_sort HSC (soundness_ty_at_sort HSC HCs Hn)
                   (wf_let _ _ _ _ _ _ _ _ _ HAs HSA HM HB ltac:(right; reflexivity)))
      end.
  (** A module [let] *)
  - match goal with
    | IHU : ⊢ ?G -> gc_deps ⍮ gc_stack ⍮ ?G ⊢ᵘ ?U ≈ ?U, IHB : ⊢ ?G ▹ₘ ?U -> _ ⊢ ?B : (nf_to_exp ?C),
      Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id ,,ₘ me_lit ?U] ?D, HG : ⊢ ?G |- _ =>
        pose proof (IHU HG) as HU;
        assert (HGU : ⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
        pose proof (IHB HGU) as HB;
        destruct (presup_exp_typ HB) as [SC HSC HC];
        pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_mod _ _ _ _ HU)) as HCs;
        exact (exp_conv_sort HSC (soundness_ty_at_sort HSC HCs Hn) (wf_let_mod _ _ _ _ _ _ _ HU HC HSC HB))
    end.
  (** A member, at the normal form of the type its module's description
      reads *)
  - match goal with
    | IHH : ⊢ ?G -> gc_deps ⍮ gc_stack ⍮ ?G ⊢ᵐ ?H0 ≈ ?H0, Hm : mdenote _ _ _ (me_mem ?H0 ?x0) _, Ht : mdesc_type _ = Some ?A0,
      Hn : nbe_ty_f ?G ?A0 ?B, HG : ⊢ ?G |- _ =>
        destruct (member_wf _ _ _ _ _ (IHH HG) Hm Ht) as ([SA HSA HA] & _ & HMt);
        exact (exp_conv_sort HSA (soundness_ty_at_sort HSA HA Hn) HMt)
    end.
  (** A variable, at the normal form of its type *)
  - match goal with
    | Hl : ?G ∋ #?x : ?A, Hn : nbe_ty_f ?G ?A ?B, HG : ⊢ ?G |- _ =>
        assert (Hx : G ⊢ #x : A) by (apply wf_vlookup; assumption);
        destruct (presup_exp_typ Hx) as [SA HSA HA];
        exact (exp_conv_sort HSA (soundness_ty_at_sort HSA HA Hn) Hx)
    end.
  (** A record's type former, a tuple and a projection *)
  - match goal with Hl : record_lookup _ _ _ = Some _, HΓ : ⊢ ?G |- _ =>
      let j := fresh "j" in let Hrt := fresh "Hrt" in let Hj := fresh "Hj" in
      destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt Hj]];
      eapply wf_conv'; [ exact Hrt | eapply soundness_ty'; eassumption ] end.
  - match goal with
    | IHT : ⊢ ?G -> ?G ⊢ ?T : (nf_to_exp ?UT), Hu : is_univ_nf ?UT ?u, HΓ : ⊢ ?G |- _ =>
        pose proof (IHT HΓ) as HT0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HT0;
        pose proof (wf_exp_universe_nf_large_index HT0) as HT;
        eapply alg_tuple_sound; [ exact HΓ | exact HT | eassumption | eassumption | eassumption | intros; eauto ]
    end.
  - match goal with HM : ⊢ ?G -> ?G ⊢ ?M : _, HΓ : ⊢ ?G, Hfk : List.nth_error (record_fields _) _ = Some _ |- _ ⊢ a_proj _ ?M : _ =>
      eapply alg_proj_sound; [ exact HΓ | exact (HM HΓ) | eassumption | exact Hfk | eassumption ] end.
  (** ** Extensions, entry by entry *)
  - apply wf_ext_eq_nil; assumption.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (sort_typed_of_is_sort_nf (IHA HP) Hs) as HAs;
        eapply wf_ext_eq_ass_same; [ exact HX | exact HAs | apply type_sort_relevance_universe | exact HAs ]
    end.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u,
      IHM : ⊢ ?P ++ ?G -> forall Srt, _ -> ?P ++ ?G ⊢ ?A : Srt -> ?P ++ ?G ⊢ ?M : ?A, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (sort_typed_of_is_sort_nf (IHA HP) Hs) as HAs;
        pose proof (IHM HP _ (type_sort_relevance_universe _ _) HAs) as HM;
        eapply wf_ext_eq_def_same; [ exact HX | exact HAs | apply type_sort_relevance_universe | exact HAs | exact HM | exact HM ]
    end.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHU : ⊢ ?P ++ ?G -> wf_unit_eq _ _ _ ?U ?U, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        eapply wf_ext_eq_mod; [ exact HX | exact (IHU HP) | exact (IHU HP) ]
    end.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hu : is_univ_nf ?UA ?u,
      IHM : ⊢ ?P ++ ?G -> forall Srt, _ -> ?P ++ ?G ⊢ ?A : Srt -> ?P ++ ?G ⊢ ?M : ?A,
      IHU : ⊢ ?P ++ ?G -> wf_unit_eq _ _ _ ?U ?U, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (IHA HP) as HA0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA0;
        pose proof (wf_exp_universe_nf_large_index HA0) as HA;
        pose proof (IHM HP _ (type_sort_universe _) HA) as HM;
        eapply wf_ext_eq_dm; [ exact HX | exact HA | apply wf_exp_eq_refl; exact HA | exact HM | apply wf_exp_eq_refl; exact HM
                             | exact HA | exact HM | exact (IHU HP) | exact (IHU HP) ]
    end.
  (** ** Parameters: each of a universe, all at one level *)
  - split; [ apply wf_ext_eq_nil; assumption | exists 0; apply params_relevant_nil ].
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P /\ _, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hu : is_univ_nf ?UA ?u, HG : ⊢ ?G |- _ =>
        destruct (IHX HG) as [HX [l Hl]]; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (IHA HP) as HA0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA0;
        pose proof (wf_exp_universe_nf_large_index HA0) as HA;
        split; [ eapply wf_ext_eq_ass_same; [ exact HX | exact HA | constructor | exact HA ] |];
        exists (max (universe_nf_large_index u) l);
        change (P ▹ A) with ((ce_ass A :: nil) ++ P);
        apply params_relevant_app;
        [ let Δ1 := fresh "Δ1" in let T := fresh "T" in let Δ2 := fresh "Δ2" in let E := fresh "E" in
          intros Δ1 T Δ2 E; destruct Δ1 as [| ? [| ? ?]]; cbn in E; try discriminate;
          let HT := fresh "HT" in let HΔ := fresh "HΔ" in injection E as HT HΔ; subst; exact HA
        | exact Hl ]
    end.
  (** ** Units *)
  - eapply alg_unit_body_sound; eassumption.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P /\ _, IHE : ⊢ ?P ++ ?G -> wf_modexp_eq _ _ _ ?E ?E, Ha : tele_ass ?P, HG : ⊢ ?G |- _ =>
        destruct (IHX HG) as [HX [l Hl]]; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        eapply wf_unit_eq_alias with (param_level := l); [ exact HX | exact Ha | exact Ha | exact (IHE HP) | exact (IHE HP) | exact Hl | exact Hl ]
    end.
  (** ** Bodies, by their own lemmas *)
  - apply alg_body_nil_sound.
  - match goal with
    | IH : alg_body_sound _ _ _, HA : ⊢ _ -> _ ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u,
      HM : ⊢ _ -> forall Srt, _ -> _ ⊢ ?A : Srt -> _ ⊢ ?M : ?A |- _ =>
        eapply (alg_body_def_sound _ _ _ _ _ _ _ _ _ (universe_nf_large_index u));
          [ exact IH | intros HC; exact (sort_typed_of_is_sort_nf (HA HC) Hs)
          | intros HC; exact (HM HC _ (type_sort_relevance_universe _ _) (sort_typed_of_is_sort_nf (HA HC) Hs)) ]
    end.
  - eapply alg_body_mod_sound; eassumption.
  - match goal with
    | IH : alg_body_sound _ _ _, HA : ⊢ _ -> _ ⊢ ?A : (nf_to_exp ?UA), Hu : is_univ_nf ?UA ?u,
      HM : ⊢ _ -> forall Srt, _ -> _ ⊢ ?A : Srt -> _ ⊢ ?M : ?A, HU : ⊢ _ -> wf_unit_eq _ _ _ ?U ?U |- _ =>
        assert (HA' : ⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : Typeω@(universe_nf_large_index u))
          by (intros HC; apply wf_exp_universe_nf_large_index; rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              exact (HA HC));
        eapply (alg_body_dm_sound _ _ _ _ _ _ _ _ (universe_nf_large_index u));
          [ exact IH | exact HA' | intros HC; exact (HM HC _ (type_sort_universe _) (HA' HC)) | exact HU ]
    end.
  - eapply alg_body_open_sound; eassumption.
  (** ** Module expressions *)
  - match goal with Hm : mdenote _ _ _ (me_unit _) _ |- wf_modexp_eq _ _ _ _ _ =>
      let Hu := fresh "Hu" in
      destruct (mdenote_unit_inv _ _ ltac:(eapply ctx_wf_gctx; eassumption) _ _ _ Hm) as (? & ? & Hu & _);
      eapply wf_me_unit; [ eauto | exact Hu ] end.
  - mautosolve 4.
  - mautosolve 4.
  - match goal with Hm : mdenote _ _ _ (me_mem ?H0 _) _, Htl : mdesc_mod_tele _ = Some _, IHH : ⊢ ?G -> _, HG : ⊢ ?G |- _ =>
      pose proof (IHH HG) as HH; eapply wf_me_mem; eassumption end.
  - match goal with
    | Hm : mdenote _ _ _ ?H0 _, Htl : mdesc_mod_tele _ = Some _, Hv : tele_view _ = Some _,
      IHH : ⊢ ?G -> wf_modexp_eq _ _ _ ?H0 ?H0, IHN : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ?B : Srt -> ?G ⊢ ?N : ?B, HG : ⊢ ?G
      |- wf_modexp_eq _ _ _ (me_app _ _) _ =>
        pose proof (IHH HG) as HH;
        destruct (mtele_head_wf _ _ _ _ _ _ HH Hm Htl Hv) as [i HB];
        pose proof (IHN HG _ (type_sort_universe _) HB) as HN;
        eapply wf_me_app; eauto using wf_exp_eq_refl
    end.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 alg_type_sound); [ eassumption | eassumption | apply type_sort_universe | eassumption ].
Qed.

(** The same at a type of any sort. *)
Lemma alg_type_check_sound_sort : forall {Γ Srt A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    type_sort Srt ->
    Γ ⊢ A : Srt ->
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

(** Checked parameters are an extension, each a type of a universe, all
    at one level ((R) of the unit rules). *)
Lemma alg_params_sound : forall {Γ Δ}, Γ ⊢aᵖ Δ -> ⊢ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ /\ exists l, params_relevant gc_deps gc_stack Γ Δ l.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 alg_type_sound)))); eassumption. Qed.

Lemma alg_unit_sound : forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 (proj2 alg_type_sound))))); eassumption. Qed.

Lemma alg_modexp_sound : forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros; eapply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_sound)))))); eassumption. Qed.

(** A checked body is read in a well-formed context, past its expansion. *)
Lemma alg_body_ctx : forall {Γ Φ Φx}, ⊢ Γ -> Γ ⊢aᵇ Φ ⇝ Φx -> ⊢ body_ctx Φx ++ Γ.
Proof.
  intros * HΓ HB.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_sound))))) _ _ _ HB Γ nil eq_refl HΓ
              ltac:(apply wf_ext_eq_nil; exact HΓ)) as [_ HX _ _].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite List.app_nil_r in HC; exact HC.
Qed.

(** A body checks to one expansion. *)
Lemma alg_body_functional : forall {Γ Φ Φx Φx'}, ⊢ᵍ gc_deps ⍮ gc_stack ->
    Γ ⊢aᵇ Φ ⇝ Φx -> Γ ⊢aᵇ Φ ⇝ Φx' -> Φx = Φx'.
Proof.
  intros * Hg Hb1; revert Φx'; induction Hb1; intros Φx' Hb2; inversion Hb2; subst;
    try match goal with IH : forall Φx', _ ⊢aᵇ ?Φ ⇝ Φx' -> _ = Φx', Hb : _ ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
      pose proof (IH _ Hb); subst Y end; try reflexivity.
  f_equal; eapply (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg))))); eassumption.
Qed.

(** The parts of a [Π] the algorithm infers: the domain at its universe, the
    codomain at the normal form of its universe, whose level's atoms are of
    the sorts they carry. *)
Lemma alg_pi_parts_sound : forall {Γ A B UA UB UB' rA u v},
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_sort_nf UA rA u ->
    Γ ▹ A ⊢a B ⟹ UB ->
    nbe_ty_f (Γ ▹ A) UB UB' ->
    is_univ_nf UB' v ->
    pi_domain_ok Γ A u /\ Γ ▹ A ⊢ B : universe_nf_tm v /\ universe_nf_well_scoped (Γ ▹ A) v.
Proof.
  intros * HΓ HAi Hs HBi HnB Hv.
  pose proof (alg_type_infer_sound HAi HΓ) as HA0.
  pose proof (sort_typed_of_is_sort_nf HA0 Hs) as HAs.
  assert (HGA : ⊢ Γ ▹ A) by (eapply wf_ctx_extend; [ exact HAs | apply type_sort_relevance_universe ]).
  split; [ exact (pi_domain_ok_of_is_sort_nf HA0 Hs) |].
  exact (typed_at_univ_nf _ _ _ _ _ (alg_type_infer_sound HBi HGA) HnB Hv).
Qed.

(** A normal form [W] of a type [T] of a sort normalises to itself. *)
Ltac normal_of_typed HS HT Hn Hnbe :=
  eapply idempotent_nbe_ty_sort; [ | exact HT | exact Hn | exact Hnbe ]; exact HS.

(** An inferred type is a normal form: most rules infer the normal form of
    a type of a sort, which normalises to itself; a [λ] the [Π] of its
    domain's normal form and of its body's type, normal by induction; a
    projection of a conjunction a part of a normal form. *)
Lemma alg_type_infer_normal : forall {Γ A A' M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A' ->
    A = A'.
Proof.
  intros Γ A A0 M HΓ0 Hinfer Hnbe0; revert A0 HΓ0 Hnbe0; induction Hinfer; intros A' HΓ0 Hnbe;
    try (symmetry; eapply nbe_ty_suniv_lit; eassumption);
    try (directed_inversion_clear_by_head nbe_ty;
         directed_inversion_by_head eval_exp; subst;
         directed_inversion_by_head read_typ; subst;
         reflexivity).
  all: lazymatch goal with
  (** A small universe: the normal form of [Type⟨succl M⟩] *)
  | HMi : ?G ⊢a ?M ⟹ Levelⁿ@?k, Hn : nbe_ty_f _ (a_univ (succl ?M)) _ |- _ =>
      pose proof (alg_type_infer_sound HMi HΓ0) as HMl;
      assert (HT : G ⊢ Type⟨succl M⟩ : Typeω@0) by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; exact HMl ]);
      normal_of_typed (type_sort_universe 0) HT Hn Hnbe
  (** Ex falso: the normal form of its target *)
  | HCi : ?G ⊢a ?C ⟹ ?UC, Hs : is_sort_nf ?UC ?r ?u, HMc : alg_type_check ?G a_False _, Hn : nbe_ty_f ?G ?C _ |- _ =>
      normal_of_typed (type_sort_relevance_universe r (universe_nf_large_index u))
        (sort_typed_of_is_sort_nf (alg_type_infer_sound HCi HΓ0) Hs) Hn Hnbe
  (** A proof of a conjunction: the normal form of its annotation *)
  | HTi : ?G ⊢a ?T ⟹ Propⁿ, Hn : nbe_ty_f ?G ?T (Σₚⁿ _ _) |- _ =>
      normal_of_typed type_sort_prop (alg_type_infer_sound HTi HΓ0) Hn Hnbe
  (** The first component of a proof of a conjunction: the first part of a
      normal form *)
  | HMi : ?G ⊢a ?M ⟹ Σₚⁿ ?P ?Q, IH : forall A0, ⊢ ?G -> nbe_ty_f ?G _ A0 -> _ = A0 |- ?P = _ =>
      pose proof (alg_type_infer_sound HMi HΓ0) as HM;
      destruct (presup_exp_typ HM) as [S0 HS0 HPQ0];
      pose proof (prop_former_typed HPQ0 ltac:(cbn [nf_to_exp]; eauto 6)) as HPQ;
      destruct (nbe_ty_exists_sort type_sort_prop HPQ) as [WPQ HWPQ];
      pose proof (IH _ HΓ0 HWPQ) as E; subst WPQ;
      cbn [nf_to_exp] in HWPQ; destruct (nbe_ty_and_inv _ _ _ _ HWPQ) as (WP & WQ & E' & HWP & _);
      injection E' as -> ->;
      functional_nbe_rewrite_clear; reflexivity
  (** The second: the normal form of its type *)
  | HMi : ?G ⊢a ?M ⟹ Σₚⁿ ?P ?Q, Hn : nbe_ty_f ?G (nf_to_exp ?Q)[Id,,a_left ?M] _ |- _ =>
      pose proof (alg_type_infer_sound (alg_type_infer_right _ _ _ _ _ HMi Hn) HΓ0) as HR;
      pose proof (alg_type_infer_sound HMi HΓ0) as HM; cbn [nf_to_exp] in HM;
      assert (HPQ : G ⊢ Σₚ (nf_to_exp P) (nf_to_exp Q) : Propₘ)
        by (let S00 := fresh "S00" in let H00 := fresh "H00" in
            destruct (presup_exp_typ HM) as [S00 _ H00]; exact (prop_former_typed H00 ltac:(eauto 6)));
      destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
      assert (HL : G ⊢ a_left M : nf_to_exp P) by (eapply wf_left; eassumption);
      normal_of_typed type_sort_prop
        (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ HP type_sort_prop HL)) Hn Hnbe
  (** The type former and a constructor: the normal forms of closed types *)
  | Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hlt : _ < ind_ndecl ?D, Hn : nbe_ty_f _ (ind_ty _ _) _ |- _ =>
      destruct (decl_of_lookup _ _ _ _ _ HΓ0 Hl) as [HD Hc];
      destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ0) as [j Hj];
      normal_of_typed (type_sort_universe j) Hj Hn Hnbe
  | Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hcon : ind_con _ _ = Some _, Hn : nbe_ty_f _ (con_ty _ _ _ _ _) _ |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ0) (decls_of_ctx _ _ _ HΓ0) Hl Hk Hcon HΓ0) as [j Hj];
      normal_of_typed (type_sort_universe j) Hj Hn Hnbe
  (** The eliminator: the normal form of the motive's instance *)
  | HMi : ?G ⊢a ?N ⟹ nf_indty _ _ _, Hg : elim_grp ?D ?oq ?p ?m,
    Hn : nbe_ty_f ?G (eb_motive ?bm)[sb_of_list Id (?Ns ++ ?N :: nil)] _ |- _ =>
      let Sm := fresh "Sm" in let HSm := fresh "HSm" in let Hm := fresh "Hm" in
      assert (exists Srt, type_sort Srt /\ G ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ N :: nil)] : Srt) as (Sm & HSm & Hm)
        by (eapply proj2; eapply (alg_elim_sound G N _ _ _ p D oq m);
            first [ exact HΓ0 | exact (alg_type_infer_sound HMi HΓ0) | eassumption
                  | intros; eapply alg_type_check_sound_sort; eauto ]);
      normal_of_typed HSm Hm Hn Hnbe
  (** A [Π]: the normal form of the join of its parts' universes *)
  | HAi : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA _ _, HBi : ?G ▹ ?A ⊢a ?B ⟹ ?UB,
    HnB : nbe_ty_f (?G ▹ ?A) (nf_to_exp ?UB) ?UB', Hv : is_univ_nf ?UB' _, Hn : nbe_ty_f ?G (universe_nf_pi_tm _ _) _ |- _ =>
      destruct (alg_pi_parts_sound HΓ0 HAi Hs HBi HnB Hv) as (HA' & HB' & Hvw);
      destruct (wf_universe_nf_pi_tm HA' HB' Hvw) as [k Hk];
      normal_of_typed (type_sort_universe k) Hk Hn Hnbe
  (** A [λ]: the [Π] of its domain's normal form, normal, and of its
      body's type, normal by induction, in the context the domain's normal
      form extends, semantically the context the domain extends *)
  | HAi : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?rA ?u, HMi : ?G ▹ ?A ⊢a ?M ⟹ ?B,
    Hr : nbe_ty_relevance (?G ▹ ?A) (nf_to_exp ?B) ?r, Hn : nbe_ty_f ?G ?A ?C,
    IH : forall A0, ⊢ ?G ▹ ?A -> nbe_ty_f (?G ▹ ?A) (nf_to_exp ?B) A0 -> ?B = A0 |- _ =>
      pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ0) Hs) as HAs;
      pose proof (type_sort_relevance_universe rA (universe_nf_large_index u)) as HSA;
      assert (HGA : ⊢ G ▹ A) by (eapply wf_ctx_extend; [ exact HAs | exact HSA ]);
      let SB := fresh "SB" in let HSB := fresh "HSB" in let HB0 := fresh "HB0" in let kB := fresh "kB" in
      let HBs := fresh "HBs" in
      destruct (presup_exp_typ (alg_type_infer_sound HMi HGA)) as [SB HSB HB0];
      destruct (typed_at_relevance_of_nbe HSB HB0 Hr) as [kB HBs];
      pose proof (soundness_ty_at_sort HSA HAs Hn) as HAC;
      cbn [nf_to_exp] in Hnbe; destruct (nbe_ty_pi_inv _ _ _ _ _ Hnbe) as (WC & WB & -> & HWC & HWB);
      pose proof (idempotent_nbe_ty_sort HSA HAs Hn HWC) as <-;
      assert (HBC : G ▹ nf_to_exp C ⊢ nf_to_exp B : relevance_sort r Typeω@kB)
        by (eapply ctxsub_exp; [ exact (sub_id_extend_of_exp_eq HSA (wf_exp_eq_sym _ _ _ _ _ _ HAC)) | exact HBs ]);
      pose proof (ctxeq_nbe_ty_eq_sort (type_sort_relevance_universe _ _) HBC
                    (ctx_extend_sem_eq HSA (wf_exp_eq_sym _ _ _ _ _ _ HAC)) HWB) as HWB';
      rewrite <- (IH _ HGA HWB'); reflexivity
  (** An application: the normal form of the codomain instantiated *)
  | HMi : ?G ⊢a ?M ⟹ nf_pi ?r ?A ?B, HNc : alg_type_check ?G (nf_to_exp ?A) ?N, Hn : nbe_ty_f ?G (nf_to_exp ?B)[Id,,?N] _ |- _ =>
      pose proof (alg_type_infer_sound HMi HΓ0) as HM; cbn [nf_to_exp] in HM;
      let Spi := fresh "Spi" in let HPi := fresh "HPi" in
      assert (exists Spi, G ⊢ a_pi r (nf_to_exp A) (nf_to_exp B) : Spi) as [Spi HPi]
        by (let S00 := fresh "S00" in let H00 := fresh "H00" in destruct (presup_exp_typ HM) as [S00 _ H00]; eauto);
      destruct (wf_pi_parts_large _ _ _ _ _ HPi) as (SA & iU & HSA & HA & HBr);
      pose proof (alg_type_check_sound_sort HNc HΓ0 HSA HA) as HN;
      normal_of_typed (type_sort_relevance_universe r iU)
        (sub_preserves_sort _ _ _ _ _ _ _ HBr (type_sort_relevance_universe _ _) (wf_sub_single _ _ _ _ _ _ HA HSA HN)) Hn Hnbe
  (** A local definition: the normal form of its body's type instantiated *)
  | Ha : alg_let_ann _ _ |- _ =>
      destruct Ha as [-> | ->]; simpl_let_guards;
      [ match goal with
        | Hr : nbe_ty_relevance ?G (nf_to_exp ?W) relevant, HMi : ?G ⊢a ?M ⟹ ?W,
          HBi : ?G ▸ (nf_to_exp ?W) ≔ ?M ⊢a ?B ⟹ ?C, Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id,,?M] _ |- _ =>
            pose proof (alg_type_infer_sound HMi HΓ0) as HM;
            let SW := fresh "SW" in let HSW := fresh "HSW" in let HW0 := fresh "HW0" in let kW := fresh "kW" in
            let HAs := fresh "HAs" in
            destruct (presup_exp_typ HM) as [SW HSW HW0];
            destruct (typed_at_relevance_of_nbe HSW HW0 Hr) as [kW HAs]; cbn [relevance_sort] in HAs;
            assert (HGd : ⊢ G ▸ (nf_to_exp W) ≔ M) by (eapply wf_ctx_extend_def; [ exact HAs | constructor | exact HM ]);
            let SC := fresh "SC" in let HSC := fresh "HSC" in let HC := fresh "HC" in
            destruct (presup_exp_typ (alg_type_infer_sound HBi HGd)) as [SC HSC HC];
            normal_of_typed HSC (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_def _ _ _ _ _ _ HAs (type_sort_universe _) HM)) Hn Hnbe
        end
      | match goal with
        | HAi : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?r ?u, HMc : alg_type_check ?G ?A ?M,
          HBi : ?G ▸ ?A ≔ ?M ⊢a ?B ⟹ ?C, Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id,,?M] _ |- _ =>
            pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ0) Hs) as HAs;
            pose proof (type_sort_relevance_universe r (universe_nf_large_index u)) as HSA;
            pose proof (alg_type_check_sound_sort HMc HΓ0 HSA HAs) as HM;
            assert (HGd : ⊢ G ▸ A ≔ M) by (eapply wf_ctx_extend_def; [ exact HAs | exact HSA | exact HM ]);
            let SC := fresh "SC" in let HSC := fresh "HSC" in let HC := fresh "HC" in
            destruct (presup_exp_typ (alg_type_infer_sound HBi HGd)) as [SC HSC HC];
            normal_of_typed HSC (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_def _ _ _ _ _ _ HAs HSA HM)) Hn Hnbe
        end ]
  (** A module [let]: the same *)
  | HUi : ?G ⊢aᵘ ?U, HBi : ?G ▹ₘ ?U ⊢a ?B ⟹ ?C, Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id ,,ₘ me_lit ?U] _ |- _ =>
      pose proof (alg_unit_sound HUi HΓ0) as HU;
      assert (HGU : ⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
      let SC := fresh "SC" in let HSC := fresh "HSC" in let HC := fresh "HC" in
      destruct (presup_exp_typ (alg_type_infer_sound HBi HGU)) as [SC HSC HC];
      normal_of_typed HSC (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_mod _ _ _ _ HU)) Hn Hnbe
  (** A member: the normal form of the type its module's description reads *)
  | HHi : ?G ⊢aᵐ ?H0, Hm : mdenote _ _ _ (me_mem _ _) _, Ht : mdesc_type _ = Some ?A0, Hn : nbe_ty_f _ ?A0 _ |- _ =>
      let SA := fresh "SA" in let HSA := fresh "HSA" in let HA := fresh "HA" in
      destruct (member_wf _ _ _ _ _ (alg_modexp_sound HHi HΓ0) Hm Ht) as ([SA HSA HA] & _);
      normal_of_typed HSA HA Hn Hnbe
  (** A variable: the normal form of its type *)
  | Hl : ?G ∋ #?x : ?A, Hn : nbe_ty_f ?G ?A _ |- _ =>
      let SA := fresh "SA" in let HSA := fresh "HSA" in let HA := fresh "HA" in
      destruct (presup_exp_typ (wf_vlookup _ _ _ _ _ HΓ0 Hl)) as [SA HSA HA];
      normal_of_typed HSA HA Hn Hnbe
  (** A record's type former, a tuple and a projection *)
  | Hl : record_lookup _ _ _ = Some _, Hn : nbe_ty_f _ (record_ty _) _ |- _ =>
      let j := fresh "j" in let Hj := fresh "Hj" in
      destruct (record_former_typed _ _ _ HΓ0 Hl) as [j [_ Hj]];
      normal_of_typed (type_sort_universe j) Hj Hn Hnbe
  | HTi : ?G ⊢a ?T ⟹ ?UT, Hu : is_univ_nf ?UT ?u, Hn : nbe_ty_f ?G ?T (nf_record _ _) |- _ =>
      pose proof (alg_type_infer_sound HTi HΓ0) as HT0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HT0;
      normal_of_typed (type_sort_universe (universe_nf_large_index u)) (wf_exp_universe_nf_large_index HT0) Hn Hnbe
  | HMi : ?G ⊢a ?N ⟹ nf_record _ _, Hfk : List.nth_error (record_fields _) _ = Some (_, ?U), Hn : nbe_ty_f _ (?U[_]) _ |- _ =>
      let m := fresh "m" in let HUt := fresh "HUt" in
      destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ0 (alg_type_infer_sound HMi HΓ0) ltac:(eassumption) Hfk) as (m & HUt & _);
      eapply idempotent_nbe_ty_sort; [ apply type_sort_relevance_universe | exact HUt | exact Hn | exact Hnbe ]
  end.
Qed.

Hint Resolve alg_type_infer_normal : mctt.

(** An inferred type is its own normal form. *)
Lemma alg_type_infer_self : forall {Γ A M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A.
Proof.
  intros * HΓ Hi.
  destruct (presup_exp_typ (alg_type_infer_sound Hi HΓ)) as [S HS HA].
  destruct (nbe_ty_exists_sort HS HA) as (C & HC).
  assert (A = C) as <- by (eapply alg_type_infer_normal; eassumption).
  exact HC.
Qed.

(** A type checked against a large universe infers a universe at an index
    below it: with the small tier that index need not be a large one. *)
Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ universe_nf_le u (universe_large i).
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [ contradiction | |].
  - exists Typeωⁿ@i0, (universe_large i0); split; [ exact Hinfer | split; [ constructor | cbn; assumption ] ].
  - exists (univⁿ c xs), (universe_small (c, xs)); split; [ exact Hinfer | split; [ constructor | exact I ] ].
Qed.

Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

(** A term checked against a [Π] of the sort [r] infers a [Π] of that sort:
    its domain the normal form of the [Π]'s, its codomain below the [Π]'s
    (equal to it at [propositional], where subtyping is equality). *)
Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M r A B S},
    ⊢ Γ ->
    Γ ⊢ a_pi r A B : S ->
    Γ ⊢a M ⟸ a_pi r A B ->
    exists A' B' SA, type_sort SA /\ Γ ⊢a M ⟹ nf_pi r A' B' /\ Γ ⊢ A' ≈ A : SA /\ Γ ▹ A ⊢a B' ⊆ B.
Proof.
  intros * HΓ HPi Hcheck.
  destruct (wf_pi_parts_large _ _ _ _ _ HPi) as (SA & k & HSA & HA & HB).
  inversion Hcheck as [? W ? ? Hinfer Hsub]; subst.
  destruct Hsub as [W1 W2 Hn1 Hn2 Hnf].
  pose proof (alg_type_infer_normal HΓ Hinfer Hn1) as <-.
  destruct (nbe_ty_pi_inv _ _ _ _ _ Hn2) as (WA & WB & -> & HnA & HnB).
  (** The inferred type is a [Π] of the sort [r] over [WA]. *)
  assert (exists WB', W = nf_pi r WA WB' /\ ⊢anf WB' ⊆ WB) as (WB' & -> & HWB).
  { inversion Hnf; subst.
    - destruct r; cbn in *; [ contradiction | exists WB; split; [ reflexivity | apply alg_subtyping_nf_refl ] ].
    - eexists; split; [ reflexivity | eassumption ]. }
  pose proof (soundness_ty_at_sort HSA HA HnA) as HAWA.
  exists WA, WB', SA; split; [ exact HSA | split; [ exact Hinfer | split; [ symmetry; exact HAWA |] ] ].
  (** The inferred codomain is normal, in the context its domain's normal
      form extends, semantically the context [A] extends. *)
  pose proof (alg_type_infer_sound Hinfer HΓ) as HM; cbn [nf_to_exp] in HM.
  destruct (presup_exp_typ HM) as [S' _ HPi'].
  destruct (wf_pi_parts_large _ _ _ _ _ HPi') as (SA' & k' & HSA' & HA' & HB').
  pose proof (alg_type_infer_self HΓ Hinfer) as Hself.
  destruct (nbe_ty_pi_inv _ _ _ _ _ Hself) as (X & Y & E & _ & HnB'); injection E as -> ->.
  pose proof (ctxeq_nbe_ty_eq_sort (type_sort_relevance_universe _ _) HB'
                (ctx_extend_sem_eq HSA ltac:(symmetry; exact HAWA)) ltac:(exact HnB')) as HnB''.
  econstructor; [ exact HnB'' | exact HnB | exact HWB ].
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

(** A term that infers the normal form of a type of a sort checks against
    the type. *)
Lemma alg_type_check_of_infer_nbe : forall {Γ M A S},
    type_sort S ->
    Γ ⊢ A : S ->
    (forall W, nbe_ty_f Γ A W -> Γ ⊢a M ⟹ W) ->
    Γ ⊢a M ⟸ A.
Proof.
  intros * HS HA Hi.
  destruct (nbe_ty_exists_sort HS HA) as [W HW].
  pose proof (soundness_ty_at_sort HS HA HW) as HE.
  econstructor; [ exact (Hi _ HW) |].
  apply alg_subtyping_complete.
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HA (presup_exp_eq_right HE) HS HE)).
Qed.

(** A term checked against [Prop] infers [Prop]: subtyping at a
    proposition is equality ([alg_subtyping_nf_not_univ_pi_eq]). *)
Lemma alg_type_check_prop_infer : forall {Γ A},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Propₘ ->
    Γ ⊢a A ⟹ Propⁿ.
Proof.
  intros * HΓ Hc.
  inversion Hc as [? W ? ? Hi [W1 W2 Hn1 Hn2 Hsub]]; subst.
  pose proof (alg_type_infer_normal HΓ Hi Hn1) as <-.
  assert (W2 = Propⁿ) as ->
    by (inversion Hn2; subst; directed_inversion_by_head eval_exp; subst;
        directed_inversion_by_head read_typ; subst; reflexivity).
  rewrite (alg_subtyping_nf_not_univ_pi_eq _ _ Hsub ltac:(right; exact I)) in Hi; exact Hi.
Qed.

(** A term checked against a sort infers a sort. *)
Lemma alg_type_check_sort_infer : forall {Γ A S},
    ⊢ Γ ->
    type_sort S ->
    Γ ⊢a A ⟸ S ->
    exists UA r u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA r u.
Proof.
  intros * HΓ [i |] Hc.
  - destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ Hc) as (UA & u & Hi & Hu & _).
    exists UA, relevant, u; split; [ exact Hi | constructor; exact Hu ].
  - exists Propⁿ, propositional, (universe_small (ordinal_of_nat 0, nil)).
    split; [ exact (alg_type_check_prop_infer HΓ Hc) | constructor ].
Qed.

(** ** Unannotated Definitions

    The number of unannotated [let]s in a term, the measure of the outer
    induction of completeness: the body of an unannotated [let] is checked in
    a context refined to the type its definiens infers, by a derivation which
    is not a subderivation, but whose subject has fewer of them.  The
    eliminators and the module expressions a term, a unit or a body reads are
    counted too: the motive and the branches of an eliminator are typed at the
    parameters the scrutinee infers, and a module expression is well-formed
    by a derivation that may go through its δ- and β-reducts, so its parts are
    reached by generation ([modexp_gen]), not as subderivations. *)
Fixpoint exp_lets (M : exp) : nat :=
  match M with
  | a_succl M | a_univ M => exp_lets M
  | a_maxl M N => exp_lets M + exp_lets N
  | a_absurd A M => exp_lets A + exp_lets M
  | a_and P Q => exp_lets P + exp_lets Q
  | a_conj T M N => exp_lets T + exp_lets M + exp_lets N
  | a_left M | a_right M => exp_lets M
  | a_elim _ _ Us _ Bks M =>
      S ((fix us_lets (Us : list exp) : nat :=
            match Us with
            | nil => 0
            | U :: Us' => exp_lets U + us_lets Us'
            end) Us +
         (fix blocks_lets (Bks : list eblock) : nat :=
            match Bks with
            | nil => 0
            | eb_mk _ oZ A Bs :: Bks' =>
                match oZ with Some Z => exp_lets Z | None => 0 end + exp_lets A +
                (fix brs_lets (Bs : list (String.string * nat * exp)) : nat :=
                   match Bs with
                   | nil => 0
                   | b :: Bs' => exp_lets (snd b) + brs_lets Bs'
                   end) Bs + blocks_lets Bks'
            end) Bks + exp_lets M)
  | a_pi _ A B => exp_lets A + exp_lets B
  | a_fn A M => exp_lets A + exp_lets M
  | a_app M N => exp_lets M + exp_lets N
  | a_let b B => binding_lets b + exp_lets B
  | a_mem H _ => S (modexp_lets H)
  | a_tuple T fs =>
      exp_lets T +
      (fix fields_lets (fs : list (String.string * exp)) : nat :=
         match fs with
         | nil => 0
         | f :: fs' => exp_lets (snd f) + fields_lets fs'
         end) fs
  | a_proj _ M => exp_lets M
  | _ => 0
  end
with modexp_lets (H : modexp) : nat :=
  match H with
  | me_mem H _ => modexp_lets H
  | me_app H N => modexp_lets H + exp_lets N
  | me_lit U => gunit_lets U
  | _ => 0
  end
with binding_lets (b : binding) : nat :=
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
  | md_body sm Φ => gmod_lets Φ
  | md_alias E => S (modexp_lets E)
  end
with gmod_lets (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ E => gmod_lets Φ + gentry_lets E
  | gm_open Φ H _ => gmod_lets Φ + S (modexp_lets H)
  end
with gentry_lets (E : gentry) : nat :=
  match E with
  | ge_def _ _ _ A B => exp_lets A + match B with Some M => exp_lets M | None => 0 end
  | ge_mod _ U => gunit_lets U
  | ge_ind _ _ _ _ Φ => gmod_lets Φ
  | ge_def_mod _ A M U => exp_lets A + exp_lets M + gunit_lets U
  | ge_record _ _ _ Φ => gmod_lets Φ
  end
with centry_lets (e : centry) : nat :=
  match e with
  | ce_ass A => exp_lets A
  | ce_def A M => exp_lets A + exp_lets M
  | ce_mod U => gunit_lets U
  | ce_dm A M U => exp_lets A + exp_lets M + gunit_lets U
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
  induction Φ as [| Φ IH x [b pv r A [M |] | pm U | ? ? ? ? ? | ? ? ? ? | ? ? ? ?] | Φ IH c its ]; cbn; rewrite ?ctx_lets_app; [ lia .. |].
  enough (ctx_lets (List.repeat (ce_ass a_placeholder_type) (List.length its)) = 0) by lia.
  induction (List.length its); cbn; auto.
Qed.

Lemma exp_lets_apps : forall M args,
    exp_lets (apps M args) = exp_lets M + List.fold_right (fun N n => exp_lets N + n) 0 args.
Proof. intros M args; revert M; induction args; intros; cbn; [ lia | rewrite IHargs; cbn; lia ]. Qed.

Ltac lets_bound :=
  repeat first
    [ progress rewrite ?gunit_lets_mk, ?ctx_lets_app in *
    | progress cbn [exp_lets modexp_lets binding_lets moddef_lets gmod_lets
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
Lemma alg_type_check_typ_of : forall Γ A UA (u : universe_nf) i,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    universe_nf_le u (universe_large i) ->
    Γ ⊢a A ⟸ Typeω@i.
Proof.
  intros * HΓ Hi Hu Hle.
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in *.
  apply alg_subtyping_complete.
  destruct u as [L | j]; cbn [universe_nf_tm universe_nf_le] in *.
  - assert (exists k, Γ ⊢ Type⟨lvl_exp_of (fst L) (List.map atom_exp (snd L))⟩ : Typeω@k) as [k Hk]
      by univ_large.
    destruct (wf_univ_lvl_inversion Hk) as [n Hn].
    eapply wf_subtyp_small_large; eassumption.
  - apply wf_subtyp_ge; [ assumption | lia ].
Qed.

Lemma alg_type_check_suniv : forall Γ A UA (u : universe_nf) m,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    universe_nf_le u (universe_nf_lit m) ->
    Γ ⊢a A ⟸ Type⟨𝕃ᵒ m⟩.
Proof.
  intros * HΓ Hi Hu Hle.
  destruct u as [[c xs] | j]; cbn [universe_nf_le universe_nf_lit] in Hle; [| contradiction ].
  (** The inferred universe is a normal form, so its level's atoms are of the
      sorts they carry, below the literal's tier ([lvl_le_lit_sorts]). *)
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  pose proof (alg_type_infer_self HΓ Hi) as HnA.
  rewrite (is_univ_nf_eq _ _ Hu) in HA, HnA; cbn [universe_nf_to_nf nf_univ_of fst snd nf_to_exp] in HA, HnA.
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [k Hk] by univ_large.
  destruct (univ_nf_well_scoped Hk HnA) as (nA & HLA & Hc & Hxs).
  set (N := Nat.max nA (fst m)).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf.
  apply alg_subtyping_complete.
  cbn [universe_nf_tm fst snd].
  eapply (wf_subtyp_suniv _ _ _ N);
    [ exact HΓ | eapply wf_exp_level_up; [| exact HLA ]; subst N; lia
    | apply wf_llit; [ subst N; lia | exact HΓ ] |].
  assert (HcN : fst c <= N) by (subst N; lia).
  assert (HmN : fst m <= N) by (subst N; lia).
  assert (HxsN : @level_atoms_well_scoped gc_deps gc_stack N Γ xs) by (eapply level_atoms_well_scoped_mono; [| exact Hxs ]; subst N; lia).
  exact (lvl_exp_of_le (n := N) c xs m nil HcN HmN HΓ HxsN I Hle).
Qed.

(** A type checked against a small universe infers a small universe, at a canonical
    level below the one [Type⟨t⟩] normalizes to. *)
Lemma alg_type_check_suniv_tm_implies_alg_type_infer_univ : forall {Γ A t},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L') /\ lvl_le L L'.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' B' Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  pose proof Hnbe2 as Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  destruct L as [d ys]; unfold nf_univ_of in *; cbn [fst snd] in *.
  inversion Hnfsub; subst; [ contradiction |].
  exists (c, xs), (d, ys); split; [ exact Hinfer | split; [ exact Hnbe2 | assumption ] ].
Qed.

(** A term checked against a type of levels infers a type of levels of a
    smaller sort: the only normal forms below [Levelⁿ@n] are the [Levelⁿ@m]
    with [m <= n]. *)
Lemma alg_type_check_level_infer : forall {Γ M n},
    ⊢ Γ ->
    Γ ⊢a M ⟸ Level@n ->
    exists m, Γ ⊢a M ⟹ Levelⁿ@m /\ m <= n.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [ contradiction |].
  eexists; split; [ exact Hinfer | assumption ].
Qed.

(** Conversely, a term that infers a type of levels checks against every
    type of levels of a larger sort. *)
Lemma alg_type_check_level_of : forall {Γ M m n},
    ⊢ Γ ->
    Γ ⊢a M ⟹ Levelⁿ@m ->
    m <= n ->
    Γ ⊢a M ⟸ Level@n.
Proof.
  intros * HΓ Hi Hmn.
  econstructor; [ exact Hi |].
  apply alg_subtyping_complete; cbn [nf_to_exp].
  apply wf_subtyp_level; assumption.
Qed.

(** ** Completeness of the [Π] Rule

    A [Π] whose parts infer universes checks against every type its
    universe ([universe_nf_pi_tm]) is below. *)
Lemma alg_pi_check_of_infer : forall Γ A B UA UB rA (u v : universe_nf) T k,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹ A ⊢a B ⟹ UB ->
    is_sort_nf UA rA u ->
    is_univ_nf UB v ->
    Γ ⊢ T : Typeω@k ->
    Γ ⊢ universe_nf_pi_tm u v ⊆ T ->
    Γ ⊢a Π A B ⟸ T.
Proof.
  intros * HΓ HAi HBi Hu Hv HT Hsub.
  assert (HnB : nbe_ty_f (Γ ▹ A) UB UB).
  { pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hu) as HAs.
    eapply alg_type_infer_self; [| eassumption ].
    eapply wf_ctx_extend; [ exact HAs | apply type_sort_relevance_universe ]. }
  destruct (alg_pi_parts_sound HΓ HAi Hu HBi HnB Hv) as (HA & HB & Hvws).
  destruct (wf_universe_nf_pi_tm HA HB Hvws) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW HeqW]].
  econstructor; [ eapply alg_type_infer_pi; [ eassumption | eassumption | eassumption | exact HnB | exact Hv | eassumption ] |].
  apply alg_subtyping_complete.
  etransitivity; [| exact Hsub ].
  eapply wf_subtyp_refl'; symmetry; exact HeqW.
Qed.

(** The universe a [Π] infers is a universe normal form: [universe_nf_pi_tm] is a
    universe term, which reads back as one. *)
Lemma nbe_ty_universe_nf_pi_tm_univ : forall Γ (u v : universe_nf) W,
    nbe_ty_f Γ (universe_nf_pi_tm u v) W ->
    exists w, is_univ_nf W w.
Proof.
  intros * Hn.
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [universe_nf_pi_tm universe_nf_max universe_nf_tm fst snd] in Hn;
    [ | destruct xs | destruct ys |];
    cbn [universe_nf_tm] in Hn;
    directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst;
    directed_inversion_by_head read_typ; subst;
    eexists; first [ constructor | match goal with |- is_univ_nf (nf_univ_of ?L) _ => destruct L; constructor end ].
Qed.

(** A [Π] whose parts infer universes infers one. *)
Lemma alg_pi_infer_univ : forall Γ A B UA UB rA (u v : universe_nf),
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹ A ⊢a B ⟹ UB ->
    is_sort_nf UA rA u ->
    is_univ_nf UB v ->
    exists W w, Γ ⊢a Π A B ⟹ W /\ is_univ_nf W w /\ nbe_ty_f Γ (universe_nf_pi_tm u v) W.
Proof.
  intros * HΓ HAi HBi Hu Hv.
  assert (HnB : nbe_ty_f (Γ ▹ A) UB UB).
  { pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hu) as HAs.
    eapply alg_type_infer_self; [| eassumption ].
    eapply wf_ctx_extend; [ exact HAs | apply type_sort_relevance_universe ]. }
  destruct (alg_pi_parts_sound HΓ HAi Hu HBi HnB Hv) as (HA & HB & Hvws).
  destruct (wf_universe_nf_pi_tm HA HB Hvws) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW _]].
  destruct (nbe_ty_universe_nf_pi_tm_univ _ _ _ _ HW) as [w Hw].
  exists W, w; split; [ eapply alg_type_infer_pi; [ eassumption | eassumption | eassumption | exact HnB | exact Hv | eassumption ] | split; assumption ].
Qed.

(** The universe of a [Π] of two types below a large universe is below it. *)
Lemma universe_nf_pi_tm_large : forall Γ (u v : universe_nf) i k,
    ⊢ Γ ->
    Γ ⊢ universe_nf_pi_tm u v : Typeω@k ->
    universe_nf_le u (universe_large i) ->
    universe_nf_le v (universe_large i) ->
    Γ ⊢ universe_nf_pi_tm u v ⊆ Typeω@i.
Proof.
  intros * HΓ Hk Hu Hv.
  destruct u as [[c xs] | i1], v as [[d ys] | j1]; cbn [universe_nf_pi_tm universe_nf_le fst snd] in *.
  - destruct (wf_univ_lvl_inversion Hk) as [? ?]; eapply wf_subtyp_small_large; eassumption.
  - destruct xs; cbn [universe_nf_max universe_nf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - destruct ys; cbn [universe_nf_max universe_nf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - cbn [universe_nf_max universe_nf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia ].
Qed.

(** The small [Π] at a level term.  The codomain's universe is below the
    normal form of the weakened level, which is fresh ([nbe_ty_wk_fresh]), so
    the bound of the codomain's level under the binder is below it too
    ([lvl_le_bound_wk]), and the [Π] is at a level below [L]: the domain's is
    below [L] in [Γ], and the codomain's bound below [L[↑]ʷ] in [Γ ▹ A],
    which strengthens.  Every level here is a normal form or an inferred
    universe's level, so its atoms are of the sorts they carry
    ([univ_nf_well_scoped], [soundness_lvl_well_scoped]).  The domain
    infers a sort at the small universe [(c, xs)], with its level and
    atoms well formed: a small universe, or [Prop], at the least level. *)
Lemma alg_pi_small_complete_at : forall Γ L A B n UA rA c xs e zs,
    Γ ⊢ L : Level@n ->
    ⊢ Γ ▹ A ->
    Γ ⊢a A ⟹ UA ->
    is_sort_nf UA rA (universe_small (c, xs)) ->
    nbe_ty_f Γ Type⟨L⟩ (nf_univ_of (e, zs)) ->
    lvl_le (c, xs) (e, zs) ->
    (exists nA, Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@nA /\ fst c <= nA /\
       @level_atoms_well_scoped gc_deps gc_stack nA Γ xs) ->
    Γ ▹ A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π A B ⟸ Type⟨L⟩.
Proof.
  intros * HL0 HΓA HAi Hs HnL HLA HAws HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓA HBc) as (LB & L' & HBi & HnL' & HLB).
  assert (HfL' : all_list (fun a => ne_fresh 0 (atom_level a)) (snd L'))
    by exact (nbe_ty_wk_fresh _ _ Γ A Type⟨L⟩ _ HnL').
  pose proof (lvl_le_bound_wk 0 _ _ HLB HfL') as HbLB.
  destruct LB as [d ys], L' as [f ws]; cbn [fst snd] in *.
  eapply (alg_pi_check_of_infer _ _ _ _ _ rA (universe_small (c, xs)) (universe_small (d, ys)) _ 0);
    [ exact HΓ | exact HAi | exact HBi | exact Hs | constructor | eapply wf_univ_large_tm; eassumption |].
  cbn [universe_nf_pi_tm fst snd]; unfold lvl_bound; cbn [fst snd].
  (** The levels and their atoms, each at its own sort. *)
  assert (HBi' : Γ ▹ A ⊢ B : Type⟨lvl_exp_of d (List.map atom_exp ys)⟩) by (eapply alg_type_infer_sound in HBi; eassumption).
  assert (exists k, Γ ▹ A ⊢ Type⟨lvl_exp_of d (List.map atom_exp ys)⟩ : Typeω@k) as [kB HkB] by univ_large.
  destruct HAws as (nA & HLAe0 & Hc & Hxs).
  destruct (univ_nf_well_scoped HkB (alg_type_infer_self HΓA HBi)) as (nB & HLBe0 & Hd & Hys).
  assert (HL1 : Γ ▹ A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ Level@n); [ exact HL0 | mauto 2 ]).
  pose proof (soundness_lvl_well_scoped HL0 (nbe_ty_univ_level (L := (e, zs)) (n := n) HnL)) as [He Hzs].
  pose proof (soundness_lvl_well_scoped HL1 (nbe_ty_univ_level (L := (f, ws)) (n := n) HnL')) as [Hf Hws].
  cbn [fst snd] in He, Hzs, Hf, Hws.
  assert (HTt : Γ ⊢ Type⟨L⟩ ≈ (nf_univ_of (e, zs) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ eapply wf_univ_large_tm; eassumption | exact HnL ]).
  assert (HTt' : Γ ▹ A ⊢ Type⟨L[↑]ʷ⟩ ≈ (nf_univ_of (f, ws) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ eapply wf_univ_large_tm; eassumption | exact HnL' ]).
  cbn [nf_to_exp nf_univ_of fst snd] in HTt, HTt'.
  apply exp_eq_suniv_tm_inj in HTt as [nT HTt0], HTt' as [nT' HTt'0].
  (** All of them move to the largest of the sorts, one above the
      codomain's, where the bound of its open atoms lives. *)
  set (cb := ordinal_max d (level_atoms_open_bound 0 ys)) in *.
  set (fp := level_atoms_fresh_part 0 ys) in *.
  set (N := S (Nat.max (Nat.max n (Nat.max nA nB)) (Nat.max nT nT'))).
  assert (Hcb : fst cb <= N)
    by (subst cb N; apply ordinal_max_fst_le;
        [ lia | eapply Nat.le_trans; [ apply level_atoms_open_bound_fst; eapply level_atoms_well_scoped_sorts; exact Hys | lia ] ]).
  assert (HxsN : @level_atoms_well_scoped gc_deps gc_stack N Γ xs) by (eapply level_atoms_well_scoped_mono; [| exact Hxs ]; subst N; lia).
  assert (HzsN : @level_atoms_well_scoped gc_deps gc_stack N Γ zs) by (eapply level_atoms_well_scoped_mono; [| exact Hzs ]; subst N; lia).
  assert (HwsN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹ A) ws) by (eapply level_atoms_well_scoped_mono; [| exact Hws ]; subst N; lia).
  assert (HfpN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹ A) fp)
    by (apply level_atoms_well_scoped_fresh_part; eapply level_atoms_well_scoped_mono; [| exact Hys ]; subst N; lia).
  assert (HL : Γ ⊢ L : Level@N) by (eapply wf_exp_level_up; [| exact HL0 ]; subst N; lia).
  assert (HLAe : Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@N) by (eapply wf_exp_level_up; [| exact HLAe0 ]; subst N; lia).
  assert (HTt : Γ ⊢ L ≈ lvl_exp_of e (List.map atom_exp zs) : Level@N) by (eapply wf_exp_eq_level_up; [| exact HTt0 ]; subst N; lia).
  assert (HTt' : Γ ▹ A ⊢ L[↑]ʷ ≈ lvl_exp_of f (List.map atom_exp ws) : Level@N)
    by (eapply wf_exp_eq_level_up; [| exact HTt'0 ]; subst N; lia).
  clear HL0 HLAe0 HTt0 HTt'0.
  set (LAe := lvl_exp_of c (List.map atom_exp xs)) in *.
  set (LBs := lvl_exp_of cb (List.map atom_exp (List.map (map_level_atom (ne_unwk 0)) fp))).
  assert (Hfresh : lvl_exp_of cb (List.map atom_exp fp) = LBs[↑]ʷ)
    by exact (nf_fresh_unwk 0 (nf_lvl cb fp) (level_atoms_fresh_part_fresh 0 ys)).
  assert (HLBl : Γ ▹ A ⊢ LBs[↑]ʷ : Level@N)
    by (rewrite <- Hfresh; apply lvl_exp_of_wf; [ exact Hcb | exact HΓA | apply level_atoms_well_scoped_wf; exact HfpN ]).
  assert (HLBs : Γ ⊢ LBs : Level@N).
  { refine (level_nf_strengthen Γ A N (nf_lvl cb (List.map (map_level_atom (ne_unwk 0)) fp)) _ HΓA HLBl).
    (* PENDING design: a level whose atoms hold proofs need not strengthen (level_nf_strengthen asks nf_proof_free). *)
    admit. }
  eapply wf_subtyp_suniv; [ exact HΓ | apply wf_maxl; eassumption | exact HL |].
  apply lvl_sub_maxl_lub; [ exact HLAe | exact HLBs | exact HL | |].
  - (** The domain's level is below [L]. *)
    unfold lvl_sub.
    assert (HcN : fst c <= N) by (subst N; lia).
    assert (HeN : fst e <= N) by (subst N; lia).
    pose proof (lvl_exp_of_le (n := N) c xs e zs HcN HeN HΓ HxsN HzsN HLA) as Hle.
    transitivity (maxl LAe (lvl_exp_of e (List.map atom_exp zs)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt ] |].
    transitivity (lvl_exp_of e (List.map atom_exp zs)); [ exact Hle | symmetry; exact HTt ].
  - (** The codomain's bound, below [L[↑]ʷ] in [Γ ▹ A], strengthened. *)
    unfold lvl_sub.
    assert (HfN : fst f <= N) by (subst N; lia).
    pose proof (lvl_exp_of_le (n := N) cb fp f ws Hcb HfN HΓA HfpN HwsN HbLB) as Hle.
    rewrite Hfresh in Hle.
    assert (Hlong : Γ ▹ A ⊢ maxl LBs[↑]ʷ L[↑]ʷ ≈ L[↑]ʷ : Level@N).
    { transitivity (maxl LBs[↑]ʷ (lvl_exp_of f (List.map atom_exp ws)));
        [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt' ] |].
      transitivity (lvl_exp_of f (List.map atom_exp ws)); [ exact Hle | symmetry; exact HTt' ]. }
    exact (exp_eq_strengthen nil Γ A (maxl LBs L) L Level@N ltac:(constructor) HΓA ltac:(mauto 3) HL Hlong).
Admitted. (* PENDING design: level_nf_strengthen at a level whose atoms hold proofs *)

(** The small [Π] over a type of the small universe. *)
Lemma alg_pi_small_complete : forall Γ L A B n,
    Γ ⊢ L : Level@n ->
    Γ ⊢ A : Type⟨L⟩ ->
    Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a A ⟸ Type⟨L⟩ ->
    Γ ▹ A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π A B ⟸ Type⟨L⟩.
Proof.
  intros * HL0 HA HB HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (HΓA : ⊢ Γ ▹ A) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓ HAc) as (LA & Lt & HAi & HnL & HLA).
  destruct LA as [c xs], Lt as [e zs].
  eapply alg_pi_small_complete_at; [ exact HL0 | exact HΓA | exact HAi | do 2 constructor | exact HnL | exact HLA | | exact HBc ].
  assert (HAi' : Γ ⊢ A : Type⟨lvl_exp_of c (List.map atom_exp xs)⟩) by (eapply alg_type_infer_sound in HAi; eassumption).
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [kA HkA] by univ_large.
  exact (univ_nf_well_scoped HkA (alg_type_infer_self HΓ HAi)).
Qed.

(** The small [Π] out of a proposition: [Prop] counts as the least small
    universe ([is_sort_nf_prop]), below every level. *)
Lemma alg_pi_small_prop_complete : forall Γ L A B n,
    Γ ⊢ L : Level@n ->
    Γ ⊢ A : Propₘ ->
    Γ ⊢a A ⟸ Propₘ ->
    Γ ▹ A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π A B ⟸ Type⟨L⟩.
Proof.
  intros * HL0 HA HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (HΓA : ⊢ Γ ▹ A) by (eapply wf_ctx_extend; [ exact HA | exact type_sort_prop ]).
  pose proof (alg_type_check_prop_infer HΓ HAc) as HAi.
  assert (HT : Γ ⊢ Type⟨L⟩ : Typeω@0) by (eapply wf_univ_large_tm; [ exact HΓ | exact HL0 ]).
  destruct (nbe_ty_exists_sort (type_sort_universe 0) HT) as [W HW].
  destruct (nbe_ty_univ_term (univ_term_suniv _) HW) as [u ->].
  destruct (nbe_ty_suniv_univ_nf HW) as ([e zs] & -> & _).
  eapply alg_pi_small_complete_at; [ exact HL0 | exact HΓA | exact HAi | exact is_sort_nf_prop | exact HW | apply lvl_le_zero | | exact HBc ].
  exists 0; split; [ cbn; eapply wf_llit; [ cbn; lia | exact HΓ ] | split; [ cbn; lia | exact I ] ].
Qed.

(** Completeness, for terms and for the module judgments at once, since a
    unit's body holds terms and a term may hold a unit.  The global context is
    an index of the judgments, so it is fixed for the induction, as in
    [subtyp_spec]. *)
(** The parts of an eliminator have fewer [let]s than it. *)
Lemma elim_lets_parts : forall r oq Us m Bks M,
    (forall U, List.In U Us -> exp_lets U < exp_lets (a_elim r oq Us m Bks M)) /\
    (forall b Z, List.In b Bks -> eb_ann b = Some Z -> exp_lets Z < exp_lets (a_elim r oq Us m Bks M)) /\
    (forall b, List.In b Bks -> exp_lets (eb_motive b) < exp_lets (a_elim r oq Us m Bks M)) /\
    (forall b br, List.In b Bks -> List.In br (eb_brs b) -> exp_lets (snd br) < exp_lets (a_elim r oq Us m Bks M)) /\
    exp_lets M < exp_lets (a_elim r oq Us m Bks M).
Proof.
  intros; cbn [exp_lets].
  set (ul := (fix us_lets (Us : list exp) : nat :=
                match Us with nil => 0 | U :: Us' => exp_lets U + us_lets Us' end) Us).
  set (brl := fix brs_lets (Bs : list (String.string * nat * exp)) : nat :=
                match Bs with nil => 0 | b :: Bs' => exp_lets (snd b) + brs_lets Bs' end).
  set (bl := (fix blocks_lets (Bks : list eblock) : nat :=
                match Bks with
                | nil => 0
                | eb_mk _ oZ A Bs :: Bks' =>
                    match oZ with Some Z => exp_lets Z | None => 0 end + exp_lets A + brl Bs + blocks_lets Bks'
                end) Bks).
  assert (HU : forall U, List.In U Us -> exp_lets U <= ul).
  { unfold ul; clear; induction Us as [| U' Us IH]; intros U HU; cbn in HU |- *; [ contradiction |].
    destruct HU as [-> | HU]; [ lia | specialize (IH _ HU); lia ]. }
  assert (Hbr : forall Bs br, List.In br Bs -> exp_lets (snd br) <= brl Bs).
  { induction Bs as [| br' Bs IH]; intros br Hin; cbn in Hin |- *; [ contradiction |].
    destruct Hin as [-> | Hin]; [ lia | specialize (IH _ Hin); lia ]. }
  assert (HB : forall b, List.In b Bks ->
             match eb_ann b with Some Z => exp_lets Z | None => 0 end + exp_lets (eb_motive b) + brl (eb_brs b) <= bl).
  { unfold bl; clear -Hbr; induction Bks as [| [nm oZ A Bs] Bks IH]; intros b Hb; cbn in Hb |- *; [ contradiction |].
    destruct Hb as [<- | Hb]; cbn; [ lia | specialize (IH _ Hb); lia ]. }
  split; [ intros U HU'; specialize (HU _ HU'); lia | split; [| split; [| split ] ] ].
  - intros b Z Hb HZ; specialize (HB _ Hb); rewrite HZ in HB; lia.
  - intros b Hb; specialize (HB _ Hb); lia.
  - intros b br Hb Hbr'; specialize (HB _ Hb); specialize (Hbr _ _ Hbr'); lia.
  - lia.
Qed.

(** A monotone property with a witness below each [j < n] has one witness
    for them all. *)
Lemma nat_bound_upto : forall (Q : nat -> nat -> Prop) n,
    (forall j, j < n -> exists l, Q j l) -> (forall j l l', l <= l' -> Q j l -> Q j l') ->
    exists L, forall j, j < n -> Q j L.
Proof.
  intros Q n; induction n as [| n IH]; intros Hex Hmon; [ exists 0; intros; lia |].
  destruct IH as [L HL]; [ intros j Hj; apply Hex; lia | exact Hmon |].
  destruct (Hex n ltac:(lia)) as [l Hl].
  exists (max L l); intros j Hj.
  destruct (Nat.eq_dec j n) as [-> | Hne]; [ eapply Hmon; [| exact Hl ]; lia | eapply Hmon; [| apply HL; lia ]; lia ].
Qed.

(** Normal forms, position by position, give [nfs_agree]. *)
Lemma nfs_agree_of_nth : forall Γ Ms Rs Ts,
    List.length Ms = List.length Ts -> List.length Rs = List.length Ts ->
    (forall j M R T, List.nth_error Ms j = Some M -> List.nth_error Rs j = Some R -> List.nth_error Ts j = Some T ->
       exists W, nbe_f Γ M T W /\ nbe_f Γ R T W) ->
    nfs_agree Γ Ms Rs Ts.
Proof.
  induction Ms as [| M Ms IH]; intros [| R Rs] [| T Ts] HMl HRl H; cbn in HMl, HRl; try discriminate; [ constructor |].
  destruct (H 0 M R T eq_refl eq_refl eq_refl) as (W & HMW & HRW).
  econstructor; [ exact HMW | exact HRW |].
  apply IH; [ lia | lia | intros j M' R' T' HM' HR' HT'; exact (H (S j) M' R' T' HM' HR' HT') ].
Qed.

(** The eliminator, from the derivation's premises at the parameters [Ps]
    and the algorithm's for its parts: the scrutinee infers the type former
    the member's type is headed by, at parameters equal to the
    derivation's ([subtyp_ind_nf]), whose uniform ones the member's
    uniform arguments normalize to, and whose others are the member's
    non-uniform ones ([mty_params_conv], [mty_params_inj]); the annotations
    and the motives are checked at one universe above them all
    ([nat_bound_upto]).  An annotation infers a sort, which is a
    universe: the annotation is below the member's type, an inductive
    type, which no proposition is below ([subtyp_prop_ind_absurd]). *)
Lemma alg_elim_complete : forall Γ p D oq m Mm bm Bks Ps M r i,
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Ps = im_np D Mm ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Γ ⊢ P : T) ->
    Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊢a M ⟸ ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks r i ->
    (forall j U T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Γ ⊢a U ⟸ T) ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       exists UA rZ u, tele_sub (im_nparams Mj) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ++ Γ ⊢a Z ⟹ UA /\ is_sort_nf UA rZ u) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       elim_mctx p D j Mj (List.firstn (ind_nu D) Ps) ++ Γ ⊢a eb_motive b ⟸ relevance_sort r Typeω@i) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       elim_bctx r p D Mj gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ
         ⊢a B ⟸ elim_branch_type p D j Mj c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊢a a_elim r oq (List.firstn (ind_nu D) Ps) m Bks M
       ⟸ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hg Hm Hb HPl HPt HMe HMc HBt HUc HZc HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgw; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  set (Us := List.firstn (ind_nu D) Ps) in *; set (NsP := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNPl : List.length NsP = im_nn Mm) by (unfold NsP; rewrite List.length_skipn; unfold im_np in HPl; lia).
  destruct (params_typed_split _ _ D Hc _ _ _ Ps Hm HPl HPt) as [HUt HNPt]; fold Us NsP in HUt, HNPt.
  destruct (im_ref p m Mm) as [pc k] eqn:Hr.
  destruct (im_ref_lookup _ _ _ _ _ _ _ HΓ Hl Hm Hr) as [Dq Hlq].
  destruct (im_ref_member _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq) as [Mk Hk].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsuf.
  pose proof (block_member_not_rview _ _ _ _ _ Hsuf (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) Hm Hb) as Hnr.
  assert (Emty : forall Us' Ns', ind_mty p D m Us' Ns' = apps (a_ind pc k) (im_pre Mm Us' ++ Ns'))
    by (intros; unfold ind_mty; rewrite Hm; unfold im_ty_at;
        destruct (im_head Mm) eqn:Hh0; [ rewrite Hr; reflexivity | rewrite Hr; reflexivity |];
        exfalso; unfold im_is_rview in Hnr; rewrite Hh0 in Hnr; discriminate).
  destruct (im_pre_params_typed _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq Hk HUl HUt HNPl HNPt) as [HXl HXt].
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq HUl HUt) as [HPrl HPrt].
  (** The scrutinee infers the type former at parameters equal to the
      derivation's. *)
  inversion HMc as [? W ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓ) as HMW.
  destruct (presup_exp_typ HMW) as [SW HSW HWt].
  destruct (presup_exp_typ HMe) as [SP HSP HPs].
  assert (HWs : Γ ⊢ (W : exp) ⊆ ind_mty p D m Us NsP) by exact (alg_subtyping_sound_sort _ _ _ _ _ HSW HSP HMs HWt HPs).
  rewrite Emty in HWs.
  pose proof (alg_type_infer_self HΓ HMi) as HWW.
  destruct (subtyp_ind_nf HWs Hlq Hk HXl HXt HWW) as (Rs & -> & HRl & HXR).
  assert (Hti : tele_insts (im_params Dq Mk) Id (im_pre Mm Us ++ NsP)
               = tele_insts (ind_uparams Dq) Id (im_pre Mm Us) ++ tele_insts (im_nparams Mk) (sb_of_list Id (im_pre Mm Us)) NsP)
    by (unfold im_params; apply tele_insts_app; [ exact (decl_closed_ass _ Hcq) | exact HPrl ]).
  assert (Hl1 : List.length (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) = ind_nu Dq)
    by (rewrite length_tele_insts by exact (decl_closed_ass _ Hcq); rewrite HPrl; unfold ind_nu in *; lia).
  assert (HPR : forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N ≈ R : T).
  { intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPrl; apply List.nth_error_Some; congruence).
    apply (HXR j); [ rewrite List.nth_error_app1 by lia; exact HN | exact HR | rewrite Hti, List.nth_error_app1 by lia; exact HT ]. }
  assert (Hag : nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us))).
  { apply nfs_agree_of_nth; [ lia | rewrite List.length_firstn; unfold im_np in HRl; lia |].
    intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPrl; apply List.nth_error_Some; congruence).
    rewrite List.nth_error_firstn in HR; destruct (Nat.ltb_spec j (ind_nu Dq)); [| discriminate ].
    exact (completeness (HPR _ _ _ _ HN HR HT)). }
  (** The rest of the inferred parameters are the member's non-uniform
      ones, equal to the derivation's. *)
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk HWt HRl) as HRt.
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq Hk HUl HUt HRl HRt HPR) as [HNl HNt [iE HE]].
  set (Ns :=List.skipn (ind_nu Dq) (List.map nf_to_exp Rs)) in *.
  destruct (subtyp_ind_inv HWs) as (SR & HSR & HeqR0).
  destruct (exp_eq_sort_large HSR HeqR0 (or_introl (presup_exp_eq_left HE))) as [kk HeqR]; clear SR HSR HeqR0.
  rewrite <- Emty in HeqR.
  assert (HmE : Γ ⊢ ind_mty p D m Us NsP ≈ ind_mty p D m Us Ns : Typeω@(max kk iE))
    by (etransitivity; [ symmetry; eapply lift_exp_eq_max_left; exact HeqR | eapply lift_exp_eq_max_right; exact HE ]).
  pose proof (mty_params_inj _ _ _ _ _ _ _ _ _ Hl Hm HUl HUt HNPl HNl HNPt HNt HmE) as HNN.
  clear HmE HeqR HE HWs HMs HWW HXR HPR Hti Hl1 HXt HXl HRt HMW HWt HPs.
  pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUt HNt) as HPt'.
  assert (HPl' : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
  assert (HPP : forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error (Us ++ Ns) j = Some P' ->
             List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Γ ⊢ P ≈ P' : T).
  { intros j P P' T HP HP' HT.
    assert (EPs : Ps = Us ++ NsP) by (unfold Us, NsP; symmetry; apply List.firstn_skipn).
    rewrite EPs in HP, HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (decl_closed_ass _ Hc); exact HUl).
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
      by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); rewrite HUl; unfold ind_nu in *; lia).
    destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HP, HP', HT by lia; rewrite HP in HP'; injection HP' as <-.
      apply wf_exp_eq_refl; exact (HUt _ _ _ HP HT).
    - rewrite List.nth_error_app2 in HP, HP', HT by lia; rewrite HUl in HP, HP'; rewrite Hl1 in HT.
      exact (HNN _ _ _ _ HP HP' HT). }
  (** So the motive's instance is the derivation's. *)
  destruct (wf_elim_params_conv _ _ _ _ _ _ _ _ _ _ r i Hl Hm Hb HPl HPt HPl' HPt' HPP HMe HBt) as (_ & _ & Hmot).
  rewrite skipn_app_len in Hmot by exact HUl; fold NsP in Hmot.
  clear HPP HPt' HNN.
  (** One universe for the annotations and the motives. *)
  assert (HΨ : forall j Mj, ind_member D j = Some Mj -> ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list).
  { intros j Mj Hj; pose proof (ext_eq_ctx_left _ _ _ _ _ (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt _ _ Hj)) as HC.
    unfold elim_mctx in HC; cbn [List.app] in HC; exact (proj1 (ctx_decomp HC)). }
  assert (Hmono : forall Δ A l l', ⊢ Δ -> l <= l' -> Δ ⊢a A ⟸ Typeω@l -> Δ ⊢a A ⟸ Typeω@l').
  { intros Δ A l l' HΔ Hll HA; destruct (Nat.eq_dec l l') as [<- | Hne]; [ exact HA |].
    eapply alg_type_check_subtyp; [ exact HA | apply wf_subtyp_univ; [ exact HΔ | lia ] ]. }
  destruct (nat_bound_upto (fun j l => forall Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
              eb_ann b = Some Z -> (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢a Z ⟸ Typeω@l)
              (List.length Bks)) as [L HL].
  { intros j _.
    destruct (ind_member D j) as [Mj |] eqn:Hj; [| exists 0; intros; discriminate ].
    destruct (List.nth_error Bks j) as [b |] eqn:Hbj; [| exists 0; intros; discriminate ].
    destruct (eb_ann b) as [Z |] eqn:HZ; [| exists 0; intros; congruence ].
    destruct (HZc _ _ _ _ Hj Hbj HZ) as (UA & rZ & u & HZi & Hs).
    destruct Hs as [? u Hu |].
    2:{ (** A propositional annotation is below the member's type, an
            inductive type: absurd. *)
        exfalso.
        pose proof (alg_type_infer_sound HZi (HΨ _ _ Hj)) as HZp; cbn [nf_to_exp] in HZp.
        destruct (ext_eq_ass_inv _ _ _ _ _ _ _ (blocks_typed_ann _ _ _ _ _ _ _ _ _ HBt _ _ _ _ Hj Hbj HZ))
          as [_ _ _ _ _ _ _ HZH _].
        pose proof (block_member_not_rview _ _ _ _ _ Hsuf (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) Hj Hbj) as Hnrj.
        unfold ind_mty in HZH; rewrite Hj in HZH; unfold im_ty_at in HZH.
        destruct (im_head Mj) eqn:Hh0;
          [ exact (subtyp_prop_ind_absurd HZH HZp) | exact (subtyp_prop_ind_absurd HZH HZp) |].
        unfold im_is_rview in Hnrj; rewrite Hh0 in Hnrj; discriminate. }
    exists (universe_nf_large_index u); intros Mj' b' Z' Hj' Hb' HZ'.
    assert (Mj' = Mj) as -> by congruence; assert (b' = b) as -> by congruence; assert (Z' = Z) as -> by congruence.
    eapply alg_type_check_typ_of; [ exact (HΨ _ _ Hj) | exact HZi | exact Hu | apply universe_nf_le_large ]. }
  { intros j l l' Hll HQ Mj b Z Hj Hbj HZ; eapply Hmono; [ exact (HΨ _ _ Hj) | exact Hll | exact (HQ _ _ _ Hj Hbj HZ) ]. }
  set (i' := max i L).
  (** The type, the normal form of the motive's instance. *)
  pose proof (type_sort_relevance_universe r i) as HSr.
  assert (HTt : Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : relevance_sort r Typeω@i) by (gen_presups; assumption).
  destruct (nbe_ty_exists_sort HSr HTt) as (T & HnT).
  pose proof (soundness_ty_at_sort HSr HTt HnT) as HTe.
  econstructor.
  - eapply alg_type_infer_elim with (p := p) (D := D) (Mm := Mm) (Dq := Dq) (Mk := Mk) (bm := bm) (i := i'); try eassumption; try reflexivity.
    + exact (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt).
    + exact (blocks_typed_binder_count _ _ _ _ _ _ _ _ _ HBt).
    + intros j Mj b Z Hj Hbj HZ.
      assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence).
      eapply (Hmono _ _ L); [ exact (HΨ _ _ Hj) | unfold i'; lia | exact (HL j Hjl _ _ _ Hj Hbj HZ) ].
    + intros j Mj b Z Hj Hbj HZ.
      destruct (ext_eq_ass_inv _ _ _ _ _ _ _ (blocks_typed_ann _ _ _ _ _ _ _ _ _ HBt _ _ _ _ Hj Hbj HZ))
        as [_ _ _ _ _ _ _ HZH HHZ].
      exact (nbe_ty_of_mutual_subtyp HZH HHZ).
    + intros j Mj b Hj Hbj; destruct r; cbn [relevance_sort] in *; [| exact (HAc _ _ _ Hj Hbj) ].
      eapply (Hmono _ _ i);
        [ exact (ext_eq_ctx_left _ _ _ _ _ (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt _ _ Hj)) | unfold i'; lia | exact (HAc _ _ _ Hj Hbj) ].
    + exact (blocks_typed_names _ _ _ _ _ _ _ _ _ HBt).
    + exact (blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt).
  - apply alg_subtyping_complete.
    assert (HE : Γ ⊢ T ≈ (eb_motive bm)[sb_of_list Id (NsP ++ M :: nil)] : relevance_sort r Typeω@i)
      by (etransitivity; [ symmetry; exact HTe | symmetry; exact Hmot ]).
    exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) HSr HE)).
Qed.

(** ** Extensions Entry by Entry

    Completeness for an extension is stated for each of its entries, under
    the bound on that entry's lets: a body's expansion has entries its local
    opens generate, whose types are the targets' member types, which the
    body's own lets do not bound; the algorithm does not check them again. *)

Definition alg_entry (Γ : ctx) (e : centry) : Prop :=
  match e with
  | ce_ass A => exists UA r u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA r u
  | ce_def A M => (exists UA r u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA r u) /\ Γ ⊢a M ⟸ A
  | ce_mod U => Γ ⊢aᵘ U
  | ce_dm A M U => ((exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ Γ ⊢a M ⟸ A) /\ Γ ⊢aᵘ U
  end.

Definition ext_entries (n : nat) (Γ Ψ : ctx) : Prop :=
  forall Ψ2 e Ψ1, Ψ = Ψ2 ++ e :: Ψ1 -> centry_lets e <= n -> alg_entry (Ψ1 ++ Γ) e.

Lemma ext_entries_nil : forall n Γ, ext_entries n Γ nil.
Proof. intros n Γ [| ? ?] * H; discriminate. Qed.

Lemma ext_entries_cons : forall n Γ Ψ e, ext_entries n Γ Ψ ->
    (centry_lets e <= n -> alg_entry (Ψ ++ Γ) e) -> ext_entries n Γ (e :: Ψ).
Proof.
  intros * Ht He [| e2 Ψ2] e' Ψ1 Heq Hle; cbn in Heq; injection Heq as -> Heq; [ subst; exact (He Hle) |].
  exact (Ht _ _ _ Heq Hle).
Qed.

Lemma ext_entries_app_r : forall n Γ Ψ2 Ψ, ext_entries n Γ (Ψ2 ++ Ψ) -> ext_entries n Γ Ψ.
Proof. intros * Hx Ψ3 e Ψ1 -> Hle; apply (Hx (Ψ2 ++ Ψ3)); [ rewrite <- List.app_assoc; reflexivity | exact Hle ]. Qed.

Lemma ext_entries_head : forall n Γ Ψ e, ext_entries n Γ (e :: Ψ) -> centry_lets e <= n -> alg_entry (Ψ ++ Γ) e.
Proof. intros * Hx Hle; exact (Hx nil e Ψ eq_refl Hle). Qed.

Lemma ext_entries_alg : forall n Γ Ψ, ext_entries n Γ Ψ -> ctx_lets Ψ <= n -> Γ ⊢aˣ Ψ.
Proof.
  intros n Γ; induction Ψ as [| e Ψ IH]; intros Hx Hl; [ constructor |]; cbn [ctx_lets] in Hl.
  pose proof (ext_entries_head _ _ _ _ Hx ltac:(lia)) as He.
  pose proof (IH (ext_entries_app_r _ _ (e :: nil) _ Hx) ltac:(lia)) as Ht.
  destruct e; cbn [alg_entry] in He; destruct_all;
    [ eapply alg_ext_ass | eapply alg_ext_def | eapply alg_ext_mod | eapply alg_ext_dm ]; eauto.
Qed.

(** [body_tagged Γ Φ]: the type of every term part of the body [Φ] over
    [Γ] is, in the context of the entries before it, of the sort its
    relevance tag says ([entry_relevance]). *)
Definition body_tagged (Γ : ctx) (Φ : gmod) : Prop :=
  forall y Φ0 E A M, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    exists i, (body_ctx Φ0 ++ Γ)%list ⊢ A : relevance_sort (entry_relevance E) Typeω@i.

(** A name a body finds is one of its names. *)
Lemma gm_prefix_upto_in : forall Φ y Φ', gm_prefix_upto Φ y = Some Φ' -> List.In y (gm_names Φ).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros y Φ' Hp; cbn in Hp |- *; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> | _]; [ left; reflexivity | right; exact (IH _ _ Hp) ].
  - destruct (List.existsb _ _); [ discriminate | apply List.in_or_app; right; exact (IH _ _ Hp) ].
Qed.

(** Entries generated under names other than [y] do not hide what [y]
    names. *)
Lemma gm_prefix_upto_gens : forall gs Φ k y, ~ List.In y (List.map generated_item_name gs) ->
    gm_prefix_upto (gens_append Φ k gs) y = gm_prefix_upto Φ y.
Proof.
  induction gs as [| g gs IH]; intros Φ k y Hy; cbn [gens_append]; [ reflexivity |].
  cbn [List.map List.In] in Hy.
  unfold generated_item_name in Hy; destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [fst] in Hy.
  rewrite IH by tauto; cbn [gm_prefix_upto].
  destruct (String.eqb_spec y d) as [-> | _]; [ tauto | reflexivity ].
Qed.

(** The tags of a body hold of its prefix before an entry of a fresh name. *)
Lemma body_tagged_ext_inv : forall Γ Φ x E, body_tagged Γ (gm_ext Φ x E) -> ~ List.In x (gm_names Φ) -> body_tagged Γ Φ.
Proof.
  intros * HT Hx y Φ0 E0 A M Hp HE; apply (HT y Φ0 E0 A M); [| exact HE ]; cbn [gm_prefix_upto].
  destruct (String.eqb_spec y x) as [-> | _]; [ exfalso; exact (Hx (gm_prefix_upto_in _ _ _ Hp)) | exact Hp ].
Qed.

(** The two parts of a list without repetition are disjoint. *)
Lemma nodup_app_disjoint : forall {X : Type} (l l' : list X) a, List.NoDup (l ++ l') -> List.In a l -> ~ List.In a l'.
Proof.
  induction l as [| x l IH]; intros l' a Hnd Hin Hin'; [ exact Hin |].
  cbn [List.app] in Hnd; apply List.NoDup_cons_iff in Hnd as [Hx Hnd].
  destruct Hin as [-> | Hin]; [ apply Hx, List.in_or_app; right; exact Hin' | exact (IH _ _ Hnd Hin Hin') ].
Qed.

(** The same before the entries an open generates, under fresh names. *)
Lemma body_tagged_gens_inv : forall Γ Φ gs, body_tagged Γ (gens_append Φ 0 gs) ->
    List.NoDup (gm_names (gens_append Φ 0 gs)) -> body_tagged Γ Φ.
Proof.
  intros * HT Hnd y Φ0 E A M Hp HE; apply (HT y Φ0 E A M); [| exact HE ].
  rewrite gm_prefix_upto_gens; [ exact Hp |].
  rewrite gens_append_names in Hnd.
  intros Hin; apply List.in_rev in Hin.
  exact (nodup_app_disjoint _ _ y Hnd Hin (gm_prefix_upto_in _ _ _ Hp)).
Qed.

(** A type of the sorts at two tags has one tag. *)
Lemma relevance_sort_agree : forall Γ A r r' i j,
    Γ ⊢ A : relevance_sort r Typeω@i -> Γ ⊢ A : relevance_sort r' Typeω@j -> r = r'.
Proof.
  intros * H H'; destruct r, r'; cbn [relevance_sort] in *; [ reflexivity | | | reflexivity ];
    exfalso; eapply typ_prop_absurd; eassumption.
Qed.

(** The entries of an expanded body are of their tagged sorts in the
    context the body before each makes, once each, filled in, is of the
    sort the tag names: the type is of a sort before it, which filling in
    keeps, and no type is of both sorts ([typ_prop_absurd]). *)
Lemma body_tagged_of_fill : forall Γ0 Φx (entry_sort : String.string -> exp),
    gm_nopens Φx = 0 -> body_shape Φx Φx -> ⊢ body_ctx Φx ++ Γ0 ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       exists i, entry_sort y = relevance_sort (entry_relevance E) Typeω@i) ->
    (forall y Φ0 E A M σ, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σ -> Γ0 ⊢ A[σ] : entry_sort y) ->
    body_tagged Γ0 Φx.
Proof.
  intros * Hn Hs HC Htag Hfill y Φ0 E A M Hp HE.
  destruct (Htag _ _ _ _ _ Hp HE) as [i Hi].
  destruct (fill_prefix _ _ _ _ (proj1 (body_shape_fill _ _ Hn Hs)) Hp) as [σ Hσf].
  pose proof (Hfill _ _ _ _ _ _ Hp HE Hσf) as HAσ; rewrite Hi in HAσ.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [X HX].
  rewrite HX, <- List.app_assoc in HC.
  pose proof (ctx_app_wf_tail _ _ _ _ HC) as HC0.
  (** The entry's type is of a sort, in the context before it. *)
  assert (HAS : ⊢ body_ctx Φ0 ++ Γ0 /\ exists Srt, type_sort Srt /\ body_ctx Φ0 ++ Γ0 ⊢ A : Srt).
  { destruct E as [b pv r A' [M' |] | | | pv A' M' U |]; cbn in HE; try discriminate; injection HE as <- <-;
      cbn [body_ctx List.app] in HC0.
    - destruct (ctx_decomp_def HC0) as (HΓ & [Srt HS HA'] & _); split; [ exact HΓ | eauto ].
    - destruct (ctx_decomp_dm HC0) as (HΓ & [k HA'] & _ & _); split; [ exact HΓ |].
      exists Typeω@k; split; [ constructor | exact HA' ]. }
  destruct HAS as (HΓ0 & Srt & HS & HA0).
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA0 HS (wf_gm_fill _ _ _ _ _ HΓ0 Hσf)) as HAσ'.
  destruct HS as [j |], (entry_relevance E); cbn [relevance_sort] in HAσ |- *;
    [ exists j; exact HA0 | | | exists 0; exact HA0 ];
    exfalso; eapply typ_prop_absurd; eassumption.
Qed.

(** The same, read off the premises of a unit rule, which fill in an entry
    together with the entry of the same name on the other side. *)
Lemma body_tagged_of_fill_left : forall Γ0 Φx Φx' (entry_sort : String.string -> exp),
    gm_nopens Φx = 0 -> body_shape Φx Φx' -> ⊢ body_ctx Φx ++ Γ0 ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       exists i, entry_sort y = relevance_sort (entry_relevance E) Typeω@i) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Γ0 ⊢ A[σ] : entry_sort y) ->
    body_tagged Γ0 Φx.
Proof.
  intros * Hn Hs HC Htag Hfill.
  destruct (body_shape_refl _ _ Hs) as (Hs1 & _ & _).
  apply (body_tagged_of_fill _ _ entry_sort Hn Hs1 HC Htag).
  intros y Φ0 E A M σ Hp HE Hσ.
  destruct (shape_prefix _ _ _ _ _ Hs Hp) as (Φ0' & E' & Hp' & Hs0 & HsE).
  destruct (entry_shape_tm _ _ _ _ HsE HE) as (A' & M' & HE').
  destruct (gm_fill Φ0') as [σ' |] eqn:Hσ'; [ exact (Hfill _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσ Hσ') |].
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn0; cbn [gm_nopens] in Hn0.
  exfalso; exact (proj2 (body_shape_fill _ _ Hn0 Hs0) Hσ').
Qed.

(** The other side's. *)
Lemma body_tagged_of_fill_right : forall Γ0 Φx Φx' (entry_sort : String.string -> exp),
    gm_nopens Φx' = 0 -> body_shape Φx Φx' -> ⊢ body_ctx Φx' ++ Γ0 ->
    (forall y Φ0' E' A' M', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       exists i, entry_sort y = relevance_sort (entry_relevance E') Typeω@i) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Γ0 ⊢ A'[σ'] : entry_sort y) ->
    body_tagged Γ0 Φx'.
Proof.
  intros * Hn' Hs HC Htag Hfill.
  destruct (body_shape_refl _ _ Hs) as (_ & Hs2 & _).
  apply (body_tagged_of_fill _ _ entry_sort Hn' Hs2 HC Htag).
  intros y Φ0' E' A' M' σ' Hp' HE' Hσ'.
  destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hs) Hp') as (Φ0 & E & Hp & Hs0 & HsE).
  destruct (entry_shape_tm _ _ _ _ HsE HE') as (A & M & HE).
  destruct (gm_fill Φ0) as [σ |] eqn:Hσ; [ exact (Hfill _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσ Hσ') |].
  pose proof (prefix_nopens _ _ _ Hn' Hp') as Hn0; cbn [gm_nopens] in Hn0.
  exfalso; exact (proj2 (body_shape_fill _ _ Hn0 Hs0) Hσ).
Qed.

(** A body checked from its expansion's entries: its own entries are
    bounded by its lets; those its opens generate are not looked at.  A
    definition is checked at the sort its tag says, which the entry's
    type has ([body_tagged]); the names are distinct, so each entry is
    the one its name finds. *)
Lemma alg_body_of_entries : forall n Γ0 Δ Φ Φx, body_xp gc_deps gc_stack (Δ ++ Γ0) Φ Φx ->
    ext_entries n Γ0 (body_ctx Φx ++ Δ) -> gmod_lets Φ <= n -> body_shape Φ Φ ->
    List.NoDup (gm_names Φx) -> body_tagged (Δ ++ Γ0) Φx ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> S (modexp_lets H) <= n -> Ψ ++ Δ ++ Γ0 ⊢aᵐ H) ->
    Δ ++ Γ0 ⊢aᵇ Φ ⇝ Φx.
Proof.
  intros * Hx; remember (Δ ++ Γ0) as G eqn:HG; revert HG.
  induction Hx as [G | G Φ Φx x E Hx IH | G Φ Φx H its R Rm gs Hx IH HR HRm Hg Hok];
    intros -> HE Hl Hs Hnd Htg Ho; cbn [gmod_lets] in Hl.
  - constructor.
  - cbn [body_shape] in Hs; destruct Hs as (Hs & _ & HsE).
    cbn [gm_names] in Hnd; apply List.NoDup_cons_iff in Hnd as [Hx' Hnd].
    assert (HEt : ext_entries n Γ0 (body_ctx Φx ++ Δ)).
    { destruct E as [? ? ? ? [] | | | | ]; cbn [body_ctx List.app] in HE; exact (ext_entries_app_r _ _ (_ :: nil) _ HE). }
    specialize (IH eq_refl HEt ltac:(lia) Hs Hnd (body_tagged_ext_inv _ _ _ _ Htg Hx') Ho).
    destruct E as [b pv r A [M |] | pm U | ? ? ? ? ? | pv A M U | ? ? ? ?]; cbn in HsE; try contradiction.
    + pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; destruct (He ltac:(lia)) as ((UA & r' & u & HA & Hu) & HM).
      (** The tag is the relevance of the type's sort. *)
      destruct (Htg x Φx _ A M ltac:(cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity) eq_refl) as [i HAt].
      cbn [entry_relevance] in HAt.
      pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HA (presup_exp_ctx HAt)) Hu) as HAs.
      pose proof (relevance_sort_agree _ _ _ _ _ _ HAs HAt) as ->.
      econstructor; eassumption.
    + pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; specialize (He ltac:(lia)).
      econstructor; eassumption.
    + (* a definition with a module part: both parts *)
      pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; destruct (He ltac:(lia)) as (((UA & u & HA & Hu) & HM) & HU).
      econstructor; eassumption.
  - cbn [body_shape] in Hs; destruct Hs as [Hs _].
    cbn [body_opens] in Ho; rewrite <- (items_gen_length _ _ _ _ _ _ Hg), gm_dropn_gens_append in Ho.
    pose proof (body_tagged_gens_inv _ _ _ Htg Hnd) as Htg'.
    assert (Hnd' : List.NoDup (gm_names Φx))
      by (rewrite gens_append_names in Hnd; exact (List.NoDup_app_remove_l _ _ Hnd)).
    rewrite gens_body_ctx_base, <- List.app_assoc in HE.
    specialize (IH eq_refl (ext_entries_app_r _ _ _ _ HE) ltac:(lia) Hs Hnd' Htg' (fun k => Ho (S k))).
    pose proof (Ho 0 _ _ eq_refl ltac:(lia)) as HH.
    econstructor; eassumption.
Qed.

(** A well-formed module expression checks, given that its arguments and
    its literals do: they are reached by generation ([modexp_gen]), whatever
    reducts its derivation goes through. *)
Lemma alg_modexp_of_wf : forall n,
    (forall Γ A M, gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : A -> exp_lets M <= n -> Γ ⊢a M ⟸ A) ->
    (forall Γ U, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> gunit_lets U <= n -> Γ ⊢aᵘ U) ->
    forall H Γ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> modexp_lets H <= n -> Γ ⊢aᵐ H.
Proof.
  intros n HM HU; induction H as [fp | x | H IH y | H IH N | U]; intros Γ HH Hl;
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as Hgen; cbn [gen_m modexp_lets] in Hgen, Hl.
  - destruct (me_mtele _ _ _ HH) as (R & T & Hm & Ht); econstructor; eassumption.
  - destruct (me_denotes _ _ _ _ _ HH) as (R & _ & Hm & _).
    inversion Hm; subst; try (unfold gc_unit in *; cbn in *; discriminate).
    econstructor; eassumption.
  - destruct (me_mtele _ _ _ HH) as (R & T & Hm & Ht).
    eapply alg_modexp_mem; [ apply IH; [ exact Hgen | lia ] | exact Hm | exact Ht ].
  - destruct Hgen as (HH0 & R & T & B & T1 & i & Hm & Ht & Hv & HB & HN).
    eapply alg_modexp_app; [ apply IH; [ exact HH0 | lia ] | exact Hm | exact Ht | exact Hv | apply HM; [ exact HN | lia ] ].
  - apply alg_modexp_lit, HU; [ exact (unit_eq_of_full _ _ _ _ Hgen) | exact Hl ].
Qed.

(** An extension of an extension is one extension. *)
Lemma alg_ext_app : forall Γ Δ Ψ, Γ ⊢aˣ Δ -> Δ ++ Γ ⊢aˣ Ψ -> Γ ⊢aˣ Ψ ++ Δ.
Proof.
  intros * HΔ HΨ; remember (Δ ++ Γ) as G eqn:HG; induction HΨ; subst; cbn [List.app];
    [ exact HΔ | .. ]; econstructor; rewrite <- ?List.app_assoc; eauto.
Qed.

(** The same for parameters. *)
Lemma alg_params_app : forall Γ Δ Ψ, Γ ⊢aᵖ Δ -> Δ ++ Γ ⊢aᵖ Ψ -> Γ ⊢aᵖ Ψ ++ Δ.
Proof.
  intros * HΔ HΨ; remember (Δ ++ Γ) as G eqn:HG; induction HΨ; subst; cbn [List.app];
    [ exact HΔ | .. ]; econstructor; rewrite <- ?List.app_assoc; eauto.
Qed.

(** A unit under parameters [Δ] is the unit over its own parameters and
    [Δ], the algorithmic counterpart of [wf_unit_eq_flatten]. *)
Lemma alg_unit_flatten : forall Γ Δ Δ' D,
    Γ ⊢aᵖ Δ -> tele_ass Δ -> Δ ++ Γ ⊢aᵘ gu_mk Δ' D -> Γ ⊢aᵘ gu_mk (Δ' ++ Δ) D.
Proof.
  intros * HΔ Ha HU; inversion HU; subst.
  - eapply alg_unit_body; [ eapply alg_params_app; eassumption | apply List.Forall_app; split; assumption
                       | rewrite <- List.app_assoc; eassumption | assumption .. ].
  - eapply alg_unit_alias; [ eapply alg_params_app; eassumption | apply List.Forall_app; split; assumption
                        | rewrite <- List.app_assoc; eassumption ].
Qed.

(** Relevant parameters, each type checked as an entry, are checked
    parameters: a type of a universe infers a universe, no proposition
    ([relevance_sort_agree]). *)
Lemma alg_params_of_entries : forall n Γ Δ l, ⊢ Γ ->
    ext_entries n Γ Δ -> ctx_lets Δ <= n -> tele_ass Δ -> params_relevant gc_deps gc_stack Γ Δ l -> Γ ⊢aᵖ Δ.
Proof.
  intros n Γ; induction Δ as [| e Δ IH]; intros l HΓ Hx Hl Ha HR; [ constructor |]; cbn [ctx_lets] in Hl.
  apply List.Forall_cons_iff in Ha as [[T ->] Ha].
  cbn [centry_lets] in Hl.
  pose proof (ext_entries_head _ _ _ _ Hx ltac:(cbn [centry_lets]; lia)) as He; cbn [alg_entry] in He.
  destruct He as (UA & r & u & HT & Hs).
  pose proof (HR nil T Δ eq_refl) as HTl.
  pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HT (presup_exp_ctx HTl)) Hs) as HTs.
  pose proof (relevance_sort_agree _ _ relevant _ _ _ HTl HTs) as <-.
  inversion Hs; subst.
  econstructor; [| eassumption | eassumption ].
  apply (IH l HΓ (ext_entries_app_r _ _ (_ :: nil) _ Hx) ltac:(lia) Ha).
  intros Δ1 T' Δ2 E; exact (HR (ce_ass T :: Δ1) T' Δ2 ltac:(rewrite E; reflexivity)).
Qed.

(** ** Records, Algorithmically *)

(** A field of a tuple has at most the tuple's unannotated [let]s. *)
Lemma tuple_field_lets : forall T (fs : list (String.string * exp)) k f M,
    List.nth_error fs k = Some (f, M) -> exp_lets M <= exp_lets (a_tuple T fs).
Proof.
  intros T fs; cbn [exp_lets].
  enough (H : forall k f M, List.nth_error fs k = Some (f, M) ->
                exp_lets M <= (fix fields_lets (fs : list (String.string * exp)) : nat :=
                                 match fs with
                                 | nil => 0
                                 | f :: fs' => exp_lets (snd f) + fields_lets fs'
                                 end) fs) by (intros; pose proof (H _ _ _ ltac:(eassumption)); lia).
  induction fs as [| [g N] fs IH]; intros [| k] f M Hk; cbn in Hk |- *; try discriminate.
  - injection Hk as <- <-; lia.
  - pose proof (IH _ _ _ Hk); lia.
Qed.

(** A record's type former checks at its type. *)
Lemma alg_record_complete : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢a a_record p ⟸ record_ty R.
Proof.
  intros * HΓ Hl.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [_ Hj]].
  destruct (soundness_ty Hj) as [W [HW HWe]].
  econstructor; [ eapply alg_type_infer_record; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
Qed.

(** A tuple checks at its annotation: the annotation normalises to the
    record type at the normal forms [Rs] of its parameters
    ([subtyp_record_nf]), and each field's type at them is its type at the
    parameters, where the field checks. *)
Lemma alg_tuple_complete : forall Γ T (fs : list (String.string * exp)) p R Ns i,
    Γ ⊢ T : Typeω@i -> Γ ⊢a T ⟸ Typeω@i ->
    Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A -> Γ ⊢ N : A) ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Γ ⊢a M ⟸ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    Γ ⊢a a_tuple T fs ⟸ T.
Proof.
  intros * HTt HTc HTeq Hrt Hl Hn HNs Hfs HMt HMc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ HTc) as (UT & u & HTi & Hu & _).
  destruct (soundness_ty HTt) as [W [HW HWe]].
  destruct (subtyp_record_nf (wf_subtyp_refl' _ _ _ _ _ _ HTeq) Hl Hn HNs HW) as (Rs & -> & HRl & HNR).
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  econstructor; [| apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  eapply alg_type_infer_tuple; [ exact HTi | exact Hu | exact HW | exact Hl | exact Hfs |].
  intros k f M U Hk Hfk.
  assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
  pose proof (record_fields_insts_eq _ _ _ p R Ns (List.map nf_to_exp Rs) fs fs Hrt Hl Hn HRl HNR Hfs eq_refl
                ltac:(intros * HM HM' HU; rewrite HM in HM'; injection HM' as <-; apply wf_exp_eq_refl; eapply HMt; eassumption)
                k ltac:(lia)) as Hins.
  destruct (record_field_typ_cong _ _ _ R k f U (Ns ++ List.firstn k (List.map snd fs))
              (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs)) Hc Hass HF HΓ Hfk
              ltac:(rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia)
              ltac:(rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia) Hins) as (SU & HSU & HUU).
  eapply alg_type_check_subtyp; [ exact (HMc _ _ _ _ Hk Hfk) |].
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HUU) (presup_exp_eq_right HUU) HSU HUU)).
Qed.

(** A projection checks at its field's type at the parameters of the
    element's type: the element infers the record type at the normal forms
    of its parameters ([subtyp_record_nf]), at which the field's type is
    equal to that one. *)
Lemma alg_proj_complete : forall Γ M p R Ns k f U,
    Γ ⊢ M : apps_exp (a_record p) Ns -> Γ ⊢a M ⟸ apps_exp (a_record p) Ns ->
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A -> Γ ⊢ N : A) ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    Γ ⊢a a_proj f M ⟸ U[sb_of_list Id (Ns ++ record_pre R k M)].
Proof.
  intros * HMt HMc Hrt Hl Hn HNs Hfk.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  inversion HMc as [? W ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓ) as HMW.
  destruct (presup_exp_typ HMW) as [SW HSW HWt].
  destruct (presup_exp_typ HMt) as [SP HSP HPs].
  assert (HWs : Γ ⊢ (W : exp) ⊆ apps_exp (a_record p) Ns) by exact (alg_subtyping_sound_sort _ _ _ _ _ HSW HSP HMs HWt HPs).
  pose proof (alg_type_infer_self HΓ HMi) as HWW.
  destruct (subtyp_record_nf HWs Hl Hn HNs HWW) as (Rs & -> & HRl & HNR).
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ HMW Hl Hfk) as (m & HUR & _).
  pose proof (type_sort_relevance_universe (record_field_rel R k) m) as HSm.
  destruct (nbe_ty_exists_sort HSm HUR) as [V HV].
  pose proof (soundness_ty_at_sort HSm HUR HV) as HVe.
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl Hn HNs) as [n Hm].
  pose proof (record_field_params_cong _ _ _ M p R Ns (List.map nf_to_exp Rs) n k f U HMt Hrt Hl Hn HRl HNs HNR Hm Hfk) as HUU.
  econstructor; [ eapply alg_type_infer_proj; [ exact HMi | exact Hl | exact (field_index_nth_nodup _ _ _ _ Hnd Hfk) | exact Hfk | exact HV ] |].
  apply alg_subtyping_complete.
  destruct (exp_eq_trans_sort HSm (type_sort_relevance_universe _ n) ltac:(symmetry; exact HVe) ltac:(symmetry; exact HUU))
    as (S0 & HS0 & HE).
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) HS0 HE)).
Qed.

(** ** Completeness of the Rules of Either Sort *)

(** Two types equal at a sort have the same normal forms. *)
Lemma nbe_ty_of_exp_eq_sort : forall {Γ A B S W},
    type_sort S -> Γ ⊢ A ≈ B : S -> nbe_ty_f Γ A W -> nbe_ty_f Γ B W.
Proof.
  intros * HS HE HW.
  destruct (completeness_ty_sort HS HE) as (W' & HW1 & HW2).
  pose proof (functional_nbe_ty _ _ _ _ HW HW1) as <-; exact HW2.
Qed.

(** A term checked against a type checks against a type equal to it at a
    sort. *)
Lemma alg_type_check_conv_sort : forall {Γ A A' M S},
    Γ ⊢a M ⟸ A -> type_sort S -> Γ ⊢ A ≈ A' : S -> Γ ⊢a M ⟸ A'.
Proof.
  intros * Hc HS HE; eapply alg_type_check_subtyp; [ exact Hc |].
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) HS HE)).
Qed.

(** A term that infers [Prop] checks against it. *)
Lemma alg_type_check_prop_of : forall {Γ A}, ⊢ Γ -> Γ ⊢a A ⟹ Propⁿ -> Γ ⊢a A ⟸ Propₘ.
Proof.
  intros * HΓ Hi.
  apply (alg_type_check_of_infer_nbe (type_sort_universe 0) (wf_prop_large (i := 0) HΓ)); intros W HW.
  replace W with Propⁿ; [ exact Hi |].
  inversion HW; subst; directed_inversion_by_head eval_exp; subst; directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** [⋆] checks against [⊤]. *)
Lemma alg_true_complete : forall Γ, ⊢ Γ -> Γ ⊢a ⋆ ⟸ ⊤.
Proof.
  intros * HΓ.
  apply (alg_type_check_of_infer_nbe type_sort_prop (wf_True _ _ _ HΓ)); intros W HW.
  replace W with ⊤ⁿ; [ constructor |].
  inversion HW; subst; directed_inversion_by_head eval_exp; subst; directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** The introduction of [⊤] checks against [⊤]. *)
Lemma alg_tt_complete : forall Γ, ⊢ Γ -> Γ ⊢a a_tt ⟸ ⊤.
Proof.
  intros * HΓ.
  apply (alg_type_check_of_infer_nbe type_sort_prop (wf_True _ _ _ HΓ)); intros W HW.
  replace W with ⊤ⁿ; [ constructor |].
  inversion HW; subst; directed_inversion_by_head eval_exp; subst; directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** The placeholder checks against its type. *)
Lemma alg_placeholder_complete : forall Γ, ⊢ Γ -> Γ ⊢a a_placeholder ⟸ a_placeholder_type.
Proof.
  intros * HΓ.
  apply (alg_type_check_of_infer_nbe (type_sort_universe 0) (wf_placeholder_type_large HΓ)); intros W HW.
  replace W with nf_placeholder_type; [ constructor |].
  inversion HW; subst; directed_inversion_by_head eval_exp; subst; directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** Ex falso checks against its target, of either sort. *)
Lemma alg_absurd_complete : forall {Γ C M S},
    ⊢ Γ -> type_sort S -> Γ ⊢ C : S -> Γ ⊢a C ⟸ S -> Γ ⊢a M ⟸ ⊥ -> Γ ⊢a efq M return C ⟸ C.
Proof.
  intros * HΓ HS HC HCc HMc.
  destruct (alg_type_check_sort_infer HΓ HS HCc) as (UC & r & u & HCi & Hs).
  apply (alg_type_check_of_infer_nbe HS HC); intros W HW.
  eapply alg_type_infer_absurd; eassumption.
Qed.

(** A proof checked against a conjunction infers its normal form: subtyping
    at a proposition is equality. *)
Lemma alg_type_check_and_infer : forall {Γ M P Q},
    ⊢ Γ -> Γ ⊢a M ⟸ Σₚ P Q ->
    exists WP WQ, Γ ⊢a M ⟹ Σₚⁿ WP WQ /\ nbe_ty_f Γ P WP /\ nbe_ty_f (Γ ▹ P) Q WQ.
Proof.
  intros * HΓ Hc.
  inversion Hc as [? W ? ? Hi [W1 W2 Hn1 Hn2 Hsub]]; subst.
  pose proof (alg_type_infer_normal HΓ Hi Hn1) as <-.
  destruct (nbe_ty_and_inv _ _ _ _ Hn2) as (WP & WQ & -> & HWP & HWQ).
  rewrite (alg_subtyping_nf_not_univ_pi_eq _ _ Hsub ltac:(right; exact I)) in Hi.
  exists WP, WQ; split; [ exact Hi | split; assumption ].
Qed.

(** The first component of a proof of a conjunction. *)
Lemma alg_left_complete : forall {Γ M P Q},
    ⊢ Γ -> Γ ⊢ P : Propₘ -> Γ ⊢a M ⟸ Σₚ P Q -> Γ ⊢a a_left M ⟸ P.
Proof.
  intros * HΓ HP Hc.
  destruct (alg_type_check_and_infer HΓ Hc) as (WP & WQ & Hi & HWP & _).
  apply (alg_type_check_of_infer_nbe type_sort_prop HP); intros W HW.
  pose proof (functional_nbe_ty _ _ _ _ HW HWP) as ->.
  econstructor; exact Hi.
Qed.

(** The second, at the first: the second part's normal form at the first
    component is a normal form of the type. *)
Lemma alg_right_complete : forall {Γ M P Q},
    ⊢ Γ -> Γ ⊢ P : Propₘ -> Γ ▹ P ⊢ Q : Propₘ -> Γ ⊢ M : Σₚ P Q -> Γ ⊢a M ⟸ Σₚ P Q ->
    Γ ⊢a a_right M ⟸ Q[Id,,a_left M].
Proof.
  intros * HΓ HP HQ HM Hc.
  destruct (alg_type_check_and_infer HΓ Hc) as (WP & WQ & Hi & HWP & HWQ).
  assert (HL : Γ ⊢ a_left M : P) by (eapply wf_left; eassumption).
  pose proof (wf_sub_single _ _ _ _ _ _ HP type_sort_prop HL) as Hσ.
  pose proof (sub_preserves_sort_eq _ _ _ _ _ _ _ _ (soundness_ty_at_sort type_sort_prop HQ HWQ) type_sort_prop Hσ) as HQWσ.
  apply (alg_type_check_of_infer_nbe type_sort_prop (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop Hσ)); intros W HW.
  eapply alg_type_infer_right; [ exact Hi | exact (nbe_ty_of_exp_eq_sort type_sort_prop HQWσ HW) ].
Qed.

(** A proof of a conjunction checks against its annotation: the
    annotation's normal form is the conjunction's, whose parts the
    components check against. *)
Lemma alg_conj_complete : forall {Γ T P Q M N},
    ⊢ Γ -> Γ ⊢ T : Propₘ -> Γ ⊢a T ⟸ Propₘ -> Γ ⊢ T ≈ Σₚ P Q : Propₘ -> Γ ⊢ P : Propₘ -> Γ ▹ P ⊢ Q : Propₘ ->
    Γ ⊢ M : P -> Γ ⊢a M ⟸ P -> Γ ⊢a N ⟸ Q[Id,,M] -> Γ ⊢a a_conj T M N ⟸ T.
Proof.
  intros * HΓ HT HTc HTe HP HQ HM HMc HNc.
  pose proof (alg_type_check_prop_infer HΓ HTc) as HTi.
  apply (alg_type_check_of_infer_nbe type_sort_prop HT); intros W HW.
  pose proof (nbe_ty_of_exp_eq_sort type_sort_prop HTe HW) as HW'.
  destruct (nbe_ty_and_inv _ _ _ _ HW') as (WP & WQ & -> & HWP & HWQ).
  pose proof (wf_sub_single _ _ _ _ _ _ HP type_sort_prop HM) as Hσ.
  eapply alg_type_infer_conj; [ exact HTi | exact HW | |].
  - exact (alg_type_check_conv_sort HMc type_sort_prop (soundness_ty_at_sort type_sort_prop HP HWP)).
  - exact (alg_type_check_conv_sort HNc type_sort_prop
             (sub_preserves_sort_eq _ _ _ _ _ _ _ _ (soundness_ty_at_sort type_sort_prop HQ HWQ) type_sort_prop Hσ)).
Qed.

(** A [∀] over a type that infers a sort is a proposition. *)
Lemma alg_all_complete_of : forall {Γ A B UA r u},
    ⊢ Γ -> ⊢ Γ ▹ A -> Γ ⊢a A ⟹ UA -> is_sort_nf UA r u -> Γ ▹ A ⊢a B ⟸ Propₘ ->
    Γ ⊢a a_pi propositional A B ⟸ Propₘ.
Proof.
  intros * HΓ HΓA HAi Hs HBc.
  apply (alg_type_check_prop_of HΓ).
  eapply alg_type_infer_all; [ exact HAi | exact Hs | exact (alg_type_check_prop_infer HΓA HBc) ].
Qed.

(** A [∀] over a type of either sort. *)
Lemma alg_all_complete : forall {Γ A B S},
    ⊢ Γ -> type_sort S -> Γ ⊢ A : S -> Γ ⊢a A ⟸ S -> Γ ▹ A ⊢a B ⟸ Propₘ -> Γ ⊢a a_pi propositional A B ⟸ Propₘ.
Proof.
  intros * HΓ HS HA HAc HBc.
  destruct (alg_type_check_sort_infer HΓ HS HAc) as (UA & r & u & HAi & Hs).
  exact (alg_all_complete_of HΓ ltac:(eapply wf_ctx_extend; eassumption) HAi Hs HBc).
Qed.

(** A term checked against a type of a sort infers a type whose instance
    along a substitution normalises below the type's instance. *)
Lemma alg_type_check_nbe_sub : forall {Γ Δ σ B C SC},
    ⊢ Δ -> Γ ⊢ˢ σ : Δ -> type_sort SC -> Δ ⊢ C : SC -> Δ ⊢a B ⟸ C ->
    exists C' W, Δ ⊢a B ⟹ C' /\ nbe_ty_f Γ (nf_to_exp C')[σ] W /\ Γ ⊢a W ⊆ C[σ].
Proof.
  intros * HΔ Hσ HSC HC Hc.
  inversion Hc as [? C' ? ? HBi HBs]; subst.
  pose proof (alg_type_infer_sound HBi HΔ) as HB'.
  destruct (presup_exp_typ HB') as [SC' HSC' HC'].
  pose proof (alg_subtyping_sound_sort _ _ _ _ _ HSC' HSC HBs HC' HC) as HCC.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC' HSC' Hσ) as HC'σ.
  destruct (nbe_ty_exists_sort HSC' HC'σ) as [W HW].
  pose proof (soundness_ty_at_sort HSC' HC'σ HW) as HE.
  exists C', W; split; [ exact HBi | split; [ exact HW |] ].
  apply alg_subtyping_complete.
  etransitivity; [| exact (sub_preserves_subtyp _ _ _ _ _ _ _ HCC Hσ) ].
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HC'σ (presup_exp_eq_right HE) HSC' HE)).
Qed.

(** An application checks against the codomain instantiated: the function
    infers a [Π] whose codomain is below the [Π]'s ([alg_type_check_pi_implies_alg_type_infer_pi]). *)
Lemma alg_app_complete : forall {Γ A B M N S r} {i : nat},
    ⊢ Γ -> type_sort S -> Γ ⊢ A : S -> Γ ▹ A ⊢ B : relevance_sort r Typeω@i ->
    Γ ⊢ M : a_pi r A B -> Γ ⊢a M ⟸ a_pi r A B -> Γ ⊢ N : A -> Γ ⊢a N ⟸ A ->
    Γ ⊢a M $ N ⟸ B[Id,,N].
Proof.
  intros * HΓ HS HA HB HM HMc HN HNc.
  destruct (presup_exp_typ HM) as [Spi _ HPi].
  destruct (alg_type_check_pi_implies_alg_type_infer_pi HΓ HPi HMc) as (A' & B' & SA & HSA & HMi & HAA & HBB).
  pose proof (alg_type_check_conv_sort HNc HSA (wf_exp_eq_sym _ _ _ _ _ _ HAA)) as HNc'.
  pose proof (alg_type_infer_sound HMi HΓ) as HM'; cbn [nf_to_exp] in HM'.
  destruct (presup_exp_typ HM') as [S' _ HPi'].
  destruct (wf_pi_parts_large _ _ _ _ _ HPi') as (SA' & k & HSA' & HA' & HB'k).
  pose proof (ctxsub_exp _ _ _ _ _ _ (sub_id_extend_of_exp_eq HSA (wf_exp_eq_sym _ _ _ _ _ _ HAA)) HB'k) as HB'A.
  pose proof (alg_subtyping_sound_sort _ _ _ _ _ (type_sort_relevance_universe r k) (type_sort_relevance_universe r i)
                HBB HB'A HB) as HBB'.
  pose proof (wf_sub_single _ _ _ _ _ _ HA HS HN) as Hσ.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HB'A (type_sort_relevance_universe r k) Hσ) as HB'N.
  destruct (nbe_ty_exists_sort (type_sort_relevance_universe r k) HB'N) as [W HW].
  pose proof (soundness_ty_at_sort (type_sort_relevance_universe r k) HB'N HW) as HE.
  econstructor; [ eapply alg_type_infer_app; [ exact HMi | exact HNc' | exact HW ] |].
  apply alg_subtyping_complete.
  etransitivity; [| exact (sub_preserves_subtyp _ _ _ _ _ _ _ HBB' Hσ) ].
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HB'N (presup_exp_eq_right HE) (type_sort_relevance_universe r k) HE)).
Qed.

(** A relevant [Π] at a large universe, over a type of it or a
    proposition: the join of the two parts' universes is below it. *)
Lemma alg_pi_large_complete : forall {Γ A B S i},
    ⊢ Γ -> pi_domain_sort Typeω@i S -> Γ ⊢ A : S -> Γ ⊢a A ⟸ S -> Γ ▹ A ⊢a B ⟸ Typeω@i ->
    Γ ⊢a Π A B ⟸ Typeω@i.
Proof.
  intros * HΓ HD HA HAc HBc.
  assert (HS : type_sort S) by (destruct HD; constructor).
  assert (exists UA rA u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA rA u /\ universe_nf_le u (universe_large i))
    as (UA & rA & u & HAi & Hs & Hle).
  { destruct HD.
    - destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ HAc) as (UA & u & HAi & Hu & Hle).
      exists UA, relevant, u; split; [ exact HAi | split; [ constructor; exact Hu | exact Hle ] ].
    - exists Propⁿ, propositional, (universe_small (ordinal_of_nat 0, nil)).
      split; [ exact (alg_type_check_prop_infer HΓ HAc) | split; [ constructor | cbn; exact I ] ]. }
  assert (HΓA : ⊢ Γ ▹ A) by (eapply wf_ctx_extend; eassumption).
  destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓA HBc) as (UB & v & HBi & Hv & Hle').
  pose proof (pi_domain_ok_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) as HAd.
  assert (HBv : Γ ▹ A ⊢ B : universe_nf_tm v)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hv); exact (alg_type_infer_sound HBi HΓA)).
  assert (Hvws : universe_nf_well_scoped (Γ ▹ A) v).
  { pose proof (alg_type_infer_self HΓA HBi) as HnB; rewrite (is_univ_nf_eq _ _ Hv) in HnB.
    assert (exists k, Γ ▹ A ⊢ universe_nf_tm v : Typeω@k) as [kv Hkv] by univ_large.
    eapply universe_nf_well_scoped_of_nbe; [ exact Hkv | rewrite <- nf_to_exp_univ_nf; exact HnB ]. }
  destruct (wf_universe_nf_pi_tm HAd HBv Hvws) as [k Hk].
  eapply (alg_pi_check_of_infer _ _ _ _ _ rA u v _ (Datatypes.S i));
    [ exact HΓ | exact HAi | exact HBi | exact Hs | exact Hv | apply wf_typ; exact HΓ |].
  eapply universe_nf_pi_tm_large; eassumption.
Qed.

(** A [λ] checks against a [Π] of the sort its body's type is of: the
    body's inferred type is below the [Π]'s codomain, so of its sort
    ([subtyp_same_relevance]), and of that relevance
    ([nbe_ty_relevance_of_typed]); the inferred [Π] is below the [Π],
    covariantly at [relevant], equal at [propositional]. *)
Lemma alg_fn_complete : forall {Γ A B M S r} {i : nat},
    ⊢ Γ -> type_sort S -> Γ ⊢ A : S -> Γ ⊢a A ⟸ S -> Γ ▹ A ⊢ B : relevance_sort r Typeω@i -> Γ ▹ A ⊢a M ⟸ B ->
    Γ ⊢a λ A M ⟸ a_pi r A B.
Proof.
  intros * HΓ HS HA HAc HB HMc.
  destruct (alg_type_check_sort_infer HΓ HS HAc) as (UA & rA & u & HAi & Hs).
  assert (HΓA : ⊢ Γ ▹ A) by (eapply wf_ctx_extend; eassumption).
  inversion HMc as [? B' ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓA) as HMB'.
  destruct (presup_exp_typ HMB') as [SB HSB HB'].
  pose proof (alg_subtyping_sound_sort _ _ _ _ _ HSB (type_sort_relevance_universe r i) HMs HB' HB) as HBB.
  assert (exists k : nat, Γ ▹ A ⊢ B' : relevance_sort r Typeω@k) as [k HBk].
  { assert (exists r' (j : nat), SB = relevance_sort r' Typeω@j) as (r' & j & ->)
      by (destruct HSB as [j |]; [ exists relevant, j | exists propositional, 0 ]; reflexivity).
    pose proof (subtyp_same_relevance _ _ _ r' r j i HBB HB' HB) as <-; exists j; exact HB'. }
  destruct (nbe_ty_exists_sort HS HA) as [C HC].
  assert (Hfi : Γ ⊢a λ A M ⟹ nf_pi r C B')
    by (eapply alg_type_infer_fn; [ exact HAi | exact Hs | exact HMi | exact (nbe_ty_relevance_of_typed HBk) | exact HC ]).
  econstructor; [ exact Hfi |].
  destruct HMs as [B1 B2 Hn1 Hn2 Hsub].
  pose proof (alg_type_infer_normal HΓA HMi Hn1) as <-.
  econstructor; [ exact (alg_type_infer_self HΓ Hfi) | exact (nbe_ty_pi_intro _ _ _ _ _ _ HC Hn2) |].
  destruct r.
  - constructor; [ reflexivity | exact Hsub ].
  - cbn [relevance_sort] in HB.
    rewrite (alg_subtyping_nf_not_univ_pi_eq _ _ Hsub ltac:(right; exact (nbe_ty_prop_not_univ_pi _ _ _ HB Hn2))).
    constructor; [ exact I | reflexivity ].
Qed.

(** The whole block, the universes included; [alg_type_complete_lets] below
    is the statement without them. *)
Lemma alg_type_complete_lets_all : forall n,
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     ext_entries n Γ Ψ /\ ext_entries n Γ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> True).
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind.
  (** A module expression, by generation, below the bound. *)
  assert (HmH : forall Γ' H0, gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H0 ≈ H0 -> modexp_lets H0 < n -> Γ' ⊢aᵐ H0).
  { intros Γ' H0 HH0 Hlt; destruct (IHn _ Hlt) as (_ & IHt & _ & _ & _ & _ & IHu & _).
    eapply (alg_modexp_of_wf (modexp_lets H0)); [| | exact HH0 | lia ].
    - intros; eapply IHt; [ eassumption | reflexivity | reflexivity | apply user_exp_all | assumption ].
    - intros * HU0 HlU; exact (proj1 (IHu _ _ _ _ _ HU0 eq_refl eq_refl) HlU). }
  apply syntactic_wf_mut_ind; intros; try exact I; subst; destruct_let_ann; destruct_univ;
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
  all: match goal with |- _ ⊢a a_elim _ _ _ _ _ ⟸ _ => idtac | |- _ ⊢a _ ⟸ _ =>
         gen_presups;
         (** A universe, [⊤] and [⊥] infer their own universe. *)
         try solve [ eapply alg_type_check_suniv;
                     [ assumption | mauto 3 | constructor | cbn; apply lvl_le_lit; lia ]
                   | eapply alg_type_check_typ_of;
                     [ assumption | mauto 3 | constructor | cbn; first [ exact I | lia ] ] ];
         (** A small universe at a level term infers the normal form of the
             universe above it. *)
         try match goal with
           | |- _ ⊢a a_univ ?M ⟸ a_univ (succl ?M) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               assert (HSU : Γ ⊢ Type⟨succl M⟩ : Typeω@0)
                 by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; eassumption ]);
               destruct (soundness_ty HSU) as [W [HW HWe]];
               econstructor; [ eapply alg_type_infer_suniv; eassumption |];
               apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe
           end;
         (** The level forms infer a type of levels below the one they are
             checked against. *)
         try solve [ lazymatch goal with
           | |- alg_type_check _ (a_level _) (a_llit _) =>
               eapply alg_type_check_level_of; [ assumption | constructor | lia ]
           | |- alg_type_check _ (a_level _) (a_succl ?M) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               eapply alg_type_check_level_of; [ assumption | constructor; eassumption | lia ]
           | |- alg_type_check _ (a_level _) (a_maxl ?M ?N) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               match goal with Hc : alg_type_check ?G (a_level _) N, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               eapply alg_type_check_level_of; [ assumption | constructor; eassumption | lia ]
           end ];
         mauto 4 using alg_subtyping_complete, alg_type_check_subtyp | _ => idtac end.
  (** A record's type former, a projection and a tuple ([alg_record_complete],
      [alg_proj_complete], [alg_tuple_complete]); the fields of a tuple are
      below its bound on [let]s ([tuple_field_lets]). *)
  all: try solve [ eapply alg_record_complete; eassumption ].
  all: try solve [ eapply alg_proj_complete; eassumption ].
  all: try match goal with
    | HTt : _ ⊢ ?T : Typeω@?i, HTc : _ ⊢a ?T ⟸ Typeω@?i, HTe : _ ⊢ ?T ≈ apps_exp (a_record _) _ : _,
      HMs : forall k f M U, List.nth_error ?fs k = Some (f, M) -> _ -> _ = _ -> _ = _ -> user_exp M -> exp_lets M <= _ -> _ ⊢a M ⟸ _,
      Hbd : exp_lets (a_tuple ?T ?fs) <= _ |- _ ⊢a a_tuple ?T ?fs ⟸ _ =>
        eapply alg_tuple_complete; [ exact HTt | exact HTc | exact HTe | eassumption .. |];
        let k := fresh "k" in let f := fresh "f" in let M := fresh "M" in let U := fresh "U" in
        let Hk := fresh "Hk" in let Hfk := fresh "Hfk" in
        intros k f M U Hk Hfk; apply (HMs _ _ _ _ Hk Hfk eq_refl eq_refl (user_exp_all _));
        pose proof (tuple_field_lets T fs k f M Hk); lia
    end.
  (** A member, at the normal form of the type its module's description
      reads; the module, by generation. *)
  all: try match goal with
    | HH : _ ⍮ _ ⍮ ?G ⊢ᵐ ?H0 ≈ ?H0, Hm : mdenote _ _ ?G (me_mem ?H0 ?x0) _, Ht : mdesc_type _ = Some ?A0,
      HA : ?G ⊢ ?A0 : ?Srt, HS : type_sort ?Srt, Hb : exp_lets (a_mem ?H0 ?x0) <= _ |-?G ⊢a a_mem ?H0 ?x0 ⟸ ?A0 =>
        cbn [exp_lets] in Hb;
        let W := fresh "W" in let HW := fresh "HW" in
        apply (alg_type_check_of_infer_nbe HS HA); intros W HW;
        eapply alg_type_infer_mem; [ apply HmH; [ exact HH | lia ] | exact Hm | exact Ht | exact HW ]
    end.
  (** [⋆] at [⊤]. *)
  - apply alg_true_complete; assumption.
  (** The introduction of [⊤] at [⊤]. *)
  - apply alg_tt_complete; assumption.
  (** [⋆] at another proposition. *)
  - (* PENDING design: [⋆] at a proposition other than [⊤] ([wf_star]) infers only [⊤]. *)
    admit.
  (** Ex falso, conjunctions and their proofs, the placeholder. *)
  - match goal with H : ?G ⊢ ?C : ?Srt, Hs : type_sort ?Srt |- ?G ⊢a efq _ return ?C ⟸ ?C =>
      eapply (alg_absurd_complete (S := Srt)); eassumption end.
  - apply alg_type_check_prop_of; [ assumption |]; apply alg_type_infer_and; apply alg_type_check_prop_infer; assumption.
  - eapply alg_conj_complete; eassumption.
  - eapply alg_left_complete; eassumption.
  - match goal with HM : _ ⊢ ?M : Σₚ ?P _ |- _ ⊢a a_right ?M ⟸ _ =>
      eapply (alg_right_complete (P := P)); eassumption end.
  - apply alg_placeholder_complete; assumption.
  (** The type former and a constructor: at the normal forms of their
      types. *)
  - destruct (decl_of_lookup _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)) as [HD Hc].
    destruct (ind_ty_typed _ _ _ _ _ _ HD Hc ltac:(eassumption) ltac:(eassumption)) as [j Hj].
    destruct (soundness_ty Hj) as [W [HW HWe]].
    econstructor; [ eapply alg_type_infer_ind_case; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  - assert (HΓ1 : ⊢ Γ) by assumption.
    match goal with Hl : ind_lookup _ _ _ = Some _, Hk : ind_member _ _ = Some _, Hcon : ind_con _ _ = Some _ |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ1) (decls_of_ctx _ _ _ HΓ1) Hl Hk Hcon HΓ1) as [j Hj] end.
    destruct (soundness_ty Hj) as [W [HW HWe]].
    econstructor; [ eapply alg_type_infer_con; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  (** The eliminator ([alg_elim_complete]): its parts by the induction
      hypotheses, under the bound on [let]s ([elim_lets_parts]). *)
  - match goal with
    | Hl : ind_lookup _ _ ?p = Some ?D, Hg : elim_grp ?D ?oq ?p ?m, Hm : ind_member ?D ?m = Some ?Mm,
      Hb : List.nth_error ?Bks ?m = Some ?bm, HPl : List.length ?Ps = im_np ?D ?Mm,
      Hbd : exp_lets (a_elim ?r ?oq _ ?m ?Bks ?M) <= _,
      HAt : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> _ ⊢ eb_motive b : relevance_sort ?r Typeω@?i,
      HUs : forall k P T, List.nth_error ?Ps k = Some P -> List.nth_error (tele_insts (im_params ?D ?Mm) Id ?Ps) k = Some T ->
              _ = _ -> _ = _ -> user_exp P -> exp_lets P <= _ -> _ ⊢a P ⟸ T,
      HZs : forall k Mk b Z, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> eb_ann b = Some Z ->
              _ = _ -> _ = _ -> ext_entries _ _ _ /\ _,
      HAs : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> _ = _ -> _ = _ ->
              user_exp (eb_motive b) -> exp_lets (eb_motive b) <= _ -> _ ⊢a eb_motive b ⟸ _,
      HBs : forall k Mk b c gs n0 B, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> ind_con Mk c = Some gs ->
              List.In (c, n0, B) (eb_brs b) -> _ = _ -> _ = _ -> user_exp B -> exp_lets B <= _ -> _ ⊢a B ⟸ _ |- _ =>
        destruct (elim_lets_parts r oq (List.firstn (ind_nu D) Ps) m Bks M) as (HLu & HLz & HLa & HLb & _);
        assert (HΓe : ⊢ Γ) by (gen_presups; assumption);
        destruct (decl_of_lookup _ _ _ _ _ HΓe Hl) as [_ Hc];
        eapply (alg_elim_complete Γ p D oq m Mm bm Bks Ps M r i);
          [ exact Hl | exact Hg | exact Hm | exact Hb | exact HPl | eassumption | eassumption | eassumption
          | constructor; assumption | | | | ];
        [ intros j U T HU HT
        | intros j Mj b Z Hj Hbj HZ; destruct (HZs _ _ _ _ Hj Hbj HZ eq_refl eq_refl) as [HE _];
          apply (ext_entries_head _ _ _ _ HE); cbn [centry_lets];
          pose proof (HLz b Z (List.nth_error_In _ _ Hbj) HZ); lia
        | intros j Mj b Hj Hbj; apply (HAs _ _ _ Hj Hbj eq_refl eq_refl (user_exp_all _));
          pose proof (HLa b (List.nth_error_In _ _ Hbj)); lia
        | intros j Mj b c gs n1 B Hj Hbj Hcon Hin; apply (HBs _ _ _ _ _ _ _ Hj Hbj Hcon Hin eq_refl eq_refl (user_exp_all _));
          pose proof (HLb b _ (List.nth_error_In _ _ Hbj) Hin); cbn [snd] in *; lia ];
        assert (Hj : j < ind_nu D)
          by (assert (j < List.length (List.firstn (ind_nu D) Ps)) by (apply List.nth_error_Some; congruence);
              rewrite List.length_firstn in *; lia);
        assert (HUP : List.nth_error Ps j = Some U)
          by (rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (rewrite List.length_firstn; unfold im_np in *; lia);
              exact HU);
        assert (HFl : List.length (List.firstn (ind_nu D) Ps) = List.length (ind_uparams D))
          by (rewrite List.length_firstn; change (List.length (ind_uparams D)) with (ind_nu D); unfold im_np in HPl; lia);
        assert (HTP : List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T)
          by (rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params;
              rewrite tele_insts_app by (try exact (decl_closed_ass _ Hc); exact HFl);
              rewrite List.nth_error_app1; [ exact HT | rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in Hj; lia ]);
        apply (HUs j U T HUP HTP eq_refl eq_refl (user_exp_all _));
        pose proof (HLu U (List.nth_error_In _ _ HU)); lia
    end.
  (** [Π] at a large universe: of functions over a type of it or a
      proposition ([alg_pi_large_complete]), or a [∀] ([alg_all_complete]). *)
  - match goal with Hd : pi_domain_sort _ ?Srt, HAt : ?G ⊢ ?A : ?Srt |- ?G ⊢a a_pi ?r ?A _ ⟸ _ =>
      assert (HSd : type_sort Srt) by (destruct Hd; constructor);
      destruct r; cbn [relevance_sort] in *; destruct_univ;
      [ eapply alg_pi_large_complete; eassumption
      | eapply (alg_all_complete (S := Srt)); [ eassumption | exact HSd | exact HAt | eassumption | cbn [exp_wk] in *; eassumption ] ]
    end.
  (** [Π] at a small universe: over a type of it ([alg_pi_small_complete])
      or a proposition ([alg_pi_small_prop_complete]), or a [∀] over a type
      of it, which infers a small universe. *)
  - match goal with Hd : pi_domain_sort _ ?Srt, HAt : ?G ⊢ ?A : ?Srt, HG : ⊢ ?G |- ?G ⊢a a_pi ?r ?A _ ⟸ _ =>
      destruct r; cbn [relevance_sort] in *; destruct_univ;
      [ destruct Hd; [ eapply alg_pi_small_complete; eassumption | eapply alg_pi_small_prop_complete; eassumption ] |];
      cbn [exp_wk] in *;
      destruct Hd;
      [ match goal with Hc : G ⊢a A ⟸ Type⟨_⟩ |- _ =>
          destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HG Hc) as ([c xs] & Lt & HAi & _ & _);
          eapply (alg_all_complete_of (r := relevant) (u := universe_small (c, xs)) HG); [ eassumption | exact HAi | do 2 constructor | eassumption ]
        end
      | eapply (alg_all_complete (S := Propₘ)); [ eassumption | constructor | eassumption .. ] ]
    end.
  (** [λ] ([alg_fn_complete]) and an application ([alg_app_complete]). *)
  - match goal with HAt : ?G ⊢ ?A : ?Srt, HS : type_sort ?Srt, HG : ⊢ ?G |- ?G ⊢a λ ?A _ ⟸ _ =>
      eapply (alg_fn_complete HG HS HAt); eassumption end.
  - match goal with HAt : ?G ⊢ ?A : ?Srt, HS : type_sort ?Srt, HG : ⊢ ?G, HM : ?G ⊢ ?M : a_pi _ ?A _ |- ?G ⊢a ?M $ _ ⟸ _ =>
      eapply (alg_app_complete HG HS HAt); eassumption end.
  (** An unannotated [let].  The definiens infers [A'], a subtype of the [A]
      of the derivation, a type of a universe, so the body's derivation is
      moved to [Γ ▸ A' ≔ M] by refinement.  That derivation is no
      subderivation, but its subject has fewer unannotated [let]s, which is
      what the outer induction is for. *)
  - match goal with
    | E : ?Srt = Typeω@?i, HAt : ?G ⊢ ?A : ?Srt, HM : ?G ⊢ ?M : ?A, Hc : ?G ⊢a ?M ⟸ ?A,
      HB : ?G ▸ ?A ≔ ?M ⊢ ?B : ?C, HG : ⊢ ?G |- ?G ⊢a ℓ ≔ ?M in ?B ⟸ _ =>
        subst Srt;
        inversion Hc as [? A' ? ? HMi HMs]; subst;
        pose proof (alg_type_infer_sound HMi HG) as HMA';
        destruct (presup_exp_typ HMA') as [SA' HSA' HA'0];
        pose proof (alg_subtyping_sound_sort _ _ _ _ _ HSA' (type_sort_universe _) HMs HA'0 HAt) as HAA;
        assert (exists k : nat, G ⊢ A' : Typeω@k) as [k HA']
          by (destruct HSA' as [k |]; [ exists k; exact HA'0 | exfalso; exact (subtyp_prop_relevant_absurd HAA HA'0 HAt) ]);
        assert (HId : G ▸ A' ≔ M ⊢ˢ Id : G ▸ A ≔ M)
          by (eapply wf_sub_id_extend_def; [ apply wf_sub_id; exact HG | exact HAt | constructor | exact HA' | constructor
                                           | exact HAA | exact HM | exact HMA' | apply wf_exp_eq_refl; exact HM ]);
        assert (HB' : G ▸ A' ≔ M ⊢ B : C) by exact (ctxsub_exp _ _ _ _ _ _ HId HB);
        assert (HBa : G ▸ A' ≔ M ⊢a B ⟸ C)
          by (destruct (IHn (exp_lets B) ltac:(lets_bound)) as (_ & IHt & _);
              eapply IHt; [ exact HB' | reflexivity | reflexivity | apply user_exp_all | lia ]);
        clear IHn;
        assert (HGd : ⊢ G ▸ A' ≔ M) by (eapply wf_ctx_extend_def; [ exact HA' | constructor | exact HMA' ]);
        destruct (presup_exp_typ HB') as [SC HSC HC];
        destruct (alg_type_check_nbe_sub HGd (wf_sub_single_def _ _ _ _ _ _ HA' (type_sort_universe _) HMA') HSC HC HBa)
          as (C' & W & HBi & HW & Hsub);
        econstructor; [ eapply alg_type_infer_let_none; [ exact HMi | exact (nbe_ty_relevance_of_typed (r := relevant) HA') | exact HBi | exact HW ]
                      | exact Hsub ]
    end.
  (** An annotated [let]: the annotation of either sort. *)
  - match goal with
    | HAt : ?G ⊢ ?A : ?Srt, HS : type_sort ?Srt, HAc : ?G ⊢a ?A ⟸ ?Srt, HM : ?G ⊢ ?M : ?A, HMc : ?G ⊢a ?M ⟸ ?A,
      HB : ?G ▸ ?A ≔ ?M ⊢ ?B : ?C, HBc : ?G ▸ ?A ≔ ?M ⊢a ?B ⟸ ?C, HG : ⊢ ?G |- ?G ⊢a ℓ ?A ≔ ?M in ?B ⟸ _ =>
        destruct (alg_type_check_sort_infer HG HS HAc) as (UA & r & u & HAi & Hs);
        assert (HGd : ⊢ G ▸ A ≔ M) by (eapply wf_ctx_extend_def; [ exact HAt | exact HS | exact HM ]);
        destruct (presup_exp_typ HB) as [SC HSC HC];
        destruct (alg_type_check_nbe_sub HGd (wf_sub_single_def _ _ _ _ _ _ HAt HS HM) HSC HC HBc)
          as (C' & W & HBi & HW & Hsub);
        econstructor; [ eapply alg_type_infer_let_some; [ exact HAi | exact Hs | exact HMc | exact HBi | exact HW ] | exact Hsub ]
    end.
  (** A module [let], through its body. *)
  - match goal with
    | HU : _ ⍮ _ ⍮ ?G ⊢ᵘ ?U ≈ ?U, HUa : ?G ⊢aᵘ ?U /\ _, HCt : ?G ▹ₘ ?U ⊢ ?C : ?Srt, HS : type_sort ?Srt,
      HBc : ?G ▹ₘ ?U ⊢a ?B ⟸ ?C |- ?G ⊢a ℓₘ ?U in ?B ⟸ _ =>
        destruct HUa as [HUa _];
        assert (HGU : ⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
        destruct (alg_type_check_nbe_sub HGU (wf_sub_single_mod _ _ _ _ HU) HS HCt HBc) as (C' & W & HBi & HW & Hsub);
        econstructor; [ eapply alg_type_infer_let_mod; [ exact HUa | exact HBi | exact HW ] | exact Hsub ]
    end.
  (** A variable, at the normal form of its type. *)
  - match goal with HA : ?G ⊢ ?A : ?S, HS : type_sort ?S |- ?G ⊢a #_ ⟸ ?A =>
      apply (alg_type_check_of_infer_nbe HS HA); intros W HW; eapply alg_type_infer_vlookup; eassumption end.
  (** Extensions, entry by entry. *)
  - split; apply ext_entries_nil.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ ?S, HS : type_sort ?S |- _ =>
        destruct (alg_type_check_sort_infer HΨ HS (IHA Hle)) as (UA & r & u & Hj & Hs) end; eauto.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ ?S, HS : type_sort ?S |- _ =>
        destruct (alg_type_check_sort_infer HΨ' HS (IHA Hle)) as (UA & r & u & Hj & Hs) end; eauto.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ ?S, HS : type_sort ?S, IHM : exp_lets M <= n -> _ ⊢a M ⟸ _ |- _ =>
        destruct (alg_type_check_sort_infer HΨ HS (IHA ltac:(lia))) as (UA & r & u & Hj & Hs);
        split; [ eauto | exact (IHM ltac:(lia)) ] end.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ ?S, HS : type_sort ?S, IHM : exp_lets M' <= n -> _ ⊢a M' ⟸ _ |- _ =>
        destruct (alg_type_check_sort_infer HΨ' HS (IHA ltac:(lia))) as (UA & r & u & Hj & Hs);
        split; [ eauto | exact (IHM ltac:(lia)) ] end.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + match goal with IHU : (gunit_lets U <= n -> _ ⊢aᵘ U) /\ _ |- _ => exact (proj1 IHU Hle) end.
    + match goal with IHU : (gunit_lets U' <= n -> ?G ⊢aᵘ U') /\ _, _ : _ ⍮ _ ⍮ ?G ⊢ᵘ U' ≈ U' |- _ => exact (proj1 IHU Hle) end.
  - (** A definition with a module part: as a definition and as a slot. *)
    match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ _, IHM : exp_lets M <= n -> _ ⊢a M ⟸ _,
                      IHU : (gunit_lets U <= n -> _ ⊢aᵘ U) /\ _ |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (IHA ltac:(lia))) as [UA [u [Hj [Hu _]]]];
        split; [ split; [ eauto | exact (IHM ltac:(lia)) ] | exact (proj1 IHU ltac:(lia)) ] end.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ _, IHM : exp_lets M' <= n -> _ ⊢a M' ⟸ _,
                      IHU : (gunit_lets U' <= n -> ?G ⊢aᵘ U') /\ _, _ : _ ⍮ _ ⍮ ?G ⊢ᵘ U' ≈ U' |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' (IHA ltac:(lia))) as [UA [u [Hj [Hu _]]]];
        split; [ split; [ eauto | exact (IHM ltac:(lia)) ] | exact (proj1 IHU ltac:(lia)) ] end.
  (** Units: the parameters, relevant, as checked parameters
      ([alg_params_of_entries]); a body from the entries of its expansion
      that are its own, each of the sort its tag says
      ([body_tagged_of_fill_left]), and the targets of its opens. *)
  - match goal with
    | HX : ext_entries _ _ (body_ctx Φx ++ Δ) /\ _ |- _ => destruct HX as [HXl _]
    end.
    match goal with
    | Hx : body_xp _ _ (Δ ++ Γ) Φ Φx, HXe : _ ⍮ _ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ _, HD : _ ⍮ _ ⍮ Γ ⊢ˣ Δ ≈ _,
      Hs : body_shape Φ Φ', Hsx : body_shape Φx Φx', Hnd : List.NoDup (gm_names Φ),
      Ho : forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> _ ⍮ _ ⍮ _ ⊢ᵐ H ≈ H,
      HR : forall Δ1 T Δ2, Δ = Δ1 ++ ce_ass T :: Δ2 -> _ ⊢ T : Typeω@_ |- _ =>
        destruct (body_shape_refl _ _ Hs) as (Hs1 & _ & _);
        destruct (body_shape_refl _ _ Hsx) as (Hsx1 & _ & _);
        pose proof (ext_eq_ctx_left _ _ _ _ _ HXe) as HCx; rewrite <- List.app_assoc in HCx;
        assert (HΓ : ⊢ Γ) by exact (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD));
        rewrite gunit_lets_mk in *; cbn [moddef_lets] in *;
        eapply alg_unit_body;
          [ eapply (alg_params_of_entries n); [ exact HΓ | exact (ext_entries_app_r _ _ _ _ HXl) | lia | assumption | exact HR ]
          | assumption | | exact Hs1 | exact Hsx1 | exact Hnd ];
        eapply alg_body_of_entries;
          [ eassumption | exact HXl | lia | exact Hs1 | rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd
          | eapply (body_tagged_of_fill_left _ _ Φx' _ (body_xp_nopens _ _ _ _ _ Hx) Hsx HCx); eassumption | ];
        intros k Ψ0 H0' Hk Hle; apply HmH; [ exact (Ho _ _ _ Hk) | lia ]
    end.
  - match goal with
    | HX : ext_entries _ _ (body_ctx Φx' ++ Δ') /\ _ |- _ => destruct HX as [HXr _]
    end.
    match goal with
    | Hx : body_xp _ _ (Δ' ++ Γ) Φ' Φx', HXe : _ ⍮ _ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ _, HD : _ ⍮ _ ⍮ Γ ⊢ˣ Δ ≈ Δ',
      Hs : body_shape Φ Φ', Hsx : body_shape Φx Φx', Hnd : List.NoDup (gm_names Φ),
      Ho : forall k Ψ H, List.nth_error (body_opens Φ' Φx') k = Some (Ψ, H) -> _ ⍮ _ ⍮ _ ⊢ᵐ H ≈ H,
      HR : forall Δ1 T Δ2, Δ' = Δ1 ++ ce_ass T :: Δ2 -> _ ⊢ T : Typeω@_ |- _ =>
        destruct (body_shape_refl _ _ Hs) as (_ & Hs2 & Hn);
        destruct (body_shape_refl _ _ Hsx) as (_ & Hsx2 & _);
        pose proof (ext_eq_ctx_left _ _ _ _ _ HXe) as HCx; rewrite <- List.app_assoc in HCx;
        assert (HΓ : ⊢ Γ) by exact (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD));
        rewrite gunit_lets_mk in *; cbn [moddef_lets] in *;
        eapply alg_unit_body;
          [ eapply (alg_params_of_entries n); [ exact HΓ | exact (ext_entries_app_r _ _ _ _ HXr) | lia | assumption | exact HR ]
          | assumption | | exact Hs2 | exact Hsx2 | rewrite <- Hn; exact Hnd ];
        eapply alg_body_of_entries;
          [ eassumption | exact HXr | lia | exact Hs2 | rewrite (body_xp_names _ _ _ _ _ Hx), <- Hn; exact Hnd
          | eapply (body_tagged_of_fill_right _ Φx _ _ (body_xp_nopens _ _ _ _ _ Hx) Hsx HCx); eassumption | ];
        intros k Ψ1 H1' Hk Hle; apply HmH; [ exact (Ho _ _ _ Hk) | lia ]
    end.
  (** An alias: its parameters, and its target, by generation. *)
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    econstructor; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXl | lia | assumption | eassumption ] | assumption | ].
    apply HmH; [ first [ eapply wf_modexp_eq_refl_left; eassumption | eassumption ] | lia ].
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [_ HXr] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    econstructor; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXr | lia | assumption | eassumption ] | assumption | ].
    apply HmH; [ first [ eapply wf_modexp_eq_refl_left; eassumption | eassumption ] | lia ].
  (** Flattening: the alias of the literal, and the unit over both
      telescopes. *)
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    match goal with HU : _ ⊢aᵘ _ /\ _ |- _ =>
      apply alg_unit_alias; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXl | lia | assumption | eassumption ] | assumption | apply alg_modexp_lit, (proj1 HU) ] end.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk, ctx_lets_app in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    match goal with HU : _ ⊢aᵘ _ /\ _ |- _ =>
      eapply alg_unit_flatten; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXl | lia | assumption | eassumption ] | assumption | exact (proj1 HU) ] end.
  - destruct H0; assumption.
  - destruct H0; assumption.
  - destruct H0 as [H01 _]; assumption.
  - destruct H2 as [_ H22]; assumption.
Admitted. (* PENDING design: [wf_star] at a proposition other than [⊤] *)

Lemma alg_type_complete_lets : forall n,
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     ext_entries n Γ Ψ /\ ext_entries n Γ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack ->
     (modexp_lets H <= n -> Γ ⊢aᵐ H) /\ (modexp_lets H' <= n -> Γ ⊢aᵐ H')).
Proof.
  intros n; destruct (alg_type_complete_lets_all n) as (H1 & H2 & H3 & H4 & _ & H5 & H6 & _).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 _)))))).
  (** A module expression and its other side, by generation. *)
  assert (Hm : forall Γ H, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> modexp_lets H <= n -> Γ ⊢aᵐ H).
  { intros Γ H HH Hl; eapply (alg_modexp_of_wf n); [| | exact HH | exact Hl ].
    - intros; eapply H2; [ eassumption | reflexivity | reflexivity | apply user_exp_all | assumption ].
    - intros * HU HlU; exact (proj1 (H6 _ _ _ _ _ HU eq_refl eq_refl) HlU). }
  intros * HH -> ->; split; intros Hl;
    [ exact (Hm _ _ (wf_modexp_eq_refl_left HH) Hl) | exact (Hm _ _ (wf_modexp_eq_refl_right HH) Hl) ].
Qed.

Lemma alg_type_complete_all :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aˣ Ψ /\ Γ ⊢aˣ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵘ U /\ Γ ⊢aᵘ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵐ H /\ Γ ⊢aᵐ H').
Proof.
  repeat split; intros; try exact I.
  - eapply (alg_type_complete_lets (exp_lets M)); eauto.
  - eapply (ext_entries_alg (ctx_lets Ψ + ctx_lets Ψ'));
      [ exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)) | lia ].
  - eapply (ext_entries_alg (ctx_lets Ψ + ctx_lets Ψ'));
      [ exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)) | lia ].
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

(** The normal forms below a universe in the order on normal forms are the
    universes below it. *)
Lemma alg_subtyping_nf_univ_inv : forall W u,
    ⊢anf W ⊆ universe_nf_to_nf u ->
    exists v, W = universe_nf_to_nf v /\ universe_nf_le v u.
Proof.
  intros W [[d ys] | j] H; cbn in H; inversion H; subst;
    try match goal with Hn : not_univ_pi _ |- _ => inversion Hn end.
  all: match goal with
       | |- exists v, univⁿ ?c ?xs = _ /\ _ => exists (universe_small (c, xs))
       | |- exists v, Typeωⁿ@?i = _ /\ _ => exists (universe_large i)
       end; split; [ reflexivity | cbn; first [ assumption | exact I ] ].
Qed.

(** Completeness at a universe: a type of a universe term [T] infers a
    universe below the normal form of [T].  The bound is the normal form of
    [T] and not [T]'s universe index read off syntactically: the sorts the
    atoms of a universe normal form carry are those of their types only in a
    normal form ([soundness_lvl_well_scoped]).  At [Typeω@i] this is
    [alg_type_infer_large_typ_complete], at [Type@n]
    [alg_type_infer_typ_complete_lit], at [Type⟨t⟩]
    [alg_type_infer_typ_complete_tm]. *)
Corollary alg_type_infer_typ_complete : forall {Γ T A},
    user_exp A ->
    univ_term T ->
    Γ ⊢ A : T ->
    exists u v, nbe_ty_f Γ T (universe_nf_to_nf u) /\ Γ ⊢a A ⟹ universe_nf_to_nf v /\ universe_nf_le v u.
Proof.
  intros * HA HT HAT.
  pose proof (alg_type_check_complete HA HAT) as Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' B' Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  destruct (nbe_ty_univ_term HT Hnbe2) as [u ->].
  destruct (alg_subtyping_nf_univ_inv _ _ Hnfsub) as (v & -> & Hle).
  exists u, v; split; [ exact Hnbe2 | split; [ exact Hinfer | exact Hle ] ].
Qed.

Corollary alg_type_infer_large_typ_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ universe_nf_le u (universe_large i).
Proof.
  intros * HA HAi.
  destruct (alg_type_infer_typ_complete HA (univ_term_typ i) HAi) as (u & v & Hu & Hinf & Hle).
  apply nbe_ty_typ_univ_nf in Hu as ->.
  exists (universe_nf_to_nf v), v; split; [ exact Hinf | split; [ apply is_univ_nf_univ_nf | exact Hle ] ].
Qed.

Hint Resolve alg_type_infer_large_typ_complete : mctt.

(** At a literal small universe, with the old precise shape: the inferred
    universe is a small universe at a literal level below [n] (an atom is
    never below a literal, [lvl_le_lit_closed]). *)
Corollary alg_type_infer_typ_complete_lit : forall {Γ n A},
    user_exp A ->
    Γ ⊢ A : Type@n ->
    exists m, Γ ⊢a A ⟹ Typeⁿ@m /\ m <= n.
Proof.
  intros * HA HAn.
  destruct (alg_type_infer_typ_complete HA (univ_term_suniv _) HAn) as (u & v & Hu & Hinf & Hle).
  apply nbe_ty_lit_univ_nf in Hu as ->.
  destruct v as [[c xs] | i]; cbn in Hle; [| contradiction].
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs; cbn in Hxs; subst xs.
  rewrite lvl_le_correct in Hle; specialize (Hle _ lvl_adm_zero); unfold lvl_eval, lvl_lit in Hle; cbn in Hle.
  destruct c as [a m]; assert (a = 0) as -> by ordinal_solve.
  exists m; split; [ exact Hinf | ordinal_solve ].
Qed.

(** At a level term [t]: the inferred universe is small, at a canonical
    level below the normal form of [t]. *)
Corollary alg_type_infer_typ_complete_tm : forall {Γ t A},
    user_exp A ->
    Γ ⊢ A : Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_f Γ t Level (nf_lvl_of L') /\ lvl_le L L'.
Proof.
  intros * HA HAt.
  destruct (alg_type_infer_typ_complete HA (univ_term_suniv _) HAt) as (u & v & Hu & Hinf & Hle).
  destruct (nbe_ty_suniv_univ_nf Hu) as (L' & -> & HL').
  destruct v as [L | i]; cbn in Hle; [| contradiction].
  exists L, L'; split; [ exact Hinf | split; [ exact HL' | exact Hle ] ].
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
