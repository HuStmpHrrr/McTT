(** * The Types the Checkers Normalize

    Each rule of a checker that normalizes a type, or checks a term
    against one, normalizes a type: these are types, by the soundness of
    the premises before.  [Extraction.Checker.TypeCheck] and
    [Reference.TypeCheck] both use them. *)

From Stdlib Require Import List ListDec Morphisms_Relations String.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing Strengthening.
From Mctt.Core Require Import Base.
From Mctt.Core Require Import Consequences.Inversions Semantic.Realizability.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Syntactic.System.Global Require Import MemberTyping.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
Context {GC : GCtx}.

Section Facts.
  (** The universe above a small universe *)
  Lemma typ_succl_univ : forall G M n, ⊢ G -> G ⊢a M ⟹ Levelⁿ@n -> G ⊢ᵗ Type⟨succl M⟩.
  Proof.
    intros * HG HM; pose proof (alg_type_infer_sound HM HG) as HMl; cbn [nf_to_exp] in HMl.
    exact (wf_type_of_sort _ (type_sort_universe 0) (wf_univ_large_tm HG (wf_succl _ _ _ _ _ HMl))).
  Qed.

  (** A domain of a kind extends the context. *)
  Lemma ctx_ass_of_sort : forall G A UA κ u, ⊢ G -> G ⊢a A ⟹ UA -> is_sort_nf UA κ u -> ⊢ G ▹{κ} A.
  Proof.
    intros * HG HA Hs.
    eapply wf_ctx_extend; [ exact (sort_typed_of_is_sort_nf (alg_type_infer_sound HA HG) Hs) | apply sort_kind_abs_kind_sort ].
  Qed.

  (** A proposition is a type. *)
  Lemma typ_of_prop : forall G P, ⊢ G -> G ⊢a P ⟹ Propⁿ -> G ⊢ᵗ P.
  Proof. intros * HG HP; exact (wf_type_of_sort _ type_sort_prop (alg_type_infer_sound HP HG)). Qed.

  (** A conjunction of propositions is a proposition. *)
  Lemma typ_and_prop : forall G P Q, ⊢ G -> G ⊢a P ⟹ Propⁿ -> G ▹{ak_propositional} P ⊢a Q ⟹ Propⁿ ->
      G ⊢ Σₚ P Q : Propₘ.
  Proof.
    intros * HG HP HQ.
    pose proof (alg_type_infer_sound HP HG) as HP'; cbn [nf_to_exp] in HP'.
    assert (HGP : ⊢ G ▹{ak_propositional} P) by (eapply wf_ctx_extend; [ exact HP' | constructor ]).
    pose proof (alg_type_infer_sound HQ HGP) as HQ'; cbn [nf_to_exp] in HQ'.
    apply wf_and; assumption.
  Qed.

  (** The second part of a conjunction, at a proof of its first *)
  Lemma typ_and_inst : forall G P Q M, ⊢ G -> G ⊢a P ⟹ Propⁿ -> G ▹{ak_propositional} P ⊢a Q ⟹ Propⁿ ->
      G ⊢a M ⟸ P -> G ⊢ᵗ Q[Id,,M].
  Proof.
    intros * HG HP HQ HM.
    pose proof (alg_type_infer_sound HP HG) as HP'; cbn [nf_to_exp] in HP'.
    assert (HGP : ⊢ G ▹{ak_propositional} P) by (eapply wf_ctx_extend; [ exact HP' | constructor ]).
    pose proof (alg_type_infer_sound HQ HGP) as HQ'; cbn [nf_to_exp] in HQ'.
    pose proof (alg_type_check_sound_sort HM HG type_sort_prop HP') as HM'.
    exact (wf_type_of_sort _ type_sort_prop
             (sub_preserves_sort _ _ _ _ _ _ _ HQ' type_sort_prop (wf_sub_single _ _ _ _ _ _ _ HP' ltac:(constructor) HM'))).
  Qed.

  (** The type of the second component of a proof of a conjunction *)
  Lemma typ_right : forall G M P Q, ⊢ G -> G ⊢a M ⟹ Σₚⁿ P Q -> G ⊢ᵗ (nf_to_exp Q)[Id,,a_left M].
  Proof.
    intros * HG HMi.
    pose proof (alg_type_infer_sound HMi HG) as HM; cbn [nf_to_exp] in HM.
    pose proof (and_typed_of_proof HM) as HPQ.
    destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _].
    assert (HL : G ⊢ a_left M : nf_to_exp P) by (eapply wf_left; eassumption).
    exact (wf_type_of_sort _ type_sort_prop
             (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ _ HP ltac:(constructor) HL))).
  Qed.

  (** The sort of a [Π]: the join of its parts' universes, [Prop] or
      [LevelSort] *)
  Lemma typ_pi_join : forall G A B UA UB UB' κd κc u v, ⊢ G ->
      G ⊢a A ⟹ UA -> is_sort_nf UA κd u -> G ▹{κd} A ⊢a B ⟹ UB ->
      nbe_ty_f (G ▹{κd} A) UB UB' -> is_sort_nf UB' κc v ->
      G ⊢ᵗ abs_kind_sort κc (universe_nf_pi_tm u v).
  Proof.
    intros * HG HA Hs HB HnB Hv.
    destruct Hv as [UB0 v0 Hv | |]; cbn [abs_kind_sort].
    - destruct (alg_pi_parts_sound HG HA Hs HB HnB Hv) as (HAd & HB' & Hvw).
      destruct (wf_universe_nf_pi_tm HAd HB' Hvw) as [k Hk].
      exact (wf_type_of_sort _ (type_sort_universe k) Hk).
    - exact (wf_type_of_sort _ (type_sort_universe 0) (wf_prop_large (i := 0) HG)).
    - exact (wf_type_level_sort HG).
  Qed.

  (** The domain of the type a function infers *)
  Lemma typ_pi_dom : forall G M κd κc A B, ⊢ G -> G ⊢a M ⟹ nf_pi κd κc A B -> G ⊢ᵗ A.
  Proof.
    intros * HG HMi.
    pose proof (alg_type_infer_sound HMi HG) as HM; cbn [nf_to_exp] in HM.
    destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (S & _ & HPi).
    destruct (wf_pi_parts HPi) as (_ & (SA & HSAk & HA) & _).
    exact (wf_type_of_sort _ (sort_kind_type_sort _ _ HSAk) HA).
  Qed.

  (** Its codomain, at a checked argument *)
  Lemma typ_app_cod : forall G M N κd κc A B, ⊢ G -> G ⊢a M ⟹ nf_pi κd κc A B -> G ⊢a N ⟸ A ->
      G ⊢ᵗ (nf_to_exp B)[Id,,N].
  Proof.
    intros * HG HMi HN.
    pose proof (alg_type_infer_sound HMi HG) as HM; cbn [nf_to_exp] in HM.
    destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (S & _ & HPi).
    destruct (wf_pi_parts HPi) as (_ & (SA & HSAk & HA) & (iU & HBr)).
    pose proof (alg_type_check_sound_sort HN HG (sort_kind_type_sort _ _ HSAk) HA) as HN'.
    pose proof (type_sort_kind_universe κc iU) as HSB.
    exact (wf_type_of_sort _ HSB (sub_preserves_sort _ _ _ _ _ _ _ HBr HSB (wf_sub_single _ _ _ _ _ _ _ HA HSAk HN'))).
  Qed.

  (** A local definition extends the context. *)
  Lemma ctx_def_of_check : forall G A M UA r u, ⊢ G -> G ⊢a A ⟹ UA -> is_sort_nf UA r u -> G ⊢a M ⟸ A ->
      ⊢ G ▸ A ≔ M.
  Proof.
    intros * HG HA Hs HM.
    pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HA HG) Hs) as HAs.
    pose proof (type_sort_kind_universe r (universe_nf_large_index u)) as HSA.
    eapply wf_ctx_extend_def; [ exact HAs | exact HSA | exact (alg_type_check_sound_sort HM HG HSA HAs) ].
  Qed.

  (** The type of the body of a [let], at the definiens *)
  Lemma typ_let_inst : forall G A M B UA r u (C : nf) κC, ⊢ G -> G ⊢a A ⟹ UA -> is_sort_nf UA r u -> G ⊢a M ⟸ A ->
      G ▸ A ≔ M ⊢a B ⟹ C -> nf_to_exp C <> LevelSort -> nbe_ty_kind (G ▸ A ≔ M) C κC ->
      G ⊢ᵗ (nf_to_exp C)[Id,,M].
  Proof.
    intros * HG HA Hs HM HB HnL Hk.
    pose proof (ctx_def_of_check _ _ _ _ _ _ HG HA Hs HM) as HGd.
    pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HA HG) Hs) as HAs.
    pose proof (type_sort_kind_universe r (universe_nf_large_index u)) as HSA.
    pose proof (alg_type_check_sound_sort HM HG HSA HAs) as HM'.
    destruct (typed_at_kind_of_nbe (alg_type_infer_sound HB HGd) HnL Hk) as [k HC].
    pose proof (type_sort_kind_universe κC k) as HSC.
    exact (wf_type_of_sort _ HSC (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_def _ _ _ _ _ _ HAs HSA HM'))).
  Qed.

  (** The type of the body of a module [let], at the unit *)
  Lemma typ_let_mod_inst : forall G U B (C : nf) κC, ⊢ G -> G ⊢aᵘ U ->
      G ▹ₘ U ⊢a B ⟹ C -> nf_to_exp C <> LevelSort -> nbe_ty_kind (G ▹ₘ U) C κC ->
      G ⊢ᵗ (nf_to_exp C)[Id ,,ₘ me_lit U].
  Proof.
    intros * HG HU HB HnL Hk.
    pose proof (alg_unit_sound HU HG) as HU'.
    assert (HGU : ⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU').
    destruct (typed_at_kind_of_nbe (alg_type_infer_sound HB HGU) HnL Hk) as [k HC].
    pose proof (type_sort_kind_universe κC k) as HSC.
    exact (wf_type_of_sort _ HSC (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_mod _ _ _ _ HU'))).
  Qed.

  (** A local definition with a module part extends the context: its type
      of a large universe, its definiens checked against it, its unit an
      alias under no parameters. *)
  Lemma ctx_dm_of_check : forall G A M E UA u, ⊢ G -> G ⊢a A ⟹ UA -> is_univ_nf UA u -> G ⊢a M ⟸ A ->
      G ⊢aᵘ gu_mk nil (md_alias E) -> ⊢ G ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E).
  Proof.
    intros * HG HA Hu HM HU.
    assert (HAu : G ⊢ A : Typeω@(universe_nf_large_index u))
      by (apply wf_exp_universe_nf_large_index; rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
          exact (alg_type_infer_sound HA HG)).
    eapply wf_ctx_extend_dm;
      [ exact HAu | exact (alg_type_check_sound_sort HM HG (type_sort_universe _) HAu) | exact (alg_unit_sound HU HG) ].
  Qed.

  (** The type of the body of a local definition with a module part, at
      the definiens and the unit *)
  Lemma typ_let_dm_inst : forall G A M E B UA u (C : nf) κC, ⊢ G -> G ⊢a A ⟹ UA -> is_univ_nf UA u -> G ⊢a M ⟸ A ->
      G ⊢aᵘ gu_mk nil (md_alias E) ->
      G ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊢a B ⟹ C -> nf_to_exp C <> LevelSort ->
      nbe_ty_kind (G ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) C κC ->
      G ⊢ᵗ (nf_to_exp C)[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))].
  Proof.
    intros * HG HA Hu HM HU HB HnL Hk.
    pose proof (ctx_dm_of_check _ _ _ _ _ _ HG HA Hu HM HU) as HGd.
    assert (HAu : G ⊢ A : Typeω@(universe_nf_large_index u))
      by (apply wf_exp_universe_nf_large_index; rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
          exact (alg_type_infer_sound HA HG)).
    pose proof (alg_type_check_sound_sort HM HG (type_sort_universe _) HAu) as HM'.
    destruct (typed_at_kind_of_nbe (alg_type_infer_sound HB HGd) HnL Hk) as [k HC].
    pose proof (type_sort_kind_universe κC k) as HSC.
    exact (wf_type_of_sort _ HSC (sub_preserves_sort _ _ _ _ _ _ _ HC HSC
                                    (wf_sub_single_dm _ _ _ _ _ _ _ HAu HM' (alg_unit_sound HU HG)))).
  Qed.

  (** A variable's type *)
  Lemma typ_vlookup : forall G x A, ⊢ G -> G ∋ #x : A -> G ⊢ᵗ A.
  Proof.
    intros * HG Hl; destruct (ctx_lookup_wf_sorted _ _ _ _ _ HG Hl) as (S & HS & HA).
    exact (wf_type_of_sort _ HS HA).
  Qed.

  (** [⊥] is a type. *)
  Lemma typ_False : forall G, ⊢ G -> G ⊢ᵗ ⊥.
  Proof. intros * HG; exact (wf_type_of_sort _ type_sort_prop (wf_False _ _ _ HG)). Qed.

  (** The outermost parameter of a checked module expression is a type
      ([mtele_head_wf]). *)
  Lemma typ_mtele_head : forall G M R T B T1, ⊢ G -> G ⊢aᵐ M -> mdenote gc_deps gc_stack G M R ->
      mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> G ⊢ᵗ B.
  Proof.
    intros * HG HM Hm Ht Hv.
    destruct (mtele_head_wf _ _ _ _ _ _ (alg_modexp_sound HM HG) Hm Ht Hv) as (S & HS & HB).
    exact (wf_type_of_sort _ (evaluated_sort_type_sort _ HS) HB).
  Qed.
End Facts.

End Fixed_GCtx.
