From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing Strengthening.
From Mctt.Core Require Import Base.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import FastDomain Evaluation Readback NbE PseudoMonadic Subtyping MemberType AppSpine.
From Mctt.Extraction Require Export TypeCheckBase.
From Mctt.Extraction Require Import IndCheck RecordCheck.
Import Domain_Notations Wk_Notations Fixed_Notations.
From Mctt.Extraction Require Import FastEval FastRead Simulation.

(** The checker evaluates with the skip on ([Extraction.NbE]). *)
#[local] Existing Instance skip_on_mode.

(** * The Checker

    The direct implementation of the algorithmic judgments, rule by rule,
    but for applications: an application keeps the type of its head as a
    value along its spine of arguments, and falls back to normalizing the
    instantiated codomain [B[Id,,N]] of the head's type where a readback
    has a proof in it (the application spine, below); [Reference.TypeCheck]
    is the checker that normalizes at every argument, and
    [Reference.TypeCheckAgreement] shows the two infer one type.  A check
    normalizes both types it compares
    ([subtyping_env_impl]).  Every normalization is at the initial
    environment of its context, which the checker carries
    ([checker_env]) and extends under binders. *)

Section Fixed_GCtx.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

(** ** The Types the Rules Normalize

    Each rule that normalizes a type, or checks a term against one,
    normalizes a type: these are types, by the soundness of the premises
    before. *)
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

  (** The type of an application, as the spine keeps it: a value related
      to the value of the inferred normal form at the initial environment
      ([Extraction.AppSpine]). *)
  #[warnings="-cannot-define-projection"]
  Record spine_value_of (G : ctx) (M : exp) (ρ : env) (v : domain) : Prop := mk_spine_value_of
    { (** The inferred type *)
      spine_value_type : nf
      (** It is inferred *)
    ; spine_value_infer : G ⊢a M ⟹ spine_value_type
      (** Its value at the initial environment *)
    ; spine_value_type_value : domain
      (** It evaluates to it *)
    ; spine_value_type_eval : ⟦ nf_to_exp spine_value_type ⟧ ρ ↘ spine_value_type_value
      (** The universe the two are related in *)
    ; spine_value_index : nat
      (** The spine's value is related to it *)
    ; spine_value_related : Dom v ≈ spine_value_type_value ∈ per_univ spine_value_index }.

  (** One step of the spine: from the value [Π] of the type of [M], a
      domain that reads back proof-free, against which [N] checks, the
      codomain at the value of [N] is the value of the type of [M N]. *)
  Lemma alg_spine_step : forall G M N ρ κd a ρ' B' A' n b,
      ⊢ G -> initial_env_f G ρ ->
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') ->
      Rtyp a in List.length G ↘ A' -> nf_proof_free A' -> evaluated_kind (domain_kind a) ->
      G ⊢a N ⟸ A' -> ⟦ N ⟧ ρ ↘ n -> ⟦ B' ⟧ ρ' ↦ n ⦂ entry_type_value a ↘ b ->
      spine_value_of G (M $ N) ρ b.
  Proof.
    intros * HG Hρ [W HMi t Ht i Hrel] HA' Hpf Hk HNc Hn Hb.
    assert (HN : nf_normal_at G W) by (intros X HX; exact (alg_type_infer_normal HG HMi HX)).
    destruct (spine_type_pi_of_related _ _ _ _ _ _ _ _ _ HN Hρ Ht Hrel) as [A B a0 -> Ha0 -> HAA].
    pose proof (proj1 nf_ne_proof_free_eq _ Hpf _ (HAA _ HA')) as <-.
    destruct (nbe_ty_exists_wf_type (typ_app_cod _ _ _ _ _ _ _ HG HMi HNc)) as [W1 HW1].
    pose proof (alg_type_infer_sound HMi HG) as HM; cbn [nf_to_exp] in HM.
    destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (S & _ & HPi).
    destruct (wf_pi_parts HPi) as (_ & (SA & HSAk & HAt) & _).
    pose proof (alg_type_check_sound_sort HNc HG (sort_kind_type_sort _ _ HSAk) HAt) as HN'.
    destruct (spine_step_related _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPi HN' Hρ Ht Hrel Hk Hn HW1) as [b' Hb' w Hw j Hbw].
    functional_eval_rewrite_clear.
    exact (mk_spine_value_of _ _ _ _ W1 (alg_type_infer_app _ _ _ _ _ _ _ _ HMi HNc HW1) w Hw j Hbw).
  Qed.

  (** The start of the spine: the value of an inferred type that is no
      [LevelSort]. *)
  Lemma alg_spine_start : forall G M W ρ t,
      ⊢ G -> G ⊢a M ⟹ W -> nf_to_exp W <> LevelSort -> initial_env_f G ρ -> ⟦ nf_to_exp W ⟧ ρ ↘ t ->
      spine_value_of G M ρ t.
  Proof.
    intros * HG HMi HnL Hρ Ht.
    destruct (presup_exp_typ_sorted (alg_type_infer_sound HMi HG) HnL) as (S & HS & HW).
    destruct (spine_start_related _ _ _ _ _ HS HW Hρ Ht) as [i Hi].
    exact (mk_spine_value_of _ _ _ _ W HMi t Ht i Hi).
  Qed.

  (** The end of the spine: a proof-free readback of its value is the
      inferred type ([nf_ne_proof_free_eq]). *)
  Lemma alg_spine_end : forall G M ρ v W',
      ⊢ G -> initial_env_f G ρ -> spine_value_of G M ρ v ->
      Rtyp v in List.length G ↘ W' -> nf_proof_free W' -> G ⊢a M ⟹ W'.
  Proof.
    intros * HG Hρ [W HMi t Ht i Hrel] Hr Hpf.
    assert (HN : nf_normal_at G W) by (intros X HX; exact (alg_type_infer_normal HG HMi HX)).
    pose proof (spine_readback_upto_proofs _ _ _ _ _ _ _ HN Hρ Ht Hrel Hr) as HE.
    rewrite (proj1 nf_ne_proof_free_eq _ Hpf _ HE); exact HMi.
  Qed.

  (** A spine's value reads back. *)
  Lemma spine_value_reads : forall G M ρ v s, spine_value_of G M ρ v -> exists W, Rtyp v in s ↘ W.
  Proof. intros * [W _ t _ i Hrel]; exact (per_univ_readback_exists _ _ _ _ Hrel). Qed.

  (** The domain of a spine's [Π] value reads back. *)
  Lemma spine_value_domain_reads : forall G M ρ κd a ρ' B' s,
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') -> exists A, Rtyp a in s ↘ A.
  Proof.
    intros * [W _ t _ i Hrel]; exact (proj1 (per_univ_pi_domain _ _ _ _ _ _ s Hrel)).
  Qed.

  (** The codomain of a spine's [Π] value, at the value of a checked
      argument, evaluates. *)
  Lemma spine_value_codomain_evals : forall G M N ρ κd a ρ' B' A' n,
      ⊢ G -> initial_env_f G ρ ->
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') ->
      Rtyp a in List.length G ↘ A' -> nf_proof_free A' -> evaluated_kind (domain_kind a) ->
      G ⊢a N ⟸ A' -> ⟦ N ⟧ ρ ↘ n ->
      exists b, ⟦ B' ⟧ ρ' ↦ n ⦂ entry_type_value a ↘ b.
  Proof.
    intros * HG Hρ [W HMi t Ht i Hrel] HA' Hpf Hk HNc Hn.
    assert (HN : nf_normal_at G W) by (intros X HX; exact (alg_type_infer_normal HG HMi HX)).
    destruct (spine_type_pi_of_related _ _ _ _ _ _ _ _ _ HN Hρ Ht Hrel) as [A B a0 -> Ha0 -> HAA].
    pose proof (proj1 nf_ne_proof_free_eq _ Hpf _ (HAA _ HA')) as <-.
    destruct (nbe_ty_exists_wf_type (typ_app_cod _ _ _ _ _ _ _ HG HMi HNc)) as [W1 HW1].
    pose proof (alg_type_infer_sound HMi HG) as HM; cbn [nf_to_exp] in HM.
    destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (S & _ & HPi).
    destruct (wf_pi_parts HPi) as (_ & (SA & HSAk & HAt) & _).
    pose proof (alg_type_check_sound_sort HNc HG (sort_kind_type_sort _ _ HSAk) HAt) as HN'.
    destruct (spine_step_related _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPi HN' Hρ Ht Hrel Hk Hn HW1) as [b Hb _ _ _ _].
    exists b; exact Hb.
  Qed.

  (** The value of a checked argument at a domain of an evaluated kind. *)
  Lemma spine_argument_evals : forall G M N ρ κd a ρ' B' A',
      ⊢ G -> initial_env_f G ρ ->
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') ->
      Rtyp a in List.length G ↘ A' -> nf_proof_free A' -> evaluated_kind (domain_kind a) ->
      G ⊢a N ⟸ A' -> exists n, ⟦ N ⟧ ρ ↘ n.
  Proof.
    intros * HG Hρ [W HMi t Ht i Hrel] HA' Hpf Hk HNc.
    assert (HN : nf_normal_at G W) by (intros X HX; exact (alg_type_infer_normal HG HMi HX)).
    destruct (spine_type_pi_of_related _ _ _ _ _ _ _ _ _ HN Hρ Ht Hrel) as [A B a0 -> Ha0 -> HAA].
    pose proof (proj1 nf_ne_proof_free_eq _ Hpf _ (HAA _ HA')) as <-.
    pose proof (alg_type_infer_sound HMi HG) as HM; cbn [nf_to_exp] in HM.
    destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (S & _ & HPi).
    destruct (wf_pi_parts HPi) as (_ & (SA & HSAk & HAt) & _).
    pose proof (alg_type_check_sound_sort HNc HG (sort_kind_type_sort _ _ HSAk) HAt) as HN'.
    pose proof (proj2 (per_univ_pi_domain _ _ _ _ _ _ 0 Hrel) _ _ _ eq_refl) as Ek.
    exact (eval_exists_at_initial_env _ _ _ _ _ HN' Hρ Ha0 ltac:(rewrite Ek; exact Hk)).
  Qed.

  (** A spine's [Π] value whose domain reads back proof-free: the type
      inferred is a [Π] of that domain. *)
  Lemma spine_infer_pi : forall G M ρ κd a ρ' B' A',
      ⊢ G -> initial_env_f G ρ ->
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') ->
      Rtyp a in List.length G ↘ A' -> nf_proof_free A' ->
      exists B, G ⊢a M ⟹ nf_pi κd ak_relevant A' B.
  Proof.
    intros * HG Hρ [W HMi t Ht i Hrel] HA' Hpf.
    assert (HN : nf_normal_at G W) by (intros X HX; exact (alg_type_infer_normal HG HMi HX)).
    destruct (spine_type_pi_of_related _ _ _ _ _ _ _ _ _ HN Hρ Ht Hrel) as [A B a0 -> Ha0 -> HAA].
    pose proof (proj1 nf_ne_proof_free_eq _ Hpf _ (HAA _ HA')) as <-.
    exists B; exact HMi.
  Qed.

  (** The domain the spine checks an argument against is a type. *)
  Lemma spine_domain_type : forall G M ρ κd a ρ' B' A',
      ⊢ G -> initial_env_f G ρ ->
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') ->
      Rtyp a in List.length G ↘ A' -> nf_proof_free A' -> G ⊢ᵗ A'.
  Proof.
    intros * HG Hρ Hs HA' Hpf.
    destruct (spine_infer_pi _ _ _ _ _ _ _ _ HG Hρ Hs HA' Hpf) as [B HMi].
    exact (typ_pi_dom _ _ _ _ _ _ HG HMi).
  Qed.

  (** An application whose head infers no type infers none. *)
  Lemma app_head_failure : forall G M N, (forall A, ~ G ⊢a M ⟹ A) -> forall A, ~ G ⊢a M $ N ⟹ A.
  Proof. intros * Hn A H; inversion H; subst; eapply Hn; eassumption. Qed.

  (** An application whose head infers a type that is no [Π] infers
      none. *)
  Lemma app_not_pi_failure : forall G M N C,
      ⊢ G -> G ⊢a M ⟹ C -> (forall κd κc A B, C <> nf_pi κd κc A B) -> forall A, ~ G ⊢a M $ N ⟹ A.
  Proof.
    intros * HG HC Hn A H; inversion H; subst.
    match goal with H1 : G ⊢a M ⟹ nf_pi _ _ _ _ |- _ =>
      pose proof (functional_alg_type_infer ltac:(gctx_wf_tac) HC H1) as -> end.
    eapply Hn; reflexivity.
  Qed.

  (** An application whose argument does not check against the domain of
      the head's [Π] infers no type. *)
  Lemma app_check_failure : forall G M N κd κc A B,
      ⊢ G -> G ⊢a M ⟹ nf_pi κd κc A B -> ~ G ⊢a N ⟸ A -> forall C, ~ G ⊢a M $ N ⟹ C.
  Proof.
    intros * HG HC Hn C H; inversion H; subst.
    match goal with H1 : G ⊢a M ⟹ nf_pi _ _ _ _ |- _ =>
      pose proof (functional_alg_type_infer ltac:(gctx_wf_tac) HC H1) as E end.
    injection E; intros; subst; contradiction.
  Qed.

  (** The same at the spine's [Π] value. *)
  Lemma spine_check_failure : forall G M N ρ κd a ρ' B' A',
      ⊢ G -> initial_env_f G ρ ->
      spine_value_of G M ρ (d_pi κd ak_relevant a ρ' B') ->
      Rtyp a in List.length G ↘ A' -> nf_proof_free A' ->
      ~ G ⊢a N ⟸ A' -> forall C, ~ G ⊢a M $ N ⟹ C.
  Proof.
    intros * HG Hρ Hs HA' Hpf Hn.
    destruct (spine_infer_pi _ _ _ _ _ _ _ _ HG Hρ Hs HA' Hpf) as [B HMi].
    exact (app_check_failure _ _ _ _ _ _ _ HG HMi Hn).
  Qed.

  (** The orders of the computations of a spine step: the readback of the
      spine's value and of its domain, the argument's value and the
      codomain's at it. *)
  (** ** The Spine, Fast

      The spine computes on fast values with the skip on: its value is
      related ([domain_simulation]) to a value the reference spine keeps
      ([spine_value_of]), at the initial environment the checker's
      environment simulates.  A readback of a fast value is the reference
      one up to proofs, so where it is proof-free it is the reference one,
      and the reference facts above apply. *)

  (** The fast value [v] of the type of [M] *)
  Definition spine_value_sim (G : ctx) (M : exp) (v : fdomain) : Prop :=
    exists ρc v0, initial_env_f G ρc /\ spine_value_of G M ρc v0 /\ domain_simulation gc_deps gc_stack v0 (fdomain_erase v).

  (** The reference spine's [Π] value, at the parts of a fast one *)
  Lemma spine_value_sim_pi : forall G M κd a ρ' B',
      spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      exists ρc a0 ρ0, initial_env_f G ρc /\ spine_value_of G M ρc (d_pi κd ak_relevant a0 ρ0 B') /\
        domain_simulation gc_deps gc_stack a0 (fdomain_erase a) /\
        env_agree gc_deps gc_stack (fun x => ~ exp_fresh (S x) B') ρ0 (fenv_erase ρ').
  Proof.
    intros * (ρc & v0 & Hi & Hs & Hsim); cbn [fdomain_erase] in Hsim; inversion Hsim; subst.
    do 3 eexists; repeat split; eassumption.
  Qed.

  (** The readback of a fast domain proof-free is the reference one. *)
  Lemma spine_domain_reference : forall G M κd a ρ' B' A' s,
      spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      fast_read_typ gc_deps gc_stack s (fdomain_erase a) A' -> nf_proof_freeb A' = true ->
      exists ρc a0 ρ0, initial_env_f G ρc /\ spine_value_of G M ρc (d_pi κd ak_relevant a0 ρ0 B') /\
        domain_simulation gc_deps gc_stack a0 (fdomain_erase a) /\
        env_agree gc_deps gc_stack (fun x => ~ exp_fresh (S x) B') ρ0 (fenv_erase ρ') /\
        Rtyp a0 in s ↘ A'.
  Proof.
    intros * Hs HA' Hpf; destruct (spine_value_sim_pi _ _ _ _ _ _ Hs) as (ρc & a0 & ρ0 & Hi & Hsv & Ha & Hag).
    destruct (spine_value_domain_reads _ _ _ _ _ _ _ s Hsv) as [A0 HA0].
    destruct (fast_read_typ_simulation _ _ _ _ _ _ HA0 Ha) as (W' & HW' & Hup).
    rewrite (functional_fast_read_typ _ _ _ _ HW' HA') in Hup.
    rewrite (eq_of_upto_proof_free _ _ Hup Hpf) in HA0.
    exists ρc, a0, ρ0; repeat split; assumption.
  Qed.

  Lemma spine_value_read_order : forall G M v s,
      spine_value_sim G M v -> fast_read_typ_order gc_deps gc_stack s (fdomain_erase v).
  Proof.
    intros * (ρc & v0 & Hi & Hs & Hsim); destruct (spine_value_reads _ _ _ _ s Hs) as [W HW].
    destruct (fast_read_typ_simulation _ _ _ _ _ _ HW Hsim) as (W' & HW' & _).
    exact (fast_read_typ_order_sound _ _ _ _ _ HW').
  Qed.

  Lemma spine_domain_read_order : forall G M κd a ρ' B' s,
      spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') -> fast_read_typ_order gc_deps gc_stack s (fdomain_erase a).
  Proof.
    intros * Hs; destruct (spine_value_sim_pi _ _ _ _ _ _ Hs) as (ρc & a0 & ρ0 & Hi & Hsv & Ha & Hag).
    destruct (spine_value_domain_reads _ _ _ _ _ _ _ s Hsv) as [W HW].
    destruct (fast_read_typ_simulation _ _ _ _ _ _ HW Ha) as (W' & HW' & _).
    exact (fast_read_typ_order_sound _ _ _ _ _ HW').
  Qed.

  (** The start of the spine *)
  Lemma alg_spine_start_fast : forall G M W ρ t,
      ⊢ G -> G ⊢a M ⟹ W -> nf_to_exp W <> LevelSort -> fast_env_simulates gc_deps gc_stack G ρ ->
      fast_eval_exp gc_deps gc_stack (nf_to_exp W) (fenv_erase ρ) (fdomain_erase t) -> spine_value_sim G M t.
  Proof.
    intros * HG HMi HnL (ρc & Hi & Hag) Ht.
    destruct (nbe_ty_exists_wf_type (wf_type_of_infer _ _ _ HG HMi)) as [W0 [ρ1 t0 Hi1 Ht0 _]].
    pose proof (functional_initial_env _ _ Hi1 _ Hi) as ->.
    exists ρc, t0; repeat split; [ exact Hi | exact (alg_spine_start _ _ _ _ _ HG HMi HnL Hi Ht0) |].
    exact (fast_eval_value_of_core _ _ _ _ _ _ _ Ht0 Hag Ht).
  Qed.

  Lemma spine_start_order : forall G M W ρ, ⊢ G -> G ⊢a M ⟹ W -> fast_env_simulates gc_deps gc_stack G ρ ->
      fast_eval_exp_order gc_deps gc_stack (nf_to_exp W) (fenv_erase ρ).
  Proof.
    intros * HG HMi Hs; destruct (nbe_ty_exists_wf_type (wf_type_of_infer _ _ _ HG HMi)) as [W0 HW0].
    exact (nbe_ty_eval_order _ _ _ _ _ (nbe_ty_order_sound _ _ _ _ _ HW0) Hs).
  Qed.

  (** The domain the spine checks an argument against is a type. *)
  Lemma spine_domain_type_fast : forall G M κd a ρ' B' A',
      ⊢ G -> spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      fast_read_typ gc_deps gc_stack (List.length G) (fdomain_erase a) A' -> nf_proof_freeb A' = true -> G ⊢ᵗ A'.
  Proof.
    intros * HG Hs HA' Hpf; destruct (spine_domain_reference _ _ _ _ _ _ _ _ Hs HA' Hpf) as (ρc & a0 & ρ0 & Hi & Hsv & _ & _ & HA0).
    exact (spine_domain_type _ _ _ _ _ _ _ _ HG Hi Hsv HA0 (proj1 (proj1 nf_proof_freeb_iff _) Hpf)).
  Qed.

  Lemma spine_check_failure_fast : forall G M N κd a ρ' B' A',
      ⊢ G -> spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      fast_read_typ gc_deps gc_stack (List.length G) (fdomain_erase a) A' -> nf_proof_freeb A' = true ->
      ~ G ⊢a N ⟸ A' -> forall C, ~ G ⊢a M $ N ⟹ C.
  Proof.
    intros * HG Hs HA' Hpf Hn; destruct (spine_domain_reference _ _ _ _ _ _ _ _ Hs HA' Hpf) as (ρc & a0 & ρ0 & Hi & Hsv & _ & _ & HA0).
    exact (spine_check_failure _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 (proj1 (proj1 nf_proof_freeb_iff _) Hpf) Hn).
  Qed.

  (** The argument and the codomain at it: their values, fast, are
      related to the reference ones. *)
  Lemma spine_argument_order : forall G M N ρ κd a ρ' B' A',
      ⊢ G -> fast_env_simulates gc_deps gc_stack G ρ -> spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      fast_read_typ gc_deps gc_stack (List.length G) (fdomain_erase a) A' -> nf_proof_freeb A' = true ->
      evaluated_kind (fdomain_kind a) -> G ⊢a N ⟸ A' -> fast_eval_exp_order gc_deps gc_stack N (fenv_erase ρ).
  Proof.
    intros * HG (ρc' & Hi' & Hag) Hs HA' Hpf Hk HNc.
    destruct (spine_domain_reference _ _ _ _ _ _ _ _ Hs HA' Hpf) as (ρc & a0 & ρ0 & Hi & Hsv & Ha & _ & HA0).
    pose proof (functional_initial_env _ _ Hi' _ Hi) as ->.
    destruct (spine_argument_evals _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 (proj1 (proj1 nf_proof_freeb_iff _) Hpf)
                ltac:(rewrite (fast_kind_of_core _ _ _ _ Ha); exact Hk) HNc) as [n Hn].
    eapply fast_eval_order_of_core; eassumption.
  Qed.

  Lemma spine_codomain_order : forall G M N ρ κd a ρ' B' A' n,
      ⊢ G -> fast_env_simulates gc_deps gc_stack G ρ -> spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      fast_read_typ gc_deps gc_stack (List.length G) (fdomain_erase a) A' -> nf_proof_freeb A' = true ->
      evaluated_kind (fdomain_kind a) -> G ⊢a N ⟸ A' ->
      fast_eval_exp gc_deps gc_stack N (fenv_erase ρ) (fdomain_erase n) ->
      fast_eval_exp_order gc_deps gc_stack B' (fenv_erase (fextend_env ρ' n (fentry_type_value a))).
  Proof.
    intros * HG (ρc' & Hi' & Hag) Hs HA' Hpf Hk HNc Hn.
    destruct (spine_domain_reference _ _ _ _ _ _ _ _ Hs HA' Hpf) as (ρc & a0 & ρ0 & Hi & Hsv & Ha & Hagc & HA0).
    pose proof (functional_initial_env _ _ Hi' _ Hi) as ->.
    pose proof (proj1 (proj1 nf_proof_freeb_iff _) Hpf) as Hpf'.
    assert (Hk0 : evaluated_kind (domain_kind a0)) by (rewrite (fast_kind_of_core _ _ _ _ Ha); exact Hk).
    destruct (spine_argument_evals _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 Hpf' Hk0 HNc) as [n0 Hn0].
    destruct (spine_value_codomain_evals _ _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 Hpf' Hk0 HNc Hn0) as [b Hb].
    rewrite fextend_env_erase.
    destruct (fast_eval_clo_sim _ _ _ _ _ _ _ (entry_type_value a0) (fentry_type_erase (fentry_type_value a)) _ Hagc
                (fast_eval_value_of_core _ _ _ _ _ _ _ Hn0 Hag Hn) Hb) as (b' & Hb' & _).
    exact (fast_eval_exp_order_sound _ _ _ _ _ Hb').
  Qed.

  (** One step of the spine *)
  Lemma alg_spine_step_fast : forall G M N ρ κd a ρ' B' A' n b,
      ⊢ G -> fast_env_simulates gc_deps gc_stack G ρ -> spine_value_sim G M (fd_pi κd ak_relevant a ρ' B') ->
      fast_read_typ gc_deps gc_stack (List.length G) (fdomain_erase a) A' -> nf_proof_freeb A' = true ->
      evaluated_kind (fdomain_kind a) -> G ⊢a N ⟸ A' ->
      fast_eval_exp gc_deps gc_stack N (fenv_erase ρ) (fdomain_erase n) ->
      fast_eval_exp gc_deps gc_stack B' (fenv_erase (fextend_env ρ' n (fentry_type_value a))) (fdomain_erase b) ->
      spine_value_sim G (M $ N) b.
  Proof.
    intros * HG (ρc' & Hi' & Hag) Hs HA' Hpf Hk HNc Hn Hb.
    destruct (spine_domain_reference _ _ _ _ _ _ _ _ Hs HA' Hpf) as (ρc & a0 & ρ0 & Hi & Hsv & Ha & Hagc & HA0).
    pose proof (functional_initial_env _ _ Hi' _ Hi) as ->.
    pose proof (proj1 (proj1 nf_proof_freeb_iff _) Hpf) as Hpf'.
    assert (Hk0 : evaluated_kind (domain_kind a0)) by (rewrite (fast_kind_of_core _ _ _ _ Ha); exact Hk).
    destruct (spine_argument_evals _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 Hpf' Hk0 HNc) as [n0 Hn0].
    destruct (spine_value_codomain_evals _ _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 Hpf' Hk0 HNc Hn0) as [b0 Hb0].
    rewrite fextend_env_erase in Hb.
    destruct (fast_eval_clo_sim _ _ _ _ _ _ _ (entry_type_value a0) (fentry_type_erase (fentry_type_value a)) _ Hagc
                (fast_eval_value_of_core _ _ _ _ _ _ _ Hn0 Hag Hn) Hb0) as (b' & Hb' & Hsb).
    rewrite <- (functional_fast_eval_exp _ _ _ _ Hb Hb') in Hsb.
    exists ρc, b0; repeat split; [ exact Hi | exact (alg_spine_step _ _ _ _ _ _ _ _ _ _ _ HG Hi Hsv HA0 Hpf' Hk0 HNc Hn0 Hb0) | exact Hsb ].
  Qed.

  (** The end of the spine: a proof-free readback of its value *)
  Lemma alg_spine_end_fast : forall G M v W',
      ⊢ G -> spine_value_sim G M v ->
      fast_read_typ gc_deps gc_stack (List.length G) (fdomain_erase v) W' -> nf_proof_freeb W' = true -> G ⊢a M ⟹ W'.
  Proof.
    intros * HG (ρc & v0 & Hi & Hs & Hsim) Hr Hpf.
    destruct (spine_value_reads _ _ _ _ (List.length G) Hs) as [W0 HW0].
    destruct (fast_read_typ_simulation _ _ _ _ _ _ HW0 Hsim) as (W1 & HW1 & Hup).
    rewrite (functional_fast_read_typ _ _ _ _ HW1 Hr) in Hup.
    rewrite (eq_of_upto_proof_free _ _ Hup Hpf) in HW0.
    exact (alg_spine_end _ _ _ _ _ HG Hi Hs HW0 (proj1 (proj1 nf_proof_freeb_iff _) Hpf)).
  Qed.
End Facts.

(** ** The Obligations of the Checker *)

(** The recursive calls of the checker in the context of its obligations:
    the functions over contexts that return a decision or an inference.
    The obligations never use them. *)
Ltac clear_defs :=
  repeat match goal with
    | H : _ |- _ =>
        lazymatch type of H with
        | context [ fixproto ] => clear H
        | forall _ : ctx, _ =>
            lazymatch type of H with
            | context [ sumbool ] => clear H
            | context [ sumor ] => clear H
            end
        end
    end.

(** Two descriptions of one module expression, or two generated entries of
    one open, are one ([mdenote_functional_all]), and so are two values of
    one function. *)
#[local]
Ltac md_unify :=
  repeat match goal with
    | H1 : mdenote ?T ?X ?G ?M ?R1, H2 : mdenote ?T ?X ?G ?M ?R2 |- _ =>
        assert_fails (constr_eq R1 R2);
        let Hg := fresh "Hg" in
        assert (Hg : ⊢ᵍ T ⍮ X) by gctx_wf_tac;
        pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ H1 _ H2); subst R2; clear H2 Hg
    | H1 : items_gen ?T ?X ?G ?M ?its ?A1, H2 : items_gen ?T ?X ?G ?M ?its ?A2 |- _ =>
        assert_fails (constr_eq A1 A2);
        let Hg := fresh "Hg" in
        assert (Hg : ⊢ᵍ T ⍮ X) by gctx_wf_tac;
        pose proof (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ _ H1 _ H2); subst A2; clear H2 Hg
    | H1 : ?f = Some ?a, H2 : ?f = Some ?b |- _ =>
        assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
    | H1 : ?f = Some _, H2 : ?f = None |- _ => rewrite H1 in H2; discriminate H2
    end.

(** One kind and universe of each type of a type, one normal form of each
    type and one kind of each type. *)
#[local]
Ltac sort_unify :=
  repeat match goal with
    | H1 : is_sort_nf ?W ?r ?u, H2 : is_sort_nf ?W ?r' ?u' |- _ =>
        assert_fails (constr_eq H1 H2);
        let E1 := fresh "E" in let E2 := fresh "E" in
        destruct (is_sort_nf_functional _ _ _ _ _ H1 H2) as [E1 E2]; clear H2; try subst
    | H1 : is_univ_nf ?W ?u, H2 : is_univ_nf ?W ?u' |- _ =>
        assert_fails (constr_eq H1 H2);
        pose proof (is_univ_nf_functional _ _ _ H1 H2); clear H2; try subst
    | H1 : nbe_ty ?T ?X ?G ?A ?W1, H2 : nbe_ty ?T ?X ?G ?A ?W2 |- _ =>
        assert_fails (constr_eq W1 W2);
        let E := fresh "E" in
        assert (E : W1 = W2) by (eapply functional_nbe_ty; [ exact H1 | exact H2 ]);
        clear H2; try (injection E; clear E; intros); try subst
    | H1 : nbe_ty_kind ?G ?A ?κ1, H2 : nbe_ty_kind ?G ?A ?κ2 |- _ =>
        assert_fails (constr_eq κ1 κ2);
        pose proof (nbe_ty_kind_functional H1 H2); clear H2; try subst
    | H1 : ?G ⊢aᵇ ?Φ ⇝ ?X, H2 : ?G ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
        assert_fails (constr_eq X Y);
        pose proof (alg_body_functional ltac:(gctx_wf_tac) H1 H2); subst Y; clear H2
    end.

(** The order of a subterm: read off the order of the term by inversion,
    at the first stage that has it, so that it is a subterm for the guard
    of the structural recursion. *)
#[local]
Ltac obligation_order :=
  clear_defs;
  try match goal with H : type_check_order _ |- _ => progressive_invert H end;
  first
    [ eassumption
    (** the order of a literal part, one inversion down: inverting further
        would take the literal's own order apart *)
    | solve [ match goal with
              | H : type_infer_order _ |- _ => progressive_invert H
              | H : body_order _ |- _ => progressive_invert H
              | H : ext_order _ |- _ => progressive_invert H
              end; eassumption ]
    | repeat match goal with
        | H : type_infer_order _ |- _ => progressive_invert H
        | H : ext_order _ |- _ => progressive_invert H
        | H : unit_order _ |- _ => progressive_invert H
        | H : body_order _ |- _ => progressive_invert H
        | H : modexp_order _ |- _ => progressive_invert H
        end;
      first
        [ eassumption
        | repeat match goal with H : type_check_order _ |- _ => progressive_invert H end;
          eassumption ] ].

(** The order of a part of an eliminator or of a tuple handed to the
    recursive call its checker makes: an order the term's order holds,
    a subterm of it for the guard. *)
#[local]
Ltac order_part :=
  match goal with
  | H0 : type_infer_order (a_elim _ _ _ _ _ _) |- _ => progressive_invert H0
  | H0 : type_infer_order (a_tuple _ _) |- _ => progressive_invert H0
  end;
  first [ match goal with Hall : forall x, In x _ -> type_check_order _, Hx : In _ _ |- type_check_order _ =>
            exact (Hall _ Hx) end
        | match goal with Hall : forall x y, In x _ -> In y _ -> type_check_order _, Hx : In _ _, Hy : In _ _ |- _ =>
            exact (Hall _ _ Hx Hy) end
        | match goal with Hall : forall x, In x _ -> type_check_order _, Hx : In _ _ |- type_infer_order _ =>
            exact (match Hall _ Hx with type_check_order_ti h => h end) end ].

(** A well-formed context the obligation knows of *)
#[local]
Ltac checker_ctx :=
  lazymatch goal with
  | |- ⊢ ?G =>
      first [ assumption
            | match goal with HA : G ⊢ᵗ _ |- _ => exact (wf_type_ctx _ _ HA) end
            | match goal with HG : ⊢ ?G0, Ha : ?G0 ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA _ _ |- ⊢ ?G0 ▹{_} ?A =>
                exact (ctx_ass_of_sort _ _ _ _ _ HG Ha Hs) end
            | match goal with HG : ⊢ ?G0, Ha : ?G0 ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA _ _, HM : ?G0 ⊢a ?M ⟸ ?A
                |- ⊢ ?G0 ▸ ?A ≔ ?M => exact (ctx_def_of_check _ _ _ _ _ _ HG Ha Hs HM) end
            | match goal with HG : ⊢ ?G0, Ha : ?G0 ⊢a ?A ⟹ Propⁿ |- ⊢ ?G0 ▹{ak_propositional} ?A =>
                exact (ctx_ass_of_sort _ _ _ _ _ HG Ha is_sort_nf_prop) end
            | match goal with HG : ⊢ ?G0, HU : ?G0 ⊢aᵘ ?U |- ⊢ ?G0 ▹ₘ ?U =>
                exact (wf_ctx_extend_mod _ _ _ _ (alg_unit_sound HU HG)) end
            | match goal with HG : ⊢ ?G0, Ha : ?G0 ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA _, HM : ?G0 ⊢a ?M ⟸ ?A,
                HU : ?G0 ⊢aᵘ gu_mk nil (md_alias ?E) |- ⊢ ?G0 ▸ₘ ?A ≔ ?M ‖ gu_mk nil (md_alias ?E) =>
                exact (ctx_dm_of_check _ _ _ _ _ _ HG Ha Hu HM HU) end
            | match goal with HG : ⊢ ?G0, HX : ?G0 ⊢aˣ ?Ψ |- ⊢ ?Ψ ++ ?G0 =>
                exact (ext_eq_ctx_left _ _ _ _ _ (alg_ext_sound HX HG)) end
            | match goal with HG : ⊢ ?G0, HX : ?G0 ⊢aᵖ ?Ψ |- ⊢ ?Ψ ++ ?G0 =>
                exact (ext_eq_ctx_left _ _ _ _ _ (proj1 (alg_params_sound HX HG))) end
            | match goal with HG : ⊢ ?G0, HB : ?G0 ⊢aᵇ ?Φ ⇝ ?Φx |- ⊢ body_ctx ?Φx ++ ?G0 =>
                exact (alg_body_ctx HG HB) end ]
  end.

(** A type the obligation knows of *)
#[local]
Ltac checker_type :=
  lazymatch goal with
  | |- ?G ⊢ᵗ ?X =>
      first [ assumption
            | match goal with HG : ⊢ G |- _ => exact (typ_False _ HG) end
            | match goal with HG : ⊢ G, Ha : G ⊢a X ⟹ ?UA, Hs : is_sort_nf ?UA _ _ |- _ =>
                exact (type_of_sort_infer _ _ _ _ _ HG Ha Hs) end
            | match goal with HG : ⊢ G, Ha : G ⊢a X ⟹ Propⁿ |- _ => exact (typ_of_prop _ _ HG Ha) end
            | match goal with HG : ⊢ G, Ha : G ⊢a X ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
                exact (type_of_sort_infer _ _ _ _ _ HG Ha (is_sort_nf_univ _ _ Hu)) end
            | match goal with HG : ⊢ G, Ha : G ⊢a _ ⟹ ?W |- _ =>
                lazymatch X with nf_to_exp W => exact (wf_type_of_infer _ _ _ HG Ha) end end
            | match goal with HG : ⊢ G, HM : G ⊢a ?M ⟹ Levelⁿ@_ |- _ =>
                lazymatch X with Type⟨succl M⟩ => exact (typ_succl_univ _ _ _ HG HM) end end
            | match goal with HG : ⊢ G, HP : G ⊢a ?P ⟹ Propⁿ, HQ : _ ▹{ak_propositional} ?P ⊢a ?Q ⟹ Propⁿ |- _ =>
                lazymatch X with
                | Σₚ P Q => exact (wf_type_of_sort _ type_sort_prop (typ_and_prop _ _ _ HG HP HQ))
                | Q[Id,,?M] => match goal with HM : G ⊢a M ⟸ P |- _ => exact (typ_and_inst _ _ _ _ HG HP HQ HM) end
                end end
            | match goal with HG : ⊢ G, HM : G ⊢a ?M ⟹ Σₚⁿ _ _ |- _ =>
                lazymatch X with _[Id,,a_left M] => exact (typ_right _ _ _ _ HG HM) end end
            | match goal with HG : ⊢ G, HA : G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?κd ?u, HB : _ ⊢a ?B ⟹ ?UB,
                HnB : nbe_ty _ _ _ (nf_to_exp ?UB) ?UB', Hv : is_sort_nf ?UB' ?κc ?v |- _ =>
                lazymatch X with abs_kind_sort κc (universe_nf_pi_tm u v) =>
                  exact (typ_pi_join _ _ _ _ _ _ _ _ _ _ HG HA Hs HB HnB Hv) end end
            | match goal with HG : ⊢ G, HM : G ⊢a ?M ⟹ nf_pi _ _ ?A ?B |- _ =>
                lazymatch X with
                | nf_to_exp A => exact (typ_pi_dom _ _ _ _ _ _ HG HM)
                | (nf_to_exp B)[Id,,?N] => match goal with HN : G ⊢a N ⟸ _ |- _ => exact (typ_app_cod _ _ _ _ _ _ _ HG HM HN) end
                end end
            | match goal with HG : ⊢ G, HA : G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA _ _, HM : G ⊢a ?M ⟸ ?A,
                HB : _ ⊢a _ ⟹ ?C, HnL : nf_to_exp ?C <> LevelSort, Hk : nbe_ty_kind _ (nf_to_exp ?C) _ |- _ =>
                lazymatch X with (nf_to_exp C)[Id,,M] => exact (typ_let_inst _ _ _ _ _ _ _ _ _ HG HA Hs HM HB HnL Hk) end end
            | match goal with HG : ⊢ G, HU : G ⊢aᵘ ?U, HB : _ ⊢a _ ⟹ ?C, HnL : nf_to_exp ?C <> LevelSort,
                Hk : nbe_ty_kind _ (nf_to_exp ?C) _ |- _ =>
                lazymatch X with (nf_to_exp C)[Id ,,ₘ me_lit U] => exact (typ_let_mod_inst _ _ _ _ _ HG HU HB HnL Hk) end end
            | match goal with HG : ⊢ G, HA : G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA _, HM : G ⊢a ?M ⟸ ?A,
                HU : G ⊢aᵘ gu_mk nil (md_alias ?E), HB : _ ⊢a _ ⟹ ?C, HnL : nf_to_exp ?C <> LevelSort,
                Hk : nbe_ty_kind _ (nf_to_exp ?C) _ |- _ =>
                lazymatch X with (nf_to_exp C)[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))] =>
                  exact (typ_let_dm_inst _ _ _ _ _ _ _ _ _ HG HA Hu HM HU HB HnL Hk) end end
            | match goal with HG : ⊢ G, Hl : G ∋ #_ : X |- _ => exact (typ_vlookup _ _ _ HG Hl) end
            | match goal with HG : ⊢ G, HM : G ⊢aᵐ ?M, Hm : mdenote _ _ G (me_mem ?M _) _, Ht : mdesc_type _ = Some X |- _ =>
                exact (member_typ_of_alg _ _ _ _ _ HG HM Hm Ht) end
            | match goal with HG : ⊢ G, HM : G ⊢aᵐ ?M, Hm : mdenote _ _ G ?M _, Ht : mdesc_mod_tele _ = Some ?T,
                Hv : tele_view ?T = Some (X, _) |- _ => exact (typ_mtele_head _ _ _ _ _ _ HG HM Hm Ht Hv) end ]
  end.

(** The contexts of the types the obligation knows of are well formed. *)
#[local]
Ltac saturate_ctx :=
  repeat match goal with
    | HA : ?G ⊢ᵗ _ |- _ =>
        assert_fails (assert (⊢ G) by assumption); pose proof (wf_type_ctx _ _ HA)
    end.

(** One inferred type of each term: two inferences of one term are made
    one, and the parts of their heads with them. *)
#[local]
Ltac infer_unify :=
  repeat match goal with
    | H1 : ?G ⊢a ?M ⟹ ?A1, H2 : ?G ⊢a ?M ⟹ ?A2 |- _ =>
        assert_fails (constr_eq A1 A2);
        let E := fresh "E" in
        assert (E : A1 = A2) by (eapply functional_alg_type_infer; [ gctx_wf_tac | exact H1 | exact H2 ]);
        clear H2; try (injection E; clear E; intros); try subst
    end.

#[local]
Ltac checker_unify := saturate_ctx; do 3 (infer_unify; md_unify; sort_unify).

(** A failure: the judgment it rules out, the newest hypothesis, inverted
    against the failing premise. *)
#[local]
Ltac checker_failure :=
  clear_defs;
  lazymatch goal with
  | H : ?J |- False =>
      lazymatch J with
      | _ ⊢a _ ⟹ _ => inversion H; subst; clear H
      | _ ⊢a _ ⟸ _ => inversion H; subst; clear H
      | _ ⊢aˣ _ => inversion H; subst; clear H
      | _ ⊢aᵖ _ => inversion H; subst; clear H
      | _ ⊢aᵘ _ => inversion H; subst; clear H
      | _ ⊢aᵐ _ => inversion H; subst; clear H
      | _ ⊢aᵇ _ ⇝ _ => inversion H; subst; clear H
      | _ ⊢a _ ⊆ _ => idtac
      end
  end;
  destruct_conjs;
  checker_unify;
  first [ contradiction
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ]
        | solve [ match goal with HN : forall _ _, ~ _ |- _ => eapply HN; eassumption end ]
        | solve [ match goal with HN : forall _ _, _ <> _ |- _ => eapply HN; reflexivity end ]
        | solve [ match goal with HN : forall _ _ _ _, _ <> _ |- _ => eapply HN; reflexivity end ]
        | solve [ match goal with HN : forall _, _ <> _ |- _ => eapply HN; reflexivity end ]
        | congruence
        | solve [ match goal with Hx : _ ∋ #_ ≔ₘ _ |- _ => apply ctx_find_mod_complete in Hx; congruence end ]
        | solve [ firstorder ] ].


Ltac checker_obligation_core :=
  intros; cbv beta in *; repeat match goal with |- ~ _ => intro end;
  lazymatch goal with
  | |- False => checker_failure
  | |- type_check_order _ => obligation_order
  | |- type_infer_order _ => obligation_order
  | |- ext_order _ => obligation_order
  | |- unit_order _ => obligation_order
  | |- body_order _ => obligation_order
  | |- modexp_order _ => obligation_order
  | |- _ => clear_defs; destruct_conjs; try subst; checker_unify; checker_obligation_positive
  end
with checker_obligation_positive :=
  lazymatch goal with
  | |- ⊢ᵍ _ ⍮ _ => gctx_wf_tac
  | |- ⊢ _ => checker_ctx
  | |- subtyping_order _ _ _ => constructor; apply nbe_order_of_type; checker_type
  | |- nbe_ty_order _ _ _ _ => apply nbe_order_of_type; checker_type
  | |- _ ⊢ᵗ _ => checker_type
  (** a body under no parameter, checked: a unit *)
  | |- _ ⍮ _ ⍮ _ ⊢ᵐ me_lit (gu_open nil _) ≈ _ =>
      eapply alg_modexp_sound;
        [ apply alg_modexp_lit; eapply alg_unit_body;
          [ constructor | constructor | eassumption | assumption | assumption | assumption | left; let D := fresh "D" in let Ed := fresh "Ed" in intros D ? ? ? Ed; destruct D; discriminate ]
        | checker_ctx ]
  | |- _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _ => eapply alg_modexp_sound; [ eassumption | checker_ctx ]
  | |- _ ⊢aᵐ me_var _ => econstructor; apply ctx_find_mod_sound; eassumption
  | |- _ ⊢aᵇ _ ⇝ _ /\ ⊢ _ =>
      split; [ econstructor; first [ eassumption | reflexivity ]
             | first [ checker_ctx | eapply alg_body_ctx; [ checker_ctx | econstructor; first [ eassumption | reflexivity ] ] ] ]
  | |- _ => first [ solve [ econstructor; first [ eassumption | reflexivity ] ] | solve [ mauto 3 ] ]
  end.

(** An obligation as it is posed, or after the simplification
    [Next Obligation] makes *)
Ltac checker_obligation :=
  first [ solve [ checker_obligation_core ] | solve [ program_simplify; checker_obligation_core ] ].

Section type_check.
  (** The decision of [levels_abstractable], given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Δ ++ G -> gc_deps ⍮ gc_stack ⍮ Δ ++ G ⊢ᵐ E ≈ E ->
      { levels_abstractable gc_deps gc_stack G Δ E } + { ~ levels_abstractable gc_deps gc_stack G Δ E }.

  (** ** The Application Spine

      The type of [M N₁ … Nₖ], kept as a value from the head's type on:
      each argument is checked against the readback of the value's domain
      and the value moves on to the codomain closure at the argument's
      value.  A domain, or the final type, that reads back with a proof in
      it is left to the reference step, which normalizes [B[Id,,N]]: the
      value is the normal form only up to proofs there
      ([Extraction.AppSpine]). *)

  (** A type inferred, or no type *)
  #[local] Abbreviation infer_result G M := ({ A : nf | G ⊢a M ⟹ A } + { forall A, ~ G ⊢a M ⟹ A })%type.

  (** A check of a term against each type *)
  #[local] Abbreviation check_against G N := (forall A, G ⊢ᵗ A -> { G ⊢a N ⟸ A } + { ~ G ⊢a N ⟸ A })%type.

  (** What the spine knows of the type of [M] *)
  Inductive spine_result G (P : checker_env G) (M : exp) : Type :=
  (** A value related to the inferred type's value at the initial
      environment *)
  | spine_value (v : fdomain) (Hv : fdomain_ok gc_deps gc_stack v) (Hs : spine_value_sim G M v)
  (** The inferred type itself *)
  | spine_exact (W : nf) (HW : G ⊢a M ⟹ W).
  Arguments spine_value {G P M}.
  Arguments spine_exact {G P M}.

  (** What the spine of [M] gives *)
  Inductive spine_outcome G (P : checker_env G) (M : exp) : Type :=
  (** [M] is no application: its type is inferred as it is *)
  | spine_not_application
  (** The type of the application [M] *)
  | spine_known (r : spine_result G P M)
  (** The application [M] infers no type *)
  | spine_ill_typed (Hn : forall A, ~ G ⊢a M ⟹ A).
  Arguments spine_not_application {G P M}.
  Arguments spine_known {G P M}.
  Arguments spine_ill_typed {G P M}.

  (** The start of the spine: the value of the head's type, unless that
      type is [LevelSort] *)
  Definition spine_start G (HG : ⊢ G) (P : checker_env G) M (W : nf) (HW : G ⊢a M ⟹ W) : spine_result G P M :=
    match nf_not_level_sort_dec W with
    | left HnL =>
        let (t, Ht) := fast_eval_exp_impl F (nf_to_exp W) (proj1_sig P) (fast_env_simulates_ok _ _ _ _ (proj2_sig P))
                         (spine_start_order _ _ _ _ HG HW (proj2_sig P)) in
        spine_value t (proj2 Ht) (alg_spine_start_fast _ _ _ _ _ HG HW HnL (proj2_sig P) (proj1 Ht))
    | right _ => spine_exact W HW
    end.

  (** The reference step, from the inferred type [C] of the head: [C] is a
      [Π], the argument checks against its domain, and the instance of its
      codomain at the argument is normalized *)
  Definition app_reference_step G (HG : ⊢ G) (P : checker_env G) M N (C : nf) (HC : G ⊢a M ⟹ C)
      (check : check_against G N) : infer_result G (M $ N) :=
    match get_pi_nf C with
    | inleft (existT _ κd (existT _ κc (existT _ A (exist _ B E)))) =>
        let HC' : G ⊢a M ⟹ nf_pi κd κc A B := eq_rect _ (fun X => G ⊢a M ⟹ X) HC _ E in
        match check (nf_to_exp A) (typ_pi_dom _ _ _ _ _ _ HG HC') with
        | left HN =>
            let (B', HB') := nbe_ty_env_impl F G P (nf_to_exp B)[Id,,N]
                               (nbe_order_of_type _ _ (typ_app_cod _ _ _ _ _ _ _ HG HC' HN)) in
            inleft (exist _ B' (alg_type_infer_app _ _ _ _ _ _ _ _ HC' HN HB'))
        | right Hn => inright (app_check_failure _ _ _ _ _ _ _ HG HC' Hn)
        end
    | inright Hn => inright (app_not_pi_failure _ _ _ _ HG HC Hn)
    end.

  (** The reference step from the head's type inferred as it is *)
  Definition app_reference G (HG : ⊢ G) (P : checker_env G) M N
      (infer_head : unit -> infer_result G M) (check : check_against G N) : infer_result G (M $ N) :=
    match infer_head tt with
    | inleft (exist _ C HC) => app_reference_step G HG P M N C HC check
    | inright Hn => inright (app_head_failure _ _ _ Hn)
    end.

  (** A type inferred as a spine result *)
  Definition spine_of_infer G P M (r : infer_result G M) : spine_result G P M + { forall A, ~ G ⊢a M ⟹ A } :=
    match r with
    | inleft (exist _ W HW) => inleft (spine_exact W HW)
    | inright Hn => inright Hn
    end.

  (** One step of the spine at a [Π] value into a relevant codomain whose
      domain is of an evaluated kind *)
  Definition spine_pi_step G (HG : ⊢ G) (P : checker_env G) M N κd a ρ' B'
      (Hv : fdomain_ok gc_deps gc_stack (fd_pi κd ak_relevant a ρ' B'))
      (Hs : spine_value_sim G M (fd_pi κd ak_relevant a ρ' B'))
      (Hk : evaluated_kind (fdomain_kind a))
      (infer_head : unit -> infer_result G M) (check : check_against G N) :
      spine_result G P (M $ N) + { forall A, ~ G ⊢a M $ N ⟹ A } :=
    let Ha := match Hv in fdomain_ok _ _ v return
                    match v with fd_pi _ _ a0 ρ0 _ => fdomain_ok gc_deps gc_stack a0 /\ fenv_ok gc_deps gc_stack ρ0 | _ => True end with
              | fdomain_ok_pi _ _ _ _ _ _ _ Ha Hρ => conj Ha Hρ
              | _ => I
              end in
    let (A', HA') := fast_read_typ_impl F (List.length G) a (proj1 Ha)
                       (spine_domain_read_order _ _ _ _ _ _ _ Hs) in
    match nf_proof_freeb A' as b return nf_proof_freeb A' = b -> _ with
    | true => fun Ef =>
        let Hρ := proj2_sig P in
        match check (nf_to_exp A') (spine_domain_type_fast _ _ _ _ _ _ _ HG Hs HA' Ef) with
        | left HN =>
            let (n, Hn) := fast_eval_exp_impl F N (proj1_sig P) (fast_env_simulates_ok _ _ _ _ Hρ)
                             (spine_argument_order _ _ _ _ _ _ _ _ _ HG Hρ Hs HA' Ef Hk HN) in
            let (b, Hb) := fast_eval_exp_impl F B' (fextend_env ρ' n (fentry_type_value a))
                             (Forall_cons _ (fdentry_ok_term _ _ _ _ (proj2 Hn) (fentry_type_ok_value _ _ _ (proj1 Ha)))
                                (proj2 Ha))
                             (spine_codomain_order _ _ _ _ _ _ _ _ _ _ HG Hρ Hs HA' Ef Hk HN (proj1 Hn)) in
            inleft (spine_value b (proj2 Hb) (alg_spine_step_fast _ _ _ _ _ _ _ _ _ _ _ HG Hρ Hs HA' Ef Hk HN (proj1 Hn) (proj1 Hb)))
        | right Hn => inright (spine_check_failure_fast _ _ _ _ _ _ _ _ HG Hs HA' Ef Hn)
        end
    | false => fun _ => spine_of_infer G P (M $ N) (app_reference G HG P M N infer_head check)
    end eq_refl.

  (** One step of the spine: at a [Π] value into a relevant codomain whose
      domain is of an evaluated kind, by the value; otherwise by the
      reference step *)
  Definition spine_step G (HG : ⊢ G) (P : checker_env G) M N (r : spine_result G P M)
      (infer_head : unit -> infer_result G M) (check : check_against G N) :
      spine_result G P (M $ N) + { forall A, ~ G ⊢a M $ N ⟹ A } :=
    match r with
    | spine_exact W HW => spine_of_infer G P (M $ N) (app_reference_step G HG P M N W HW check)
    | spine_value v Hv Hs =>
        match v return fdomain_ok gc_deps gc_stack v -> spine_value_sim G M v -> _ with
        | fd_pi κd ak_relevant a ρ' B' => fun Hv Hs =>
            match abs_kind_eq_dec (fdomain_kind a) ak_propositional with
            | right Hk =>
                spine_pi_step G HG P M N κd a ρ' B' Hv Hs (evaluated_kind_of_not_propositional _ Hk) infer_head check
            | left _ => spine_of_infer G P (M $ N) (app_reference G HG P M N infer_head check)
            end
        | _ => fun _ _ => spine_of_infer G P (M $ N) (app_reference G HG P M N infer_head check)
        end Hv Hs
    end.

  (** The spine of the head [M] of an application: the outcome of its own
      spine if it is one, else its type inferred as it is *)
  Definition spine_head G (HG : ⊢ G) (P : checker_env G) M (o : spine_outcome G P M)
      (infer_head : unit -> infer_result G M) : spine_result G P M + { forall A, ~ G ⊢a M ⟹ A } :=
    match o with
    | spine_not_application =>
        match infer_head tt with
        | inleft (exist _ W HW) => inleft (spine_start G HG P M W HW)
        | inright Hn => inright Hn
        end
    | spine_known r => inleft r
    | spine_ill_typed Hn => inright Hn
    end.

  (** The spine of [M N], from the outcome of the spine of [M] *)
  Definition spine_extend G (HG : ⊢ G) (P : checker_env G) M N (o : spine_outcome G P M)
      (infer_head : unit -> infer_result G M) (check : check_against G N) :
      spine_result G P (M $ N) + { forall A, ~ G ⊢a M $ N ⟹ A } :=
    match spine_head G HG P M o infer_head with
    | inleft r => spine_step G HG P M N r infer_head check
    | inright Hn => inright (app_head_failure _ _ _ Hn)
    end.

  (** The end of the spine: the readback of the value, if it is proof-free;
      otherwise the reference step *)
  Definition spine_finish G (HG : ⊢ G) (P : checker_env G) M N
      (r : spine_result G P (M $ N) + { forall A, ~ G ⊢a M $ N ⟹ A })
      (infer_head : unit -> infer_result G M) (check : check_against G N) : infer_result G (M $ N) :=
    match r with
    | inleft (spine_exact W HW) => inleft (exist _ W HW)
    | inleft (spine_value v Hv Hs) =>
        let (W', HW') := fast_read_typ_impl F (List.length G) v Hv (spine_value_read_order _ _ _ _ Hs) in
        match nf_proof_freeb W' as b return nf_proof_freeb W' = b -> _ with
        | true => fun Ef => inleft (exist _ W' (alg_spine_end_fast _ _ _ _ HG Hs HW' Ef))
        | false => fun _ => app_reference G HG P M N infer_head check
        end eq_refl
    | inright Hn => inright Hn
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations type_check_in G A (HA : G ⊢ᵗ A) (P : checker_env G) M (H : type_check_order M) :
      { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, P, M, H =>
      let*o->b (exist _ B _) := type_infer_in G _ P M _ while _ in
      let*b _ := subtyping_env_impl F G P (B : nf) A _ while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : checker_env G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with M => {
    | Typeω@j =>
        pureo (exist _ Typeωⁿ@(S j) _)
    | Type⟨M'⟩ =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let (W, _) := nbe_ty_env_impl F G P Type⟨succl M'⟩ _ in
        pureo (exist _ W _)
    | Level@k =>
        pureo (exist _ LevelSortⁿ _)
    (** [LevelSort] is of no type *)
    | LevelSort =>
        inright _
    | 𝕃ᵒ m =>
        pureo (exist _ Levelⁿ@(fst m) _)
    | succl M' =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        pureo (exist _ Levelⁿ@k _)
    | maxl M' N' =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let*o (exist _ LN _) := type_infer_in G _ P N' _ while _ in
        let*o (exist _ k' _) := get_level_sort_nf LN while _ in
        pureo (exist _ Levelⁿ@(Nat.max k k') _)
    (** [Prop], the closed propositions and the introduction of [⊤] *)
    | Propₘ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⊤ =>
        pureo (exist _ Propⁿ _)
    | a_tt =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Propⁿ _)
    (** Ex falso: the target is a type of a universe or a proposition, the
        proof is checked at [⊥] *)
    | efq M' return C' =>
        let*o (exist _ UC _) := type_infer_in G _ P C' _ while _ in
        let*o (existT _ rC (exist _ uC _)) := sort_nf_dec UC while _ in
        let*b->o _ := kind_not_level_dec rC while _ in
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let (C'', _) := nbe_ty_env_impl F G P C' _ in
        pureo (exist _ C'' _)
    (** A conjunction of two propositions *)
    | Σₚ P' Q' =>
        let*o (exist _ UP _) := type_infer_in G _ P P' _ while _ in
        let*b->o _ := prop_nf_dec UP while _ in
        let HGP : ⊢ G ▹{ak_propositional} P' := _ in
        let*o (exist _ UQ _) := type_infer_in (G ▹{ak_propositional} P') HGP
                                  (checker_env_ass F G P ak_propositional P' HGP) Q' _ while _ in
        let*b->o _ := prop_nf_dec UQ while _ in
        pureo (exist _ Propⁿ _)
    (** A proof of a conjunction: the annotations are propositions, the
        components check at their parts, and the proof infers the normal
        form of the conjunction *)
    | a_conj P' Q' M' N' =>
        let*o (exist _ UP _) := type_infer_in G _ P P' _ while _ in
        let*b->o _ := prop_nf_dec UP while _ in
        let HGP : ⊢ G ▹{ak_propositional} P' := _ in
        let*o (exist _ UQ _) := type_infer_in (G ▹{ak_propositional} P') HGP
                                  (checker_env_ass F G P ak_propositional P' HGP) Q' _ while _ in
        let*b->o _ := prop_nf_dec UQ while _ in
        let*b->o _ := type_check_in G P' _ P M' _ while _ in
        let*b->o _ := type_check_in G Q'[Id,,M'] _ P N' _ while _ in
        let (W, _) := nbe_ty_env_impl F G P (Σₚ P' Q') _ in
        pureo (exist _ W _)
    (** The components of a proof of a conjunction *)
    | a_left M' =>
        let*o (exist _ T _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ Pc (exist _ Qc _)) := get_and_nf T while _ in
        pureo (exist _ Pc _)
    | a_right M' =>
        let*o (exist _ T _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ Pc (exist _ Qc _)) := get_and_nf T while _ in
        let (W, _) := nbe_ty_env_impl F G P (Qc : nf)[Id,,a_left M'] _ in
        pureo (exist _ W _)
    (** The forms of inductive types ([Extraction.IndCheck]); the
        eliminator's recursive calls are passed on. *)
    | a_ind pq k => ind_infer F G HG P pq k
    | a_con pq k c => con_infer F G HG P pq k c
    | a_elim r pq Us m Bks M' =>
        elim_infer F G HG P r pq Us m Bks M'
          (type_infer_in G HG P M' ltac:(obligation_order))
          (fun U HU G' A'' HA'' P' => type_check_in G' A'' HA'' P' U ltac:(order_part))
          (fun b Hb G' HG' P' => type_infer_in G' HG' P' (eb_scrutinee_type b) ltac:(order_part))
          (fun b Hb G' HG' P' => type_infer_in G' HG' P' (eb_motive b) ltac:(order_part))
          (fun b br Hb Hbr G' A'' HA'' P' => type_check_in G' A'' HA'' P' (snd br) ltac:(order_part))
    (** The forms of record types ([Extraction.RecordCheck]). *)
    | a_record pq => record_infer F G HG P pq
    | a_tuple T' fs =>
        tuple_infer F G HG P T' fs (type_infer_in G HG P T' ltac:(obligation_order))
          (fun fm Hfm A'' HA'' => type_check_in G A'' HA'' P (snd fm) ltac:(order_part))
    | a_proj f M' => proj_infer F G HG P f M' (type_infer_in G HG P M' ltac:(obligation_order))
    (** A [Π]: the domain a type of the kind [κd] it carries, the codomain
        one of the kind [κc], at kinds a [Π] may join; at the normal form
        of the sort of [κc] at the join of their universes *)
    | a_pi κd κc A' B' =>
        let*o (exist _ UA _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ κA (exist _ u _)) := sort_nf_dec UA while _ in
        let*b->o _ := abs_kind_eq_dec κA κd while _ in
        let HGA : ⊢ G ▹{κd} A' := _ in
        let PA := checker_env_ass F G P κd A' HGA in
        let*o (exist _ UB _) := type_infer_in (G ▹{κd} A') HGA PA B' _ while _ in
        let (UB', _) := nbe_ty_env_impl F (G ▹{κd} A') PA UB _ in
        let*o (existT _ κB (exist _ v _)) := sort_nf_dec UB' while _ in
        let*b->o _ := abs_kind_eq_dec κB κc while _ in
        let*b->o _ := pi_kinds_dec κd κc while _ in
        let (W, _) := nbe_ty_env_impl F G P (abs_kind_sort κc (universe_nf_pi_tm u v)) _ in
        pureo (exist _ W _)
    (** A λ over a type of the kind [κd] its sort says, its body's type of
        a kind [κc] the two may join, and no [LevelSort] *)
    | λ A' M' =>
        let*o (exist _ UA _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ κd (exist _ u _)) := sort_nf_dec UA while _ in
        let HGA : ⊢ G ▹{κd} A' := _ in
        let PA := checker_env_ass F G P κd A' HGA in
        let*o (exist _ B _) := type_infer_in (G ▹{κd} A') HGA PA M' _ while _ in
        let*b->o _ := nf_not_level_sort_dec B while _ in
        let (κc, _) := checker_kind F (G ▹{κd} A') PA B _ in
        let*b->o _ := pi_kinds_dec κd κc while _ in
        let (C, _) := nbe_ty_env_impl F G P A' _ in
        pureo (exist _ (nf_pi κd κc C B) _)
    (** An application *)
    | M' $ N' =>
        spine_finish G HG P M' N'
          (spine_extend G HG P M' N' (app_type_in G HG P M' _)
             (fun _ => type_infer_in G HG P M' _) (fun A HA => type_check_in G A HA P N' _))
          (fun _ => type_infer_in G HG P M' _) (fun A HA => type_check_in G A HA P N' _)
    (** A local definition *)
    | a_let (b_def A' M') B' =>
        let*o (exist _ UA _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ r (exist _ u _)) := sort_nf_dec UA while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let PD := checker_env_def F G P A' M' HGD in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD PD B' _ while _ in
        let*b->o _ := nf_not_level_sort_dec C while _ in
        let (κC, _) := checker_kind F (G ▸ A' ≔ M') PD C _ in
        let*b->o _ := level_binding_dec κC r while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** A local module *)
    | a_let (b_mod U) B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let HGU : ⊢ G ▹ₘ U := _ in
        let PU := checker_env_mod F G P U HGU in
        let*o (exist _ C _) := type_infer_in (G ▹ₘ U) HGU PU B' _ while _ in
        let*b->o _ := nf_not_level_sort_dec C while _ in
        let (κC, _) := checker_kind F (G ▹ₘ U) PU C _ in
        let*b->o _ := kind_not_level_dec κC while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    (** A local definition with a module part: its type of a large
        universe, its definiens checked against it, its unit, an alias
        under no parameters, as a local module's, the body's type as for a
        local module *)
    | a_let (b_def_mod A' M' (gu_mk nil (md_alias E))) B' =>
        let*o (exist _ UA _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let*b->o _ := unit_check G HG (gu_mk nil (md_alias E)) _ while _ in
        let HGD : ⊢ G ▸ₘ A' ≔ M' ‖ gu_mk nil (md_alias E) := _ in
        let PD := checker_env_dm F G P A' M' (gu_mk nil (md_alias E)) HGD in
        let*o (exist _ C _) := type_infer_in (G ▸ₘ A' ≔ M' ‖ gu_mk nil (md_alias E)) HGD PD B' _ while _ in
        let*b->o _ := nf_not_level_sort_dec C while _ in
        let (κC, _) := checker_kind F (G ▸ₘ A' ≔ M' ‖ gu_mk nil (md_alias E)) PD C _ in
        let*b->o _ := kind_not_level_dec κC while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id ,,ᵈ M' ‖ me_lit (gu_mk nil (md_alias E))] _ in
        pureo (exist _ D _)
    (** A unit of another shape infers nothing *)
    | a_let (b_def_mod A' M' U) B' => inright _
    (** A member infers the normal form of the type that the description of
        its module reads. *)
    | a_mem M' x =>
        let*b->o HM := modexp_check G HG M' _ while _ in
        let*o (exist _ R _) := mem_denote_dec F _ G M' x _ while _ in
        let*o (exist _ A _) := mdesc_type_dec R while _ in
        let (B, _) := nbe_ty_env_impl F G P A _ in
        pureo (exist _ B _)
    | #x =>
        let*o (exist _ A _) := lookup F G _ x while _ in
        let (A', _) := nbe_ty_env_impl F G P A _ in
        pureo (exist _ A' _)
    }
  (** The spine of an application, as a value of its type ([spine_extend]);
      no spine for a term that is no application *)
  with app_type_in G (HG : ⊢ G) (P : checker_env G) M (H : type_infer_order M) : spine_outcome G P M by struct H :=
  | G, HG, P, M, H with M => {
    | M1 $ N1 =>
        match spine_extend G HG P M1 N1 (app_type_in G HG P M1 _)
                (fun _ => type_infer_in G HG P M1 _) (fun A HA => type_check_in G A HA P N1 _) with
        | inleft r => spine_known r
        | inright Hn => spine_ill_typed Hn
        end
    | _ => spine_not_application
    }
  (** The parameters of a unit: assumptions of types of universes or of
      types of levels. *)
  with params_check G (HG : ⊢ G) Δ (H : ext_order Δ) : { G ⊢aᵖ Δ } + { ~ G ⊢aᵖ Δ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass ak_relevant A :: Δ, H =>
      let*b _ := params_check G HG Δ _ while _ in
      let HΔ : ⊢ Δ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Δ ++ G) HΔ (checker_env_of F (Δ ++ G) HΔ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, ce_ass ak_level A :: Δ, H =>
      let*b _ := params_check G HG Δ _ while _ in
      let HΔ : ⊢ Δ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Δ ++ G) HΔ (checker_env_of F (Δ ++ G) HΔ) A _ while _ in
      let*b _ := level_sort_nf_dec UA while _ in
      pureb _
  | G, HG, _ :: Δ, H => right _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body sm_closed Φ), H => right (alg_unit_closed_no G Δ Φ)
  | G, HG, gu_mk Δ (md_body sm_open Φ), H =>
      let*b _ := params_check G HG Δ _ while _ in
      let*b _ := all_assumptions_dec Δ while _ in
      let HΔ : ⊢ Δ ++ G := _ in
      let*o->b (exist _ Φx _) := body_check (Δ ++ G) HΔ Φ _ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := body_shape_dec Φx Φx while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      let*b _ := levels_abstractable_dec G Δ (me_lit (gu_open nil Φ)) HΔ _ while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := params_check G HG Δ _ while _ in
      let*b _ := all_assumptions_dec Δ while _ in
      let HΔ : ⊢ Δ ++ G := _ in
      let*b _ := modexp_check (Δ ++ G) HΔ E _ while _ in
      let*b _ := levels_abstractable_dec G Δ E HΔ _ while _ in
      (** the target is no module still being defined *)
      let*b _ := frame_free_target_dec F _ (Δ ++ G) E _ while _ in
      pureb _
  with modexp_check G (HG : ⊢ G) M (H : modexp_order M) : { G ⊢aᵐ M } + { ~ G ⊢aᵐ M } by struct H :=
  | G, HG, me_unit fp, H =>
      let*o->b (exist _ R _) := path_denote_dec F _ G fp while _ in
      let*o->b (exist _ T _) := mdesc_mod_tele_dec R while _ in
      pureb _
  | G, HG, me_var x, H with inspect (ctx_find_mod G x) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_lit U, H =>
      let*b _ := unit_check G HG U _ while _ in
      pureb _
  | G, HG, me_mem M y, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ R _) := mem_denote_dec F _ G M y _ while _ in
      let*o->b (exist _ T _) := mdesc_mod_tele_dec R while _ in
      pureb _
  | G, HG, me_app M N, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ R _) := mdenote_dec F _ G M _ while _ in
      let*o->b (exist _ T _) := mdesc_mod_tele_dec R while _ in
      let*o->b (existT _ B (exist _ T1 _)) := tele_view_dec T while _ in
      let*b _ := type_check_in G B _ (checker_env_of F G HG) N _ while _ in
      pureb _
  (** A body, entry by entry, as the entries its opens generate: each in the
      context of the expanded body before it. *)
  with body_check G (HG : ⊢ G) Φ (H : body_order Φ) :
      { Φx | G ⊢aᵇ Φ ⇝ Φx /\ ⊢ body_ctx Φx ++ G } + { forall Φx, ~ G ⊢aᵇ Φ ⇝ Φx } by struct H :=
  | G, HG, gm_nil, H => inleft (exist _ gm_nil _)
  (** A definition, of a type of the kind its tag says *)
  | G, HG, gm_ext Φ x (ge_def b pv r A (Some M)), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let PGx := checker_env_of F _ HGx in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx PGx A _ while _ in
      let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      let*b->o _ := abs_kind_eq_dec rA r while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ PGx M _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def b pv r A (Some M))) _)
  | G, HG, gm_ext Φ x (ge_mod pm U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) _ U _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_mod pm U)) _)
  (** A definition with a module part: its term part as a definition, then
      its unit, an alias under no parameters ([alg_body_dm]). *)
  | G, HG, gm_ext Φ x (ge_def_mod pv A M (gu_mk nil (md_alias E))), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let PGx := checker_env_of F _ HGx in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx PGx A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ PGx M _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) HGx (gu_mk nil (md_alias E)) _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def_mod pv A M (gu_mk nil (md_alias E)))) _)
  | G, HG, gm_ext Φ x E, H => inright _
  | G, HG, gm_open Φ M its Φg, H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o HM := modexp_check (body_ctx Φx ++ G) _ M _ while _ in
      let*o (exist _ R _) := mdenote_dec F _ (body_ctx Φx ++ G) M _ while _ in
      let*o (exist _ Rm _) := mdesc_mod_dec R while _ in
      (** the module opened is no module still being defined *)
      let*b->o _ := frame_free_target_dec F _ (body_ctx Φx ++ G) M _ while _ in
      let*o (exist _ gs _) := items_gen_dec F _ (body_ctx Φx ++ G) M its _ while _ in
      let*b->o _ := items_ok_dec its while _ in
      let*b->o _ := gmod_eq_dec Φg (gens_body gs) while _ in
      pureo (exist _ (gens_append Φx 0 gs) _)
  .
  Solve All Obligations with checker_obligation.

  Extraction Inline type_check_in_functional type_infer_in_functional app_type_in_functional
    params_check_functional unit_check_functional body_check_functional modexp_check_functional.

  (** A context extension, entry by entry, each in the context of the
      entries before it.  Nothing in the checker above calls it, so it is
      defined after it, on its own. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  (** An assumption of a type of the kind it says *)
  | G, HG, ce_ass κ A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (checker_env_of F (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (existT _ κA (exist _ u _)) := sort_nf_dec UA while _ in
      let*b _ := abs_kind_eq_dec κA κ while _ in
      pureb _
  (** A definition of a type of a sort *)
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      pureb _
  (** A module, by its unit *)
  | G, HG, ce_mod U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*b _ := unit_check (Ψ ++ G) _ U _ while _ in
      pureb _
  (** A definition with a module part: as a definition, then its unit, an
      alias under no parameters ([alg_ext_dm]). *)
  | G, HG, ce_dm A M (gu_mk nil (md_alias E)) :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      let*b _ := unit_check (Ψ ++ G) HΨ (gu_mk nil (md_alias E)) _ while _ in
      pureb _
  (** A unit of another shape is rejected *)
  | G, HG, ce_dm A M U :: Ψ, H => right _.
  Solve All Obligations with checker_obligation.

  (** The checker from scratch: the initial environment of the context is
      computed once, at the start. *)
  Definition type_check G A (HA : G ⊢ᵗ A) M (H : type_check_order M) :
      { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } :=
    type_check_in G A HA (checker_env_of F G (wf_type_ctx _ _ HA)) M H.

  Definition type_infer G (HG : ⊢ G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A } + { forall A, ~ G ⊢a M ⟹ A } :=
    type_infer_in G HG (checker_env_of F G HG) M H.

  (** A term of a well-formed context: the type it infers, at which it is
      typed *)
  Definition type_infer_at G (HG : ⊢ G) M : { A : nf | G ⊢a M ⟹ A /\ G ⊢ M : A } + { forall A, ~ G ⊢a M ⟹ A } :=
    match type_infer G HG M (type_infer_order_all M) with
    | inleft (exist _ A HA) => inleft (exist _ A (conj HA (alg_type_infer_sound HA HG)))
    | inright Hn => inright Hn
    end.

  (** The checker decides the judgments. *)
  Lemma type_check_complete : forall G M A (HA : G ⊢ᵗ A),
      G ⊢a M ⟸ A -> exists H', type_check G A HA M (type_check_order_all M) = left H'.
  Proof. intros; decision_complete. Qed.

  Lemma type_infer_complete : forall G M A (HG : ⊢ G),
      G ⊢a M ⟹ A -> exists H', type_infer G HG M (type_infer_order_all M) = inleft (exist _ A H').
  Proof.
    intros * HM.
    destruct (type_infer G HG M (type_infer_order_all M)) as [[A' HA'] | Hn]; [| exfalso; exact (Hn _ HM) ].
    assert (A' = A) as -> by (eapply functional_alg_type_infer; [ exact (ctx_wf_gctx _ _ _ HG) | exact HA' | exact HM ]).
    eexists; reflexivity.
  Qed.

  Lemma ext_check_complete : forall G Ψ (HG : ⊢ G),
      G ⊢aˣ Ψ -> exists H', ext_check G HG Ψ (ext_order_all Ψ) = left H'.
  Proof. intros; decision_complete. Qed.

  Lemma unit_check_complete : forall G U (HG : ⊢ G),
      G ⊢aᵘ U -> exists H', unit_check G HG U (unit_order_all U) = left H'.
  Proof. intros; decision_complete. Qed.

  Lemma modexp_check_complete : forall G M (HG : ⊢ G),
      G ⊢aᵐ M -> exists H', modexp_check G HG M (modexp_order_all M) = left H'.
  Proof. intros; decision_complete. Qed.
End type_check.
End Fixed_GCtx.
