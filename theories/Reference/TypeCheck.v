From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import Evaluation NbE PseudoMonadic Subtyping MemberType TypeCheckBase IndCheck RecordCheck.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * The Reference Checker

    The direct implementation of the algorithmic judgments, rule by rule:
    an application normalizes the instantiated codomain [B[Id,,N]] of the
    head's type, and a check normalizes both types it compares.  It is not
    extracted; [Extraction.TypeCheck] is the checker that is, and
    [Reference.Refinement] proves that the two compute the same.  The parts
    they share (orders, decisions of side conditions, the initial
    environment, the obligation tactics) are in [Extraction.TypeCheckBase]. *)

Section Fixed_GCtx.
(** The reference checker runs on a fast context, as the extracted one:
    it shares the eliminator, record and normalization code of
    [Extraction], which runs on one ([Reference.Refinement]). *)
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

Section type_check.
  #[local]
  Hint Constructors type_check_order type_infer_order ext_order unit_order modexp_order : mctt.


  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations type_check_in G A (HA : (exists i, G ⊢ A : Typeω@i)) (P : checker_env G) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, P, M, H =>
      let*o->b (exist _ B _) := type_infer_in G _ P M _ while _ in
      let*b _ := subtyping_env_impl F G P (B : nf) A _ while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : checker_env G) M (H : type_infer_order M) : { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with M => {
    | Typeω@j =>
        pureo (exist _ Typeωⁿ@(S j) _)
    | Type⟨M'⟩ =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let (W, _) := nbe_ty_env_impl F G P Type⟨succl M'⟩ _ in
        pureo (exist _ W _)
    | Level@k =>
        pureo (exist _ Typeⁿ@0 _)
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
    | ⊤ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Typeⁿ@0 _)
    | efq M' return A' =>
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let HGF : ⊢ G ▹ ⊥ := _ in
        let*o (exist _ UA' _) := type_infer_in (G ▹ ⊥) HGF (checker_env_ass F G P ⊥ HGF) A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let (A'', _) := nbe_ty_env_impl F G P A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | Π B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (checker_env_ass F G P B HGB) C _ while _ in
        let (UC', _) := nbe_ty_env_impl F (G ▹ B) (checker_env_ass F G P B HGB) UC _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC' while _ in
        let (W, _) := nbe_ty_env_impl F G P (universe_nf_pi_tm u v) _ in
        pureo (exist _ W _)
    (** The forms of inductive types ([Extraction.IndCheck]); the
        eliminator's recursive calls are passed on. *)
    | a_ind r k => ind_infer F G HG P r k
    | a_con r k c => con_infer F G HG P r k c
    (** The forms of record types ([Extraction.RecordCheck]). *)
    | a_record r => record_infer F G HG P r
    | a_tuple T' fs =>
        tuple_infer F G HG P T' fs (type_infer_in G HG P T' ltac:(obligation_order_record))
          (fun fm Hfm A'' HA'' => type_check_in G A'' HA'' P (snd fm) ltac:(obligation_order_record))
    | a_proj f M' => proj_infer F G HG P f M' (type_infer_in G HG P M' ltac:(obligation_order_record))
    | a_nlit n => inright (fun A HA => alg_nlit_no_infer G n A HA)
    | a_ntok => inright (fun A HA => alg_ntok_no_infer G A HA)
    | a_elim oq Us m Bks M' =>
        elim_infer F G HG P oq Us m Bks M'
          (type_infer_in G HG P M' ltac:(obligation_order_elim))
          (fun U HU G' A'' HA'' P' => type_check_in G' A'' HA'' P' U ltac:(obligation_order_elim))
          (fun b Z Hb HZ G' HG' P' => type_infer_in G' HG' P' Z ltac:(obligation_order_elim))
          (fun b Hb G' HG' P' => type_infer_in G' HG' P' (eb_motive b) ltac:(obligation_order_elim))
          (fun b br Hb Hbr G' A'' HA'' P' => type_check_in G' A'' HA'' P' (snd br) ltac:(obligation_order_elim))
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let HGA : ⊢ G ▹ A' := _ in
        let*o (exist _ B' _) := type_infer_in (G ▹ A') HGA (checker_env_ass F G P A' HGA) M' _ while _ in
        let (A'', _) := nbe_ty_env_impl F G P A' _ in
        pureo (exist _ (Πⁿ A'' B') _)
    | M' $ N' =>
        let*o (exist _ C _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ A (exist _ B _)) := get_subterms_of_pi_nf C while _ in
        let*b->o _ := type_check_in G (A : nf) _ P N' _ while _ in
        let (B', _) := nbe_ty_env_impl F G P (B : nf)[Id,,N'] _ in
        pureo (exist _ B' _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD (checker_env_def F G P A' M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer_in G _ P M' _ while _ in
        let HGD : ⊢ G ▸ (A : nf) ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ (A : nf) ≔ M') HGD (checker_env_def F G P (A : nf) M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let HGU : ⊢ G ▹ₘ U := _ in
        let*o (exist _ C _) := type_infer_in (G ▹ₘ U) HGU (checker_env_mod F G P U HGU) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
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
  with ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (checker_env_of F (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      pureb _
  | G, HG, ce_mod U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*b _ := unit_check (Ψ ++ G) _ U _ while _ in
      pureb _
  (** A definition with a module part: as a definition, then its unit. *)
  | G, HG, ce_dm A M U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      let*b _ := unit_check (Ψ ++ G) HΨ U _ while _ in
      pureb _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body sm_closed Φ), H => right (alg_unit_closed_no G Δ Φ)
  | G, HG, gu_mk Δ (md_body sm_open Φ), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*o->b (exist _ Φx _) := body_check (Δ ++ G) _ Φ _ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := body_shape_dec Φx Φx while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := modexp_check (Δ ++ G) _ E _ while _ in
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
  | G, HG, gm_ext Φ x (ge_def b pv A (Some M)), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (checker_env_of F _ HGx) A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (checker_env_of F _ HGx) M _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def b pv A (Some M))) _)
  | G, HG, gm_ext Φ x (ge_mod pm U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) _ U _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_mod pm U)) _)
  (** A definition with a module part: its term part as a definition, then
      its unit. *)
  | G, HG, gm_ext Φ x (ge_def_mod pv A M U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (checker_env_of F _ HGx) A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (checker_env_of F _ HGx) M _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) HGx U _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def_mod pv A M U)) _)
  | G, HG, gm_ext Φ x E, H => inright _
  | G, HG, gm_open Φ M its, H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o HM := modexp_check (body_ctx Φx ++ G) _ M _ while _ in
      let*o (exist _ R _) := mdenote_dec F _ (body_ctx Φx ++ G) M _ while _ in
      let*o (exist _ Rm _) := mdesc_mod_dec R while _ in
      let*o (exist _ gs _) := items_gen_dec F _ (body_ctx Φx ++ G) M its _ while _ in
      let*b->o _ := items_ok_dec its while _ in
      pureo (exist _ (gens_append Φx 0 gs) _)
  .

  (** One obligation per hole of the program, in order, each proved by the
      tactic for its kind (see the [obligation_*] and [module_obligation_*] tactics above). *)
  Obligation 1. (* ⊢ G *) obligation_ctx_ext. Qed.
  Obligation 2. (* type_infer_order M *) obligation_order. Defined.
  Obligation 3. (* False *) obligation_failure. Qed.
  Obligation 4. (* subtyping_order G B A *) obligation_suborder. Qed.
  Obligation 5. (* False *) obligation_failure. Qed.
  Obligation 6. (* G ⊢a M ⟸ A *) obligation_check. Qed.
  Obligation 7. (* G ⊢a Typeω@j ⟹ Typeωⁿ@(S j) /\ (exists (UA : nf) (u : universe_nf),... *) obligation_post. Qed.
  Obligation 8. (* ⊢ G *) Qed.
  Obligation 9. (* type_infer_order M' *) obligation_order. Defined.
  Obligation 10. (* False *) obligation_failure. Qed.
  Obligation 11. (* False *) obligation_failure. Qed.
  Obligation 12. (* nbe_ty_order gc_deps gc_stack G Type⟨succl M'⟩ *) obligation_suniv_nbe. Qed.
  Obligation 13. (* G ⊢a Type⟨M'⟩ ⟹ W /\ (exists (UA : nf) (u : universe_nf), G ⊢a W... *) obligation_suniv_post. Qed.
  Obligation 14. (* G ⊢a Level@k ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : universe_nf), G ⊢... *) obligation_post_suniv0. Qed.
  Obligation 15. (* G ⊢a 𝕃ᵒ m ⟹ Levelⁿ@(fst m) /\ (exists (UA : nf) (u : universe_nf), G ⊢a Le... *) obligation_post_lvl. Qed.
  Obligation 16. (* ⊢ G *) Qed.
  Obligation 17. (* type_infer_order M' *) obligation_order. Defined.
  Obligation 18. (* False *) obligation_failure. Qed.
  Obligation 19. (* False *) obligation_failure. Qed.
  Obligation 20. (* G ⊢a succl M' ⟹ Levelⁿ@k /\ (exists (UA : nf) (u : universe_nf), G ... *) obligation_post_lvl. Qed.
  Obligation 21. (* ⊢ G *) Qed.
  Obligation 22. (* type_infer_order M' *) obligation_order. Defined.
  Obligation 23. (* False *) obligation_failure. Qed.
  Obligation 24. (* False *) obligation_failure. Qed.
  Obligation 25. (* ⊢ G *) Qed.
  Obligation 26. (* type_infer_order N' *) obligation_order. Defined.
  Obligation 27. (* False *) obligation_failure. Qed.
  Obligation 28. (* False *) obligation_failure. Qed.
  Obligation 29. (* G ⊢a maxl M' N' ⟹ Levelⁿ@(max k k') /\ (exists (UA : nf) (u : universe_nf), ... *) obligation_post_lvl. Qed.
  Obligation 30. (* G ⊢a ⊤ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : universe_nf), G ⊢a Ty... *) obligation_post_suniv0. Qed.
  Obligation 31. (* G ⊢a ⋆ ⟹ ⊤ⁿ /\ (exists (UA : nf) (u : universe_nf), G ⊢a ⊤ ⟹ UA /... *) obligation_post. Qed.
  Obligation 32. (* G ⊢a ⊥ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : universe_nf), G ⊢a Ty... *) obligation_post_suniv0. Qed.
  Obligation 33. (* exists i : nat, G ⊢ ⊥ : Typeω@i *) obligation_typ_closed. Qed.
  Obligation 34. (* type_check_order M' *) obligation_order. Defined.
  Obligation 35. (* False *) obligation_failure. Qed.
  Obligation 36. (* ⊢ G ▹ ⊥ *) obligation_ctx_ext. Qed.
  Obligation 37. (* type_infer_order A' *) obligation_order. Defined.
  Obligation 38. (* False *) obligation_failure. Qed.
  Obligation 39. (* False *) obligation_failure. Qed.
  Obligation 40. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeω@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ˢ Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 41. (* G ⊢a efq M' return A' ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ˢ Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 42. Qed.
  Obligation 43. (* type_infer_order B *) obligation_order. Defined.
  Obligation 44. (* False *) obligation_failure. Qed.
  Obligation 45. (* False *) obligation_failure. Qed.
  Obligation 46. (* ⊢ G ▹ B *) obligation_ctx. Qed.
  Obligation 47. (* type_infer_order C *) obligation_order. Defined.
  Obligation 48. (* False *) obligation_failure. Qed.
  Obligation 49. (* nbe_ty_order gc_deps gc_stack (G ▹ B) UC *)
    clear_defs.
    destruct_conjs.
    match goal with H : G ▹ B ⊢ (?UC : exp) : Typeω@?i |- nbe_ty_order _ _ _ ?UC =>
      destruct (soundness_ty H) as [W [HW _]] end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 50. (* False: the codomain's universe, normalised, is no universe *)
    clear_defs.
    lazymatch goal with H : _ ⊢a _ ⟹ _ |- False => inversion H; subst; clear H end.
    destruct_conjs.
    functional_alg_type_infer_rewrite_clear.
    functional_nbe_rewrite_clear.
    firstorder.
  Qed.
  Obligation 51. (* nbe_ty_order gc_deps gc_stack G (universe_nf_pi_tm u v) *)
    clear_defs.
    destruct_conjs.
    match goal with
    | HB : G ⊢a B ⟹ ?UB, Hu : is_univ_nf ?UB u, HC : G ▹ B ⊢a C ⟹ ?UC,
      HnC : nbe_ty gc_deps gc_stack (G ▹ B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
        destruct (alg_pi_parts_sound HG HB Hu HC HnC Hv) as (HBu & HCv & Hvw)
    end.
    destruct (wf_universe_nf_pi_tm HBu HCv Hvw) as [k Hk].
    destruct (soundness_ty Hk) as [W [HW _]].
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 52. (* G ⊢a Π B C ⟹ W, the normal form of its universe, and that is a type *)
    clear_defs.
    destruct_conjs.
    match goal with
    | HB : G ⊢a B ⟹ ?UB, Hu : is_univ_nf ?UB u, HC : G ▹ B ⊢a C ⟹ ?UC,
      HnC : nbe_ty gc_deps gc_stack (G ▹ B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
        destruct (alg_pi_parts_sound HG HB Hu HC HnC Hv) as (HBu & HCv & Hvw)
    end.
    destruct (wf_universe_nf_pi_tm HBu HCv Hvw) as [k Hk].
    assert (G ⊢ universe_nf_pi_tm u v ≈ W : Typeω@k) by (eapply soundness_ty'; eassumption).
    assert (HWk : G ⊢ W : Typeω@k) by (gen_presups; assumption).
    split; [ eapply alg_type_infer_pi; eassumption |].
    split; [| eexists; exact HWk ].
    destruct (alg_type_infer_large_typ_complete (user_exp_nf W) HWk) as [? [? [? [? _]]]].
    do 2 eexists; split; eassumption.
  Qed.
  Obligation 53. Qed.
  Obligation 54. (* type_infer_order A' *) obligation_order. Defined.
  Obligation 55. (* False *) obligation_failure. Qed.
  Obligation 56. (* False *) obligation_failure. Qed.
  Obligation 57. (* ⊢ G ▹ A' *) obligation_ctx. Qed.
  Obligation 58. (* type_infer_order M' *) obligation_order. Defined.
  Obligation 59. (* False *) obligation_failure. Qed.
  Obligation 60. (* nbe_ty_order gc_deps gc_stack G A' *)
    clear_defs.
    saturate_infer_univ.
    match goal with H : G ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A' : Typeω@k) as [? []]%soundness_ty by exact H end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 61. (* G ⊢a λ A' M' ⟹ Πⁿ A'' B', and [Π A'' B'] is a type *)
    clear_defs.
    saturate_infer_univ.
    (** The annotation's normal form is a type at the same level, and the
        body's type is one in the context of that normal form. *)
    assert (⊢ G ▹ A') by mauto 2.
    assert (G ⊢ A' ≈ A'' : Typeω@(universe_nf_large_index u)) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (G ⊢ A'' : Typeω@(universe_nf_large_index u)) by (gen_presups; mauto 2).
    assert (⊢ G ▹ (A'' : exp)) by mauto 2.
    assert (exists l, G ▹ (A'' : exp) ⊢ B' : Typeω@l) as [l HB'] by (eexists; mauto 4).
    split; [ mauto 3 | split ].
    - destruct (alg_type_infer_large_typ_complete (user_exp_nf A'') ltac:(eassumption)) as [UA'' [w [HUA'' [HwA'' _]]]].
      destruct (alg_type_infer_large_typ_complete (user_exp_nf B') HB') as [UB' [w' [HUB' [HwB' _]]]].
      destruct (alg_pi_infer_univ G _ _ _ _ _ _ HG HUA'' HUB' HwA'' HwB') as (W0 & w0 & HW0 & Hw0 & _).
      do 2 eexists; split; eassumption.
    - exists (max (universe_nf_large_index u) l); apply wf_pi_large;
        [ mauto 3 using lift_exp_max_left | mauto 3 using lift_exp_max_right ].
  Qed.
  Obligation 62. Qed.
  Obligation 63. (* type_infer_order M' *) obligation_order. Defined.
  Obligation 64. (* False *) obligation_failure. Qed.
  Obligation 65. (* False *) obligation_failure. Qed.
  Obligation 66. (* exists i : nat, G ⊢ A : Typeω@i *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 67. (* type_check_order N' *) obligation_order. Defined.
  Obligation 68. (* False *) obligation_failure. Qed.
  Obligation 69. (* nbe_ty_order gc_deps gc_stack G s[Id,,N'] *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    saturate_infer_univ.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    (** The codomain is a type at the large level of the index of its
        normalised universe. *)
    assert (G ⊢ s[Id,,N'] : Typeω@(universe_nf_large_index v)) as [? []]%soundness_ty by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 70. (* G ⊢a M' $ N' ⟹ B' /\ (B' is a type) *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    split; [mauto 3 |].
    saturate_infer_univ.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ s[Id,,N'] : Typeω@(universe_nf_large_index v)) by mauto 3.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 71. Qed.
  Obligation 72. (* False *) obligation_failure. Qed.
  Obligation 73. (* nbe_ty_order gc_deps gc_stack G A *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [? [? []]%soundness_ty] by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 74. (* G ⊢a #x ⟹ A', and [A'] is a type *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [i] by mauto 3.
    split; [ mauto 3 |].
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 75. Qed.
  Obligation 76. (* type_infer_order A' *) obligation_order. Defined.
  Obligation 77. (* False *) obligation_failure. Qed.
  Obligation 78. (* False *) obligation_failure. Qed.
  Obligation 79. (* exists i, G ⊢ A' : Typeω@i *)
    clear_defs.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 80. (* type_check_order M' *) obligation_order. Defined.
  Obligation 81. (* False *) obligation_failure. Qed.
  Obligation 82. (* ⊢ G ▸ A' ≔ M' *) obligation_ctx. Qed.
  Obligation 83. (* type_infer_order B' *) obligation_order. Defined.
  Obligation 84. (* False *) obligation_failure. Qed.
  Obligation 85. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 86. (* G ⊢a ℓ A' ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 87. Qed.
  Obligation 88. (* type_infer_order M' *) obligation_order. Defined.
  Obligation 89. (* False *) obligation_failure. Qed.
  Obligation 90. (* ⊢ G ▸ A ≔ M' *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    mauto 3.
  Qed.
  Obligation 91. (* type_infer_order B' *) obligation_order. Defined.
  Obligation 92. (* False *) obligation_failure. Qed.
  Obligation 93. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 94. (* G ⊢a ℓ ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 95. (* unit_order U *) obligation_order. Defined.
  Obligation 96. (* False *) obligation_failure. Qed.
  Obligation 97. (* ⊢ G ▹ₘ U *) obligation_ctx. Qed.
  Obligation 98. (* type_infer_order B' *) obligation_order. Defined.
  Obligation 99. (* False *) obligation_failure. Qed.
  Obligation 100. (* nbe_ty_order gc_deps gc_stack G C[Id ,,ₘ me_lit U] *)
    clear_defs.
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢ˢ Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? [? []]%soundness_ty]
        by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 101. (* G ⊢a ℓₘ U in B' ⟹ D, and [D] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢ˢ Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 102. (* modexp_order M' *) obligation_order. Defined.
  Obligation 103. (* False *) obligation_mem_failure. Qed.
  Obligation 104. (* ⊢ᵍ gc_deps ⍮ gc_stack *) obligation_check. Qed.
  Obligation 105. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M' ≈ M' *) module_obligation_18. Qed.
  Obligation 106. (* False: the member denotes nothing *) obligation_mem_failure. Qed.
  Obligation 107. (* False: what it denotes has no type *) obligation_mem_failure. Qed.
  Obligation 108. (* nbe_ty_order gc_deps gc_stack G A *) module_obligation_7. Qed.
  Obligation 109. (* G ⊢a a_mem M' x ⟹ B /\ (exists (UA : nf) (u : universe_nf), G ⊢a ... *) module_obligation_8. Qed.
  Obligation 110. (* G ⊢aˣ ⋅ *) obligation_check. Qed.
  Obligation 111. (* ext_order Ψ *) obligation_order. Defined.
  Obligation 112. (* False *) module_obligation_10. Qed.
  Obligation 113. (* ⊢ Ψ ++ G *) obligation_ctx. Qed.
  Obligation 114. (* type_infer_order A *) obligation_order. Defined.
  Obligation 115. (* False *) module_obligation_10. Qed.
  Obligation 116. (* False *) module_obligation_10. Qed.
  Obligation 117. (* G ⊢aˣ Ψ ▹ A *) obligation_check. Qed.
  Obligation 118. (* ext_order Ψ *) obligation_order. Defined.
  Obligation 119. (* False *) module_obligation_10. Qed.
  Obligation 120. (* ⊢ Ψ ++ G *) obligation_ctx. Qed.
  Obligation 121. (* type_infer_order A *) obligation_order. Defined.
  Obligation 122. (* False *) module_obligation_10. Qed.
  Obligation 123. (* False *) module_obligation_10. Qed.
  Obligation 124. (* exists i0 : nat, Ψ ++ G ⊢ A : Typeω@i0 *) module_obligation_14. Qed.
  Obligation 125. (* type_check_order M *) obligation_order. Defined.
  Obligation 126. (* False *) module_obligation_10. Qed.
  Obligation 127. (* G ⊢aˣ Ψ ▸ A ≔ M *) obligation_check. Qed.
  Obligation 128. (* ext_order Ψ *) obligation_order. Defined.
  Obligation 129. (* False *) module_obligation_10. Qed.
  Obligation 130. (* ⊢ Ψ ++ G *) obligation_ctx. Qed.
  Obligation 131. (* unit_order U *) obligation_order. Defined.
  Obligation 132. (* False *) module_obligation_10. Qed.
  Obligation 133. (* G ⊢aˣ Ψ ▹ₘ U *) obligation_check. Qed.
  Obligation 134. (* ext_order Ψ *) obligation_order. Defined.
  Obligation 135. (* False *) module_obligation_10. Qed.
  Obligation 136. (* ⊢ Ψ ++ G *) obligation_ctx. Qed.
  Obligation 137. (* type_infer_order A *) obligation_order. Defined.
  Obligation 138. (* False *) module_obligation_10. Qed.
  Obligation 139. (* False *) module_obligation_10. Qed.
  Obligation 140. (* exists i0 : nat, Ψ ++ G ⊢ A : Typeω@i0 *) module_obligation_14. Qed.
  Obligation 141. (* type_check_order M *) obligation_order. Defined.
  Obligation 142. (* False *) module_obligation_10. Qed.
  Obligation 143. (* unit_order U *) obligation_order. Defined.
  Obligation 144. (* False *) module_obligation_10. Qed.
  Obligation 145. (* G ⊢aˣ Ψ ▸ₘ A ≔ M ‖ U *) obligation_check. Qed.
  Obligation 146. (* ext_order Δ *) obligation_order. Defined.
  Obligation 147. (* False *) module_obligation_10. Qed.
  Obligation 148. (* False *) module_obligation_10. Qed.
  Obligation 149. (* ⊢ Δ ++ G *) obligation_ctx. Qed.
  Obligation 150. (* body_order Φ *) obligation_order. Defined.
  Obligation 151. (* False: the body does not check *) body_obligation. Qed.
  Obligation 152. (* False *) module_obligation_10. Qed.
  Obligation 153. (* False: its expansion is of no shape *) body_obligation. Qed.
  Obligation 154. (* False *) module_obligation_10. Qed.
  Obligation 155. (* G ⊢aᵘ gu_open Δ Φ *) obligation_check. Qed.
  Obligation 156. (* ext_order Δ *) obligation_order. Defined.
  Obligation 157. (* False *) module_obligation_10. Qed.
  Obligation 158. (* False *) module_obligation_10. Qed.
  Obligation 159. (* ⊢ Δ ++ G *) obligation_ctx. Qed.
  Obligation 160. (* modexp_order E *) obligation_order. Defined.
  Obligation 161. (* False *) module_obligation_10. Qed.
  Obligation 162. (* G ⊢aᵘ gu_mk Δ (md_alias E) *) obligation_check. Qed.
  Obligation 163. (* ⊢ᵍ gc_deps ⍮ gc_stack *) obligation_check. Qed.
  Obligation 164. (* False: the path denotes nothing *) module_obligation_10. Qed.
  Obligation 165. (* False: it is no module *) module_obligation_10. Qed.
  Obligation 166. (* G ⊢aᵐ me_unit fp *) module_obligation_2. Qed.
  Obligation 167. (* G ⊢aᵐ me_var x *) module_obligation_19. Qed.
  Obligation 168. (* False *) module_obligation_20. Qed.
  Obligation 169. (* modexp_order M *) obligation_order. Defined.
  Obligation 170. (* False *) module_obligation_10. Qed.
  Obligation 171. (* ⊢ᵍ gc_deps ⍮ gc_stack *) obligation_check. Qed.
  Obligation 172. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) module_obligation_18. Qed.
  Obligation 173. (* False: the selection denotes nothing *) module_obligation_3. Qed.
  Obligation 174. (* False: it is no module *) module_obligation_3. Qed.
  Obligation 175. (* G ⊢aᵐ me_mem M y *) obligation_check. Qed.
  Obligation 176. (* modexp_order M *) obligation_order. Defined.
  Obligation 177. (* False *) module_obligation_10. Qed.
  Obligation 178. (* ⊢ᵍ gc_deps ⍮ gc_stack *) obligation_check. Qed.
  Obligation 179. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) module_obligation_18. Qed.
  Obligation 180. (* False: the module expression denotes nothing *) module_obligation_10. Qed.
  Obligation 181. (* False: it is no module *) module_obligation_10. Qed.
  Obligation 182. (* False: it takes no parameter *) module_obligation_21. Qed.
  Obligation 183. (* exists i : nat, G ⊢ B : Typeω@i *) module_obligation_22. Qed.
  Obligation 184. (* type_check_order N *) obligation_order. Defined.
  Obligation 185. (* False *) module_obligation_21. Qed.
  Obligation 186. (* G ⊢aᵐ me_app M N *) obligation_check. Qed.
  Obligation 187. (* unit_order U *) obligation_order. Defined.
  Obligation 188. (* False *) module_obligation_10. Qed.
  Obligation 189. (* G ⊢aᵐ me_lit U *) obligation_check. Qed.
  Obligation 190. all: body_obligation. Qed.
  Obligation 191. obligation_order. Defined.
  Obligation 192. all: body_obligation. Qed.
  Obligation 193. all: body_obligation. Qed.
  Obligation 194. obligation_order. Defined.
  Obligation 195. all: body_obligation. Qed.
  Obligation 196. all: body_obligation. Qed.
  Obligation 197. all: body_obligation. Qed.
  Obligation 198. obligation_order. Defined.
  Obligation 199. all: body_obligation. Qed.
  Obligation 200. all: body_obligation. Qed.
  Obligation 201. all: body_obligation. Qed.
  Obligation 202. obligation_order. Defined.
  Obligation 203. all: body_obligation. Qed.
  Obligation 204. all: body_obligation. Qed.
  Obligation 205. obligation_order. Defined.
  Obligation 206. all: body_obligation. Qed.
  Obligation 207. all: body_obligation. Qed.
  Obligation 208. (* no body holds an inductive type *) all: body_obligation. Qed.
  (* a definition with a module part *)
  Obligation 209. obligation_order. Defined.
  Obligation 210. all: body_obligation. Qed.
  Obligation 211. all: body_obligation. Qed.
  Obligation 212. obligation_order. Defined.
  Obligation 213. all: body_obligation. Qed.
  Obligation 214. all: body_obligation. Qed.
  Obligation 215. all: body_obligation. Qed.
  Obligation 216. obligation_order. Defined.
  Obligation 217. all: body_obligation. Qed.
  Obligation 218. obligation_order. Defined.
  Obligation 219. all: body_obligation. Qed.
  Obligation 220. all: body_obligation. Qed.
  Obligation 221. (* no body holds a record entry *) all: body_obligation. Qed.
  Obligation 222. obligation_order. Defined.
  Obligation 223. all: body_obligation. Qed.
  Obligation 224. all: body_obligation. Qed.
  Obligation 225. obligation_order. Defined.
  Obligation 226. all: body_obligation. Qed.
  Obligation 227. all: body_obligation. Qed.
  Obligation 228. all: body_obligation. Qed.
  Obligation 229. all: body_obligation. Qed.
  Obligation 230. all: body_obligation. Qed.
  Obligation 231. all: body_obligation. Qed.
  Obligation 232. all: body_obligation. Qed.
  Obligation 233. all: body_obligation. Qed.
  Obligation 234. all: body_obligation. Qed.
  Obligation 235. all: body_obligation. Qed.

  (** The checker from scratch: the initial environment of the context is
      computed once, at the start. *)
End type_check.
End Fixed_GCtx.
