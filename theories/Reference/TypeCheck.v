From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Syntactic.System Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import Evaluation NbE PseudoMonadic Subtyping MemberType TypeCheckBase.
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
Context {GC : GCtx}.

Section type_check.
  #[local]
  Hint Constructors type_check_order type_infer_order ext_order unit_order modexp_order : mctt.


  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations type_check_in G A (HA : (exists i, G ⊢ A : Typeω@i)) (P : tenv G) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, P, M, H =>
      let*o->b (exist _ B _) := type_infer_in G _ P M _ while _ in
      let*b _ := subtyping_env_impl G P (B : nf) A _ while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : tenv G) M (H : type_infer_order M) : { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with M => {
    | Typeω@j =>
        pureo (exist _ Typeωⁿ@(S j) _)
    | Type⟨M'⟩ =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let (W, _) := nbe_ty_env_impl gc_deps gc_stack G P Type⟨succl M'⟩ _ in
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
    | ℕ =>
        pureo (exist _ Typeⁿ@0 _)
    | zero =>
        pureo (exist _ ℕⁿ _)
    | succ M' =>
        let*b->o _ := type_check_in G ℕ _ P M' _ while _ in
        pureo (exist _ ℕⁿ _)
    | rec M' return A' | zero -> MZ | succ -> MS end =>
        let*b->o _ := type_check_in G ℕ _ P M' _ while _ in
        let HGN : ⊢ G ▹ ℕ := _ in
        let PN := tenv_ass G P ℕ HGN in
        let*o (exist _ UA' _) := type_infer_in (G ▹ ℕ) HGN PN A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check_in G A'[Id,,zero] _ P MZ _ while _ in
        let HAS : exists i, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Typeω@i := _ in
        let*b->o _ := type_check_in (G ▹ ℕ ▹ A') A'[Wk ⨟ Wk,,succ #1] HAS
                        (tenv_ass (G ▹ ℕ) PN A' (tenv_ctx_of_typ _ _ HAS)) MS _ while _ in
        let (A'', _) := nbe_ty_env_impl gc_deps gc_stack G P A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | ⊤ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Typeⁿ@0 _)
    | efq M' return A' =>
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let HGF : ⊢ G ▹ ⊥ := _ in
        let*o (exist _ UA' _) := type_infer_in (G ▹ ⊥) HGF (tenv_ass G P ⊥ HGF) A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let (A'', _) := nbe_ty_env_impl gc_deps gc_stack G P A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | Π B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (tenv_ass G P B HGB) C _ while _ in
        let (UC', _) := nbe_ty_env_impl gc_deps gc_stack (G ▹ B) (tenv_ass G P B HGB) UC _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC' while _ in
        let (W, _) := nbe_ty_env_impl gc_deps gc_stack G P (unf_pi_tm u v) _ in
        pureo (exist _ W _)
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let HGA : ⊢ G ▹ A' := _ in
        let*o (exist _ B' _) := type_infer_in (G ▹ A') HGA (tenv_ass G P A' HGA) M' _ while _ in
        let (A'', _) := nbe_ty_env_impl gc_deps gc_stack G P A' _ in
        pureo (exist _ (Πⁿ A'' B') _)
    | M' $ N' =>
        let*o (exist _ C _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ A (exist _ B _)) := get_subterms_of_pi_nf C while _ in
        let*b->o _ := type_check_in G (A : nf) _ P N' _ while _ in
        let (B', _) := nbe_ty_env_impl gc_deps gc_stack G P (B : nf)[Id,,N'] _ in
        pureo (exist _ B' _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD (tenv_def G P A' M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl gc_deps gc_stack G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer_in G _ P M' _ while _ in
        let HGD : ⊢ G ▸ (A : nf) ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ (A : nf) ≔ M') HGD (tenv_def G P (A : nf) M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl gc_deps gc_stack G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let*o (exist _ C _) := type_infer_in (G ▹ₘ U) _ (tenv_mod G P U) B' _ while _ in
        let (D, _) := nbe_ty_env_impl gc_deps gc_stack G P (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    (** A global infers the closed type that resolution returns for it,
        normalized at [G]; any other member, through its module. *)
    | a_mem M' x with inspect (modexp_spine M') => {
      | exist _ (R, nil, pre) Es with inspect (glob_lookup R pre x) => {
        | exist _ (Some A) Eg =>
            let (C, _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
            pureo (exist _ C _)
        | exist _ None Eg =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := member_term_dec _ G M' (x :: nil) _ while _ in
          let (B, _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
          pureo (exist _ B _) }
      | exist _ (R, N :: args, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := type_infer_in G HG P (apps (member_ref R (pre ++ x :: nil)) (N :: args)) _ while _ in
          pureo (exist _ A _) }
    | #x =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let (A', _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
        pureo (exist _ A' _)
    }
  with ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (tenv_of (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := tenv_of (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      pureb _
  | G, HG, ce_mod U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*b _ := unit_check (Ψ ++ G) _ U _ while _ in
      pureb _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body Φ), H =>
      let*b _ := ext_check G HG (body_ctx Φ ++ Δ) _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := modexp_check (Δ ++ G) _ E _ while _ in
      pureb _
  with modexp_check G (HG : ⊢ G) M (H : modexp_order M) : { G ⊢aᵐ M } + { ~ G ⊢aᵐ M } by struct H :=
  | G, HG, me_unit fp, H =>
      let*o->b (exist _ T _) := member_chain_mod_dec _ G (me_unit fp) (q_abs fp nil) eq_refl while _ in
      pureb _
  | G, HG, me_var x, H with inspect (ctx_find_mod G x) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_lit U, H =>
      let*b _ := unit_check G HG U _ while _ in
      pureb _
  | G, HG, me_mem M y, H with inspect (mod_qname (me_mem M y)) := {
    | exist _ (Some mq) Ep =>
        let*o->b (exist _ T _) := member_chain_mod_dec _ G (me_mem M y) mq Ep while _ in
        pureb _
    | exist _ None Ep =>
        let*b HM := modexp_check G HG M _ while _ in
        let*o->b (exist _ T _) := member_mod_dec _ G M (y :: nil) _ while _ in
        pureb _ }
  | G, HG, me_app M N, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ T _) := member_mod_dec _ G M nil _ while _ in
      let*o->b (existT _ B (exist _ T1 _)) := tele_view_dec T while _ in
      let*b _ := type_check_in G B _ (tenv_of G HG) N _ while _ in
      pureb _
  .

  (** One obligation per hole of the program, in order, each proved by the
      tactic for its kind (see the [ob_*] and [mo_*] tactics above). *)
  Obligation 1. (* ⊢ G *) ob_ctx_ext. Qed.
  Obligation 2. (* type_infer_order M *) ob_ord. Defined.
  Obligation 3. (* False *) ob_neg. Qed.
  Obligation 4. (* subtyping_order G B A *) ob_subord. Qed.
  Obligation 5. (* False *) ob_neg. Qed.
  Obligation 6. (* G ⊢a M ⟸ A *) ob_check. Qed.
  Obligation 7. (* G ⊢a Typeω@j ⟹ Typeωⁿ@(S j) /\ (exists (UA : nf) (u : unf),... *) ob_post. Qed.
  Obligation 8. (* ⊢ G *) Qed.
  Obligation 9. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 10. (* False *) ob_neg. Qed.
  Obligation 11. (* False *) ob_neg. Qed.
  Obligation 12. (* nbe_ty_order gc_deps gc_stack G Type⟨succl M'⟩ *) ob_suniv_nbe. Qed.
  Obligation 13. (* G ⊢a Type⟨M'⟩ ⟹ W /\ (exists (UA : nf) (u : unf), G ⊢a W... *) ob_suniv_post. Qed.
  Obligation 14. (* G ⊢a Level@k ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢... *) ob_post_suniv0. Qed.
  Obligation 15. (* G ⊢a 𝕃ᵒ m ⟹ Levelⁿ@(fst m) /\ (exists (UA : nf) (u : unf), G ⊢a Le... *) ob_post_lvl. Qed.
  Obligation 16. (* ⊢ G *) Qed.
  Obligation 17. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 18. (* False *) ob_neg. Qed.
  Obligation 19. (* False *) ob_neg. Qed.
  Obligation 20. (* G ⊢a succl M' ⟹ Levelⁿ@k /\ (exists (UA : nf) (u : unf), G ... *) ob_post_lvl. Qed.
  Obligation 21. (* ⊢ G *) Qed.
  Obligation 22. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 23. (* False *) ob_neg. Qed.
  Obligation 24. (* False *) ob_neg. Qed.
  Obligation 25. (* ⊢ G *) Qed.
  Obligation 26. (* type_infer_order N' *) ob_ord. Defined.
  Obligation 27. (* False *) ob_neg. Qed.
  Obligation 28. (* False *) ob_neg. Qed.
  Obligation 29. (* G ⊢a maxl M' N' ⟹ Levelⁿ@(max k k') /\ (exists (UA : nf) (u : unf), ... *) ob_post_lvl. Qed.
  Obligation 30. (* G ⊢a ℕ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 31. (* G ⊢a zero ⟹ ℕⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ℕ ⟹ U... *) ob_post. Qed.
  Obligation 32. (* exists i : nat, G ⊢ ℕ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 33. (* type_check_order M' *) ob_ord. Defined.
  Obligation 34. (* False *) ob_neg. Qed.
  Obligation 35. (* G ⊢a succ M' ⟹ ℕⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ℕ ... *) ob_post. Qed.
  Obligation 36. (* exists i : nat, G ⊢ ℕ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 37. (* type_check_order M' *) ob_ord. Defined.
  Obligation 38. (* False *) ob_neg. Qed.
  Obligation 39. (* ⊢ G ▹ ℕ *) ob_ctx_ext. Qed.
  Obligation 40. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 41. (* False *) ob_neg. Qed.
  Obligation 42. (* False *) ob_neg. Qed.
  Obligation 43. (* exists j, G ⊢ A'[Id,,zero] : Typeω@j *)
    clear_defs.
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢s Id,,zero : G ▹ ℕ) as Hσ by mauto 3.
    (** [sub_preserves_exp] is applied by hand: unifying its conclusion would
        require solving [?A[?σ] ≟ Typeω@i], which [eapply] cannot do. *)
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 44. (* type_check_order MZ *) ob_ord. Defined.
  Obligation 45. (* False *) ob_neg. Qed.
  Obligation 46. (* exists j, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Typeω@j *)
    clear_defs.
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (⊢ G ▹ ℕ ▹ A') by mauto 2.
    assert (G ▹ ℕ ▹ A' ⊢s Wk ⨟ Wk,,succ #1 : G ▹ ℕ) as Hσ by mauto 3.
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 47. (* type_check_order MS *) ob_ord. Defined.
  Obligation 48. (* False *) ob_neg. Qed.
  Obligation 49. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeω@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 50. (* G ⊢a rec M' … end ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    (** The motive at the scrutinee is a type, so its normal form is one too,
        and [level_of_nbe] gives both halves at once. *)
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 51. (* G ⊢a ⊤ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 52. (* G ⊢a ⋆ ⟹ ⊤ⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ⊤ ⟹ UA /... *) ob_post. Qed.
  Obligation 53. (* G ⊢a ⊥ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 54. (* exists i : nat, G ⊢ ⊥ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 55. (* type_check_order M' *) ob_ord. Defined.
  Obligation 56. (* False *) ob_neg. Qed.
  Obligation 57. (* ⊢ G ▹ ⊥ *) ob_ctx_ext. Qed.
  Obligation 58. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 59. (* False *) ob_neg. Qed.
  Obligation 60. (* False *) ob_neg. Qed.
  Obligation 61. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeω@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 62. (* G ⊢a efq M' return A' ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 63. Qed.
  Obligation 64. (* type_infer_order B *) ob_ord. Defined.
  Obligation 65. (* False *) ob_neg. Qed.
  Obligation 66. (* False *) ob_neg. Qed.
  Obligation 67. (* ⊢ G ▹ B *) ob_ctx. Qed.
  Obligation 68. (* type_infer_order C *) ob_ord. Defined.
  Obligation 69. (* False *) ob_neg. Qed.
  Obligation 70. (* nbe_ty_order gc_deps gc_stack (G ▹ B) UC *)
    clear_defs.
    destruct_conjs.
    match goal with H : G ▹ B ⊢ (?UC : exp) : Typeω@?i |- nbe_ty_order _ _ _ ?UC =>
      destruct (soundness_ty H) as [W [HW _]] end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 71. (* False: the codomain's universe, normalised, is no universe *)
    clear_defs.
    lazymatch goal with H : _ ⊢a _ ⟹ _ |- False => inversion H; subst; clear H end.
    destruct_conjs.
    functional_alg_type_infer_rewrite_clear.
    functional_nbe_rewrite_clear.
    firstorder.
  Qed.
  Obligation 72. (* nbe_ty_order gc_deps gc_stack G (unf_pi_tm u v) *)
    clear_defs.
    destruct_conjs.
    match goal with
    | HB : G ⊢a B ⟹ ?UB, Hu : is_univ_nf ?UB u, HC : G ▹ B ⊢a C ⟹ ?UC,
      HnC : nbe_ty gc_deps gc_stack (G ▹ B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
        destruct (alg_pi_parts_sound HG HB Hu HC HnC Hv) as (HBu & HCv & Hvw)
    end.
    destruct (wf_unf_pi_tm HBu HCv Hvw) as [k Hk].
    destruct (soundness_ty Hk) as [W [HW _]].
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 73. (* G ⊢a Π B C ⟹ W, the normal form of its universe, and that is a type *)
    clear_defs.
    destruct_conjs.
    match goal with
    | HB : G ⊢a B ⟹ ?UB, Hu : is_univ_nf ?UB u, HC : G ▹ B ⊢a C ⟹ ?UC,
      HnC : nbe_ty gc_deps gc_stack (G ▹ B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
        destruct (alg_pi_parts_sound HG HB Hu HC HnC Hv) as (HBu & HCv & Hvw)
    end.
    destruct (wf_unf_pi_tm HBu HCv Hvw) as [k Hk].
    assert (G ⊢ unf_pi_tm u v ≈ W : Typeω@k) by (eapply soundness_ty'; eassumption).
    assert (HWk : G ⊢ W : Typeω@k) by (gen_presups; assumption).
    split; [ eapply ati_pi; eassumption |].
    split; [| eexists; exact HWk ].
    destruct (alg_type_infer_large_typ_complete (user_exp_nf W) HWk) as [? [? [? [? _]]]].
    do 2 eexists; split; eassumption.
  Qed.
  Obligation 74. Qed.
  Obligation 75. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 76. (* False *) ob_neg. Qed.
  Obligation 77. (* False *) ob_neg. Qed.
  Obligation 78. (* ⊢ G ▹ A' *) ob_ctx. Qed.
  Obligation 79. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 80. (* False *) ob_neg. Qed.
  Obligation 81. (* nbe_ty_order gc_deps gc_stack G A' *)
    clear_defs.
    saturate_infer_univ.
    match goal with H : G ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A' : Typeω@k) as [? []]%soundness_ty by exact H end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 82. (* G ⊢a λ A' M' ⟹ Πⁿ A'' B', and [Π A'' B'] is a type *)
    clear_defs.
    saturate_infer_univ.
    (** The annotation's normal form is a type at the same level, and the
        body's type is one in the context of that normal form. *)
    assert (⊢ G ▹ A') by mauto 2.
    assert (G ⊢ A' ≈ A'' : Typeω@(unf_large u)) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (G ⊢ A'' : Typeω@(unf_large u)) by (gen_presups; mauto 2).
    assert (⊢ G ▹ (A'' : exp)) by mauto 2.
    assert (exists l, G ▹ (A'' : exp) ⊢ B' : Typeω@l) as [l HB'] by (eexists; mauto 4).
    split; [ mauto 3 | split ].
    - destruct (alg_type_infer_large_typ_complete (user_exp_nf A'') ltac:(eassumption)) as [UA'' [w [HUA'' [HwA'' _]]]].
      destruct (alg_type_infer_large_typ_complete (user_exp_nf B') HB') as [UB' [w' [HUB' [HwB' _]]]].
      destruct (alg_pi_infer_univ G _ _ _ _ _ _ HG HUA'' HUB' HwA'' HwB') as (W0 & w0 & HW0 & Hw0 & _).
      do 2 eexists; split; eassumption.
    - exists (max (unf_large u) l); apply wf_pi;
        [ mauto 3 using lift_exp_max_left | mauto 3 using lift_exp_max_right ].
  Qed.
  Obligation 83. Qed.
  Obligation 84. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 85. (* False *) ob_neg. Qed.
  Obligation 86. (* False *) ob_neg. Qed.
  Obligation 87. (* exists i : nat, G ⊢ A : Typeω@i *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 88. (* type_check_order N' *) ob_ord. Defined.
  Obligation 89. (* False *) ob_neg. Qed.
  Obligation 90. (* nbe_ty_order gc_deps gc_stack G s[Id,,N'] *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    saturate_infer_univ.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    (** The codomain is a type at the large level of the index of its
        normalised universe. *)
    assert (G ⊢ s[Id,,N'] : Typeω@(unf_large v)) as [? []]%soundness_ty by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 91. (* G ⊢a M' $ N' ⟹ B' /\ (B' is a type) *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    split; [mauto 3 |].
    saturate_infer_univ.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ s[Id,,N'] : Typeω@(unf_large v)) by mauto 3.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 92. Qed.
  Obligation 93. (* False *) ob_neg. Qed.
  Obligation 94. (* nbe_ty_order gc_deps gc_stack G A *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [? [? []]%soundness_ty] by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 95. (* G ⊢a #x ⟹ A', and [A'] is a type *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [i] by mauto 3.
    split; [ mauto 3 |].
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 96. Qed.
  Obligation 97. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 98. (* False *) ob_neg. Qed.
  Obligation 99. (* False *) ob_neg. Qed.
  Obligation 100. (* exists i, G ⊢ A' : Typeω@i *)
    clear_defs.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 101. (* type_check_order M' *) ob_ord. Defined.
  Obligation 102. (* False *) ob_neg. Qed.
  Obligation 103. (* ⊢ G ▸ A' ≔ M' *) ob_ctx. Qed.
  Obligation 104. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 105. (* False *) ob_neg. Qed.
  Obligation 106. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 107. (* G ⊢a ℓ A' ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 108. Qed.
  Obligation 109. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 110. (* False *) ob_neg. Qed.
  Obligation 111. (* ⊢ G ▸ A ≔ M' *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    mauto 3.
  Qed.
  Obligation 112. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 113. (* False *) ob_neg. Qed.
  Obligation 114. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 115. (* G ⊢a ℓ ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 116. (* unit_order U *) ob_ord. Defined.
  Obligation 117. (* False *) ob_neg. Qed.
  Obligation 118. (* ⊢ G ▹ₘ U *) ob_ctx. Qed.
  Obligation 119. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 120. (* False *) ob_neg. Qed.
  Obligation 121. (* nbe_ty_order gc_deps gc_stack G C[Id ,,ₘ me_lit U] *)
    clear_defs.
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢s Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? [? []]%soundness_ty]
        by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 122. (* G ⊢a ℓₘ U in B' ⟹ D, and [D] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢s Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 123. (* nbe_ty_order gc_deps gc_stack G A *) mo_1. Qed.
  Obligation 124. (* G ⊢a a_mem M' x ⟹ C /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_1. Qed.
  Obligation 125. (* modexp_order M' *) ob_ord. Defined.
  Obligation 126. (* False *) ob_mem_neg. Qed.
  Obligation 127. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 128. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M' ≈ M' *) mo_18. Qed.
  Obligation 129. (* False *) ob_mem_neg. Qed.
  Obligation 130. (* nbe_ty_order gc_deps gc_stack G A *) mo_7. Qed.
  Obligation 131. (* G ⊢a a_mem M' x ⟹ B /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_8. Qed.
  Obligation 132. (* modexp_order M' *) ob_ord. Defined.
  Obligation 133. (* False *) ob_mem_neg. Qed.
  Obligation 134. (* type_infer_order (apps (member_ref R (pre ++ x :: nil) $ ... *) ob_ord_apps. Defined.
  Obligation 135. (* False *) ob_mem_neg. Qed.
  Obligation 136. (* G ⊢a a_mem M' x ⟹ A /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_9. Qed.
  Obligation 137. (* G ⊢aˣ ⋅ *) ob_check. Qed.
  Obligation 138. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 139. (* False *) mo_10. Qed.
  Obligation 140. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 141. (* type_infer_order A *) ob_ord. Defined.
  Obligation 142. (* False *) mo_10. Qed.
  Obligation 143. (* False *) mo_10. Qed.
  Obligation 144. (* G ⊢aˣ Ψ ▹ A *) ob_check. Qed.
  Obligation 145. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 146. (* False *) mo_10. Qed.
  Obligation 147. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 148. (* type_infer_order A *) ob_ord. Defined.
  Obligation 149. (* False *) mo_10. Qed.
  Obligation 150. (* False *) mo_10. Qed.
  Obligation 151. (* exists i0 : nat, Ψ ++ G ⊢ A : Typeω@i0 *) mo_14. Qed.
  Obligation 152. (* type_check_order M *) ob_ord. Defined.
  Obligation 153. (* False *) mo_10. Qed.
  Obligation 154. (* G ⊢aˣ Ψ ▸ A ≔ M *) ob_check. Qed.
  Obligation 155. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 156. (* False *) mo_10. Qed.
  Obligation 157. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 158. (* unit_order U *) ob_ord. Defined.
  Obligation 159. (* False *) mo_10. Qed.
  Obligation 160. (* G ⊢aˣ Ψ ▹ₘ U *) ob_check. Qed.
  Obligation 161. (* ext_order (body_ctx Φ ++ Δ) *) ob_ord. Defined.
  Obligation 162. (* False *) mo_10. Qed.
  Obligation 163. (* False *) mo_10. Qed.
  Obligation 164. (* False *) mo_10. Qed.
  Obligation 165. (* False *) mo_10. Qed.
  Obligation 166. (* G ⊢aᵘ gu_body Δ Φ *) ob_check. Qed.
  Obligation 167. (* ext_order Δ *) ob_ord. Defined.
  Obligation 168. (* False *) mo_10. Qed.
  Obligation 169. (* False *) mo_10. Qed.
  Obligation 170. (* ⊢ Δ ++ G *) ob_ctx. Qed.
  Obligation 171. (* modexp_order E *) ob_ord. Defined.
  Obligation 172. (* False *) mo_10. Qed.
  Obligation 173. (* G ⊢aᵘ gu_mk Δ (md_alias E) *) ob_check. Qed.
  Obligation 174. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 175. (* False *) mo_10. Qed.
  Obligation 176. (* G ⊢aᵐ me_unit fp *) mo_2. Qed.
  Obligation 177. (* G ⊢aᵐ me_var x *) mo_19. Qed.
  Obligation 178. (* False *) mo_20. Qed.
  Obligation 179. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 180. (* False *) mo_3. Qed.
  Obligation 181. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 182. (* modexp_order M *) ob_ord. Defined.
  Obligation 183. (* False *) mo_3. Qed.
  Obligation 184. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 185. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 186. (* False *) mo_10. Qed.
  Obligation 187. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 188. (* modexp_order M *) ob_ord. Defined.
  Obligation 189. (* False *) mo_10. Qed.
  Obligation 190. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 191. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 192. (* False *) mo_10. Qed.
  Obligation 193. (* False *) mo_21. Qed.
  Obligation 194. (* exists i : nat, G ⊢ B : Typeω@i *) mo_22. Qed.
  Obligation 195. (* type_check_order N *) ob_ord. Defined.
  Obligation 196. (* False *) mo_21. Qed.
  Obligation 197. (* G ⊢aᵐ me_app M N *) ob_check. Qed.
  Obligation 198. (* unit_order U *) ob_ord. Defined.
  Obligation 199. (* False *) mo_10. Qed.
  Obligation 200. (* G ⊢aᵐ me_lit U *) ob_check. Qed.

  (** The checker from scratch: the initial environment of the context is
      computed once, at the start. *)
End type_check.
End Fixed_GCtx.
