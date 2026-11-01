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
  Equations type_check_in G A (HA : G ⊢ᵗ A) (P : checker_env G) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, P, M, H =>
      let*o->b (exist _ B _) := type_infer_in G _ P M _ while _ in
      let*b _ := subtyping_env_impl F G P (B : nf) A _ while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : checker_env G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A /\ (exists UA r u, G ⊢a A ⟹ UA /\ is_sort_nf UA r u) /\ G ⊢ᵗ A } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
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
    (** [Prop] and the closed propositions *)
    | Propₘ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⊤ =>
        pureo (exist _ Propⁿ _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | a_tt =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Propⁿ _)
    (** Ex falso: the target is a type of either sort, the proof is checked
        at [⊥] *)
    | efq M' return C' =>
        let*o (exist _ UC _) := type_infer_in G _ P C' _ while _ in
        let*o (existT _ rC (exist _ uC _)) := sort_nf_dec UC while _ in
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let (C'', _) := nbe_ty_env_impl F G P C' _ in
        pureo (exist _ C'' _)
    (** A conjunction of two propositions *)
    | Σₚ P' Q' =>
        let*o (exist _ UP _) := type_infer_in G _ P P' _ while _ in
        let*b->o _ := prop_nf_dec UP while _ in
        let HGP : ⊢ G ▹ P' := _ in
        let*o (exist _ UQ _) := type_infer_in (G ▹ P') HGP (checker_env_ass F G P P' HGP) Q' _ while _ in
        let*b->o _ := prop_nf_dec UQ while _ in
        pureo (exist _ Propⁿ _)
    (** A proof of a conjunction: the annotation is a proposition whose
        normal form is a conjunction, and the components check at its parts *)
    | a_conj T' M' N' =>
        let*o (exist _ UT _) := type_infer_in G _ P T' _ while _ in
        let*b->o _ := prop_nf_dec UT while _ in
        let (W, _) := nbe_ty_env_impl F G P T' _ in
        let*o (existT _ Pc (exist _ Qc _)) := get_and_nf W while _ in
        let*b->o _ := type_check_in G (Pc : nf) _ P M' _ while _ in
        let*b->o _ := type_check_in G (Qc : nf)[Id,,M'] _ P N' _ while _ in
        pureo (exist _ (Σₚⁿ Pc Qc) _)
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
    (** The placeholder type and its element *)
    | a_placeholder_type =>
        pureo (exist _ Typeⁿ@0 _)
    | a_placeholder =>
        pureo (exist _ nf_placeholder_type _)
    (** A [Π] over a type of either sort *)
    | Π B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (existT _ rB (exist _ u _)) := sort_nf_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (checker_env_ass F G P B HGB) C _ while _ in
        let (UC', _) := nbe_ty_env_impl F (G ▹ B) (checker_env_ass F G P B HGB) UC _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC' while _ in
        let (W, _) := nbe_ty_env_impl F G P (universe_nf_pi_tm u v) _ in
        pureo (exist _ W _)
    (** A [∀]: over a type of either sort, into propositions *)
    | ∀ₚ B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (existT _ rB (exist _ u _)) := sort_nf_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (checker_env_ass F G P B HGB) C _ while _ in
        let*b->o _ := prop_nf_dec UC while _ in
        pureo (exist _ Propⁿ _)
    (** The forms of inductive types ([Extraction.IndCheck]); the
        eliminator's recursive calls are passed on. *)
    | a_ind pq k => ind_infer F G HG P pq k
    | a_con pq k c => con_infer F G HG P pq k c
    (** The forms of record types ([Extraction.RecordCheck]). *)
    | a_record pq => record_infer F G HG P pq
    | a_tuple T' fs =>
        tuple_infer F G HG P T' fs (type_infer_in G HG P T' ltac:(obligation_order_record))
          (fun fm Hfm A'' HA'' => type_check_in G A'' HA'' P (snd fm) ltac:(obligation_order_record))
    | a_proj f M' => proj_infer F G HG P f M' (type_infer_in G HG P M' ltac:(obligation_order_record))
    | a_nlit n => inright (fun A HA => alg_nlit_no_infer G n A HA)
    | a_ntok => inright (fun A HA => alg_ntok_no_infer G A HA)
    | a_elim r oq Us m Bks M' =>
        elim_infer F G HG P r oq Us m Bks M'
          (type_infer_in G HG P M' ltac:(obligation_order_elim))
          (fun U HU G' A'' HA'' P' => type_check_in G' A'' HA'' P' U ltac:(obligation_order_elim))
          (fun b Z Hb HZ G' HG' P' => type_infer_in G' HG' P' Z ltac:(obligation_order_elim))
          (fun b Hb G' HG' P' => type_infer_in G' HG' P' (eb_motive b) ltac:(obligation_order_elim))
          (fun b br Hb Hbr G' A'' HA'' P' => type_check_in G' A'' HA'' P' (snd br) ltac:(obligation_order_elim))
    (** A λ over a type of either sort: a function, or a proof of a [∀], by
        the sort of its body's type *)
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA' while _ in
        let HGA : ⊢ G ▹ A' := _ in
        let*o (exist _ B' _) := type_infer_in (G ▹ A') HGA (checker_env_ass F G P A' HGA) M' _ while _ in
        let (r, _) := checker_relevance F (G ▹ A') (checker_env_ass F G P A' HGA) B' _ in
        let (A'', _) := nbe_ty_env_impl F G P A' _ in
        pureo (exist _ (nf_pi r A'' B') _)
    (** An application of a function or of a proof of a [∀] *)
    | M' $ N' =>
        let*o (exist _ C _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ r (existT _ A (exist _ B _))) := get_pi_nf C while _ in
        let*b->o _ := type_check_in G (A : nf) _ P N' _ while _ in
        let (B', _) := nbe_ty_env_impl F G P (B : nf)[Id,,N'] _ in
        pureo (exist _ B' _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA' while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD (checker_env_def F G P A' M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred, and is a
        relevant type. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer_in G _ P M' _ while _ in
        let (r, _) := checker_relevance F G P (A : nf) _ in
        let*b->o _ := relevance_eq_dec r relevant while _ in
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
  (** An assumption of a type of either sort *)
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (checker_env_of F (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      pureb _
  (** A definition of a type of either sort *)
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
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
  (** The parameters of a unit: assumptions of types of universes. *)
  with params_check G (HG : ⊢ G) Δ (H : ext_order Δ) : { G ⊢aᵖ Δ } + { ~ G ⊢aᵖ Δ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Δ, H =>
      let*b _ := params_check G HG Δ _ while _ in
      let HΔ : ⊢ Δ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Δ ++ G) HΔ (checker_env_of F (Δ ++ G) HΔ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, _ :: Δ, H => right _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body sm_closed Φ), H => right (alg_unit_closed_no G Δ Φ)
  | G, HG, gu_mk Δ (md_body sm_open Φ), H =>
      let*b _ := params_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*o->b (exist _ Φx _) := body_check (Δ ++ G) _ Φ _ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := body_shape_dec Φx Φx while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := params_check G HG Δ _ while _ in
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
  (** A definition, of a type of the sort its tag says *)
  | G, HG, gm_ext Φ x (ge_def b pv r A (Some M)), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (checker_env_of F _ HGx) A _ while _ in
      let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      let*b->o _ := relevance_eq_dec rA r while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (checker_env_of F _ HGx) M _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def b pv r A (Some M))) _)
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
  Solve All Obligations with checker_obligation.
End type_check.
End Fixed_GCtx.
