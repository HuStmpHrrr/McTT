From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval FastDomain Simulation NbE PseudoMonadic Subtyping FastDesc MemberType.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * What the Two Checkers Share

    The extracted checker ([Extraction.TypeCheck]) and the reference checker
    it refines ([Reference.TypeCheck]) recurse along the same orders, decide
    the same side conditions, carry the same initial environment, and prove
    their obligations with the same tactics, which are therefore defined
    here, outside any section, rather than locally to one checker. *)

Section Fixed_GCtx.
Context {GC : GCtx}.

Section type_check.
  (** Whether a normal form is a universe, and at which index: the side
      condition of every rule that asks for a type.  A plain [match], so that
      the extracted code is one case analysis and the two universe cases are
      visibly the only ones. *)
  Definition univ_nf_idx_dec (A : nf) : { u : universe_nf | is_univ_nf A u } + { forall u, ~ is_univ_nf A u }.
  Proof.
    refine (match A with
            | nf_typ i => inleft (exist _ (universe_large i) _)
            | nf_univ c xs => inleft (exist _ (universe_small (c, xs)) _)
            | _ => inright _
            end);
      first [ constructor | intros ? H; inversion H ].
  Defined.

  (** Whether a normal form is the type of a type, of which sort and in
      which universe: a universe, or [Prop] ([is_sort_nf]). *)
  Definition sort_nf_dec (A : nf) : { r & { u : universe_nf | is_sort_nf A r u } } + { forall r u, ~ is_sort_nf A r u }.
  Proof.
    destruct (univ_nf_idx_dec A) as [[u Hu] | Hnu]; [ left; exists relevant, u; constructor; exact Hu |].
    destruct A; try (right; intros ? ? H; inversion H; subst; eapply Hnu; eassumption).
    left; exists propositional, (universe_small (ordinal_of_nat 0, nil)); constructor.
  Defined.

  (** Whether a normal form is [Prop]. *)
  #[derive(equations=no,eliminator=no)]
  Equations prop_nf_dec (A : nf) : { A = Propⁿ } + { A <> Propⁿ } :=
  | Propⁿ => left eq_refl
  | _ => right _
  .

  (** Whether a normal form is a [Π] of either sort, and its parts. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_pi_nf (A : nf) : { r & { B & { C | A = nf_pi r B C } } } + { forall r B C, A <> nf_pi r B C } :=
  | nf_pi r B C => pureo (existT _ r (existT _ B (exist _ C _)))
  | _ => inright _
  .

  (** Whether a normal form is a conjunction, and its parts. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_and_nf (A : nf) : { P & { Q | A = Σₚⁿ P Q } } + { forall P Q, A <> Σₚⁿ P Q } :=
  | Σₚⁿ P Q => pureo (existT _ P (exist _ Q _))
  | _ => inright _
  .

  (** Whether a normal form is a type of levels, and of which sort. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_level_sort_nf (A : nf) : { k | A = Levelⁿ@k } + { forall k, A <> Levelⁿ@k } :=
  | Levelⁿ@k => pureo (exist _ k _)
  | _        => inright _
  .

  (** Extraction should set the 9th bit of [Extraction Flag] (for example,
      [Set Extraction Flag 1007.]); otherwise the decisions that return
      parts introduce redundant pair construction and pattern matching. *)
  Extraction Inline univ_nf_idx_dec sort_nf_dec prop_nf_dec get_pi_nf get_and_nf get_level_sort_nf.

  (** ** Deciding the Side Conditions of Units *)

  Definition tele_ass_dec : forall Δ, { tele_ass Δ } + { ~ tele_ass Δ }.
  Proof.
    induction Δ as [| [A | A M | U | A M U] Δ IH].
    - left; constructor.
    - destruct IH as [H | H]; [ left; constructor; eauto | right; intros Hf; inversion Hf; contradiction ].
    - right; intros Hf; inversion Hf as [| ? ? He _]; destruct He; discriminate.
    - right; intros Hf; inversion Hf as [| ? ? He _]; destruct He; discriminate.
    - right; intros Hf; inversion Hf as [| ? ? He _]; destruct He; discriminate.
  Defined.

  (** [ListDec.NoDup_dec] is opaque, so extraction would bypass it. *)
  Definition names_nodup_dec : forall l : list string, { NoDup l } + { ~ NoDup l }.
  Proof.
    induction l as [| x l IH].
    - left; constructor.
    - destruct (in_dec string_dec x l) as [Hin | Hn].
      + right; intros Hnd; inversion Hnd; contradiction.
      + destruct IH as [H | H]; [ left; constructor; assumption | right; intros Hnd; inversion Hnd; contradiction ].
  Defined.

  Definition entry_shape_dec : forall E E', { entry_shape E E' } + { ~ entry_shape E E' }.
  Proof.
    intros [b pv r A [M |] | pm U | pvi Di Φi | pd ? ? ? | ? ? ?] [b' pv' r' A' [M' |] | pm' U' | pvi' Di' Φi' | pd' ? ? ? | ? ? ?]; cbn;
      try (right; intros []; fail); try (left; exact I).
    - destruct b, b', (Bool.bool_dec pv pv'), (relevance_eq_dec r r'); try (right; intuition congruence; fail); left; auto.
    - exact (Bool.bool_dec pm pm').
    - exact (Bool.bool_dec pd pd').
  Defined.

  Definition import_item_eq_dec : forall it it' : import_item, { it = it' } + { it <> it' }.
  Proof. repeat decide equality; apply string_dec. Defined.

  Definition body_shape_dec : forall Φ Φ', { body_shape Φ Φ' } + { ~ body_shape Φ Φ' }.
  Proof.
    induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its']; cbn;
      try (left; exact I); try (right; intros []; fail).
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (string_dec x x') as [H2 | H2]; [| right; intuition ].
      destruct (entry_shape_dec E E') as [H3 | H3]; [ left; auto | right; intuition ].
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (list_eq_dec import_item_eq_dec its its') as [H2 | H2]; [ left; auto | right; intuition ].
  Defined.

  (** The outermost parameter of an arity, if any. *)
  Equations tele_view_dec (T : ctx) : { B : typ & { T1 : ctx | tele_view T = Some (B, T1) } } + { tele_view T = None } :=
  tele_view_dec T with inspect (tele_view T) := {
    | exist _ (Some (B, T1)) E => inleft (existT _ B (exist _ T1 E))
    | exist _ None E => inright E }.

  (** What a description gives the rules: a member's type ([mdesc_type]), a
      module's telescope ([mdesc_mod_tele]) and module part ([mdesc_mod]), read off
      the fast description of [MemberType.mdenote_impl]. *)
  Equations mdesc_type_dec (R : fmdesc) : { A | mdesc_type (decode_desc R) = Some A } + { mdesc_type (decode_desc R) = None } :=
  mdesc_type_dec R with fmdesc_type_s R := {
    | exist _ (Some A) E => inleft (exist _ A E)
    | exist _ None E => inright E }.

  Equations mdesc_mod_tele_dec (R : fmdesc) : { T | mdesc_mod_tele (decode_desc R) = Some T } + { mdesc_mod_tele (decode_desc R) = None } :=
  mdesc_mod_tele_dec R with inspect (fmdesc_mod_tele R) := {
    | exist _ (Some T) E => inleft (exist _ T (eq_trans (fmdesc_mod_tele_dec R) E))
    | exist _ None E => inright (eq_trans (fmdesc_mod_tele_dec R) E) }.

  Equations mdesc_mod_dec (R : fmdesc) : { Rm : fmdesc | mdesc_mod (decode_desc R) = Some (decode_desc Rm) } + { mdesc_mod (decode_desc R) = None } :=
  mdesc_mod_dec R with fmdesc_mod_s R := {
    | exist _ (Some Rm) E => inleft (exist _ Rm E)
    | exist _ None E => inright E }.

  Extraction Inline mdesc_type_dec mdesc_mod_tele_dec mdesc_mod_dec tele_view_dec.

  (** ** Facts the Obligations Use *)


  Lemma nbe_order_of_typ : forall G X i, G ⊢ X : Typeω@i -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * HX; destruct (soundness_ty HX) as [W [HW _]]; eauto using nbe_ty_order_sound. Qed.

  (** The same for a type of either sort. *)
  Lemma nbe_order_of_type : forall G X, G ⊢ᵗ X -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * [S HS HX]; destruct (nbe_ty_exists_sort HS HX) as [W HW]; eauto using nbe_ty_order_sound. Qed.

  (** The normal form of a type is a type, both algorithmically and
      declaratively: the two halves of [type_infer]'s postcondition. *)
  Lemma level_of_nbe : forall G X D,
      G ⊢ᵗ X ->
      nbe_ty_f G X D ->
      (exists UD r u, G ⊢a D ⟹ UD /\ is_sort_nf UD r u) /\ G ⊢ᵗ D.
  Proof.
    intros * [S HS HX] HD.
    assert (G ⊢ X ≈ D : S) by (eapply soundness_ty_at_sort; eassumption).
    assert (HDS : G ⊢ D : S) by (gen_presups; eassumption).
    assert (⊢ G) by (gen_presups; assumption).
    destruct (alg_type_check_sort_infer ltac:(eassumption) HS (alg_type_check_complete (user_exp_nf D) HDS))
      as (UD & r & u & ? & ?).
    split; [ exists UD, r, u; split; assumption | exact (mk_wf_type _ HS HDS) ].
  Qed.

  (** The postcondition of a type of a large universe. *)
  Lemma level_of_nbe_typ : forall G X i D,
      G ⊢ X : Typeω@i ->
      nbe_ty_f G X D ->
      (exists UD r u, G ⊢a D ⟹ UD /\ is_sort_nf UD r u) /\ G ⊢ᵗ D.
  Proof. intros * HX; apply level_of_nbe, (wf_type_univ HX). Qed.

  (** The postcondition of a normal form that is a type. *)
  Lemma infer_post_of_type : forall G (T : nf),
      G ⊢ᵗ T -> (exists UD r u, G ⊢a T ⟹ UD /\ is_sort_nf UD r u) /\ G ⊢ᵗ T.
  Proof.
    intros * [S HS HT].
    assert (⊢ G) by (gen_presups; assumption).
    destruct (alg_type_check_sort_infer ltac:(eassumption) HS (alg_type_check_complete (user_exp_nf T) HT))
      as (UD & r & u & ? & ?).
    split; [ exists UD, r, u; split; assumption | exact (mk_wf_type _ HS HT) ].
  Qed.

  (** A type of either sort, read off the sort its inference gives. *)
  (** A type stays one along a substitution. *)
  Lemma wf_type_sub_preserves : forall Γ Δ σ A, Δ ⊢ᵗ A -> Γ ⊢ˢ σ : Δ -> Γ ⊢ᵗ A[σ].
  Proof.
    intros * [S HS HA] Hσ; apply (mk_wf_type S HS).
    rewrite <- (type_sort_sub S σ HS); exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ).
  Qed.

  (** The normal form of a type is a type. *)
  Lemma wf_type_nbe : forall G X W, G ⊢ᵗ X -> nbe_ty_f G X W -> G ⊢ᵗ W.
  Proof. intros * HX HW; exact (proj2 (level_of_nbe _ _ _ HX HW)). Qed.

  (** The parts of a [Π] or a [∀] that is a type are types. *)
  Lemma wf_type_pi_inv : forall G r A B, G ⊢ᵗ a_pi r A B -> G ⊢ᵗ A /\ G ▹ A ⊢ᵗ B.
  Proof.
    intros * [S HS H]; destruct r.
    - destruct (wf_pi_typed_large H) as [k Hk]; destruct (wf_pi_inversion' Hk) as [[HA | HA] HB].
      + split; [ exact (wf_type_univ HA) | exact (wf_type_univ HB) ].
      + split; [ exact (wf_type_prop HA) | exact (wf_type_univ HB) ].
    - destruct (wf_all_inversion _ _ _ _ _ _ H) as [S' HS' HA HP _].
      split; [ exact (mk_wf_type _ HS' HA) | exact (wf_type_prop HP) ].
  Qed.

  (** A type is of one sort. *)
  Lemma nbe_ty_relevance_functional : forall G A r r', nbe_ty_relevance G A r -> nbe_ty_relevance G A r' -> r = r'.
  Proof.
    intros * (ρ & a & Hρ & Ha & <-) (ρ' & a' & Hρ' & Ha' & <-).
    functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; reflexivity.
  Qed.

  (** A [Π] or a [∀] of a type of either sort and a type of the tag's sort
      over it is a type. *)
  Lemma wf_type_pi_of_parts : forall G r A B, G ⊢ᵗ A ->
      (exists l : nat, G ▹ A ⊢ B : relevance_sort r Typeω@l) -> G ⊢ᵗ a_pi r A B.
  Proof.
    intros * [SA HSA HA] [l HB].
    assert (⊢ G) by (gen_presups; assumption).
    destruct HSA as [k |].
    - pose (m := Nat.max k l).
      assert (HAm : G ⊢ A : Typeω@m) by (eapply lift_exp_max_left; exact HA).
      assert (HGA : ⊢ G ▹ A) by (eapply wf_ctx_extend; [ exact HA | constructor ]).
      assert (HBm : G ▹ A ⊢ B : relevance_sort r Typeω@m)
        by (destruct r; cbn [relevance_sort] in *; [ eapply lift_exp_max_right; exact HB | exact HB ]).
      eapply wf_type_relevance.
      eapply wf_pi; [ apply wf_is_univ_large; assumption | exact HAm | apply pi_domain_universe |].
      destruct r; exact HBm.
    - eapply wf_type_relevance.
      eapply wf_pi; [ apply wf_is_univ_large; eassumption | exact HA | apply pi_domain_prop |].
      destruct r; exact HB.
  Qed.

  (** The type a λ infers is a type: the [Π] or [∀], of the sort of the
      body's type, of the domain's normal form. *)
  Lemma wf_type_fn_post : forall G A' A'' B r, G ⊢ᵗ A' -> nbe_ty_f G A' A'' -> G ▹ A' ⊢ᵗ B ->
      nbe_ty_relevance (G ▹ A') B r -> G ⊢ᵗ a_pi r A'' B.
  Proof.
    intros * [SA HSA HA] Hn [SB HSB HB] (ρ & a & Hρ & Ha & Hr).
    assert (HAA : G ⊢ A' ≈ A'' : SA) by (eapply soundness_ty_at_sort; eassumption).
    assert (HA'' : G ⊢ A'' : SA) by (gen_presups; assumption).
    destruct (typed_at_sort_of_initial_relevance HSB HB Hρ Ha) as [l Hl]; rewrite Hr in Hl.
    assert (Hσ : G ▹ A'' ⊢ˢ Id : G ▹ A') by (eapply sub_id_extend_of_exp_eq; [ exact HSA | symmetry; exact HAA ]).
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hl Hσ) as Hl'.
    rewrite !exp_sub_id in Hl'.
    eapply wf_type_pi_of_parts; [ exact (mk_wf_type _ HSA HA'') | exists l; exact Hl' ].
  Qed.

  (** The parts of a conjunction that is a type are propositions. *)
  Lemma wf_type_and_inv : forall G P Q, G ⊢ᵗ Σₚ P Q -> G ⊢ P : Propₘ /\ G ▹ P ⊢ Q : Propₘ.
  Proof. intros * [S HS H]; destruct (wf_and_inversion _ _ _ _ _ _ H) as [HP HQ _]; split; assumption. Qed.

  Lemma type_of_sort_infer : forall G A UA r u, ⊢ G -> G ⊢a A ⟹ UA -> is_sort_nf UA r u -> G ⊢ᵗ A.
  Proof.
    intros * HG HA Hs.
    exact (mk_wf_type _ (type_sort_relevance_universe r (universe_nf_large_index u))
             (sort_typed_of_is_sort_nf (alg_type_infer_sound HA HG) Hs)).
  Qed.

  (** The type a member of a checked module expression is read at is a
      type ([member_wf]). *)
  Lemma member_typ_of_alg : forall G M x R A, ⊢ G -> G ⊢aᵐ M ->
      mdenote gc_deps gc_stack G (me_mem M x) R -> mdesc_type R = Some A -> G ⊢ᵗ A.
  Proof.
    intros * HG HM Hm Ht.
    exact (proj1 (member_wf _ _ _ _ _ (alg_modexp_sound HM HG) Hm Ht)).
  Qed.

  (** ** The Initial Environment the Checker Carries

      Every normalization the checker does is at the initial environment of
      its context, or rather at an environment related to it entry by entry
      ([fast_env]), which the fast evaluation computes.  The checker computes it
      once, where it enters a context, and extends it entry by entry under
      binders, rather than once per normalization ([nbe_ty_env_impl]). *)
  Definition checker_env G := fast_env gc_deps gc_stack G.

  Lemma checker_env_order_of_wf : forall G, ⊢ G -> initial_env_order gc_deps gc_stack G.
  Proof.
    intros G HG.
    assert (G ⊢ Typeω@0 : Typeω@1) as [W [HW _]]%soundness_ty by mauto 2.
    inversion HW; subst; eauto using initial_env_order_sound.
  Qed.

  (** The reference value of the type an assumption adds. *)
  Lemma checker_env_ref_ass : forall G A p, ⊢ G ▹ A -> initial_env gc_deps gc_stack G p -> exists a, ⟦ A ⟧ p ↘ a.
  Proof.
    intros * HGA Hp; inversion HGA; subst.
    match goal with HA : G ⊢ A : ?S, HS : type_sort ?S |- _ => destruct (nbe_ty_exists_sort HS HA) as [W HW] end.
    inversion HW; subst.
    functional_initial_env_rewrite_clear; eauto.
  Qed.

  (** The reference value of the type a definition adds. *)
  Lemma checker_env_ref_def_typ : forall G A M p, ⊢ G ▸ A ≔ M -> initial_env gc_deps gc_stack G p -> exists a, ⟦ A ⟧ p ↘ a.
  Proof.
    intros * HGA Hp; inversion HGA; subst.
    match goal with HA : G ⊢ A : ?S, HS : type_sort ?S |- _ => destruct (nbe_ty_exists_sort HS HA) as [W HW] end.
    inversion HW; subst.
    functional_initial_env_rewrite_clear; eauto.
  Qed.

  (** The reference value of its body, at a relevant type. *)
  Lemma checker_env_ref_def : forall G A M p a, ⊢ G ▸ A ≔ M -> initial_env gc_deps gc_stack G p ->
      ⟦ A ⟧ p ↘ a -> domain_relevance a = relevant -> exists m, ⟦ M ⟧ p ↘ m.
  Proof.
    intros * HGA Hp Ha Hr; inversion HGA; subst.
    match goal with HM : G ⊢ M : A |- _ => destruct (soundness HM) as [W [HW _]] end.
    destruct (nbe_relevant_inv HW _ _ Hp Ha Hr) as (m & Hm & _); eauto.
  Qed.

  (** The sort of a reference type, read off the related fast one. *)
  Lemma relevance_of_fast_sim : forall a a' r, domain_simulation gc_deps gc_stack a (fdomain_erase a') ->
      fdomain_relevance a' = r -> domain_relevance a = r.
  Proof. intros * Hs Er; rewrite (domain_relevance_sim _ _ _ _ Hs); apply fdomain_relevance_erase_eq; exact Er. Qed.

  (** The fast environment the checker carries is right. *)
  Lemma checker_env_ok : forall G p',
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fenv_ok gc_deps gc_stack p'.
  Proof. intros * (p & _ & Hag); eapply fast_env_agree_ok; exact Hag. Qed.

  Lemma checker_env_eval_order_ass : forall G A p', ⊢ G ▹ A ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fast_eval_exp_order gc_deps gc_stack A (fenv_erase p').
  Proof.
    intros * HGA (p & Hp & Hag); destruct (checker_env_ref_ass _ _ _ HGA Hp) as [a Ha].
    eapply (fast_eval_of_ref _ _ _ _ _ _ Ha), fast_env_agree_all, Hag.
  Qed.

  Lemma checker_env_eval_order_def_typ : forall G A M p', ⊢ G ▸ A ≔ M ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fast_eval_exp_order gc_deps gc_stack A (fenv_erase p').
  Proof.
    intros * HGA (p & Hp & Hag); destruct (checker_env_ref_def_typ _ _ _ _ HGA Hp) as [a Ha].
    eapply (fast_eval_of_ref _ _ _ _ _ _ Ha), fast_env_agree_all, Hag.
  Qed.

  (** The reference value of a definition's type, related to the fast one,
      and of the same sort. *)
  Lemma checker_env_def_typ_sim : forall G A M p' a', ⊢ G ▸ A ≔ M ->
      forall p, initial_env gc_deps gc_stack G p -> fast_env_agree gc_deps gc_stack (fun _ => True) p p' ->
      ⟦ A ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase a' ->
      exists a, ⟦ A ⟧ p ↘ a /\ domain_relevance a = fdomain_relevance a'.
  Proof.
    intros * HGA p Hp Hag Ha'; destruct (checker_env_ref_def_typ _ _ _ _ HGA Hp) as [a Ha].
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag)) _ Ha') as Hs.
    exists a; split; [ exact Ha | eapply relevance_of_fast_sim; [ exact Hs | reflexivity ] ].
  Qed.

  Lemma checker_env_eval_order_def : forall G A M p' a', ⊢ G ▸ A ≔ M ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ A ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase a' -> fdomain_relevance a' = relevant ->
      fast_eval_exp_order gc_deps gc_stack M (fenv_erase p').
  Proof.
    intros * HGA (p & Hp & Hag) Ha' Er.
    destruct (checker_env_def_typ_sim _ _ _ _ _ HGA _ Hp Hag Ha') as (a & Ha & Hr); rewrite Er in Hr.
    destruct (checker_env_ref_def _ _ _ _ _ HGA Hp Ha Hr) as [m Hm].
    eapply (fast_eval_of_ref _ _ _ _ _ _ Hm), fast_env_agree_all, Hag.
  Qed.

  (** An assumption: a fresh variable of its type, the proof at a
      proposition. *)
  Lemma checker_env_ass_sim : forall G A p' a', ⊢ G ▹ A ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ A ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase a' /\ fdomain_ok gc_deps gc_stack a' ->
      exists p, initial_env gc_deps gc_stack (G ▹ A) p /\
             fast_env_agree gc_deps gc_stack (fun _ => True) p
               (fextend_env p' (frelevant_value a' (fd_neut a' (fd_var (List.length G))))).
  Proof.
    intros * HGA (p & Hp & Hag) [Ha' Hok]; destruct (checker_env_ref_ass _ _ _ HGA Hp) as [a Ha].
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag)) _ Ha').
    eexists; split; [ econstructor; eassumption |].
    eapply fast_env_agree_term;
      [ exact Hag
      | rewrite frelevant_value_erase; apply relevant_value_sim; [ assumption | cbn; repeat constructor; assumption ]
      | apply frelevant_value_ok; repeat constructor; assumption ].
  Qed.

  (** A definition of a relevant type: its body's value. *)
  Lemma checker_env_def_sim : forall G A M p' a' m', ⊢ G ▸ A ≔ M ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ A ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase a' /\ fdomain_ok gc_deps gc_stack a' ->
      fdomain_relevance a' = relevant ->
      ⟦ M ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase m' /\ fdomain_ok gc_deps gc_stack m' ->
      exists p, initial_env gc_deps gc_stack (G ▸ A ≔ M) p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p (fextend_env p' m').
  Proof.
    intros * HGA (p & Hp & Hag) [Ha' _] Er [Hm' Hok].
    destruct (checker_env_def_typ_sim _ _ _ _ _ HGA _ Hp Hag Ha') as (a & Ha & Hr); rewrite Er in Hr.
    destruct (checker_env_ref_def _ _ _ _ _ HGA Hp Ha Hr) as [m Hm].
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hm (fast_env_agree_all _ _ _ _ _ Hag)) _ Hm').
    eexists; split; [ eapply initial_env_cons_def; eassumption |].
    eapply fast_env_agree_term; eassumption.
  Qed.

  (** A definition of a proposition: the proof, its body not evaluated. *)
  Lemma checker_env_def_proof_sim : forall G A M p' a', ⊢ G ▸ A ≔ M ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ A ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase a' /\ fdomain_ok gc_deps gc_stack a' ->
      fdomain_relevance a' = propositional ->
      exists p, initial_env gc_deps gc_stack (G ▸ A ≔ M) p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p (fextend_env p' fd_true).
  Proof.
    intros * HGA (p & Hp & Hag) [Ha' _] Er.
    destruct (checker_env_def_typ_sim _ _ _ _ _ HGA _ Hp Hag Ha') as (a & Ha & Hr); rewrite Er in Hr.
    eexists; split; [ eapply initial_env_cons_def_proof; eassumption |].
    eapply fast_env_agree_term; [ exact Hag | cbn; constructor | constructor ].
  Qed.

  (** The reference value of the unit a module slot adds. *)
  Lemma checker_env_ref_mod : forall G U p, ⊢ G ▹ₘ U -> initial_env gc_deps gc_stack G p ->
      exists h, ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ p ↘ h.
  Proof.
    intros * HGU Hp.
    assert (G ▹ₘ U ⊢ Typeω@0 : Typeω@1) as [W [HW _]]%soundness_ty by mauto 2.
    inversion HW as [? ? Hi _ _]; subst.
    inversion Hi; subst; functional_initial_env_rewrite_clear; eauto.
  Qed.

  Lemma checker_env_eval_order_mod : forall G U p', ⊢ G ▹ₘ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fast_eval_modexp_order gc_deps gc_stack (me_lit U) (fenv_erase p').
  Proof.
    intros * HGU (p & Hp & Hag); destruct (checker_env_ref_mod _ _ _ HGU Hp) as [h Hh].
    eapply (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh), fast_env_agree_all, Hag.
  Qed.

  Lemma checker_env_mod_sim : forall G U p' h', ⊢ G ▹ₘ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ me_lit U ⟧ᵐᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdmod_erase h' /\ fdmod_ok gc_deps gc_stack h' ->
      exists p, initial_env gc_deps gc_stack (G ▹ₘ U) p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p (fextend_env_mod p' h').
  Proof.
    intros * HGU (p & Hp & Hag) [Hh' Hok]; destruct (checker_env_ref_mod _ _ _ HGU Hp) as [h Hh].
    pose proof (proj2 (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh (fast_env_agree_all _ _ _ _ _ Hag)) _ Hh').
    eexists; split; [ econstructor; eassumption |].
    eapply fast_env_agree_mod; eassumption.
  Qed.

  (** The reference values of the term and the unit a definition with a
      module part adds. *)
  Lemma checker_env_ref_dm : forall G A M U p, ⊢ G ▸ₘ A ≔ M ‖ U -> initial_env gc_deps gc_stack G p ->
      exists m h, ⟦ M ⟧ p ↘ m /\ ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ p ↘ h.
  Proof.
    intros * HG Hp.
    assert (G ▸ₘ A ≔ M ‖ U ⊢ Typeω@0 : Typeω@1) as [W [HW _]]%soundness_ty by mauto 2.
    inversion HW as [? ? Hi _ _]; subst.
    inversion Hi; subst; functional_initial_env_rewrite_clear; eauto.
  Qed.

  Lemma checker_env_eval_order_dm_tm : forall G A M U p', ⊢ G ▸ₘ A ≔ M ‖ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fast_eval_exp_order gc_deps gc_stack M (fenv_erase p').
  Proof.
    intros * HG (p & Hp & Hag); destruct (checker_env_ref_dm _ _ _ _ _ HG Hp) as (m & h & Hm & _).
    eapply (fast_eval_of_ref _ _ _ _ _ _ Hm), fast_env_agree_all, Hag.
  Qed.

  Lemma checker_env_eval_order_dm_unit : forall G A M U p', ⊢ G ▸ₘ A ≔ M ‖ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fast_eval_modexp_order gc_deps gc_stack (me_lit U) (fenv_erase p').
  Proof.
    intros * HG (p & Hp & Hag); destruct (checker_env_ref_dm _ _ _ _ _ HG Hp) as (m & h & _ & Hh).
    eapply (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh), fast_env_agree_all, Hag.
  Qed.

  Lemma checker_env_dm_sim : forall G A M U p' m' h', ⊢ G ▸ₘ A ≔ M ‖ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ M ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase m' /\ fdomain_ok gc_deps gc_stack m' ->
      ⟦ me_lit U ⟧ᵐᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdmod_erase h' /\ fdmod_ok gc_deps gc_stack h' ->
      exists p, initial_env gc_deps gc_stack (G ▸ₘ A ≔ M ‖ U) p /\
             fast_env_agree gc_deps gc_stack (fun _ => True) p (fextend_env_dm p' m' h').
  Proof.
    intros * HG (p & Hp & Hag) [Hm' Hokm] [Hh' Hokh]; destruct (checker_env_ref_dm _ _ _ _ _ HG Hp) as (m & h & Hm & Hh).
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hm (fast_env_agree_all _ _ _ _ _ Hag)) _ Hm').
    pose proof (proj2 (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh (fast_env_agree_all _ _ _ _ _ Hag)) _ Hh').
    eexists; split; [ econstructor; eassumption |].
    eapply fast_env_agree_dm; eassumption.
  Qed.

  Lemma checker_env_ctx_of_typ : forall G X, G ⊢ᵗ X -> ⊢ G.
  Proof. intros * [? ? HX]; gen_presups; assumption. Qed.

  (** The reference value of a type at the initial environment. *)
  Lemma checker_env_ref_type : forall G T p, G ⊢ᵗ T -> initial_env gc_deps gc_stack G p -> exists a, ⟦ T ⟧ p ↘ a.
  Proof.
    intros * [S HS HT] Hp; destruct (nbe_ty_exists_sort HS HT) as [W HW]; inversion HW; subst.
    functional_initial_env_rewrite_clear; eauto.
  Qed.

  Lemma checker_env_eval_order_type : forall G T p', G ⊢ᵗ T ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      fast_eval_exp_order gc_deps gc_stack T (fenv_erase p').
  Proof.
    intros * HT (p & Hp & Hag); destruct (checker_env_ref_type _ _ _ HT Hp) as [a Ha].
    eapply (fast_eval_of_ref _ _ _ _ _ _ Ha), fast_env_agree_all, Hag.
  Qed.

  (** The sort of a type is that of its fast value at the environment the
      checker carries. *)
  Lemma checker_relevance_sound : forall G T p' a', G ⊢ᵗ T ->
      (exists p, initial_env gc_deps gc_stack G p /\ fast_env_agree gc_deps gc_stack (fun _ => True) p p') ->
      ⟦ T ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase p' ↘ fdomain_erase a' ->
      nbe_ty_relevance G T (fdomain_relevance a').
  Proof.
    intros * HT (p & Hp & Hag) Ha'; destruct (checker_env_ref_type _ _ _ HT Hp) as [a Ha].
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag)) _ Ha') as Hs.
    exists p, a; repeat split; [ exact Hp | exact Ha | eapply relevance_of_fast_sim; [ exact Hs | reflexivity ] ].
  Qed.

  Inductive type_check_order : exp -> Prop :=
  | type_check_order_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order : exp -> Prop :=
  | type_infer_order_typ : forall {i}, type_infer_order Typeω@i
  | type_infer_order_suniv : forall {M}, type_infer_order M -> type_infer_order Type⟨M⟩
  | type_infer_order_level : forall {n}, type_infer_order Level@n
  | type_infer_order_llit : forall {o}, type_infer_order (𝕃ᵒ o)
  | type_infer_order_succl : forall {M}, type_infer_order M -> type_infer_order (succl M)
  | type_infer_order_maxl : forall {M N}, type_infer_order M -> type_infer_order N -> type_infer_order (maxl M N)
  (** [Prop] and the closed propositions recurse on nothing *)
  | type_infer_order_prop : type_infer_order Propₘ
  | type_infer_order_True : type_infer_order ⊤
  | type_infer_order_true : type_infer_order ⋆
  | type_infer_order_False : type_infer_order ⊥
  (** Ex falso infers its target and checks its proof *)
  | type_infer_order_absurd : forall {C M}, type_infer_order C -> type_check_order M -> type_infer_order (efq M return C)
  (** A conjunction infers its parts *)
  | type_infer_order_and : forall {P Q}, type_infer_order P -> type_infer_order Q -> type_infer_order (Σₚ P Q)
  (** A proof of a conjunction infers its annotation and checks its components *)
  | type_infer_order_conj : forall {T M N}, type_infer_order T -> type_check_order M -> type_check_order N ->
      type_infer_order (a_conj T M N)
  (** The components of a proof of a conjunction infer it *)
  | type_infer_order_left : forall {M}, type_infer_order M -> type_infer_order (a_left M)
  | type_infer_order_right : forall {M}, type_infer_order M -> type_infer_order (a_right M)
  (** The placeholder type and its element recurse on nothing *)
  | type_infer_order_placeholder_type : type_infer_order a_placeholder_type
  | type_infer_order_placeholder : type_infer_order a_placeholder
  | type_infer_order_indty : forall {p k}, type_infer_order (a_ind p k)
  | type_infer_order_con : forall {p k c}, type_infer_order (a_con p k c)
  (** A numeral is expanded before it is checked; it has no type. *)
  | type_infer_order_nlit : forall {n}, type_infer_order (a_nlit n)
  | type_infer_order_ntok : type_infer_order a_ntok
  (** An eliminator: its scrutinee and the annotations and motives of its
      blocks infer, its uniform parameters and the branches are checked. *)
  | type_infer_order_elim : forall {r oq Us m Bks M}, type_infer_order M ->
      (forall U, List.In U Us -> type_check_order U) ->
      (forall b Z, List.In b Bks -> eb_ann b = Some Z -> type_infer_order Z) ->
      (forall b, List.In b Bks -> type_infer_order (eb_motive b)) ->
      (forall b br, List.In b Bks -> List.In br (eb_brs b) -> type_check_order (snd br)) ->
      type_infer_order (a_elim r oq Us m Bks M)
  (** A [Π] or a [∀] infers its domain and its codomain *)
  | type_infer_order_pi : forall {r A B}, type_infer_order A -> type_infer_order B -> type_infer_order (a_pi r A B)
  | type_infer_order_fn : forall {A M}, type_infer_order A -> type_infer_order M -> type_infer_order λ A M
  | type_infer_order_app : forall {M N}, app_order M N -> type_infer_order (M $ N)
  | type_infer_order_let : forall {A M B}, type_infer_order A -> type_check_order M -> type_infer_order B -> type_infer_order (ℓ A ≔ M in B)
  | type_infer_order_let_infer : forall {M B}, type_infer_order M -> type_infer_order B -> type_infer_order (ℓ ≔ M in B)
  | type_infer_order_let_mod : forall {U B}, unit_order U -> type_infer_order B -> type_infer_order (ℓₘ U in B)
  | type_infer_order_mem : forall {H x}, modexp_order H -> type_infer_order (a_mem H x)
  | type_infer_order_vlookup : forall {x}, type_infer_order #x
  (** A record's type former recurses on nothing *)
  | type_infer_order_record : forall {p}, type_infer_order (a_record p)
  (** A tuple infers its annotation and checks its fields *)
  | type_infer_order_tuple : forall {T fs}, type_infer_order T -> (forall fm, List.In fm fs -> type_check_order (snd fm)) ->
      type_infer_order (a_tuple T fs)
  (** A projection infers its element *)
  | type_infer_order_proj : forall {f M}, type_infer_order M -> type_infer_order (a_proj f M)
  (** An application, apart from its head: the checker computes the type
      of a spine of applications as a value ([type_infer_app_in]), and
      checks its head ([type_infer_val_in]) at the order of a check. *)
  with app_order : exp -> exp -> Prop :=
  | app_order_app : forall {M N}, type_check_order M -> type_check_order N -> app_order M N
  with ext_order : ctx -> Prop :=
  | ext_order_nil : ext_order nil
  | ext_order_ass : forall {A Ψ}, ext_order Ψ -> type_infer_order A -> ext_order (Ψ ▹ A)
  | ext_order_def : forall {A M Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> ext_order (Ψ ▸ A ≔ M)
  | ext_order_mod : forall {U Ψ}, ext_order Ψ -> unit_order U -> ext_order (Ψ ▹ₘ U)
  (** A definition with a module part: as a definition and as a slot *)
  | ext_order_dm : forall {A M U Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> unit_order U ->
      ext_order (Ψ ▸ₘ A ≔ M ‖ U)
  with unit_order : gunit -> Prop :=
  | unit_order_body : forall {Δ sm Φ}, ext_order Δ -> body_order Φ -> unit_order (gu_mk Δ (md_body sm Φ))
  | unit_order_alias : forall {Δ E}, ext_order Δ -> modexp_order E -> unit_order (gu_mk Δ (md_alias E))
  (** A body, entry by entry; an entry no body may hold has nothing to
      check. *)
  with body_order : gmod -> Prop :=
  | body_order_nil : body_order gm_nil
  | body_order_def : forall {Φ x b pv r A M}, body_order Φ -> type_infer_order A -> type_check_order M ->
      body_order (gm_ext Φ x (ge_def b pv r A (Some M)))
  | body_order_mod : forall {Φ x pm U}, body_order Φ -> unit_order U -> body_order (gm_ext Φ x (ge_mod pm U))
  | body_order_axiom : forall {Φ x b pv r A}, body_order Φ -> body_order (gm_ext Φ x (ge_def b pv r A None))
  | body_order_ind_case : forall {Φ x pv p k D Φi}, body_order Φ -> body_order (gm_ext Φ x (ge_ind pv p k D Φi))
  (** A definition with a module part: its term part as a definition, its
      unit as a submodule *)
  | body_order_def_mod : forall {Φ x pv A M U}, body_order Φ -> type_infer_order A -> type_check_order M -> unit_order U ->
      body_order (gm_ext Φ x (ge_def_mod pv A M U))
  (** A record declaration: as written in no local body, only the entries
      before it *)
  | body_order_record : forall {Φ x pv pr R Φr}, body_order Φ -> body_order (gm_ext Φ x (ge_record pv pr R Φr))
  | body_order_open : forall {Φ H its}, body_order Φ -> modexp_order H -> body_order (gm_open Φ H its)
  with modexp_order : modexp -> Prop :=
  | modexp_order_unit : forall {fp}, modexp_order (me_unit fp)
  | modexp_order_var : forall {x}, modexp_order (me_var x)
  | modexp_order_lit : forall {U}, unit_order U -> modexp_order (me_lit U)
  | modexp_order_mem : forall {H y}, modexp_order H -> modexp_order (me_mem H y)
  | modexp_order_app : forall {H N}, modexp_order H -> type_check_order N -> modexp_order (me_app H N)
  .

  #[local]
  Hint Constructors type_check_order type_infer_order app_order ext_order unit_order body_order modexp_order : mctt.

  (** Every term has an order. *)
  Definition centry_order (e : centry) : Prop :=
    match e with
    | ce_ass A => type_infer_order A
    | ce_def A M => type_infer_order A /\ type_check_order M
    | ce_mod U => unit_order U
    | ce_dm A M U => type_infer_order A /\ type_check_order M /\ unit_order U
    end.

  Lemma ext_order_app : forall X Δ, List.Forall centry_order X -> ext_order Δ -> ext_order (X ++ Δ).
  Proof.
    induction X as [| [A | A M | U | A M U] X IH]; intros * HX HΔ; cbn; [ exact HΔ | | | |];
      inversion HX as [| ? ? He HX']; subst; cbn in He; destruct_conjs; constructor; auto.
  Qed.

  Lemma ext_order_of_forall : forall X, List.Forall centry_order X -> ext_order X.
  Proof. intros X HX; rewrite <- (app_nil_r X); apply ext_order_app; [ exact HX | constructor ]. Qed.

  Lemma syn_orders_all :
    (forall M, type_infer_order M) /\
    (forall H, modexp_order H) /\
    (forall b, match b with
           | b_def oA M => (forall A, oA = Some A -> type_infer_order A) /\ type_infer_order M
           | b_mod U => unit_order U
           end) /\
    (forall U, unit_order U) /\
    (forall D, match D with
           | md_body sm Φ => body_order Φ
           | md_alias E => modexp_order E
           end) /\
    (forall Φ, body_order Φ) /\
    (forall E, match E with
           | ge_def _ _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
           | ge_mod _ U => unit_order U
           | ge_def_mod _ A M U => type_infer_order A /\ type_infer_order M /\ unit_order U
           | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => True
           end) /\
    (forall e, centry_order e).
  Proof.
    apply (syn_mut_ind type_infer_order modexp_order
      (fun b => match b with
             | b_def oA M => (forall A, oA = Some A -> type_infer_order A) /\ type_infer_order M
             | b_mod U => unit_order U
             end)
      unit_order
      (fun D => match D with
             | md_body sm Φ => body_order Φ
             | md_alias E => modexp_order E
             end)
      body_order
      (fun E => match E with
             | ge_def _ _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
             | ge_mod _ U => unit_order U
             | ge_def_mod _ A M U => type_infer_order A /\ type_infer_order M /\ unit_order U
             | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => True
             end)
      centry_order); intros; cbn in *; destruct_conjs; eauto 6 with mctt.
    (* a tuple: its fields are checked *)
    all: try match goal with HF : List.Forall _ ?fs |- type_infer_order (a_tuple _ ?fs) =>
           rewrite List.Forall_forall in HF; constructor; [ assumption | intros fm Hfm; apply type_check_order_ti; auto ] end.
    - (* an eliminator: its uniform parameters and branches are checked *)
      match goal with
      | HU : List.Forall _ ?Us, HB : List.Forall _ ?Bks |- type_infer_order (a_elim _ _ ?Us _ ?Bks _) =>
          rewrite List.Forall_forall in HU, HB
      end.
      constructor; [ assumption | intros U HU'; apply type_check_order_ti; auto
                   | intros b Z Hb HZ; match goal with HB : forall x, List.In x _ -> _ |- _ => exact (proj1 (HB b Hb) Z HZ) end
                   | intros b Hb; match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ => exact (proj1 (proj2 (HB b Hb))) end
                   | intros b br Hb Hbr; apply type_check_order_ti;
                     match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ =>
                       exact (proj1 (List.Forall_forall _ _) (proj2 (proj2 (HB b Hb))) br Hbr) end ].
    - (* a local binding *)
      destruct b as [[A |] M | U]; destruct_conjs;
        [ apply type_infer_order_let; [ eauto | constructor; assumption | assumption ]
        | apply type_infer_order_let_infer; assumption
        | apply type_infer_order_let_mod; assumption ].
    - destruct D; destruct_conjs; constructor; auto using ext_order_of_forall.
    - destruct E as [b pv r A [M |] | pm U | pvi pk ki Di Φi | ? ? ? ? | ? ? ?]; destruct_conjs;
        first [ apply body_order_def; eauto with mctt | apply body_order_mod; assumption
              | apply body_order_axiom; assumption | apply body_order_ind_case; assumption | apply body_order_def_mod; eauto with mctt
              | apply body_order_record; assumption ].
  Qed.

  Lemma type_infer_order_all : forall M, type_infer_order M.
  Proof. exact (proj1 syn_orders_all). Qed.

  Lemma modexp_order_all : forall H, modexp_order H.
  Proof. exact (proj1 (proj2 syn_orders_all)). Qed.

  Lemma unit_order_all : forall U, unit_order U.
  Proof. exact (proj1 (proj2 (proj2 (proj2 syn_orders_all)))). Qed.

  Lemma ext_order_all : forall Ψ, ext_order Ψ.
  Proof.
    intros; apply ext_order_of_forall, Forall_forall; intros.
    destruct syn_orders_all as (_ & _ & _ & _ & _ & _ & _ & Hc); apply Hc.
  Qed.

  Lemma user_exp_to_type_infer_order : forall M,
      user_exp M ->
      type_infer_order M.
  Proof. intros; apply type_infer_order_all. Qed.

  (** A literal has no type: the literals of a command are generated
      before it is checked. *)
  Lemma alg_nlit_no_infer : forall G n A, ~ G ⊢a a_nlit n ⟹ A.
  Proof. intros * H; inversion H. Qed.

  Lemma alg_ntok_no_infer : forall G A, ~ G ⊢a a_ntok ⟹ A.
  Proof. intros * H; inversion H. Qed.

  (** A closed body is a filed module's or an open frame's: no unit the
      checker is given is one. *)
  Lemma alg_unit_closed_no : forall G Δ Φ, ~ G ⊢aᵘ gu_body Δ Φ.
  Proof. intros * H; inversion H. Qed.

End type_check.
End Fixed_GCtx.

(** ** The Computations, Through a Fast Context

    The checker's helpers that run: they take the fast context [F], and
    the judgments are those of the global context it stands for
    ([fc_gctx F]). *)
Section Fast.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

Section lookup.
  #[local]
  Ltac impl_obligation_tac1 :=
    match goal with
    | |- ~ _ => intro
    | H: ⊢ _ :: _ |- _ => inversion_clear H
    | H: ⋅ ∋ #_ : _ |- _ => inversion_clear H
    | H: _ :: _ ∋ #(S _) : _ |- _ => inversion_clear H
    | H: ce_mod _ :: _ ∋ #0 : _ |- _ => inversion H
    end.

  #[local]
  Ltac impl_obligation_tac :=
    intros;
    repeat impl_obligation_tac1;
    intuition (mauto 4).

  #[tactic="impl_obligation_tac",derive(equations=no,eliminator=no)]
  Equations lookup G (HG : ⊢ G) x : { A | G ∋ #x : A } + { forall A, ~ G ∋ #x : A } :=
  | cons e G, HG, x with x => {
    | 0 with e => {
      | ce_ass A => pureo (exist _ A[↑]ʷ _)
      | ce_def A M => pureo (exist _ A[↑]ʷ _)
      | ce_mod _ => inright _
      | ce_dm A M U => pureo (exist _ A[↑]ʷ _) }
    | S x' =>
        let*o (exist _ B _) := lookup G _ x' while _ in
        pureo (exist _ B[↑]ʷ _)
    }
  | ⋅, HG, x => inright _.
End lookup.

(** *** Deciding What Module Expressions Denote

    What a module expression denotes is computed by [mdenote_impl], at
    the order a well-formed module expression, or a selection from one,
    has ([mdenote_order_of_wf], [mdenote_order_mem_of_wf]); a path has one
    outright. *)

Definition mdenote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
    { R : fmdesc | mdenote gc_deps gc_stack Γ H (decode_desc R) } + { forall R, ~ mdenote gc_deps gc_stack Γ H R } :=
  mdenote_impl F Hg Γ H (mdenote_order_of_wf _ _ Hg _ _ _ HH).

Definition mem_denote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H y (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
    { R : fmdesc | mdenote gc_deps gc_stack Γ (me_mem H y) (decode_desc R) } + { forall R, ~ mdenote gc_deps gc_stack Γ (me_mem H y) R } :=
  mdenote_impl F Hg Γ (me_mem H y) (mdenote_order_mem_of_wf _ _ Hg _ _ _ y HH).

Definition path_denote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ fp :
    { R : fmdesc | mdenote gc_deps gc_stack Γ (me_unit fp) (decode_desc R) } + { forall R, ~ mdenote gc_deps gc_stack Γ (me_unit fp) R } :=
  mdenote_impl F Hg Γ (me_unit fp) (mdenote_order_path _ _ Γ fp).

(** What a local open of a module generates. *)
Definition items_gen_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H its (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
    { gs | items_gen gc_deps gc_stack Γ H its gs } + { forall gs, ~ items_gen gc_deps gc_stack Γ H its gs } :=
  items_gen_impl F Hg Γ H its (items_gen_order_of_wf _ _ Hg _ _ _ its HH).

Extraction Inline mdenote_dec mem_denote_dec path_denote_dec items_gen_dec.

(** *** The Initial Environment, Computed *)

(** The initial environment of a context, from scratch. *)
Definition checker_env_of G (HG : ⊢ G) : checker_env G :=
  initial_env_impl F G (checker_env_order_of_wf G HG).

(** The initial environment of an extended context, from that of the
    context: one entry more, by its rule of [initial_env]. *)
Definition checker_env_ass G (P : checker_env G) A (HGA : ⊢ G ▹ A) : checker_env (G ▹ A) :=
  let (p, Hp) := P in
  let (a, Ha) := fast_eval_exp_impl F A p (checker_env_ok G p Hp) (checker_env_eval_order_ass G A p HGA Hp) in
  exist _ (fextend_env p (frelevant_value a (fd_neut a (fd_var (List.length G))))) (checker_env_ass_sim _ _ _ _ HGA Hp Ha).

(** The same for a definition entry, by the sort of its type: its body's
    value, or the proof at a proposition. *)
Definition checker_env_def G (P : checker_env G) A M (HGA : ⊢ G ▸ A ≔ M) : checker_env (G ▸ A ≔ M) :=
  let (p, Hp) := P in
  let (a, Ha) := fast_eval_exp_impl F A p (checker_env_ok G p Hp) (checker_env_eval_order_def_typ G A M p HGA Hp) in
  match fdomain_relevance a as r return fdomain_relevance a = r -> checker_env (G ▸ A ≔ M) with
  | relevant => fun Er =>
      let (m, Hm) := fast_eval_exp_impl F M p (checker_env_ok G p Hp) (checker_env_eval_order_def G A M p a HGA Hp (proj1 Ha) Er) in
      exist _ (fextend_env p m) (checker_env_def_sim _ _ _ _ _ _ HGA Hp Ha Er Hm)
  | propositional => fun Er => exist _ (fextend_env p fd_true) (checker_env_def_proof_sim _ _ _ _ _ HGA Hp Ha Er)
  end eq_refl.

(** The same for a module slot: the closure of its unit. *)
Definition checker_env_mod G (P : checker_env G) U (HGU : ⊢ G ▹ₘ U) : checker_env (G ▹ₘ U) :=
  let (p, Hp) := P in
  let (h, Hh) := fast_eval_modexp_impl F (me_lit U) p (checker_env_ok G p Hp) (checker_env_eval_order_mod G U p HGU Hp) in
  exist _ (fextend_env_mod p h) (checker_env_mod_sim _ _ _ _ HGU Hp Hh).

(** The same for a definition with a module part: the value of its term
    part's body and the closure of its unit, side by side. *)
Definition checker_env_dm G (P : checker_env G) A M U (HG : ⊢ G ▸ₘ A ≔ M ‖ U) : checker_env (G ▸ₘ A ≔ M ‖ U) :=
  let (p, Hp) := P in
  let (m, Hm) := fast_eval_exp_impl F M p (checker_env_ok G p Hp) (checker_env_eval_order_dm_tm G A M U p HG Hp) in
  let (h, Hh) := fast_eval_modexp_impl F (me_lit U) p (checker_env_ok G p Hp) (checker_env_eval_order_dm_unit G A M U p HG Hp) in
  exist _ (fextend_env_dm p m h) (checker_env_dm_sim _ _ _ _ _ _ _ HG Hp Hm Hh).

(** The sort of a type, read off its fast value at the environment the
    checker carries ([nbe_ty_relevance]). *)
Definition checker_relevance G (P : checker_env G) T (HT : G ⊢ᵗ T) : { r | nbe_ty_relevance G T r } :=
  let (p, Hp) := P in
  let (a, Ha) := fast_eval_exp_impl F T p (checker_env_ok G p Hp) (checker_env_eval_order_type G T p HT Hp) in
  exist _ (fdomain_relevance a) (checker_relevance_sound G T p a HT Hp (proj1 Ha)).

(** The initial environment of an extension [Ψ ++ G], from that of [G]:
    one entry more per entry of [Ψ], rather than all of [G]'s again. *)
Fixpoint checker_env_ext G (P : checker_env G) (Ψ : ctx) {struct Ψ} : ⊢ Ψ ++ G -> checker_env (Ψ ++ G) :=
  match Ψ as Ψ0 return ⊢ Ψ0 ++ G -> checker_env (Ψ0 ++ G) with
  | nil => fun _ => P
  | ce_ass A :: Ψ' => fun H => checker_env_ass (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) A H
  | ce_def A M :: Ψ' => fun H => checker_env_def (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) A M H
  | ce_mod U :: Ψ' => fun H => checker_env_mod (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) U H
  | ce_dm A M U :: Ψ' => fun H => checker_env_dm (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) A M U H
  end.
End Fast.

(** The recursive calls of a checker in the context of its obligations:
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

(** A context the checker extends is well formed by the soundness of the
    check of the extension. *)
Ltac ctx_wf_tac :=
  match goal with
  | |- ⊢ ?G => assumption
  | |- ⊢ ?G ▹ ?A =>
      let HA := fresh "HA" in
      assert (HA : G ⊢ᵗ A) by type_sound;
      destruct HA as [? ? ?]; eapply wf_ctx_extend; eassumption
  | |- ⊢ ?G ▸ ?A ≔ ?M =>
      first
        [ match goal with H' : G ⊢a M ⟸ A |- _ =>
            let HA := fresh "HA" in
            assert (HA : G ⊢ᵗ A) by type_sound;
            destruct HA as [? ? ?];
            eapply wf_ctx_extend_def; [ eassumption | eassumption | eapply alg_type_check_sound_sort; [ exact H' | ctx_wf_tac | eassumption | eassumption ] ]
          end
        (** Without an annotation, at the type the body infers *)
        | match goal with H' : G ⊢a M ⟹ ?B |- _ =>
            change (⊢ G ▸ (B : exp) ≔ M);
            let HA := fresh "HA" in
            assert (HA : G ⊢ᵗ B) by type_sound;
            destruct HA as [? ? ?];
            eapply wf_ctx_extend_def; [ eassumption | eassumption | exact (alg_type_infer_sound H' ltac:(ctx_wf_tac)) ]
          end ]
  | |- ⊢ ?G ▹ₘ ?U =>
      match goal with H : G ⊢aᵘ U |- _ => apply wf_ctx_extend_mod; eapply alg_unit_sound; eassumption end
  | |- ⊢ ?G ▸ₘ ?A ≔ ?M ‖ ?U =>
      match goal with Ha : G ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA ?u, H' : G ⊢a M ⟸ A, HU : G ⊢aᵘ U |- _ =>
        assert (G ⊢ A : universe_nf_tm u)
          by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              eapply alg_type_infer_sound; eassumption);
        assert (G ⊢ A : Typeω@(universe_nf_large_index u))
          by (apply wf_exp_universe_nf_large_index; eassumption);
        assert (G ⊢ M : A) by (eapply alg_type_check_sound; eassumption);
        eapply wf_ctx_extend_dm; [ eassumption | eassumption | eapply alg_unit_sound; eassumption ] end
  | |- ⊢ ?Ψ ++ ?G =>
      first [ match goal with H : G ⊢aˣ Ψ |- _ => eapply ext_eq_ctx_left, alg_ext_sound; eassumption end
            | match goal with H : G ⊢aᵖ Ψ |- _ => eapply ext_eq_ctx_left, (proj1 (alg_params_sound H ltac:(ctx_wf_tac))) end ]
  | |- ⊢ body_ctx ?Φ0 ++ ?Δ ++ ?G =>
      match goal with Hls : forall Φ c, In (Φ, c) _ -> ⊢ body_ctx Φ ++ Δ ++ G |- _ =>
        eapply Hls; left; reflexivity end
  end
(** A type the checker has inferred a sort of is a type of either sort
    ([type_of_sort_infer]). *)
with type_sound :=
  match goal with
  | |- ?G ⊢ᵗ ?A =>
      first [ assumption
            | match goal with Ha : G ⊢a A ⟹ ?UA, Hs : is_sort_nf ?UA _ _ |- _ =>
                eapply type_of_sort_infer; [ ctx_wf_tac | exact Ha | exact Hs ] end
            | match goal with Ha : G ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA _ |- _ =>
                eapply type_of_sort_infer; [ ctx_wf_tac | exact Ha | constructor; exact Hu ] end
            | match goal with Ha : G ⊢a A ⟹ Propⁿ |- _ =>
                eapply type_of_sort_infer; [ ctx_wf_tac | exact Ha | constructor ] end ]
  end.

(** A closed type, or one the context types directly, is a type of either
    sort. *)
(** A type of a large universe; the universe index the typing leaves open
    may be any. *)
Ltac type_closed_large := unshelve (eapply wf_type_univ); [ .. | solve [ mauto 3 ] ]; try exact 0.

Ltac type_closed :=
  cbn; first [ type_closed_large | eapply wf_type_prop; solve [ mauto 3 ] ].

(** The last two components of [type_infer]'s postcondition: the inferred
    type infers a sort, and is a type ([infer_post_of_type]). *)
Ltac is_type_obligation :=
  apply infer_post_of_type; first [ type_closed | type_sound ].

(** The subject of a universe premise, as a typing at the large level the
    index of its side condition lives at: that is the form the obligations
    need.  [is_univ_nf_eq] turns the side condition into the shape of the
    inferred normal form. *)
Ltac saturate_infer_univ :=
  repeat match goal with
    | Ha : ?G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
        let T := constr:(G ⊢ A : a_typ (universe_nf_large_index u)) in
        assert_fails (assert T by assumption);
        assert (G ⊢ A : universe_nf_tm u)
          by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              eapply alg_type_infer_sound; [ exact Ha | ctx_wf_tac ]);
        assert T by (apply wf_exp_universe_nf_large_index; eassumption)
    (** A type of either sort: its typing at the sort *)
    | Ha : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?r ?u |- _ =>
        let T := constr:(G ⊢ A : relevance_sort r (a_typ (universe_nf_large_index u))) in
        assert_fails (assert T by assumption);
        assert T by (eapply sort_typed_of_is_sort_nf; [ eapply alg_type_infer_sound; [ exact Ha | ctx_wf_tac ] | exact Hs ])
    (** A proposition *)
    | Ha : ?G ⊢a ?A ⟹ Propⁿ |- _ =>
        let T := constr:(G ⊢ A : Propₘ) in
        assert_fails (assert T by assumption);
        assert T by (exact (alg_type_infer_sound Ha ltac:(ctx_wf_tac)))
    | HnC : nbe_ty _ _ (?G ▹ ?A) _ ?UB', Hv : is_univ_nf ?UB' ?v,
      HC : ?G ▹ ?A ⊢a ?B ⟹ ?UB, HB : ?G ⊢a ?A ⟹ ?UA, Hu : is_sort_nf ?UA _ _ |- _ =>
        (** A codomain whose universe was normalised ([alg_type_infer_pi]): its
            typing at the large level of the normal form's index. *)
        let T := constr:(G ▹ A ⊢ B : a_typ (universe_nf_large_index v)) in
        assert_fails (assert T by assumption);
        let HG' := fresh "HG" in
        assert (HG' : ⊢ G) by ctx_wf_tac;
        let HCv := fresh "HCv" in
        destruct (alg_pi_parts_sound HG' HB Hu HC HnC Hv) as (_ & HCv & _);
        clear HG';
        assert T by (apply wf_exp_universe_nf_large_index; exact HCv)
    end.

(** A type whose inferred universe is [universe_nf_to_nf u] is a type of [universe_nf_tm u],
    and so of the large universe [Typeω@(universe_nf_large_index u)] the index lives at. *)
Ltac typ_of_infer := saturate_infer_univ.

(** ** Obligations of the Module Cases *)

(** Two descriptions of one module expression, or two generated blocks of
    one open, are one ([mdenote_functional_all]), and so are two values of
    one function. *)
Ltac md_unify :=
  repeat match goal with
    | H1 : mdenote ?T ?X ?G ?M ?R1, H2 : mdenote ?T ?X ?G ?M ?R2 |- _ =>
        assert_fails (constr_eq R1 R2);
        let Hg := fresh "Hg" in
        assert (Hg : ⊢ᵍ T ⍮ X) by gctx_wf_tac;
        pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ H1 _ H2); subst R2; clear H2 Hg
    | H1 : items_gen ?T ?X ?b ?G ?M ?its ?A1, H2 : items_gen ?T ?X ?b ?G ?M ?its ?A2 |- _ =>
        assert_fails (constr_eq A1 A2);
        let Hg := fresh "Hg" in
        assert (Hg : ⊢ᵍ T ⍮ X) by gctx_wf_tac;
        pose proof (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ _ _ H1 _ H2); subst A2; clear H2 Hg
    | H1 : ?f = Some ?a, H2 : ?f = Some ?b |- _ =>
        assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
    | H1 : ?f = Some _, H2 : ?f = None |- _ => rewrite H1 in H2; discriminate H2
    end.

(** One sort and universe of each type of a type. *)
Ltac sort_unify :=
  repeat match goal with
    | H1 : is_sort_nf ?W ?r ?u, H2 : is_sort_nf ?W ?r' ?u' |- _ =>
        assert_fails (constr_eq H1 H2);
        let E1 := fresh "E" in let E2 := fresh "E" in
        destruct (is_sort_nf_functional _ _ _ _ _ H1 H2) as [E1 E2]; clear H2; try subst
    | H1 : is_univ_nf ?W ?u, H2 : is_univ_nf ?W ?u' |- _ =>
        assert_fails (constr_eq H1 H2);
        pose proof (is_univ_nf_functional _ _ _ H1 H2); clear H2; try subst
    end.

Ltac failure_contradiction :=
  match goal with
  | Hx : _ ⊢aˣ (_ :: _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵖ (_ :: _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵘ (gu_mk _ _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵐ (_ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
  | Hx : _ ⊢aᵐ (_ _ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
  end;
  functional_alg_type_infer_rewrite_clear;
  md_unify;
  sort_unify;
  first [ match goal with H : forall u : universe_nf, ?X <> universe_nf_to_nf u |- _ => exact (H _ eq_refl) end
        | congruence
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ]
        | solve [ match goal with HN : forall _ _, ~ _ |- _ => eapply HN; eassumption end ]
        | firstorder ].

Ltac typ_sound :=
  match goal with
  | |- exists i, ?G ⊢ ?A : Typeω@i =>
      saturate_infer_univ;
      match goal with H : wf_exp gc_deps gc_stack G (a_typ ?k) A |- _ => exists k; exact H end
  | |- ?G ⊢ᵗ ?A => type_sound
  end.

Ltac ctx_premise :=
  first [ assumption
        | ctx_wf_tac
        | match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; left; reflexivity end ].

(** ** The Obligations of the Module Cases

    One tactic per kind of obligation; each obligation below names the one
    that proves it. *)

(** A loaded unit: what it denotes, and that is a module. *)
Ltac module_obligation_2 :=
  clear_defs; destruct_conjs;
  solve [ eapply alg_modexp_unit; eassumption ].

(** A failure of a selection or an application: its rule's premises are
    read off what it denotes. *)
Ltac module_obligation_3 :=
  clear_defs; destruct_conjs;
  solve [ failure_contradiction ].

(** The type a member is read at is a type. *)
Ltac module_obligation_7 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : mdenote _ _ ?G (me_mem ?M _) _, Ht : mdesc_type _ = Some ?A
                |- nbe_ty_order _ _ ?G ?A =>
                  exact (nbe_order_of_type _ _ (member_typ_of_alg _ _ _ _ _ HG HM Hm Ht))
              end ].

(** A member infers the normal form of that type. *)
Ltac module_obligation_8 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : mdenote _ _ ?G (me_mem ?M _) _, Ht : mdesc_type _ = Some ?A,
                Hn : nbe_ty_f ?G ?A _ |- _ =>
                  pose proof (member_typ_of_alg _ _ _ _ _ HG HM Hm Ht)
              end;
              split; [ eapply alg_type_infer_mem; eassumption | eapply level_of_nbe; eassumption ] ].

Ltac module_obligation_10 :=
  clear_defs; destruct_conjs;
  solve [ failure_contradiction ].

Ltac module_obligation_14 :=
  clear_defs; destruct_conjs;
  solve [ typ_sound ].

Ltac module_obligation_18 :=
  clear_defs; destruct_conjs;
  solve [ eapply alg_modexp_sound; [ eassumption | ctx_premise ] ].

Ltac module_obligation_19 :=
  clear_defs; destruct_conjs;
  solve [ econstructor; apply ctx_find_mod_sound; eassumption ].

Ltac module_obligation_20 :=
  clear_defs; destruct_conjs;
  solve [ match goal with Hx : _ ⊢aᵐ me_var _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
              match goal with Hl : ctx_lookup_mod _ _ _ |- _ => apply ctx_find_mod_complete in Hl end; congruence ].

Ltac module_obligation_21 :=
  clear_defs; destruct_conjs;
  solve [ failure_contradiction ].

(** The outermost parameter of a checked module expression is a type
    ([mtele_head_wf]). *)
Ltac module_obligation_22 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : mdenote _ _ ?G ?M _, Ht : mdesc_mod_tele _ = Some ?T,
                Hv : tele_view ?T = Some (?B, _) |- ?G ⊢ᵗ ?B =>
                  destruct (mtele_head_wf _ _ _ _ _ _ (alg_modexp_sound HM HG) Hm Ht Hv) as [? HB];
                  exact (wf_type_univ HB)
              end ].

(** ** The Obligations of the Term Cases *)

(** An order premise: the order of a subterm, read off the order of the
    term by inversion.  The premise is an assumption at the first stage
    that has it, and only then: an inversion one stage too far would leave
    the subterm's order behind, and a reconstructed order is not a subterm
    for the guard of the checker's structural recursion.  An application
    reaches its head and its argument through [app_order], whose components
    are the orders of checks. *)
Ltac obligation_order :=
  clear_defs;
  try match goal with H : type_check_order _ |- _ => progressive_invert H end;
  first
    [ eassumption
    | repeat match goal with
        | H : type_infer_order _ |- _ => progressive_invert H
        | H : ext_order _ |- _ => progressive_invert H
        | H : unit_order _ |- _ => progressive_invert H
        | H : body_order _ |- _ => progressive_invert H
        | H : modexp_order _ |- _ => progressive_invert H
        end;
      first
        [ eassumption
        | repeat match goal with H : app_order _ _ |- _ => progressive_invert H end;
          first
            [ eassumption
            | repeat match goal with H : type_check_order _ |- _ => progressive_invert H end;
              eassumption ] ] ].

(** The orders of the parts of an eliminator: its scrutinee, a uniform
    parameter, and an annotation, a motive or a branch of a block. *)
Ltac obligation_order_elim :=
  clear_defs;
  match goal with H : type_infer_order (a_elim _ _ _ _ _ _) |- _ => progressive_invert H end;
  first
    [ eassumption
    | match goal with Hall : forall _ : _, _ |- _ => solve [ eapply Hall; eassumption ] end ].

(** The orders of the parts of a tuple and of a projection: the annotation
    or a field, the element. *)
Ltac obligation_order_record :=
  clear_defs;
  match goal with
  | H : type_infer_order (a_tuple _ _) |- _ => progressive_invert H
  | H : type_infer_order (a_proj _ _) |- _ => progressive_invert H
  end;
  first
    [ eassumption
    | match goal with Hall : forall _ : _, _ |- _ => solve [ eapply Hall; eassumption ] end ].

(** A context premise. *)
Ltac obligation_ctx := clear_defs; destruct_conjs; solve [ ctx_wf_tac ].

Ltac obligation_ctx_ext := clear_defs; destruct_conjs; saturate_infer_univ; mauto 3.

(** One normal form of each type: two normalizations of one type are made
    one, and normal forms of one head have the same parts. *)
Ltac nbe_ty_unify :=
  repeat match goal with
    | H1 : nbe_ty ?T ?X ?G ?A ?W1, H2 : nbe_ty ?T ?X ?G ?A ?W2 |- _ =>
        let E := fresh "E" in
        assert (E : W1 = W2) by (eapply functional_nbe_ty; [ exact H1 | exact H2 ]);
        clear H2; try (injection E; clear E; intros); try subst
    end.

(** A failure branch: the judgment the branch rules out is inverted against
    the failure of the premise. *)
Ltac obligation_failure :=
  clear_defs;
  (** The judgment ruled out is the newest hypothesis. *)
  lazymatch goal with
  | H : ?J |- False =>
      lazymatch J with
      | _ ⊢a _ ⟹ _ => idtac
      | _ ⊢a _ ⟸ _ => idtac
      | _ => fail "obligation_failure: the newest hypothesis is not a judgment:" J
      end;
      inversion H; subst; clear H
  end;
  simpl_let_guards;
  destruct_conjs;
  functional_alg_type_infer_rewrite_clear;
  nbe_ty_unify;
  sort_unify;
  (** One sort of each type *)
  repeat match goal with
    | H1 : nbe_ty_relevance ?G ?A ?r, H2 : nbe_ty_relevance ?G ?A ?r' |- _ =>
        assert_fails (constr_eq r r');
        pose proof (nbe_ty_relevance_functional _ _ _ _ H1 H2); clear H2; try subst
    end;
  first [ contradiction
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ]
        (** A normal form of no shape the rule asks *)
        | solve [ match goal with HN : forall _ _, _ <> _ |- _ => eapply HN; reflexivity end ]
        | solve [ match goal with HN : forall _ _ _, _ <> _ |- _ => eapply HN; reflexivity end ]
        | solve [ eauto 2 ] | congruence | solve [ firstorder ] ].

(** A failure branch of a member: the member's inference is inverted, and
    each rule it could come from contradicts the branch's premises. *)
Ltac obligation_mem_failure :=
  clear_defs;
  lazymatch goal with H : _ ⊢a a_mem _ _ ⟹ _ |- False => inversion H; subst; clear H end;
  md_unify;
  first [ contradiction
        | congruence
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ] ].

(** The postcondition of a closed small type: it infers [Typeⁿ@0], and
    [Type@0] is a type, so it infers a universe. *)
Ltac obligation_post_suniv0 :=
  clear_defs;
  match goal with HG : ⊢ ?G |- _ =>
    let HT := fresh "HT" in
    assert (HT : G ⊢ Type@0 : Typeω@0) by (apply wf_univ_large; exact HG);
    split; [ mauto 3 | apply infer_post_of_type, (wf_type_univ HT) ]
  end.

(** The postcondition of a closed type or level form: the inference by its
    rule, and the inferred type is a type. *)
Ltac obligation_post := clear_defs; split; [ mauto 3 | is_type_obligation ].

(** The postcondition of a level operation: its arguments infer types of
    levels, so its rule applies. *)
Ltac obligation_post_lvl :=
  clear_defs; destruct_conjs; subst;
  split; [ econstructor; eassumption |];
  apply infer_post_of_type; eapply wf_type_univ; apply wf_level_large; assumption.

(** A closed type is a type. *)
Ltac obligation_typ_closed := clear_defs; type_closed.

(** The subtyping order of [type_check]: both types are types. *)
Ltac obligation_suborder :=
  clear_defs; destruct_conjs;
  match goal with
  | |- subtyping_order ?G ?A ?B =>
      constructor; apply nbe_order_of_type; first [ assumption | type_sound ]
  end.

(** The positive case of [type_check]. *)
Ltac obligation_check := clear_defs; destruct_conjs; mauto 3.

(** The obligations of a body: a failure inverts the body's judgment,
    whose prefix has one expansion ([alg_body_functional]); a success is
    the rule, past a context the soundness of the prefix makes. *)
Ltac body_obligation_failure :=
  intros;
  repeat match goal with
    | Hb : _ ⊢aᵇ gm_ext _ _ _ ⇝ _ |- _ => inversion Hb; subst; clear Hb
    | Hb : _ ⊢aᵇ gm_open _ _ _ ⇝ _ |- _ => inversion Hb; subst; clear Hb
    | Hu : _ ⊢aᵘ gu_mk _ (md_body _ _) |- _ => inversion Hu; subst; clear Hu
    end;
  repeat match goal with
    | H1 : ?G ⊢aᵇ ?Φ ⇝ ?X, H2 : ?G ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
        assert_fails constr_eq X Y; pose proof (alg_body_functional ltac:(gctx_wf_tac) H1 H2); subst Y; clear H2
    end;
  functional_alg_type_infer_rewrite_clear;
  md_unify;
  sort_unify;
  first [ contradiction
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ]
        | solve [ match goal with HN : forall _ _, ~ _ |- _ => eapply HN; eassumption end ]
        | solve [ firstorder ]
        | congruence
        | match goal with H : forall u : universe_nf, ?X <> universe_nf_to_nf u |- _ => exact (H _ eq_refl) end ].

Ltac body_obligation1 :=
  first [ solve [ body_obligation_failure ]
        | solve [ split; [ constructor | cbn; assumption ] ]
        | solve [ split; [ econstructor; eassumption | first [ ctx_wf_tac | eapply alg_body_ctx; [ eassumption | econstructor; eassumption ] ] ] ]
        | solve [ obligation_check ]
        | assumption
        | solve [ ctx_wf_tac ]
        | solve [ eapply ctx_wf_gctx; ctx_premise ]
        | solve [ eapply alg_modexp_sound; [ eassumption | ctx_premise ] ]
        | solve [ typ_sound ] ].

Ltac body_obligation :=
  first [ obligation_order | clear_defs; intros; destruct_conjs; body_obligation1 ].


(** A small universe: its level infers a type of levels, so the universe
    above is a type, whose normal form is the inferred universe. *)
Ltac obligation_suniv_lvl :=
  destruct_conjs; subst;
  match goal with HM : ?G ⊢a ?M ⟹ Levelⁿ@?k, HG : ⊢ ?G |- _ =>
    assert (G ⊢ M : Level@k) by (exact (alg_type_infer_sound HM HG));
    assert (G ⊢ Type⟨succl M⟩ : Typeω@0)
      by (eapply wf_univ_large_tm; [ exact HG | eapply wf_succl; eassumption ])
  end.

Ltac obligation_suniv_nbe := clear_defs; obligation_suniv_lvl; eapply nbe_order_of_typ; eassumption.

Ltac obligation_suniv_post :=
  clear_defs; obligation_suniv_lvl;
  split; [ eapply alg_type_infer_suniv; eassumption | eapply level_of_nbe_typ; eassumption ].

(** ** One Tactic for the Obligations of the Checkers

    The obligations of the checkers ([Reference.TypeCheck],
    [Extraction.TypeCheck]) are proved by one tactic, [checker_obligation],
    that reads the kind of each off its goal; the tactics before it prove
    each kind. *)

(** The types the obligations know of: the types the checker has inferred
    a sort of, the normal forms of types, and the parts of [Π]s, [∀]s and
    conjunctions among them. *)
Ltac saturate_types :=
  repeat match goal with
    | Ha : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA _ _ |- _ =>
        let T := constr:(G ⊢ᵗ A) in assert_fails (assert T by assumption);
        assert T by (eapply type_of_sort_infer; [ ctx_wf_tac | exact Ha | exact Hs ])
    | Ha : ?G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
        let T := constr:(G ⊢ᵗ A) in assert_fails (assert T by assumption);
        assert T by (eapply type_of_sort_infer; [ ctx_wf_tac | exact Ha | constructor; exact Hu ])
    | Ha : ?G ⊢a ?A ⟹ Propⁿ |- _ =>
        let T := constr:(G ⊢ᵗ A) in assert_fails (assert T by assumption);
        assert T by (eapply type_of_sort_infer; [ ctx_wf_tac | exact Ha | constructor ])
    | HX : ?G ⊢ᵗ ?X, Hn : nbe_ty _ _ ?G ?X ?W |- _ =>
        let T := constr:(G ⊢ᵗ (W : exp)) in assert_fails (assert T by assumption);
        pose proof (wf_type_nbe _ _ _ HX Hn)
    | H : ?G ⊢ᵗ nf_to_exp (nf_pi ?r ?A ?B) |- _ =>
        let T := constr:(G ▹ (A : exp) ⊢ᵗ (B : exp)) in assert_fails (assert T by assumption);
        destruct (wf_type_pi_inv G r A B H)
    | H : ?G ⊢ᵗ a_pi ?r ?A ?B |- _ =>
        let T := constr:(G ▹ A ⊢ᵗ B) in assert_fails (assert T by assumption);
        destruct (wf_type_pi_inv G r A B H)
    | H : ?G ⊢ᵗ nf_to_exp (nf_and ?P ?Q) |- _ =>
        let T := constr:(G ▹ (P : exp) ⊢ᵗ (Q : exp)) in assert_fails (assert T by assumption);
        let HP := fresh "HP" in let HQ := fresh "HQ" in
        destruct (wf_type_and_inv G P Q H) as [HP HQ];
        pose proof (wf_type_prop HP); pose proof (wf_type_prop HQ)
    end.

(** A term the checker has inferred or checked is typed. *)
Ltac checker_term :=
  lazymatch goal with
  | |- ?G ⊢ a_left ?M : ?P =>
      eapply wf_left; [ eassumption | eassumption | checker_term ]
  | |- ?G ⊢ ?M : ?A =>
      first [ assumption
            | match goal with H : G ⊢a M ⟹ _ |- _ => exact (alg_type_infer_sound H ltac:(ctx_wf_tac)) end
            | match goal with H : G ⊢a M ⟸ A |- _ =>
                let HA := fresh "HA" in assert (HA : G ⊢ᵗ A) by checker_type;
                destruct HA as [? ? ?]; eapply alg_type_check_sound_sort; [ exact H | ctx_wf_tac | eassumption | eassumption ] end ]
  end
(** A substitution of a term for the last entry of a context. *)
with checker_sub :=
  lazymatch goal with
  | |- ?G ⊢ˢ Id,,?M : ?G ▸ ?A ≔ ?M =>
      let HA := fresh "HA" in assert (HA : G ⊢ᵗ A) by checker_type;
      destruct HA as [? ? ?]; eapply wf_sub_single_def; [ eassumption | eassumption | checker_term ]
  | |- ?G ⊢ˢ Id,,?M : ?G ▹ ?A =>
      let HA := fresh "HA" in assert (HA : G ⊢ᵗ A) by checker_type;
      destruct HA as [? ? ?]; eapply wf_sub_single; [ eassumption | eassumption | checker_term ]
  | |- ?G ⊢ˢ Id ,,ₘ me_lit ?U : ?G ▹ₘ ?U =>
      eapply wf_sub_single_mod; eapply alg_unit_sound; [ eassumption | ctx_wf_tac ]
  end
(** A type the obligation knows of, or one built from those. *)
with checker_type :=
  saturate_types;
  lazymatch goal with
  | |- ?G ⊢ᵗ ?X =>
      first [ assumption
            | type_closed
            | type_sound
            (** A variable's type *)
            | match goal with H : G ∋ #_ : X |- _ => eapply ctx_lookup_wf; [ ctx_wf_tac | exact H ] end
            (** An instance *)
            | lazymatch X with
              | _[_] => eapply wf_type_sub_preserves; [ eassumption | checker_sub ]
              end
            (** The universe above a small universe *)
            | lazymatch X with
              | Type⟨succl _⟩ => obligation_suniv_lvl; eapply wf_type_univ; eassumption
              end
            (** The universe of a [Π] *)
            | lazymatch X with
              | universe_nf_pi_tm ?u ?v =>
                  match goal with
                  | HB : ?G ⊢a ?B ⟹ ?UB, Hu : is_sort_nf ?UB _ u, HC : ?G ▹ ?B ⊢a ?C ⟹ ?UC,
                    HnC : nbe_ty _ _ (?G ▹ ?B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
                      let HBu := fresh "HBu" in let HCv := fresh "HCv" in let Hvw := fresh "Hvw" in
                      let HG' := fresh "HG" in assert (HG' : ⊢ G) by ctx_wf_tac;
                      destruct (alg_pi_parts_sound HG' HB Hu HC HnC Hv) as (HBu & HCv & Hvw);
                      let k := fresh "k" in let Hk := fresh "Hk" in
                      destruct (wf_universe_nf_pi_tm HBu HCv Hvw) as [k Hk]; exact (wf_type_univ Hk)
                  end
              end
            (** The type of a λ: a [Π] or [∀] of its domain's normal form *)
            | let r := lazymatch X with a_pi ?r _ _ => r | nf_to_exp (nf_pi ?r _ _) => r end in
              match goal with
              | Hr : nbe_ty_relevance (G ▹ ?A0) ?B0 r, Hn : nbe_ty _ _ G ?A0 ?W |- _ =>
                  eapply (wf_type_fn_post G A0 W B0 r); [ checker_type | exact Hn | checker_type | exact Hr ]
              end
            (** A member's type *)
            | match goal with
              | HM : G ⊢aᵐ ?M, Hm : mdenote _ _ G (me_mem ?M _) _, Ht : mdesc_type _ = Some X |- _ =>
                  eapply member_typ_of_alg; [ ctx_wf_tac | exact HM | exact Hm | exact Ht ]
              end
            (** A parameter a module expression still takes *)
            | match goal with
              | HM : G ⊢aᵐ ?M, Hm : mdenote _ _ G ?M _, Ht : mdesc_mod_tele _ = Some ?T,
                Hv : tele_view ?T = Some (X, _) |- _ =>
                  let HB := fresh "HB" in
                  destruct (mtele_head_wf _ _ _ _ _ _ (alg_modexp_sound HM ltac:(ctx_wf_tac)) Hm Ht Hv) as [? HB];
                  exact (wf_type_univ HB)
              end ]
  end.

(** The postcondition of an inference: its rule, and that the inferred type
    infers a sort and is a type. *)
Ltac checker_post :=
  lazymatch goal with
  | |- ?G ⊢a ?M ⟹ ?W /\ _ =>
      split;
      [ first [ solve [ econstructor; eassumption ] | solve [ mauto 3 ] ]
      | first [ match goal with
                | Hn : nbe_ty _ _ G ?X W |- _ => apply (level_of_nbe G X W); [ checker_type | exact Hn ]
                end
              | apply (infer_post_of_type G W); checker_type ] ]
  end.

(** A failure: the judgment it rules out inverted against the failing
    premise. *)
Ltac checker_failure :=
  first [ solve [ obligation_failure ]
        | solve [ obligation_mem_failure ]
        | solve [ module_obligation_10 ]
        | solve [ module_obligation_20 ]
        | solve [ body_obligation ] ].

(** One inferred type, sort and universe of each term: the copies a chain
    of [let*o] leaves are made one. *)
Ltac checker_unify :=
  repeat match goal with
    | H1 : ?G ⊢a ?M ⟹ ?A1, H2 : ?G ⊢a ?M ⟹ ?A2 |- _ =>
        assert_fails (constr_eq A1 A2);
        let E := fresh "E" in
        assert (E : A1 = A2) by (eapply functional_alg_type_infer; [ gctx_wf_tac | exact H1 | exact H2 ]);
        clear H2; try subst
    end;
  nbe_ty_unify;
  sort_unify.

Ltac checker_obligation :=
  program_simplify; intros; cbv beta; repeat match goal with |- ~ _ => intro end;
  lazymatch goal with
  | |- False => checker_failure
  | |- type_check_order _ => clear_defs; obligation_order
  | |- type_infer_order _ => clear_defs; obligation_order
  | |- app_order _ _ => clear_defs; obligation_order
  | |- ext_order _ => clear_defs; obligation_order
  | |- unit_order _ => clear_defs; obligation_order
  | |- body_order _ => clear_defs; obligation_order
  | |- modexp_order _ => clear_defs; obligation_order
  | |- _ => clear_defs; destruct_conjs; try subst; checker_unify; checker_obligation_positive
  end
with checker_obligation_positive :=
  lazymatch goal with
  | |- type_check_order _ => obligation_order
  | |- type_infer_order _ => obligation_order
  | |- app_order _ _ => obligation_order
  | |- ext_order _ => obligation_order
  | |- unit_order _ => obligation_order
  | |- body_order _ => obligation_order
  | |- modexp_order _ => obligation_order
  | |- ⊢ᵍ _ ⍮ _ => obligation_check
  | |- ⊢ ?G => first [ assumption
                     | match goal with HA : G ⊢ᵗ _ |- _ => exact (checker_env_ctx_of_typ _ _ HA) end
                     | ctx_wf_tac | obligation_ctx_ext | body_obligation ]
  | |- subtyping_order _ _ _ => obligation_suborder
  | |- nbe_ty_order _ _ _ _ => apply nbe_order_of_type; checker_type
  | |- _ ⊢ᵗ _ => checker_type
  | |- _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _ => module_obligation_18
  | |- _ ⊢a _ ⟹ _ /\ _ => checker_post
  | |- _ ⊢a _ ⟸ _ => obligation_check
  | |- _ => first [ solve [ obligation_check ] | solve [ body_obligation ] | module_obligation_2 | module_obligation_19 ]
  end.
