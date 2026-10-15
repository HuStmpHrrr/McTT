From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Syntactic.System Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval Simulation NbE PseudoMonadic Subtyping MemberType.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * What the Two Checkers Share

    The extracted checker ([Extraction.TypeCheck]) and the reference checker
    it refines ([Reference.TypeCheck]) recurse along the same orders, decide
    the same side conditions, carry the same initial environment, and prove
    their obligations with the same tactics, which are therefore defined
    here, outside any section, rather than locally to one checker. *)

Section Fixed_GCtx.
Context {GC : GCtx} {F : FCtx gc_deps gc_stack}.

Section lookup.
  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | |- ~ _ => intro
    | H: ⊢ _ :: _ |- _ => inversion_clear H
    | H: ⋅ ∋ #_ : _ |- _ => inversion_clear H
    | H: _ :: _ ∋ #(S _) : _ |- _ => inversion_clear H
    | H: ce_mod _ :: _ ∋ #0 : _ |- _ => inversion H
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros;
    repeat impl_obl_tac1;
    intuition (mauto 4).

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations lookup G (HG : ⊢ G) x : { A | G ∋ #x : A } + { forall A, ~ G ∋ #x : A } :=
  | cons e G, HG, x with x => {
    | 0 with e => {
      | ce_ass A => pureo (exist _ A[↑]ʷ _)
      | ce_def A M => pureo (exist _ A[↑]ʷ _)
      | ce_mod _ => inright _ }
    | S x' =>
        let*o (exist _ B _) := lookup G _ x' while _ in
        pureo (exist _ B[↑]ʷ _)
    }
  | ⋅, HG, x => inright _.
End lookup.

Section type_check.
  (** Whether a normal form is a universe, and at which index: the side
      condition of every rule that asks for a type.  A plain [match], so that
      the extracted code is one case analysis and the two universe cases are
      visibly the only ones. *)
  Definition univ_nf_idx_dec (A : nf) : { u : unf | is_univ_nf A u } + { forall u, ~ is_univ_nf A u }.
  Proof.
    destruct A as [ i | c xs | | ? ? | | | | ? ? | ? ? | ? ? | ? ? ? | ? ];
      [ left; exists (unl i); constructor
      | left; exists (uns (c, xs)); constructor
      | right; intros ? H; inversion H .. ].
  Defined.

  (** Extraction should set the 9th bit of [Extraction Flag] (for example,
      [Set Extraction Flag 1007.]); otherwise this function introduces
      redundant pair construction and pattern matching. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_subterms_of_pi_nf (A : nf) : { B & { C | A = Πⁿ B C } } + { forall B C, A <> Πⁿ B C } :=
  | Πⁿ B C => pureo (existT _ B (exist _ C _))
  | _              => inright _
  .

  (** Whether a normal form is a type of levels, and of which sort. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_level_sort_nf (A : nf) : { k | A = Levelⁿ@k } + { forall k, A <> Levelⁿ@k } :=
  | Levelⁿ@k => pureo (exist _ k _)
  | _        => inright _
  .

  Extraction Inline univ_nf_idx_dec get_subterms_of_pi_nf get_level_sort_nf.

  (** ** Deciding the Side Conditions of Units *)

  Definition tele_ass_dec : forall Δ, { tele_ass Δ } + { ~ tele_ass Δ }.
  Proof.
    induction Δ as [| [A | A M | U] Δ IH].
    - left; constructor.
    - destruct IH as [H | H]; [ left; constructor; eauto | right; intros Hf; inversion Hf; contradiction ].
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
    intros [b pv A [M |] | pm U | pvi Di Φi | ? ? ? ?] [b' pv' A' [M' |] | pm' U' | pvi' Di' Φi' | ? ? ? ?]; cbn; try (right; intros []; fail); try (left; exact I).
    - destruct b, b', (Bool.bool_dec pv pv'); try (right; intuition congruence; fail); left; auto.
    - exact (Bool.bool_dec pm pm').
  Defined.

  Definition iitem_eq_dec : forall it it' : iitem, { it = it' } + { it <> it' }.
  Proof. repeat decide equality; apply string_dec. Defined.

  Definition body_shape_dec : forall Φ Φ', { body_shape Φ Φ' } + { ~ body_shape Φ Φ' }.
  Proof.
    induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its']; cbn;
      try (left; exact I); try (right; intros []; fail).
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (string_dec x x') as [H2 | H2]; [| right; intuition ].
      destruct (entry_shape_dec E E') as [H3 | H3]; [ left; auto | right; intuition ].
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (list_eq_dec iitem_eq_dec its its') as [H2 | H2]; [ left; auto | right; intuition ].
  Defined.

  (** ** Deciding Member Types *)

  Definition member_type_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H ch
      (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
      { R | member_type gc_deps gc_stack Γ H ch R } + { forall R, ~ member_type gc_deps gc_stack Γ H ch R } :=
    member_type_impl gc_deps gc_stack (gctx_closed_of_wf _ _ Hg) Γ H ch (mt_order_of_wf _ _ _ _ Hg HH ch).

  (** A member type asked for as a definition's type, or as a module's
      arity: member types are unique, so the other sort is none. *)
  Definition mres_term_dec {Γ H ch}
      (d : { R | member_type gc_deps gc_stack Γ H ch R } + { forall R, ~ member_type gc_deps gc_stack Γ H ch R }) :
      { A | member_type gc_deps gc_stack Γ H ch (mr_term A) } +
      { forall A, ~ member_type gc_deps gc_stack Γ H ch (mr_term A) }.
  Proof.
    destruct d as [[[A | T | T] HR] | HN]; [ left; exists A; exact HR | right | right | right; intros A HA; exact (HN _ HA) ];
      intros A HA; pose proof (proj1 (member_type_functional _ _) _ _ _ _ HR _ HA); discriminate.
  Defined.

  Lemma mres_ty_tl : forall R T, mres_tl R = Some T -> mres_ty R = ctx_pi T a_True.
  Proof. intros [A | T0 | T0] T H; cbn in H; try discriminate; injection H as <-; reflexivity. Qed.

  (** A module's arity: the parameters a module still takes. *)
  Definition mres_mod_dec {Γ H ch}
      (d : { R | member_type gc_deps gc_stack Γ H ch R } + { forall R, ~ member_type gc_deps gc_stack Γ H ch R }) :
      { T | exists R, member_type gc_deps gc_stack Γ H ch R /\ mres_tl R = Some T } +
      { forall R, member_type gc_deps gc_stack Γ H ch R -> mres_tl R = None }.
  Proof.
    destruct d as [[[A | T | T] HR] | HN].
    - right; intros R HR'; pose proof (proj1 (member_type_functional _ _) _ _ _ _ HR _ HR') as <-; reflexivity.
    - left; exists T, (mr_mod T); split; [ exact HR | reflexivity ].
    - left; exists T, (mr_indm T); split; [ exact HR | reflexivity ].
    - right; intros R HR'; destruct (HN _ HR').
  Defined.

  Definition member_term_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H ch (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :=
    mres_term_dec (member_type_dec Hg Γ H ch HH).

  Definition member_mod_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H ch (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :=
    mres_mod_dec (member_type_dec Hg Γ H ch HH).

  (** A chain from a unit has an order whether or not it is a module. *)
  Definition member_chain_mod_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H mq (Hp : mod_qname H = Some mq) :
      { T | exists R, member_type gc_deps gc_stack Γ H nil R /\ mres_tl R = Some T } +
      { forall R, member_type gc_deps gc_stack Γ H nil R -> mres_tl R = None } :=
    mres_mod_dec (member_type_impl gc_deps gc_stack (gctx_closed_of_wf _ _ Hg) Γ H nil
                    (mt_order_chain_self _ _ _ _ _ Hg Hp nil)).

  (** What a local open of a module generates. *)
  Definition items_gen_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H its (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
      { gs | items_gen gc_deps gc_stack None Γ H its gs } + { forall gs, ~ items_gen gc_deps gc_stack None Γ H its gs } :=
    items_gen_impl gc_deps gc_stack (gctx_closed_of_wf _ _ Hg) None Γ H its
      (igo_of _ _ _ _ (mt_order_of_wf _ _ _ _ Hg HH) its).

  (** The outermost parameter of an arity, if any. *)
  Equations tele_view_dec (T : ctx) : { B : typ & { T1 : ctx | tele_view T = Some (B, T1) } } + { tele_view T = None } :=
  tele_view_dec T with inspect (tele_view T) := {
    | exist _ (Some (B, T1)) E => inleft (existT _ B (exist _ T1 E))
    | exist _ None E => inright E }.

  Extraction Inline member_type_dec member_term_dec member_mod_dec member_chain_mod_dec mres_term_dec mres_mod_dec tele_view_dec
    items_gen_dec.

  (** ** Facts the Obligations Use *)


  Lemma nbe_order_of_typ : forall G X i, G ⊢ X : Typeω@i -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * HX; destruct (soundness_ty HX) as [W [HW _]]; eauto using nbe_ty_order_sound. Qed.

  (** The normal form of a type is a type, both algorithmically and
      declaratively: the two halves of [type_infer]'s postcondition. *)
  Lemma level_of_nbe : forall G X i D,
      G ⊢ X : Typeω@i ->
      nbe_ty_f G X D ->
      (exists UD u, G ⊢a D ⟹ UD /\ is_univ_nf UD u) /\ (exists j, G ⊢ D : Typeω@j).
  Proof.
    intros * HX HD.
    assert (G ⊢ X ≈ D : Typeω@i) by (eapply soundness_ty'; eassumption).
    assert (G ⊢ D : Typeω@i) by (gen_presups; eassumption).
    destruct (alg_type_infer_large_typ_complete (user_exp_nf D) ltac:(eassumption)) as [UD [u [? []]]].
    split; [ exists UD, u; split; assumption | exists i; assumption ].
  Qed.

  Lemma member_typ_of_alg : forall G M ch R, ⊢ G -> G ⊢aᵐ M ->
      member_type gc_deps gc_stack G M ch R -> (mres_kind R = mk_term -> ch <> nil) -> exists i, G ⊢ mres_ty R : Typeω@i.
  Proof.
    intros * HG HM Hm Hch.
    exact (proj1 (proj1 member_wf _ _ _ _ Hm (alg_modexp_sound HM HG) Hch)).
  Qed.

  (** The universe is lifted to the large one of its tier before the
      substitution: a small universe's level may mention the module. *)
  Lemma let_mod_typ_of_alg : forall G U C (u : unf), ⊢ G -> G ⊢aᵘ U -> G ▹ₘ U ⊢a C ⟹ univ_nf u ->
      G ⊢ C[Id ,,ₘ me_lit U] : Typeω@(unf_large u).
  Proof.
    intros * HG HU HC.
    pose proof (alg_unit_sound HU HG) as HU'.
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU').
    assert (HCt : G ▹ₘ U ⊢ C : unf_tm u)
      by (rewrite <- nf_to_exp_univ_nf; eapply alg_type_infer_sound; eassumption).
    apply wf_exp_unf_large in HCt.
    exact (sub_preserves_exp _ _ _ _ _ _ _ HCt (wf_sub_single_mod _ _ _ _ HU')).
  Qed.

  (** ** The Initial Environment the Checker Carries

      Every normalization the checker does is at the initial environment of
      its context, or rather at an environment related to it entry by entry
      ([fenv]), which the fast evaluation computes.  The checker computes it
      once, where it enters a context, and extends it entry by entry under
      binders, rather than once per normalization ([nbe_ty_env_impl]). *)
  Definition tenv G := fenv gc_deps gc_stack G.

  Lemma tenv_order_of_wf : forall G, ⊢ G -> initial_env_order gc_deps gc_stack G.
  Proof.
    intros G HG.
    assert (G ⊢ ⊤ : Typeω@0) as [W [HW _]]%soundness_ty by mauto 2.
    inversion HW; subst; eauto using initial_env_order_sound.
  Qed.

  (** The reference value of the type or definition an extension adds. *)
  Lemma tenv_ref_ass : forall G A p, ⊢ G ▹ A -> initial_env gc_deps gc_stack G p -> exists a, ⟦ A ⟧ p ↘ a.
  Proof.
    intros * HGA Hp; inversion HGA as [| ? ? ? i ? HA | |]; subst.
    destruct (soundness_ty HA) as [W [HW _]]; inversion HW; subst.
    functional_initial_env_rewrite_clear; eauto.
  Qed.

  Lemma tenv_ref_def : forall G A M p, ⊢ G ▸ A ≔ M -> initial_env gc_deps gc_stack G p -> exists m, ⟦ M ⟧ p ↘ m.
  Proof.
    intros * HGA Hp; inversion HGA as [| | ? ? ? i ? ? HA HM |]; subst.
    destruct (soundness HM) as [W [HW _]]; inversion HW; subst.
    functional_initial_env_rewrite_clear; eauto.
  Qed.

  Lemma tenv_eval_order_ass : forall G A p', ⊢ G ▹ A ->
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      feval_exp_order gc_deps gc_stack A p'.
  Proof.
    intros * HGA (p & Hp & Hag); destruct (tenv_ref_ass _ _ _ HGA Hp) as [a Ha].
    eapply (feval_of_ref _ _ _ _ _ _ Ha), agree_all, Hag.
  Qed.

  Lemma tenv_eval_order_def : forall G A M p', ⊢ G ▸ A ≔ M ->
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      feval_exp_order gc_deps gc_stack M p'.
  Proof.
    intros * HGA (p & Hp & Hag); destruct (tenv_ref_def _ _ _ _ HGA Hp) as [m Hm].
    eapply (feval_of_ref _ _ _ _ _ _ Hm), agree_all, Hag.
  Qed.

  Lemma tenv_ass_sim : forall G A p' a', ⊢ G ▹ A ->
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      ⟦ A ⟧ᶠ gc_deps ⍮ gc_stack ⍮ p' ↘ a' ->
      exists p, initial_env gc_deps gc_stack (G ▹ A) p /\ env_agree (fun _ => True) p (p' ↦ ⇑! a' (List.length G)).
  Proof.
    intros * HGA (p & Hp & Hag) Ha'; destruct (tenv_ref_ass _ _ _ HGA Hp) as [a Ha].
    pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha (agree_all _ _ _ Hag)) _ Ha').
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ exact Hag | repeat constructor; assumption | intros; exact I ].
  Qed.

  Lemma tenv_def_sim : forall G A M p' m', ⊢ G ▸ A ≔ M ->
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      ⟦ M ⟧ᶠ gc_deps ⍮ gc_stack ⍮ p' ↘ m' ->
      exists p, initial_env gc_deps gc_stack (G ▸ A ≔ M) p /\ env_agree (fun _ => True) p (p' ↦ m').
  Proof.
    intros * HGA (p & Hp & Hag) Hm'; destruct (tenv_ref_def _ _ _ _ HGA Hp) as [m Hm].
    pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Hm (agree_all _ _ _ Hag)) _ Hm').
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ exact Hag | constructor; assumption | intros; exact I ].
  Qed.

  Lemma tenv_mod_sim : forall G U p',
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      exists p, initial_env gc_deps gc_stack (G ▹ₘ U) p /\ env_agree (fun _ => True) p (p' ↦ᵐ dm_local p' U nil).
  Proof.
    intros * (p & Hp & Hag).
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ exact Hag | | intros; exact I ].
    apply des_mod, dms_local; [ apply agree_all; exact Hag | constructor ].
  Qed.

  Lemma tenv_ctx_of_typ : forall G X, (exists j, G ⊢ X : Typeω@j) -> ⊢ G.
  Proof. intros * [? HX]; gen_presups; assumption. Qed.

  (** The initial environment of a context, from scratch. *)
  Definition tenv_of G (HG : ⊢ G) : tenv G :=
    initial_env_impl gc_deps gc_stack G (tenv_order_of_wf G HG).

  (** The initial environment of an extended context, from that of the
      context: one entry more, by its rule of [initial_env]. *)
  Definition tenv_ass G (P : tenv G) A (HGA : ⊢ G ▹ A) : tenv (G ▹ A) :=
    let (p, Hp) := P in
    let (a, Ha) := feval_exp_impl gc_deps gc_stack A p (tenv_eval_order_ass G A p HGA Hp) in
    exist _ (p ↦ ⇑! a (List.length G)) (tenv_ass_sim _ _ _ _ HGA Hp Ha).

  Definition tenv_def G (P : tenv G) A M (HGA : ⊢ G ▸ A ≔ M) : tenv (G ▸ A ≔ M) :=
    let (p, Hp) := P in
    let (m, Hm) := feval_exp_impl gc_deps gc_stack M p (tenv_eval_order_def G A M p HGA Hp) in
    exist _ (p ↦ m) (tenv_def_sim _ _ _ _ _ HGA Hp Hm).

  Definition tenv_mod G (P : tenv G) U : tenv (G ▹ₘ U) :=
    let (p, Hp) := P in
    exist _ (p ↦ᵐ dm_local p U nil) (tenv_mod_sim _ U _ Hp).

  (** The initial environment of an extension [Ψ ++ G], from that of [G]:
      one entry more per entry of [Ψ], rather than all of [G]'s again. *)
  Fixpoint tenv_ext G (P : tenv G) (Ψ : ctx) {struct Ψ} : ⊢ Ψ ++ G -> tenv (Ψ ++ G) :=
    match Ψ as Ψ0 return ⊢ Ψ0 ++ G -> tenv (Ψ0 ++ G) with
    | nil => fun _ => P
    | ce_ass A :: Ψ' => fun H => tenv_ass (Ψ' ++ G) (tenv_ext G P Ψ' (ctx_decomp_tail H)) A H
    | ce_def A M :: Ψ' => fun H => tenv_def (Ψ' ++ G) (tenv_ext G P Ψ' (ctx_decomp_tail H)) A M H
    | ce_mod U :: Ψ' => fun H => tenv_mod (Ψ' ++ G) (tenv_ext G P Ψ' (ctx_decomp_tail H)) U
    end.

  (** A member of a chain from a unit, read off the global context: the type
      of the global, if it is one. *)
  (** The type of a global, of the type former that the module of an
      inductive type is as a term, or of the term an inductive alias
      δ-unfolds to. *)
  Definition glob_lookup_spec (R : modexp) (pre : list string) (x : string) : option typ :=
    match R with
    | me_unit fp =>
        match gc_resolve gc_deps gc_stack (q_abs fp (pre ++ x :: nil)) with
        | Some (ge_def _ _ A _) => Some A
        | Some _ => None
        | None =>
            match ind_lookup gc_deps gc_stack (q_abs fp (pre ++ x :: nil)) with
            | Some D => Some (ind_ty D)
            | None =>
                match ind_alias_lookup gc_deps gc_stack (q_abs fp (pre ++ x :: nil)) with
                | Some (Δ, p, Ns) =>
                    match ind_lookup gc_deps gc_stack p with
                    | Some D => Some (ctx_pi Δ (ind_ty_at D Ns))
                    | None => None
                    end
                | None => None
                end
            end
        end
    | _ => None
    end.

  Definition glob_lookup (R : modexp) (pre : list string) (x : string) : option typ :=
    match R with
    | me_unit fp =>
        match gc_resolve_u (fc_units F) gc_stack (q_abs fp (pre ++ x :: nil)) with
        | Some (ge_def _ _ A _) => Some A
        | Some _ => None
        | None =>
            match ind_lookup_u (fc_units F) gc_stack (q_abs fp (pre ++ x :: nil)) with
            | Some D => Some (ind_ty D)
            | None =>
                match ind_alias_lookup_u (fc_units F) gc_stack (q_abs fp (pre ++ x :: nil)) with
                | Some (Δ, p, Ns) =>
                    match ind_lookup_u (fc_units F) gc_stack p with
                    | Some D => Some (ctx_pi Δ (ind_ty_at D Ns))
                    | None => None
                    end
                | None => None
                end
            end
        end
    | _ => None
    end.

  Lemma glob_lookup_spec_eq : forall R pre x, glob_lookup R pre x = glob_lookup_spec R pre x.
  Proof.
    intros [] pre x; try reflexivity; unfold glob_lookup, glob_lookup_spec.
    rewrite (gc_resolve_u_ok _ _ (fc_units_ok F)), (ind_lookup_u_ok _ _ (fc_units_ok F)),
      (ind_alias_lookup_u_ok _ _ (fc_units_ok F)).
    destruct (gc_resolve _ _ _) as [[] |]; try reflexivity.
    destruct (ind_lookup _ _ _); try reflexivity.
    destruct (ind_alias_lookup _ _ _) as [[[d0 q0] n0] |]; try reflexivity.
    rewrite (ind_lookup_u_ok _ _ (fc_units_ok F)); reflexivity.
  Qed.

  Lemma spine_unit_path : forall H fp pre, modexp_spine H = (me_unit fp, nil, pre) -> mod_qname H = Some (q_abs fp pre).
  Proof.
    induction H as [fp0 | x | H IH y | H IH N | U]; intros * Hs; cbn in Hs |- *; try discriminate.
    - injection Hs as <- <-; reflexivity.
    - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as -> -> <-.
      rewrite (IH _ _ eq_refl); reflexivity.
    - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as _ Ha _; destruct a0; discriminate.
  Qed.

  Lemma glob_lookup_some : forall H R pre x A, modexp_spine H = (R, nil, pre) -> glob_lookup R pre x = Some A ->
      exists mq, mod_qname H = Some mq /\
        ((exists b pv B, gc_resolve gc_deps gc_stack (qname_app mq (x :: nil)) = Some (ge_def b pv A B)) \/
         (exists D, ind_lookup gc_deps gc_stack (qname_app mq (x :: nil)) = Some D /\ A = ind_ty D) \/
         (exists Δ p Ns D, ind_alias_lookup gc_deps gc_stack (qname_app mq (x :: nil)) = Some (Δ, p, Ns) /\
            ind_lookup gc_deps gc_stack p = Some D /\ A = ctx_pi Δ (ind_ty_at D Ns))).
  Proof.
    intros * Hs Hg; rewrite glob_lookup_spec_eq in Hg; destruct R; cbn in Hg; try discriminate.
    exists (q_abs l pre); split; [ exact (spine_unit_path _ _ _ Hs) |].
    destruct (gc_resolve _ _ _) as [[b pv A0 B | pm U | pv D Φ | ? ? ? ?] |] eqn:Er; try discriminate.
    - injection Hg as ->; left; eauto.
    - destruct (ind_lookup _ _ _) as [D |] eqn:El; [ injection Hg as <-; right; left; eauto |].
      destruct (ind_alias_lookup _ _ _) as [[[Δ p] Ns] |] eqn:Ea; [| discriminate ].
      destruct (ind_lookup _ _ p) as [D |] eqn:Ep; [| discriminate ]; injection Hg as <-.
      right; right; do 4 eexists; eauto.
  Qed.

  Lemma glob_lookup_none : forall H R args pre x mq b pv A B, modexp_spine H = (R, args, pre) -> glob_lookup R pre x = None ->
      mod_qname H = Some mq -> gc_resolve gc_deps gc_stack (qname_app mq (x :: nil)) = Some (ge_def b pv A B) -> False.
  Proof.
    intros * Hs Hg Hp Hr; rewrite glob_lookup_spec_eq in Hg; rewrite (mod_qname_spine _ _ Hp) in Hs; injection Hs as <- <- <-.
    cbn in Hg; change (qname_app mq (x :: nil)) with (q_abs (q_unit mq) (q_chain mq ++ x :: nil)) in Hr.
    rewrite Hr in Hg; discriminate.
  Qed.

  Lemma glob_lookup_none_ind_alias : forall H R args pre x mq Δ p Ns D, modexp_spine H = (R, args, pre) -> glob_lookup R pre x = None ->
      mod_qname H = Some mq -> ind_alias_lookup gc_deps gc_stack (qname_app mq (x :: nil)) = Some (Δ, p, Ns) ->
      ind_lookup gc_deps gc_stack p = Some D -> False.
  Proof.
    intros * Hs Hg Hp Ha Hl; rewrite glob_lookup_spec_eq in Hg; rewrite (mod_qname_spine _ _ Hp) in Hs; injection Hs as <- <- <-.
    cbn in Hg; change (qname_app mq (x :: nil)) with (q_abs (q_unit mq) (q_chain mq ++ x :: nil)) in Ha.
    pose proof (ind_alias_lookup_module _ _ _ _ _ _ Ha) as Hm.
    rewrite (gc_module_resolve _ _ _ _ Hm), (ind_lookup_not_ind_alias_rev _ _ _ _ _ _ Ha), Ha, Hl in Hg; discriminate.
  Qed.

  Lemma glob_lookup_none_ind : forall H R args pre x mq D, modexp_spine H = (R, args, pre) -> glob_lookup R pre x = None ->
      mod_qname H = Some mq -> ind_lookup gc_deps gc_stack (qname_app mq (x :: nil)) = Some D -> False.
  Proof.
    intros * Hs Hg Hp Hl; rewrite glob_lookup_spec_eq in Hg; rewrite (mod_qname_spine _ _ Hp) in Hs; injection Hs as <- <- <-.
    cbn in Hg; change (qname_app mq (x :: nil)) with (q_abs (q_unit mq) (q_chain mq ++ x :: nil)) in Hl.
    rewrite (proj1 (ind_lookup_not_def _ _ _ _ Hl)), Hl in Hg; discriminate.
  Qed.

  Inductive type_check_order : exp -> Prop :=
  | tc_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order : exp -> Prop :=
  | ti_typ : forall {i}, type_infer_order Typeω@i
  | ti_suniv : forall {M}, type_infer_order M -> type_infer_order Type⟨M⟩
  | ti_level : forall {n}, type_infer_order Level@n
  | ti_llit : forall {o}, type_infer_order (𝕃ᵒ o)
  | ti_succl : forall {M}, type_infer_order M -> type_infer_order (succl M)
  | ti_maxl : forall {M N}, type_infer_order M -> type_infer_order N -> type_infer_order (maxl M N)
  | ti_True : type_infer_order ⊤
  | ti_true : type_infer_order ⋆
  | ti_False : type_infer_order ⊥
  | ti_exfalso : forall {A M}, type_check_order M -> type_infer_order A -> type_infer_order (efq M return A)
  | ti_indty : forall {p}, type_infer_order (a_ind p)
  | ti_con : forall {p c}, type_infer_order (a_con p c)
  (** A numeral is expanded before it is checked; it has no type. *)
  | ti_nlit : forall {n}, type_infer_order (a_nlit n)
  | ti_ntok : type_infer_order a_ntok
  | ti_elim : forall {nm A Bs M}, type_infer_order M -> type_infer_order A ->
      (forall b, List.In b Bs -> type_check_order (snd b)) -> type_infer_order (a_elim nm A Bs M)
  | ti_pi : forall {A B}, type_infer_order A -> type_infer_order B -> type_infer_order Π A B
  | ti_fn : forall {A M}, type_infer_order A -> type_infer_order M -> type_infer_order λ A M
  | ti_app : forall {M N}, app_order M N -> type_infer_order (M $ N)
  | ti_let : forall {A M B}, type_infer_order A -> type_check_order M -> type_infer_order B -> type_infer_order (ℓ A ≔ M in B)
  | ti_let_infer : forall {M B}, type_infer_order M -> type_infer_order B -> type_infer_order (ℓ ≔ M in B)
  | ti_let_mod : forall {U B}, unit_order U -> type_infer_order B -> type_infer_order (ℓₘ U in B)
  (** A member of an applied module recurses into its root's member applied,
      which is not a subterm. *)
  | ti_mem : forall {H x}, modexp_order H ->
      (forall R args pre, modexp_spine H = (R, args, pre) -> args <> nil ->
         type_infer_order (apps (member_ref R (pre ++ x :: nil)) args)) ->
      type_infer_order (a_mem H x)
  | ti_vlookup : forall {x}, type_infer_order #x
  (** An application, apart from its head: the checker computes the type
      of a spine of applications as a value ([type_infer_app_in]), and
      checks its head ([type_infer_val_in]) at the order of a check. *)
  with app_order : exp -> exp -> Prop :=
  | ao_app : forall {M N}, type_check_order M -> type_check_order N -> app_order M N
  with ext_order : ctx -> Prop :=
  | eo_nil : ext_order nil
  | eo_ass : forall {A Ψ}, ext_order Ψ -> type_infer_order A -> ext_order (Ψ ▹ A)
  | eo_def : forall {A M Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> ext_order (Ψ ▸ A ≔ M)
  | eo_mod : forall {U Ψ}, ext_order Ψ -> unit_order U -> ext_order (Ψ ▹ₘ U)
  with unit_order : gunit -> Prop :=
  | uo_body : forall {Δ Φ}, ext_order Δ -> body_order Φ -> unit_order (gu_body Δ Φ)
  | uo_alias : forall {Δ E}, ext_order Δ -> modexp_order E -> unit_order (gu_mk Δ (md_alias E))
  (** A body, entry by entry; an entry no body may hold has nothing to
      check. *)
  with body_order : gmod -> Prop :=
  | bo_nil : body_order gm_nil
  | bo_def : forall {Φ x b pv A M}, body_order Φ -> type_infer_order A -> type_check_order M ->
      body_order (gm_ext Φ x (ge_def b pv A (Some M)))
  | bo_mod : forall {Φ x pm U}, body_order Φ -> unit_order U -> body_order (gm_ext Φ x (ge_mod pm U))
  | bo_axiom : forall {Φ x b pv A}, body_order Φ -> body_order (gm_ext Φ x (ge_def b pv A None))
  | bo_ind : forall {Φ x pv D Φi}, body_order Φ -> body_order (gm_ext Φ x (ge_ind pv D Φi))
  | bo_ind_alias : forall {Φ x pv Δ p Ns}, body_order Φ -> body_order (gm_ext Φ x (ge_ind_alias pv Δ p Ns))
  | bo_open : forall {Φ H its}, body_order Φ -> modexp_order H -> body_order (gm_open Φ H its)
  with modexp_order : modexp -> Prop :=
  | mo_unit : forall {fp}, modexp_order (me_unit fp)
  | mo_var : forall {x}, modexp_order (me_var x)
  | mo_lit : forall {U}, unit_order U -> modexp_order (me_lit U)
  | mo_mem : forall {H y}, modexp_order H -> modexp_order (me_mem H y)
  | mo_app : forall {H N}, modexp_order H -> type_check_order N -> modexp_order (me_app H N)
  .

  #[local]
  Hint Constructors type_check_order type_infer_order app_order ext_order unit_order body_order modexp_order : mctt.

  (** Every term has an order.  The order of a member of an applied module
      is built from the orders of its root and of its arguments. *)
  Definition centry_order (e : centry) : Prop :=
    match e with
    | ce_ass A => type_infer_order A
    | ce_def A M => type_infer_order A /\ type_check_order M
    | ce_mod U => unit_order U
    end.

  Lemma ext_order_app : forall X Δ, List.Forall centry_order X -> ext_order Δ -> ext_order (X ++ Δ).
  Proof.
    induction X as [| [A | A M | U] X IH]; intros * HX HΔ; cbn; [ exact HΔ | | |];
      inversion HX as [| ? ? He HX']; subst; cbn in He; destruct_conjs; constructor; auto.
  Qed.

  Lemma ext_order_of_forall : forall X, List.Forall centry_order X -> ext_order X.
  Proof. intros X HX; rewrite <- (app_nil_r X); apply ext_order_app; [ exact HX | constructor ]. Qed.

  Lemma apps_order : forall args M, type_infer_order M -> List.Forall type_check_order args ->
      type_infer_order (apps M args).
  Proof.
    induction args as [| N args IH]; intros * HM Hargs; cbn; [ exact HM |].
    inversion Hargs; subst; apply IH; [ do 2 constructor; [ constructor |] |]; assumption.
  Qed.

  Lemma me_mems_order : forall pre H, modexp_order H -> modexp_order (me_mems H pre).
  Proof. induction pre; intros; cbn; auto using mo_mem. Qed.

  Lemma spine_root_self : forall H R args pre, modexp_spine H = (R, args, pre) -> modexp_spine R = (R, nil, nil).
  Proof.
    intros * Hs; pose proof (modexp_spine_root _ _ _ _ Hs) as Hr.
    destruct R; cbn in Hr |- *; try contradiction; reflexivity.
  Qed.

  Lemma member_ref_order : forall R pre x, modexp_spine R = (R, nil, nil) -> modexp_order R ->
      type_infer_order (member_ref R (pre ++ x :: nil)).
  Proof.
    intros * Hs HR; rewrite member_ref_mems.
    constructor; [ apply me_mems_order; exact HR |].
    intros R' args pre' Hs' Hne.
    rewrite (me_mems_spine _ _ _ _ _ Hs) in Hs'; injection Hs' as _ <- _; contradiction.
  Qed.

  Lemma syn_orders_all :
    (forall M, type_infer_order M) /\
    (forall H, modexp_order H /\
       forall R args pre, modexp_spine H = (R, args, pre) -> modexp_order R /\ List.Forall type_check_order args) /\
    (forall b, match b with
           | b_def oA M => (forall A, oA = Some A -> type_infer_order A) /\ type_infer_order M
           | b_mod U => unit_order U
           end) /\
    (forall U, unit_order U) /\
    (forall D, match D with
           | md_body Φ => body_order Φ
           | md_alias E => modexp_order E
           end) /\
    (forall Φ, body_order Φ) /\
    (forall E, match E with
           | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
           | ge_mod _ U => unit_order U
           | ge_ind _ _ _ | ge_ind_alias _ _ _ _ => True
           end) /\
    (forall e, centry_order e).
  Proof.
    apply (syn_mut_ind type_infer_order
      (fun H => modexp_order H /\
         forall R args pre, modexp_spine H = (R, args, pre) -> modexp_order R /\ List.Forall type_check_order args)
      (fun b => match b with
             | b_def oA M => (forall A, oA = Some A -> type_infer_order A) /\ type_infer_order M
             | b_mod U => unit_order U
             end)
      unit_order
      (fun D => match D with
             | md_body Φ => body_order Φ
             | md_alias E => modexp_order E
             end)
      body_order
      (fun E => match E with
             | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
             | ge_mod _ U => unit_order U
             | ge_ind _ _ _ | ge_ind_alias _ _ _ _ => True
             end)
      centry_order); intros; cbn in *; destruct_conjs; eauto 6 with mctt.
    - (* an eliminator: its branches are checked *)
      constructor; [ assumption | assumption |].
      match goal with HF : List.Forall _ _ |- _ => rewrite List.Forall_forall in HF end.
      intros b Hb; apply tc_ti; auto.
    - (* a local binding *)
      destruct b as [[A |] M | U]; destruct_conjs;
        [ apply ti_let; [ eauto | constructor; assumption | assumption ]
        | apply ti_let_infer; assumption
        | apply ti_let_mod; assumption ].
    - (* a member *)
      constructor; [ assumption |].
      intros R args pre Hs Hne.
      destruct (H1 _ _ _ Hs) as [HR Hargs].
      apply apps_order; [ apply member_ref_order; [ eapply spine_root_self; eassumption | exact HR ] | exact Hargs ].
    - split; [ constructor | intros * [= <- <- <-]; split; constructor ].
    - split; [ constructor | intros * [= <- <- <-]; split; constructor ].
    - split; [ constructor; assumption |].
      intros R args pre Hs.
      destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-; eauto.
    - split; [ constructor; [ assumption | constructor; assumption ] |].
      intros R args pre Hs.
      destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
      destruct (H2 _ _ _ eq_refl) as [? ?].
      split; [ assumption | apply Forall_app; split; [ assumption | constructor; [ constructor; assumption | constructor ] ] ].
    - split; [ constructor; assumption | intros * [= <- <- <-]; split; [ constructor; assumption | constructor ] ].
    - destruct D; destruct_conjs; constructor; auto using ext_order_of_forall.
    - destruct E as [b pv A [M |] | pm U | pvi Di Φi | ? ? ? ?]; destruct_conjs;
        first [ apply bo_def; eauto with mctt | apply bo_mod; assumption
              | apply bo_axiom; assumption | apply bo_ind; assumption | apply bo_ind_alias; assumption ].
  Qed.

  Lemma type_infer_order_all : forall M, type_infer_order M.
  Proof. exact (proj1 syn_orders_all). Qed.

  Lemma modexp_order_all : forall H, modexp_order H.
  Proof. intros; exact (proj1 (proj1 (proj2 syn_orders_all) H)). Qed.

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

End type_check.
End Fixed_GCtx.

Ltac clear_defs :=
  repeat lazymatch goal with
    | H: (forall (G : ctx) (A : typ),
             (exists i : nat, G ⊢ A : Typeω@i) ->
             tenv G ->
             forall M : typ,
               type_check_order M ->
               ({ G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A }))
      |- _ =>
        clear H
    | H: (let H := fixproto in
          forall (G : ctx) (A : typ),
            (exists i : nat, G ⊢ A : Typeω@i) -> tenv G -> forall M : typ, type_check_order M -> { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A })
      |- _ =>
        clear H
    | H: (let H := fixproto in
          forall G : ctx,
            ⊢ G ->
            tenv G ->
            forall M : typ,
              type_infer_order M ->
              ({ B : nf | G ⊢a M ⟹ B /\
                  (exists UA u, G ⊢a (nf_to_exp B) ⟹ UA /\ is_univ_nf UA u) /\
                  (exists i : nat, G ⊢ (nf_to_exp B) : Typeω@i) } + { forall C : nf, ~ G ⊢a M ⟹ C }))
      |- _ =>
        clear H
    | H: (forall G : ctx,
             ⊢ G ->
             tenv G ->
             forall M : typ,
               type_infer_order M ->
               ({ B : nf | G ⊢a M ⟹ B /\
                   (exists UA u, G ⊢a (nf_to_exp B) ⟹ UA /\ is_univ_nf UA u) /\
                   (exists i : nat, G ⊢ (nf_to_exp B) : Typeω@i) } + { forall C : nf, ~ G ⊢a M ⟹ C }))
      |- _ =>
        clear H
  end.

(** A context the checker extends is well formed by the soundness of the
    check of the extension. *)
Ltac ctx_wf_tac :=
  match goal with
  | |- ⊢ ?G => assumption
  | |- ⊢ ?G ▹ ?A =>
      match goal with Ha : G ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
        assert (G ⊢ A : unf_tm u)
          by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              eapply alg_type_infer_sound; eassumption);
        assert (G ⊢ A : Typeω@(unf_large u))
          by (apply wf_exp_unf_large; eassumption);
        mauto 2 end
  | |- ⊢ ?G ▸ ?A ≔ ?M =>
      match goal with Ha : G ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA ?u, H' : G ⊢a M ⟸ A |- _ =>
        assert (G ⊢ A : unf_tm u)
          by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              eapply alg_type_infer_sound; eassumption);
        assert (G ⊢ A : Typeω@(unf_large u))
          by (apply wf_exp_unf_large; eassumption);
        assert (G ⊢ M : A) by (eapply alg_type_check_sound; eassumption); mauto 2 end
  | |- ⊢ ?G ▹ₘ ?U =>
      match goal with H : G ⊢aᵘ U |- _ => apply wf_ctx_extend_mod; eapply alg_unit_sound; eassumption end
  | |- ⊢ ?Ψ ++ ?G =>
      match goal with H : G ⊢aˣ Ψ |- _ => eapply ext_eq_ctx_left, alg_ext_sound; eassumption end
  | |- ⊢ body_ctx ?Φ0 ++ ?Δ ++ ?G =>
      match goal with Hls : forall Φ c, In (Φ, c) _ -> ⊢ body_ctx Φ ++ Δ ++ G |- _ =>
        eapply Hls; left; reflexivity end
  end.

(** The last two components of [type_infer]'s postcondition: the inferred
    type infers a universe, and is a type. *)
Ltac is_type_obl :=
  split; [ do 2 eexists; split; [ mauto 3 | constructor ] | eexists; mauto 3 ].

(** The subject of a universe premise, as a typing at the large level the
    index of its side condition lives at: that is the form the obligations
    need.  [is_univ_nf_eq] turns the side condition into the shape of the
    inferred normal form. *)
Ltac saturate_infer_univ :=
  repeat match goal with
    | Ha : ?G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
        let T := constr:(wf_exp gc_deps gc_stack G (a_typ (unf_large u)) A) in
        assert_fails (assert T by assumption);
        assert (wf_exp gc_deps gc_stack G (unf_tm u) A)
          by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              eapply alg_type_infer_sound; [ exact Ha | ctx_wf_tac ]);
        assert T by (apply wf_exp_unf_large; eassumption)
    | HnC : nbe_ty _ _ (?G ▹ ?A) _ ?UB', Hv : is_univ_nf ?UB' ?v,
      HC : ?G ▹ ?A ⊢a ?B ⟹ ?UB, HB : ?G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA _ |- _ =>
        (** A codomain whose universe was normalised ([ati_pi]): its
            typing at the large level of the normal form's index. *)
        let T := constr:(wf_exp gc_deps gc_stack (G ▹ A) (a_typ (unf_large v)) B) in
        assert_fails (assert T by assumption);
        let HG' := fresh "HG" in
        assert (HG' : ⊢ G) by ctx_wf_tac;
        let HCv := fresh "HCv" in
        destruct (alg_pi_parts_sound HG' HB Hu HC HnC Hv) as (_ & HCv & _);
        clear HG';
        assert T by (apply wf_exp_unf_large; exact HCv)
    end.

(** A type whose inferred universe is [univ_nf u] is a type of [unf_tm u],
    and so of the large universe [Typeω@(unf_large u)] the index lives at. *)
Ltac typ_of_infer := saturate_infer_univ.

(** ** Obligations of the Module Cases *)

Ltac negc :=
  match goal with
  | Hx : _ ⊢aˣ (_ :: _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵘ (gu_mk _ _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵐ (_ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
  | Hx : _ ⊢aᵐ (_ _ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
  end;
  functional_alg_type_infer_rewrite_clear;
  first [ match goal with H : forall u : unf, ?X <> univ_nf u |- _ => exact (H _ eq_refl) end
        | match goal with
          | HN : forall R, member_type _ _ _ ?M ?c R -> mres_tl R = None, Hm : member_type _ _ _ ?M ?c ?R0,
            Ht : mres_tl ?R0 = Some _ |- _ => rewrite (HN _ Hm) in Ht; discriminate Ht
          end
        | firstorder ].

Ltac typ_sound :=
  match goal with
  | |- exists i, ?G ⊢ ?A : Typeω@i =>
      saturate_infer_univ;
      match goal with H : wf_exp gc_deps gc_stack G (a_typ ?k) A |- _ => exists k; exact H end
  end.

Ltac ctxp :=
  first [ assumption
        | ctx_wf_tac
        | match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; left; reflexivity end ].

Ltac mt_unify :=
  repeat match goal with
    | H1 : member_type ?T ?X ?G ?M ?c ?A1, H2 : member_type ?T ?X ?G ?M ?c ?A2 |- _ =>
        assert_fails (constr_eq A1 A2);
        let E := fresh "E" in
        pose proof (proj1 (member_type_functional _ _) _ _ _ _ H1 _ H2) as E; try injection E as E; subst; clear H2
    end.

(** The obligations of a global: its type is a type at [G]. *)
Ltac glob_mem_obl :=
  match goal with
  | Hs : modexp_spine ?M = (?R, nil, ?pre), Eg : glob_lookup ?R ?pre ?x = Some ?A, HG : ⊢ ?G |- _ =>
      let mq := fresh "mq" in let Hp := fresh "Hp" in let Hr := fresh "Hr" in
      let i := fresh "i" in let HA := fresh "HA" in
      destruct (glob_lookup_some _ _ _ _ _ Hs Eg) as (mq & Hp & [(? & ? & ? & Hr) | [(? & Hr & ->) | (? & ? & ? & ? & Ha & Hl & ->)]]);
      [ assert (exists i, G ⊢ A : Typeω@i) as [i HA] by (eapply wf_glob_typ; [ exact HG | exact Hr ]);
        first [ solve [ eapply nbe_order_of_typ; exact HA ]
              | split; [ eapply ati_mem_glob; eassumption | eapply level_of_nbe; eassumption ] ]
      | let D := fresh "D" in let Hc := fresh "Hc" in
        destruct (decl_of_lookup _ _ _ _ _ HG Hr) as [D Hc];
        destruct (ind_ty_typed _ _ _ _ D Hc HG) as [i HA];
        first [ solve [ eapply nbe_order_of_typ; exact HA ]
              | split; [ eapply ati_mem_glob_ind; eassumption | eapply level_of_nbe; eassumption ] ]
      | let D' := fresh "D'" in let HD' := fresh "HD'" in
        destruct (wf_ind_alias _ _ _ _ _ _ _ HG Ha) as (D' & HD' & _ & [i HA] & _);
        rewrite Hl in HD'; injection HD' as <-;
        first [ solve [ eapply nbe_order_of_typ; exact HA ]
              | split; [ eapply ati_mem_glob_ind_alias; eassumption | eapply level_of_nbe; eassumption ] ] ]
  end.

(** ** The Obligations of the Module Cases

    One tactic per kind of obligation; each obligation below names the one
    that proves it ([mod_obl] used to try them all in turn). *)
Ltac mo_1 :=
  clear_defs; destruct_conjs;
  solve [ glob_mem_obl ].

Ltac mo_2 :=
  clear_defs; destruct_conjs;
  solve [ eapply amod_glob; [ first [ reflexivity | eassumption ] | eassumption | eassumption ] ].

Ltac mo_3 :=
  clear_defs; destruct_conjs;
  solve [ match goal with Hx : _ ⊢aᵐ me_mem _ _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
              match goal with
              | HN : forall R, member_type _ _ _ (me_mem _ _) nil R -> mres_tl R = None,
                Hm : member_type _ _ _ (me_mem _ _) nil ?R0, Ht : mres_tl ?R0 = Some _ |- _ =>
                  rewrite (HN _ Hm) in Ht; discriminate Ht
              | HN : forall R, member_type _ _ _ (me_mem _ _) nil R -> mres_tl R = None,
                Hm : member_type _ _ _ _ (_ :: nil) ?R0, Ht : mres_tl ?R0 = Some _ |- _ =>
                  let Hk := fresh "Hk" in
                  assert (Hk : mres_kind R0 = mk_term -> nil <> (nil : list string))
                    by (let Hk' := fresh in intros Hk'; destruct R0; cbn in Hk', Ht; discriminate);
                  rewrite (HN _ (mt_mem _ _ _ _ _ _ _ Hk Hm)) in Ht; discriminate Ht
              end ].

Ltac mo_4 :=
  clear_defs; destruct_conjs;
  solve [ match goal with Hx : _ ⊢aᵐ _ |- False => inversion Hx; subst end; congruence ].

Ltac mo_5 :=
  clear_defs; destruct_conjs;
  solve [ eapply nbe_order_of_typ, let_mod_typ_of_alg; eassumption ].

Ltac mo_6 :=
  clear_defs; destruct_conjs;
  solve [ split; [ eapply ati_let_mod; eassumption
                     | eapply level_of_nbe; [ eapply let_mod_typ_of_alg; eassumption | eassumption ] ] ].

Ltac mo_7 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M _ (mr_term ?A) |- nbe_ty_order _ _ ?G ?A =>
                  destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?];
                  eapply nbe_order_of_typ; eassumption
              end ].

Ltac mo_8 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M _ (mr_term ?A), Hn : nbe_ty_f ?G ?A _ |- _ =>
                  destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?]
              end;
              split; [ eapply ati_mem; [ eapply spine_nil_noargs; eassumption | eassumption | eassumption | eassumption ]
                     | eapply level_of_nbe; eassumption ] ].

Ltac mo_9 :=
  clear_defs; destruct_conjs;
  solve [ split; [ eapply ati_mem_app; [ eassumption | eassumption | discriminate | eassumption ]
                     | split; [ do 2 eexists; split; eassumption | eexists; eassumption ] ] ].

Ltac mo_10 :=
  clear_defs; destruct_conjs;
  solve [ negc ].

Ltac mo_11 :=
  clear_defs; destruct_conjs;
  solve [ split; intros * [] ].

Ltac mo_12 :=
  clear_defs; destruct_conjs;
  solve [ econstructor; eassumption ].

Ltac mo_13 :=
  clear_defs; destruct_conjs;
  solve [ econstructor; eauto ].

Ltac mo_14 :=
  clear_defs; destruct_conjs;
  solve [ typ_sound ].

Ltac mo_15 :=
  clear_defs; destruct_conjs;
  solve [ ctx_wf_tac ].

Ltac mo_16 :=
  clear_defs; destruct_conjs;
  solve [ intros; match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; right; eassumption end ].

Ltac mo_17 :=
  clear_defs; destruct_conjs;
  solve [ eapply ctx_wf_gctx; ctxp ].

Ltac mo_18 :=
  clear_defs; destruct_conjs;
  solve [ eapply alg_modexp_sound; [ eassumption | ctxp ] ].

Ltac mo_19 :=
  clear_defs; destruct_conjs;
  solve [ econstructor; apply ctx_find_mod_sound; eassumption ].

Ltac mo_20 :=
  clear_defs; destruct_conjs;
  solve [ match goal with Hx : _ ⊢aᵐ me_var _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
              match goal with Hl : ctx_lookup_mod _ _ _ |- _ => apply ctx_find_mod_complete in Hl end; congruence ].

Ltac mo_21 :=
  clear_defs; destruct_conjs;
  solve [ match goal with Hx : _ ⊢aᵐ me_app _ _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
              mt_unify;
              repeat match goal with
                | H1 : mres_tl ?R = Some ?T1, H2 : mres_tl ?R = Some ?T2 |- _ =>
                    assert_fails constr_eq T1 T2; rewrite H1 in H2; injection H2; intros; subst; clear H2
                | H1 : tele_view ?T = Some _, H2 : tele_view ?T = Some _ |- _ =>
                    rewrite H1 in H2; injection H2; intros; subst; clear H2
                | H1 : tele_view ?T = Some _, H2 : tele_view ?T = None |- _ => rewrite H1 in H2; discriminate H2
                end;
              first [ contradiction | eauto ] ].

Ltac mo_22 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M nil ?R, Ht : mres_tl ?R = Some ?T,
                Hv : tele_view ?T = Some (?B, _) |- exists i, ?G ⊢ ?B : Typeω@i =>
                  let i := fresh "i" in
                  let HA := fresh "HA" in
                  let Hk := fresh "Hk" in
                  assert (Hk : mres_kind R = mk_term -> nil <> (nil : list string))
                    by (let Hk' := fresh in intros Hk'; destruct R; cbn in Hk', Ht; discriminate);
                  destruct (member_typ_of_alg _ _ _ _ HG HM Hm Hk) as [i HA];
                  rewrite (mres_ty_tl _ _ Ht) in HA;
                  exists i; exact (proj1 (proj2 (tele_view_wf _ _ _ _ _ HA Hv)))
              end ].

Ltac mo_23 :=
  clear_defs; destruct_conjs;
  solve [ eapply amod_app; eassumption ].

(** ** The Obligations of the Term Cases *)

(** An order premise: the order of a subterm, read off the order of the
    term by inversion.  The premise is an assumption at the first stage
    that has it, and only then: an inversion one stage too far would leave
    the subterm's order behind, and a reconstructed order is not a subterm
    for the guard of the checker's structural recursion.  An application
    reaches its head and its argument through [app_order], whose components
    are the orders of checks. *)
Ltac ob_ord :=
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

(** The orders of the scrutinee, the motive and a branch of an
    eliminator. *)
Ltac ob_ord_elim :=
  clear_defs;
  match goal with H : type_infer_order (a_elim _ _ _ _) |- _ => progressive_invert H end;
  first
    [ eassumption
    | match goal with
      | Hall : forall b, List.In b _ -> type_check_order (snd b), Hb : List.In ?b _ |- type_check_order (snd ?b) =>
          exact (Hall b Hb)
      end ].

(** The order of the applied root of a member of an applied module. *)
Ltac ob_ord_apps :=
  clear_defs;
  repeat match goal with H : type_infer_order (a_mem _ _) |- _ => progressive_invert H end;
  match goal with
  | H : forall R args pre, modexp_spine _ = _ -> _ -> type_infer_order _,
    Es : modexp_spine _ = (_, _ :: _, _) |- _ =>
      exact (H _ _ _ Es ltac:(discriminate))
  end.

(** A context premise. *)
Ltac ob_ctx := clear_defs; destruct_conjs; solve [ ctx_wf_tac ].

Ltac ob_ctx_ext := clear_defs; destruct_conjs; saturate_infer_univ; mauto 3.

(** A failure branch: the judgment the branch rules out is inverted against
    the failure of the premise. *)
Ltac ob_neg :=
  clear_defs;
  (** The judgment ruled out is the newest hypothesis. *)
  lazymatch goal with
  | H : ?J |- False =>
      lazymatch J with
      | _ ⊢a _ ⟹ _ => idtac
      | _ ⊢a _ ⟸ _ => idtac
      | _ => fail "ob_neg: the newest hypothesis is not a judgment:" J
      end;
      inversion H; subst; clear H
  end;
  destruct_conjs;
  functional_alg_type_infer_rewrite_clear;
  first [ contradiction | solve [ eauto 2 ] | congruence | solve [ firstorder ] ].

(** A failure branch of a member: the member's inference is inverted, and
    each rule it could come from contradicts the branch's premises. *)
Ltac ob_mem_neg :=
  clear_defs;
  lazymatch goal with H : _ ⊢a a_mem _ _ ⟹ _ |- False => inversion H; subst; clear H end;
  repeat match goal with
    | H1 : modexp_spine ?M = _, H2 : modexp_spine ?M = _ |- _ =>
        rewrite H1 in H2; injection H2; intros; subst; clear H2
    end;
  first [ contradiction
        | congruence
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ]
        | solve [ match goal with
                  | Hp : mod_qname ?M = Some _, Hr : gc_resolve _ _ _ = Some (ge_def _ _ _ _),
                    Hs : modexp_spine ?M = _, Eg : glob_lookup _ _ _ = None |- _ =>
                      eapply glob_lookup_none; [ exact Hs | exact Eg | exact Hp | exact Hr ] end ]
        | solve [ match goal with
                  | Hp : mod_qname ?M = Some _, Hl : ind_lookup _ _ _ = Some _,
                    Hs : modexp_spine ?M = _, Eg : glob_lookup _ _ _ = None |- _ =>
                      eapply glob_lookup_none_ind; [ exact Hs | exact Eg | exact Hp | exact Hl ] end ]
        | solve [ match goal with
                  | Hp : mod_qname ?M = Some _, Ha : ind_alias_lookup _ _ _ = Some _, Hl : ind_lookup _ _ _ = Some _,
                    Hs : modexp_spine ?M = _, Eg : glob_lookup _ _ _ = None |- _ =>
                      eapply glob_lookup_none_ind_alias; [ exact Hs | exact Eg | exact Hp | exact Ha | exact Hl ] end ]
        | solve [ match goal with
                  | Hp : mod_qname ?M = Some _, Hs : modexp_spine ?M = (_, _ :: _, _) |- _ =>
                      rewrite (mod_qname_spine _ _ Hp) in Hs; discriminate end ]
        | match goal with Hn : me_noargs ?M, Hs : modexp_spine ?M = _ |- _ =>
            pose proof (me_noargs_spine _ _ _ _ Hn Hs); discriminate end ].

(** The postcondition of a closed small type: it infers [Typeⁿ@0], and
    [Type@0] is a type, so it infers a universe. *)
Ltac ob_post_suniv0 :=
  clear_defs;
  match goal with HG : ⊢ ?G |- _ =>
    let HT := fresh "HT" in
    assert (HT : G ⊢ Type@0 : Typeω@0) by (apply wf_univ_large; exact HG);
    split; [ mauto 3 | ];
    destruct (alg_type_infer_large_typ_complete (user_exp_all _) HT) as (? & ? & ? & ? & _);
    split; [ do 2 eexists; split; eassumption | eexists; exact HT ]
  end.

(** The postcondition of a closed type or level form: the inference by its
    rule, and the inferred type is a type. *)
Ltac ob_post := clear_defs; split; [ mauto 3 | is_type_obl ].

(** The postcondition of a level operation: its arguments infer types of
    levels, so its rule applies. *)
Ltac ob_post_lvl :=
  clear_defs; destruct_conjs; subst;
  split; [ econstructor; eassumption |];
  split; [ do 2 eexists; split; [ apply ati_level | constructor ] | exists 0; apply wf_level_large; assumption ].

(** A closed type is a type. *)
Ltac ob_typ_closed := clear_defs; exists 0; mauto 3.

(** The subtyping order of [type_check]. *)
Ltac ob_subord :=
  clear_defs; destruct_conjs;
  match goal with
  | |- subtyping_order ?G ?A ?B =>
      enough (exists i, G ⊢ A : Typeω@i) as [? [? []]%soundness_ty];
      only 1: enough (exists j, G ⊢ B : Typeω@j) as [? [? []]%soundness_ty];
      only 1: solve [econstructor; eauto 3 using nbe_ty_order_sound];
      solve [ typ_of_infer | mauto 4 using alg_type_infer_sound ]
  end.

(** The positive case of [type_check]. *)
Ltac ob_check := clear_defs; destruct_conjs; mauto 3.

(** The obligations of a body: a failure inverts the body's judgment,
    whose prefix has one expansion ([alg_body_functional]); a success is
    the rule, past a context the soundness of the prefix makes. *)
Ltac bc_neg :=
  intros;
  repeat match goal with
    | Hb : _ ⊢aᵇ gm_ext _ _ _ ⇝ _ |- _ => inversion Hb; subst; clear Hb
    | Hb : _ ⊢aᵇ gm_open _ _ _ ⇝ _ |- _ => inversion Hb; subst; clear Hb
    | Hu : _ ⊢aᵘ gu_mk _ (md_body _) |- _ => inversion Hu; subst; clear Hu
    end;
  repeat match goal with
    | H1 : ?G ⊢aᵇ ?Φ ⇝ ?X, H2 : ?G ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
        assert_fails constr_eq X Y; pose proof (alg_body_functional H1 H2); subst Y; clear H2
    end;
  functional_alg_type_infer_rewrite_clear;
  first [ contradiction
        | solve [ firstorder ]
        | match goal with
          | HN : forall R, member_type _ _ _ ?M ?c R -> mres_tl R = None, Hm : member_type _ _ _ ?M ?c ?R0,
            Ht : mres_tl ?R0 = Some _ |- _ => rewrite (HN _ Hm) in Ht; discriminate Ht
          end
        | match goal with H : forall u : unf, ?X <> univ_nf u |- _ => exact (H _ eq_refl) end ].

Ltac bc_obl1 :=
  first [ solve [ bc_neg ]
        | solve [ split; [ constructor | cbn; assumption ] ]
        | solve [ split; [ econstructor; eassumption | first [ ctx_wf_tac | eapply alg_body_ctx; [ eassumption | econstructor; eassumption ] ] ] ]
        | solve [ ob_check ]
        | assumption
        | solve [ ctx_wf_tac ]
        | solve [ eapply ctx_wf_gctx; ctxp ]
        | solve [ eapply alg_modexp_sound; [ eassumption | ctxp ] ]
        | solve [ typ_sound ] ].

Ltac bc_obl :=
  first [ ob_ord | clear_defs; intros; destruct_conjs; bc_obl1 ].


(** A small universe: its level infers a type of levels, so the universe
    above is a type, whose normal form is the inferred universe. *)
Ltac ob_suniv_lvl :=
  destruct_conjs; subst;
  match goal with HM : ?G ⊢a ?M ⟹ Levelⁿ@?k, HG : ⊢ ?G |- _ =>
    assert (G ⊢ M : Level@k) by (exact (alg_type_infer_sound HM HG));
    assert (G ⊢ Type⟨succl M⟩ : Typeω@0)
      by (eapply wf_univ_large_tm; [ exact HG | eapply wf_succl; eassumption ])
  end.

Ltac ob_suniv_nbe := clear_defs; ob_suniv_lvl; eapply nbe_order_of_typ; eassumption.

Ltac ob_suniv_post :=
  clear_defs; ob_suniv_lvl;
  split; [ eapply ati_suniv; eassumption | eapply level_of_nbe; eassumption ].
