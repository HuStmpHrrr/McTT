From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Syntactic.System Require Import MemberWf.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import Evaluation NbE PseudoMonadic Subtyping MemberType.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
Context {GC : GCtx}.

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
    destruct A as [ i | c xs | | ? ? | | | ? | | | | ? ? | ? ? | ? ];
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

  Extraction Inline univ_nf_idx_dec get_subterms_of_pi_nf.

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
    intros [b pv A [M |] | pm U] [b' pv' A' [M' |] | pm' U']; cbn; try (right; intros []; fail); try (left; exact I).
    - destruct b, b', (Bool.bool_dec pv pv'); try (right; intuition congruence; fail); left; auto.
    - exact (Bool.bool_dec pm pm').
  Defined.

  Definition body_shape_dec : forall Φ Φ', { body_shape Φ Φ' } + { ~ body_shape Φ Φ' }.
  Proof.
    induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c']; cbn;
      try (left; exact I); try (right; intros []; fail).
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (string_dec x x') as [H2 | H2]; [| right; intuition ].
      destruct (entry_shape_dec E E') as [H3 | H3]; [ left; auto | right; intuition ].
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
    destruct d as [[[A | T] HR] | HN]; [ left; exists A; exact HR | right | right; intros A HA; exact (HN _ HA) ].
    intros A HA; pose proof (proj1 (member_type_functional _ _) _ _ _ _ HR _ HA); discriminate.
  Defined.

  Definition mres_mod_dec {Γ H ch}
      (d : { R | member_type gc_deps gc_stack Γ H ch R } + { forall R, ~ member_type gc_deps gc_stack Γ H ch R }) :
      { T | member_type gc_deps gc_stack Γ H ch (mr_mod T) } +
      { forall T, ~ member_type gc_deps gc_stack Γ H ch (mr_mod T) }.
  Proof.
    destruct d as [[[A | T] HR] | HN]; [ right | left; exists T; exact HR | right; intros T HT; exact (HN _ HT) ].
    intros T HT; pose proof (proj1 (member_type_functional _ _) _ _ _ _ HR _ HT); discriminate.
  Defined.

  Definition member_term_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H ch (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :=
    mres_term_dec (member_type_dec Hg Γ H ch HH).

  Definition member_mod_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H ch (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :=
    mres_mod_dec (member_type_dec Hg Γ H ch HH).

  (** A chain from a unit has an order whether or not it is a module. *)
  Definition member_chain_mod_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H mq (Hp : mod_qname H = Some mq) :
      { T | member_type gc_deps gc_stack Γ H nil (mr_mod T) } +
      { forall T, ~ member_type gc_deps gc_stack Γ H nil (mr_mod T) } :=
    mres_mod_dec (member_type_impl gc_deps gc_stack (gctx_closed_of_wf _ _ Hg) Γ H nil
                    (mt_order_chain_self _ _ _ _ _ Hg Hp nil)).

  (** The outermost parameter of an arity, if any. *)
  Equations tele_view_dec (T : ctx) : { B : typ & { T1 : ctx | tele_view T = Some (B, T1) } } + { tele_view T = None } :=
  tele_view_dec T with inspect (tele_view T) := {
    | exist _ (Some (B, T1)) E => inleft (existT _ B (exist _ T1 E))
    | exist _ None E => inright E }.

  Extraction Inline member_type_dec member_term_dec member_mod_dec member_chain_mod_dec mres_term_dec mres_mod_dec tele_view_dec.

  (** ** Facts the Obligations Use *)


  Lemma nbe_order_of_typ : forall G X i, G ⊢ X : Type@i -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * HX; destruct (soundness_ty HX) as [W [HW _]]; eauto using nbe_ty_order_sound. Qed.

  (** The normal form of a type is a type, both algorithmically and
      declaratively: the two halves of [type_infer]'s postcondition. *)
  Lemma level_of_nbe : forall G X i D,
      G ⊢ X : Type@i ->
      nbe_ty_f G X D ->
      (exists UD u, G ⊢a D ⟹ UD /\ is_univ_nf UD u) /\ (exists j, G ⊢ D : Type@j).
  Proof.
    intros * HX HD.
    assert (G ⊢ X ≈ D : Type@i) by (eapply soundness_ty'; eassumption).
    assert (G ⊢ D : Type@i) by (gen_presups; eassumption).
    destruct (alg_type_infer_typ_complete (user_exp_nf D) ltac:(eassumption)) as [UD [u [? []]]].
    split; [ exists UD, u; split; assumption | exists i; assumption ].
  Qed.

  Lemma member_typ_of_alg : forall G M ch R, ⊢ G -> G ⊢aᵐ M ->
      member_type gc_deps gc_stack G M ch R -> (mres_kind R = mk_term -> ch <> nil) -> exists i, G ⊢ mres_ty R : Type@i.
  Proof.
    intros * HG HM Hm Hch.
    exact (proj1 (proj1 member_wf _ _ _ _ Hm (alg_modexp_sound HM HG) Hch)).
  Qed.

  (** The universe is lifted to the large one of its tier before the
      substitution: a small universe's level may mention the module. *)
  Lemma let_mod_typ_of_alg : forall G U C (u : unf), ⊢ G -> G ⊢aᵘ U -> G ▹ₘ U ⊢a C ⟹ univ_nf u ->
      G ⊢ C[Id ,,ₘ me_lit U] : Type@(unf_large u).
  Proof.
    intros * HG HU HC.
    pose proof (alg_unit_sound HU HG) as HU'.
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU').
    assert (HCt : G ▹ₘ U ⊢ C : unf_tm u)
      by (rewrite <- nf_to_exp_univ_nf; eapply alg_type_infer_sound; eassumption).
    apply wf_exp_unf_large in HCt.
    exact (sub_preserves_exp _ _ _ _ _ _ _ HCt (wf_sub_single_mod _ _ _ _ HU')).
  Qed.

  (** A member of a chain from a unit, read off the global context: the type
      of the global, if it is one. *)
  Definition glob_lookup (R : modexp) (pre : list string) (x : string) : option typ :=
    match R with
    | me_unit fp =>
        match gc_resolve gc_deps gc_stack (q_abs fp (pre ++ x :: nil)) with
        | Some (ge_def _ _ A _) => Some A
        | _ => None
        end
    | _ => None
    end.

  Lemma spine_unit_path : forall H fp pre, modexp_spine H = (me_unit fp, nil, pre) -> mod_qname H = Some (q_abs fp pre).
  Proof.
    induction H as [fp0 | x | H IH y | H IH N | U]; intros * Hs; cbn in Hs |- *; try discriminate.
    - injection Hs as <- <-; reflexivity.
    - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as -> -> <-.
      rewrite (IH _ _ eq_refl); reflexivity.
    - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as _ Ha _; destruct a0; discriminate.
  Qed.

  Lemma glob_lookup_some : forall H R pre x A, modexp_spine H = (R, nil, pre) -> glob_lookup R pre x = Some A ->
      exists mq b pv B, mod_qname H = Some mq /\ gc_resolve gc_deps gc_stack (qname_app mq (x :: nil)) = Some (ge_def b pv A B).
  Proof.
    intros * Hs Hg; destruct R; cbn in Hg; try discriminate.
    destruct (gc_resolve _ _ _) as [[b pv A0 B | pm U] |] eqn:Er; try discriminate; injection Hg as ->.
    exists (q_abs l pre), b, pv, B; split; [ exact (spine_unit_path _ _ _ Hs) | exact Er ].
  Qed.

  Lemma glob_lookup_none : forall H R args pre x mq b pv A B, modexp_spine H = (R, args, pre) -> glob_lookup R pre x = None ->
      mod_qname H = Some mq -> gc_resolve gc_deps gc_stack (qname_app mq (x :: nil)) = Some (ge_def b pv A B) -> False.
  Proof.
    intros * Hs Hg Hp Hr; rewrite (mod_qname_spine _ _ Hp) in Hs; injection Hs as <- <- <-.
    cbn in Hg; change (qname_app mq (x :: nil)) with (q_abs (q_unit mq) (q_chain mq ++ x :: nil)) in Hr.
    rewrite Hr in Hg; discriminate.
  Qed.

  Inductive type_check_order : exp -> Prop :=
  | tc_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order : exp -> Prop :=
  | ti_typ : forall {i}, type_infer_order Type@i
  | ti_suniv : forall {M}, type_check_order M -> type_infer_order Typeˢ⟨M⟩
  | ti_level : type_infer_order Level
  | ti_llit : forall {n}, type_infer_order 𝕃@n
  | ti_succl : forall {M}, type_check_order M -> type_infer_order (succl M)
  | ti_maxl : forall {M N}, type_check_order M -> type_check_order N -> type_infer_order (maxl M N)
  | ti_nat : type_infer_order ℕ
  | ti_zero : type_infer_order zero
  | ti_succ : forall {M}, type_check_order M -> type_infer_order succ M
  | ti_natrec : forall {A MZ MS M}, type_check_order M -> type_infer_order A -> type_check_order MZ -> type_check_order MS -> type_infer_order rec M return A | zero -> MZ | succ -> MS end
  | ti_True : type_infer_order ⊤
  | ti_true : type_infer_order ⋆
  | ti_False : type_infer_order ⊥
  | ti_exfalso : forall {A M}, type_check_order M -> type_infer_order A -> type_infer_order (efq M return A)
  | ti_pi : forall {A B}, type_infer_order A -> type_infer_order B -> type_infer_order Π A B
  | ti_fn : forall {A M}, type_infer_order A -> type_infer_order M -> type_infer_order λ A M
  | ti_app : forall {M N}, type_infer_order M -> type_check_order N -> type_infer_order (M $ N)
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
  with ext_order : ctx -> Prop :=
  | eo_nil : ext_order nil
  | eo_ass : forall {A Ψ}, ext_order Ψ -> type_infer_order A -> ext_order (Ψ ▹ A)
  | eo_def : forall {A M Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> ext_order (Ψ ▸ A ≔ M)
  | eo_mod : forall {U Ψ}, ext_order Ψ -> unit_order U -> ext_order (Ψ ▹ₘ U)
  with unit_order : gunit -> Prop :=
  | uo_body : forall {Δ Φ}, ext_order (body_ctx Φ ++ Δ) -> unit_order (gu_body Δ Φ)
  | uo_alias : forall {Δ E}, ext_order Δ -> modexp_order E -> unit_order (gu_mk Δ (md_alias E))
  with modexp_order : modexp -> Prop :=
  | mo_unit : forall {fp}, modexp_order (me_unit fp)
  | mo_var : forall {x}, modexp_order (me_var x)
  | mo_lit : forall {U}, unit_order U -> modexp_order (me_lit U)
  | mo_mem : forall {H y}, modexp_order H -> modexp_order (me_mem H y)
  | mo_app : forall {H N}, modexp_order H -> type_check_order N -> modexp_order (me_app H N)
  .

  #[local]
  Hint Constructors type_check_order type_infer_order ext_order unit_order modexp_order : mctt.

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
    inversion Hargs; subst; apply IH; [ constructor |]; assumption.
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
           | md_body Φ => List.Forall centry_order (body_ctx Φ)
           | md_alias E => modexp_order E
           end) /\
    (forall Φ, List.Forall centry_order (body_ctx Φ)) /\
    (forall E, match E with
           | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
           | ge_mod _ U => unit_order U
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
             | md_body Φ => List.Forall centry_order (body_ctx Φ)
             | md_alias E => modexp_order E
             end)
      (fun Φ => List.Forall centry_order (body_ctx Φ))
      (fun E => match E with
             | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
             | ge_mod _ U => unit_order U
             end)
      centry_order); intros; cbn in *; destruct_conjs; eauto 6 with mctt.
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
    - destruct D; destruct_conjs; constructor; auto using ext_order_of_forall, ext_order_app.
    - destruct E as [b pv A [M |] | pm U]; destruct_conjs; constructor; cbn; eauto with mctt.
    - apply Forall_app; split; [| assumption ].
      induction (List.length its); cbn; constructor; [ constructor | assumption ].
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

  #[local]
  Ltac clear_defs :=
    repeat lazymatch goal with
      | H: (forall (G : ctx) (A : typ),
               (exists i : nat, G ⊢ A : Type@i) ->
               forall M : typ,
                 type_check_order M ->
                 ({ G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A }))
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall (G : ctx) (A : typ),
              (exists i : nat, G ⊢ A : Type@i) -> forall M : typ, type_check_order M -> { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A })
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall G : ctx,
              ⊢ G ->
              forall M : typ,
                type_infer_order M ->
                ({ B : nf | G ⊢a M ⟹ B /\
                    (exists UA u, G ⊢a (nf_to_exp B) ⟹ UA /\ is_univ_nf UA u) /\
                    (exists i : nat, G ⊢ (nf_to_exp B) : Type@i) } + { forall C : nf, ~ G ⊢a M ⟹ C }))
        |- _ =>
          clear H
      | H: (forall G : ctx,
               ⊢ G ->
               forall M : typ,
                 type_infer_order M ->
                 ({ B : nf | G ⊢a M ⟹ B /\
                     (exists UA u, G ⊢a (nf_to_exp B) ⟹ UA /\ is_univ_nf UA u) /\
                     (exists i : nat, G ⊢ (nf_to_exp B) : Type@i) } + { forall C : nf, ~ G ⊢a M ⟹ C }))
        |- _ =>
          clear H
    end.

  (** A context the checker extends is well formed by the soundness of the
      check of the extension. *)
  #[local]
  Ltac ctx_wf_tac :=
    match goal with
    | |- ⊢ ?G => assumption
    | |- ⊢ ?G ▹ ?A =>
        match goal with Ha : G ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
          assert (G ⊢ A : unf_tm u)
            by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
                eapply alg_type_infer_sound; eassumption);
          assert (G ⊢ A : Type@(unf_large u))
            by (apply wf_exp_unf_large; eassumption);
          mauto 2 end
    | |- ⊢ ?G ▸ ?A ≔ ?M =>
        match goal with Ha : G ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA ?u, H' : G ⊢a M ⟸ A |- _ =>
          assert (G ⊢ A : unf_tm u)
            by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
                eapply alg_type_infer_sound; eassumption);
          assert (G ⊢ A : Type@(unf_large u))
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
  #[local]
  Ltac is_type_obl :=
    split; [ do 2 eexists; split; [ mauto 3 | constructor ] | eexists; mauto 3 ].

  (** The universe a [Π] infers is a type: a large universe, or a small one at
      a literal level. *)
  Lemma wf_unf_max_tm : forall G (u v : unf),
      ⊢ G ->
      exists j, G ⊢ unf_tm (unf_max u v) : Type@j.
  Proof.
    intros * HG.
    destruct u as [[c []] | i], v as [[d []] | j]; cbn [unf_max unf_tm fst snd lvl_lit la_to_list lvl_exp_of];
      first [ exists 0; apply wf_univ_large; assumption | eexists; apply wf_typ; assumption ].
  Qed.

  (** The same when the inferred type is itself the join of two universes: it
      is a type, so it infers a universe. *)
  #[local]
  Tactic Notation "univ_is_type_obl" constr(u) constr(v) :=
    let j := fresh "j" in
    let Hj := fresh "Hj" in
    destruct (wf_unf_max_tm _ u v ltac:(eassumption)) as [j Hj];
    rewrite nf_to_exp_univ_nf; split;
      [ destruct (alg_type_infer_typ_complete (user_exp_all _) Hj) as [? [? [? [? _]]]];
        do 2 eexists; split; eassumption
      | eexists; exact Hj ].

  (** The subject of a universe premise, as a typing at the large level the
      index of its side condition lives at: that is the form the obligations
      need.  [is_univ_nf_eq] turns the side condition into the shape of the
      inferred normal form. *)
  #[local]
  Ltac saturate_infer_univ :=
    repeat match goal with
      | Ha : ?G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA ?u |- _ =>
          let T := constr:(wf_exp gc_deps gc_stack G (a_typ (unf_large u)) A) in
          assert_fails (assert T by assumption);
          assert (wf_exp gc_deps gc_stack G (unf_tm u) A)
            by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
                eapply alg_type_infer_sound; [ exact Ha | ctx_wf_tac ]);
          assert T by (apply wf_exp_unf_large; eassumption)
      end.

  (** A type whose inferred universe is [univ_nf u] is a type of [unf_tm u],
      and so of the large universe [Type@(unf_large u)] the index lives at. *)
  #[local]
  Ltac typ_of_infer := saturate_infer_univ.

  (** ** Obligations of the Module Cases *)

  #[local]
  Ltac negc :=
    match goal with
    | Hx : _ ⊢aˣ (_ :: _) |- False => inversion Hx; subst
    | Hx : _ ⊢aᵘ (gu_mk _ _) |- False => inversion Hx; subst
    | Hx : _ ⊢aᵐ (_ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
    | Hx : _ ⊢aᵐ (_ _ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
    end;
    functional_alg_type_infer_rewrite_clear;
    first [ match goal with H : forall u : unf, ?X <> univ_nf u |- _ => exact (H _ eq_refl) end | firstorder ].

  #[local]
  Ltac typ_sound :=
    match goal with
    | |- exists i, ?G ⊢ ?A : Type@i =>
        saturate_infer_univ;
        match goal with H : wf_exp gc_deps gc_stack G (a_typ ?k) A |- _ => exists k; exact H end
    end.

  #[local]
  Ltac ctxp :=
    first [ assumption
          | ctx_wf_tac
          | match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; left; reflexivity end ].

  #[local]
  Ltac mt_unify :=
    repeat match goal with
      | H1 : member_type ?T ?X ?G ?M ?c ?A1, H2 : member_type ?T ?X ?G ?M ?c ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          let E := fresh "E" in
          pose proof (proj1 (member_type_functional _ _) _ _ _ _ H1 _ H2) as E; try injection E as E; subst; clear H2
      end.

  (** The obligations of a global: its type is a type at [G]. *)
  #[local]
  Ltac glob_mem_obl :=
    match goal with
    | Hs : modexp_spine ?M = (?R, nil, ?pre), Eg : glob_lookup ?R ?pre ?x = Some ?A, HG : ⊢ ?G |- _ =>
        let mq := fresh "mq" in let Hp := fresh "Hp" in let Hr := fresh "Hr" in
        let i := fresh "i" in let HA := fresh "HA" in
        destruct (glob_lookup_some _ _ _ _ _ Hs Eg) as (mq & ? & ? & ? & Hp & Hr);
        assert (exists i, G ⊢ A : Type@i) as [i HA] by (eapply wf_glob_typ; [ exact HG | exact Hr ]);
        first [ solve [ eapply nbe_order_of_typ; exact HA ]
              | split; [ eapply ati_mem_glob; eassumption | eapply level_of_nbe; eassumption ] ]
    end.

  (** ** The Obligations of the Module Cases

      One tactic per kind of obligation; each obligation below names the one
      that proves it ([mod_obl] used to try them all in turn). *)
  #[local]
  Ltac mo_1 :=
    clear_defs; destruct_conjs;
    solve [ glob_mem_obl ].

  #[local]
  Ltac mo_2 :=
    clear_defs; destruct_conjs;
    solve [ eapply amod_glob; [ first [ reflexivity | eassumption ] | eassumption ] ].

  #[local]
  Ltac mo_3 :=
    clear_defs; destruct_conjs;
    solve [ match goal with Hx : _ ⊢aᵐ me_mem _ _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
                match goal with HN : forall T, ~ member_type _ _ _ (me_mem _ _) nil (mr_mod T) |- _ =>
                  first [ eapply HN; eassumption | eapply HN; eapply mt_mem; [ discriminate | eassumption ] ] end ].

  #[local]
  Ltac mo_4 :=
    clear_defs; destruct_conjs;
    solve [ match goal with Hx : _ ⊢aᵐ _ |- False => inversion Hx; subst end; congruence ].

  #[local]
  Ltac mo_5 :=
    clear_defs; destruct_conjs;
    solve [ eapply nbe_order_of_typ, let_mod_typ_of_alg; eassumption ].

  #[local]
  Ltac mo_6 :=
    clear_defs; destruct_conjs;
    solve [ split; [ eapply ati_let_mod; eassumption
                       | eapply level_of_nbe; [ eapply let_mod_typ_of_alg; eassumption | eassumption ] ] ].

  #[local]
  Ltac mo_7 :=
    clear_defs; destruct_conjs;
    solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M _ (mr_term ?A) |- nbe_ty_order _ _ ?G ?A =>
                    destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?];
                    eapply nbe_order_of_typ; eassumption
                end ].

  #[local]
  Ltac mo_8 :=
    clear_defs; destruct_conjs;
    solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M _ (mr_term ?A), Hn : nbe_ty_f ?G ?A _ |- _ =>
                    destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?]
                end;
                split; [ eapply ati_mem; [ eapply spine_nil_noargs; eassumption | eassumption | eassumption | eassumption ]
                       | eapply level_of_nbe; eassumption ] ].

  #[local]
  Ltac mo_9 :=
    clear_defs; destruct_conjs;
    solve [ split; [ eapply ati_mem_app; [ eassumption | eassumption | discriminate | eassumption ]
                       | split; [ do 2 eexists; split; eassumption | eexists; eassumption ] ] ].

  #[local]
  Ltac mo_10 :=
    clear_defs; destruct_conjs;
    solve [ negc ].

  #[local]
  Ltac mo_11 :=
    clear_defs; destruct_conjs;
    solve [ split; intros * [] ].

  #[local]
  Ltac mo_12 :=
    clear_defs; destruct_conjs;
    solve [ econstructor; eassumption ].

  #[local]
  Ltac mo_13 :=
    clear_defs; destruct_conjs;
    solve [ econstructor; eauto ].

  #[local]
  Ltac mo_14 :=
    clear_defs; destruct_conjs;
    solve [ typ_sound ].

  #[local]
  Ltac mo_15 :=
    clear_defs; destruct_conjs;
    solve [ ctx_wf_tac ].

  #[local]
  Ltac mo_16 :=
    clear_defs; destruct_conjs;
    solve [ intros; match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; right; eassumption end ].

  #[local]
  Ltac mo_17 :=
    clear_defs; destruct_conjs;
    solve [ eapply ctx_wf_gctx; ctxp ].

  #[local]
  Ltac mo_18 :=
    clear_defs; destruct_conjs;
    solve [ eapply alg_modexp_sound; [ eassumption | ctxp ] ].

  #[local]
  Ltac mo_19 :=
    clear_defs; destruct_conjs;
    solve [ econstructor; apply ctx_find_mod_sound; eassumption ].

  #[local]
  Ltac mo_20 :=
    clear_defs; destruct_conjs;
    solve [ match goal with Hx : _ ⊢aᵐ me_var _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
                match goal with Hl : ctx_lookup_mod _ _ _ |- _ => apply ctx_find_mod_complete in Hl end; congruence ].

  #[local]
  Ltac mo_21 :=
    clear_defs; destruct_conjs;
    solve [ match goal with Hx : _ ⊢aᵐ me_app _ _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
                mt_unify;
                repeat match goal with
                  | H1 : tele_view ?T = Some _, H2 : tele_view ?T = Some _ |- _ =>
                      rewrite H1 in H2; injection H2; intros; subst; clear H2
                  | H1 : tele_view ?T = Some _, H2 : tele_view ?T = None |- _ => rewrite H1 in H2; discriminate H2
                  end;
                first [ contradiction | eauto ] ].

  #[local]
  Ltac mo_22 :=
    clear_defs; destruct_conjs;
    solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M nil (mr_mod ?T),
                  Hv : tele_view ?T = Some (?B, _) |- exists i, ?G ⊢ ?B : Type@i =>
                    let i := fresh "i" in
                    let HA := fresh "HA" in
                    destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [i HA];
                    cbn [mres_ty] in HA;
                    exists i; exact (proj1 (proj2 (tele_view_wf _ _ _ _ _ HA Hv)))
                end ].

  #[local]
  Ltac mo_23 :=
    clear_defs; destruct_conjs;
    solve [ eapply amod_app; eassumption ].

  (** ** The Obligations of the Term Cases *)

  (** An order premise: the order of a subterm, read off the order of the
      term by inversion. *)
  #[local]
  Ltac ob_ord :=
    clear_defs;
    try match goal with H : type_check_order _ |- _ => progressive_invert H end;
    repeat match goal with
      | H : type_infer_order _ |- _ => progressive_invert H
      | H : ext_order _ |- _ => progressive_invert H
      | H : unit_order _ |- _ => progressive_invert H
      | H : modexp_order _ |- _ => progressive_invert H
      end;
    eassumption.

  (** The order of the applied root of a member of an applied module. *)
  #[local]
  Ltac ob_ord_apps :=
    clear_defs;
    repeat match goal with H : type_infer_order (a_mem _ _) |- _ => progressive_invert H end;
    match goal with
    | H : forall R args pre, modexp_spine _ = _ -> _ -> type_infer_order _,
      Es : modexp_spine _ = (_, _ :: _, _) |- _ =>
        exact (H _ _ _ Es ltac:(discriminate))
    end.

  (** A context premise. *)
  #[local]
  Ltac ob_ctx := clear_defs; destruct_conjs; solve [ ctx_wf_tac ].

  #[local]
  Ltac ob_ctx_ext := clear_defs; destruct_conjs; saturate_infer_univ; mauto 3.

  (** A failure branch: the judgment the branch rules out is inverted against
      the failure of the premise. *)
  #[local]
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
  #[local]
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
                    | Hp : mod_qname ?M = Some _, Hs : modexp_spine ?M = (_, _ :: _, _) |- _ =>
                        rewrite (mod_qname_spine _ _ Hp) in Hs; discriminate end ]
          | match goal with Hn : me_noargs ?M, Hs : modexp_spine ?M = _ |- _ =>
              pose proof (me_noargs_spine _ _ _ _ Hn Hs); discriminate end ].

  (** The postcondition of a closed small type: it infers [Typeˢⁿ@0], and
      [Typeˢ@0] is a type, so it infers a universe. *)
  #[local]
  Ltac ob_post_suniv0 :=
    clear_defs;
    match goal with HG : ⊢ ?G |- _ =>
      let HT := fresh "HT" in
      assert (HT : G ⊢ Typeˢ@0 : Type@0) by (apply wf_univ_large; exact HG);
      split; [ mauto 3 | ];
      destruct (alg_type_infer_typ_complete (user_exp_all _) HT) as (? & ? & ? & ? & _);
      split; [ do 2 eexists; split; eassumption | eexists; exact HT ]
    end.

  (** The postcondition of a closed type or level form: the inference by its
      rule, and the inferred type is a type. *)
  #[local]
  Ltac ob_post := clear_defs; split; [ mauto 3 | is_type_obl ].

  (** A closed type is a type. *)
  #[local]
  Ltac ob_typ_closed := clear_defs; exists 0; mauto 3.

  (** The subtyping order of [type_check]. *)
  #[local]
  Ltac ob_subord :=
    clear_defs; destruct_conjs;
    match goal with
    | |- subtyping_order ?G ?A ?B =>
        enough (exists i, G ⊢ A : Type@i) as [? [? []]%soundness_ty];
        only 1: enough (exists j, G ⊢ B : Type@j) as [? [? []]%soundness_ty];
        only 1: solve [econstructor; eauto 3 using nbe_ty_order_sound];
        solve [ typ_of_infer | mauto 4 using alg_type_infer_sound ]
    end.

  (** The positive case of [type_check]. *)
  #[local]
  Ltac ob_check := clear_defs; destruct_conjs; mauto 3.

  (** A small universe: its level is a level, so the universe above is a type,
      whose normal form is the inferred universe. *)
  #[local]
  Ltac ob_suniv_lvl :=
    match goal with HM : ?G ⊢a ?M ⟸ Level, HG : ⊢ ?G |- _ =>
      assert (G ⊢ M : Level)
        by (eapply alg_type_check_sound; [ exact HM | exact HG | exact (wf_level_large (i := 0) HG) ]);
      assert (G ⊢ Typeˢ⟨succl M⟩ : Type@0) by (apply wf_univ_large_tm; mauto 3)
    end.

  #[local]
  Ltac ob_suniv_nbe := clear_defs; ob_suniv_lvl; eapply nbe_order_of_typ; eassumption.

  #[local]
  Ltac ob_suniv_post :=
    clear_defs; ob_suniv_lvl;
    split; [ eapply ati_suniv; eassumption | eapply level_of_nbe; eassumption ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations type_check G A (HA : (exists i, G ⊢ A : Type@i)) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, M, H =>
      let*o->b (exist _ B _) := type_infer G _ M _ while _ in
      let*b _ := subtyping_impl G (B : nf) A _ while _ in
      pureb _
  with type_infer G (HG : ⊢ G) M (H : type_infer_order M) : { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Type@i) } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, M, H with M => {
    | Type@j =>
        pureo (exist _ Typeⁿ@(S j) _)
    | Typeˢ⟨M'⟩ =>
        let*b->o _ := type_check G Level _ M' _ while _ in
        let (W, _) := nbe_ty_impl gc_deps gc_stack G Typeˢ⟨succl M'⟩ _ in
        pureo (exist _ W _)
    | Level =>
        pureo (exist _ Typeˢⁿ@0 _)
    | 𝕃@m =>
        pureo (exist _ Levelⁿ _)
    | succl M' =>
        let*b->o _ := type_check G Level _ M' _ while _ in
        pureo (exist _ Levelⁿ _)
    | maxl M' N' =>
        let*b->o _ := type_check G Level _ M' _ while _ in
        let*b->o _ := type_check G Level _ N' _ while _ in
        pureo (exist _ Levelⁿ _)
    | ℕ =>
        pureo (exist _ Typeˢⁿ@0 _)
    | zero =>
        pureo (exist _ ℕⁿ _)
    | succ M' =>
        let*b->o _ := type_check G ℕ _ M' _ while _ in
        pureo (exist _ ℕⁿ _)
    | rec M' return A' | zero -> MZ | succ -> MS end =>
        let*b->o _ := type_check G ℕ _ M' _ while _ in
        let*o (exist _ UA' _) := type_infer (G ▹ ℕ) _ A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check G A'[Id,,zero] _ MZ _ while _ in
        let*b->o _ := type_check (G ▹ ℕ ▹ A') A'[Wk ⨟ Wk,,succ #1] _ MS _ while _ in
        let (A'', _) := nbe_ty_impl gc_deps gc_stack G A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | ⊤ =>
        pureo (exist _ Typeˢⁿ@0 _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Typeˢⁿ@0 _)
    | efq M' return A' =>
        let*b->o _ := type_check G ⊥ _ M' _ while _ in
        let*o (exist _ UA' _) := type_infer (G ▹ ⊥) _ A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let (A'', _) := nbe_ty_impl gc_deps gc_stack G A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | Π B C =>
        let*o (exist _ UB _) := type_infer G _ B _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UB while _ in
        let*o (exist _ UC _) := type_infer (G ▹ B) _ C _ while _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC while _ in
        pureo (exist _ (univ_nf (unf_max u v)) _)
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*o (exist _ B' _) := type_infer (G ▹ A') _ M' _ while _ in
        let (A'', _) := nbe_ty_impl gc_deps gc_stack G A' _ in
        pureo (exist _ (Πⁿ A'' B') _)
    | M' $ N' =>
        let*o (exist _ C _) := type_infer G _ M' _ while _ in
        let*o (existT _ A (exist _ B _)) := get_subterms_of_pi_nf C while _ in
        let*b->o _ := type_check G (A : nf) _ N' _ while _ in
        let (B', _) := nbe_ty_impl gc_deps gc_stack G (B : nf)[Id,,N'] _ in
        pureo (exist _ B' _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check G A' _ M' _ while _ in
        let*o (exist _ C _) := type_infer (G ▸ A' ≔ M') _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_deps gc_stack G (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer G _ M' _ while _ in
        let*o (exist _ C _) := type_infer (G ▸ (A : nf) ≔ M') _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_deps gc_stack G (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let*o (exist _ C _) := type_infer (G ▹ₘ U) _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_deps gc_stack G (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    (** A global infers the closed type that resolution returns for it,
        normalized at [G]; any other member, through its module. *)
    | a_mem M' x with inspect (modexp_spine M') => {
      | exist _ (R, nil, pre) Es with inspect (glob_lookup R pre x) => {
        | exist _ (Some A) Eg =>
            let (C, _) := nbe_ty_impl gc_deps gc_stack G A _ in
            pureo (exist _ C _)
        | exist _ None Eg =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := member_term_dec _ G M' (x :: nil) _ while _ in
          let (B, _) := nbe_ty_impl gc_deps gc_stack G A _ in
          pureo (exist _ B _) }
      | exist _ (R, N :: args, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := type_infer G HG (apps (member_ref R (pre ++ x :: nil)) (N :: args)) _ while _ in
          pureo (exist _ A _) }
    | #x =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let (A', _) := nbe_ty_impl gc_deps gc_stack G A _ in
        pureo (exist _ A' _)
    }
  with ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*o->b (exist _ UA _) := type_infer (Ψ ++ G) _ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*o->b (exist _ UA _) := type_infer (Ψ ++ G) _ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check (Ψ ++ G) A _ M _ while _ in
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
      let*b _ := type_check G B _ N _ while _ in
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
  Obligation 7. (* G ⊢a Type@j ⟹ Typeⁿ@(S j) /\ (exists (UA : nf) (u : unf),... *) ob_post. Qed.
  Obligation 8. (* exists i : nat, G ⊢ Level : Type@i *) ob_typ_closed. Qed.
  Obligation 9. (* type_check_order M' *) ob_ord. Defined.
  Obligation 10. (* False *) ob_neg. Qed.
  Obligation 11. (* nbe_ty_order gc_deps gc_stack G Typeˢ⟨succl M'⟩ *) ob_suniv_nbe. Qed.
  Obligation 12. (* G ⊢a Typeˢ⟨M'⟩ ⟹ W /\ (exists (UA : nf) (u : unf), G ⊢a W... *) ob_suniv_post. Qed.
  Obligation 13. (* G ⊢a Level ⟹ Typeˢⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢... *) ob_post_suniv0. Qed.
  Obligation 14. (* G ⊢a 𝕃@m ⟹ Levelⁿ /\ (exists (UA : nf) (u : unf), G ⊢a Le... *) ob_post. Qed.
  Obligation 15. (* exists i : nat, G ⊢ Level : Type@i *) ob_typ_closed. Qed.
  Obligation 16. (* type_check_order M' *) ob_ord. Defined.
  Obligation 17. (* False *) ob_neg. Qed.
  Obligation 18. (* G ⊢a succl M' ⟹ Levelⁿ /\ (exists (UA : nf) (u : unf), G ... *) ob_post. Qed.
  Obligation 19. (* exists i : nat, G ⊢ Level : Type@i *) ob_typ_closed. Qed.
  Obligation 20. (* type_check_order M' *) ob_ord. Defined.
  Obligation 21. (* False *) ob_neg. Qed.
  Obligation 22. (* exists i : nat, G ⊢ Level : Type@i *) ob_typ_closed. Qed.
  Obligation 23. (* type_check_order N' *) ob_ord. Defined.
  Obligation 24. (* False *) ob_neg. Qed.
  Obligation 25. (* G ⊢a maxl M' N' ⟹ Levelⁿ /\ (exists (UA : nf) (u : unf), ... *) ob_post. Qed.
  Obligation 26. (* G ⊢a ℕ ⟹ Typeˢⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 27. (* G ⊢a zero ⟹ ℕⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ℕ ⟹ U... *) ob_post. Qed.
  Obligation 28. (* exists i : nat, G ⊢ ℕ : Type@i *) ob_typ_closed. Qed.
  Obligation 29. (* type_check_order M' *) ob_ord. Defined.
  Obligation 30. (* False *) ob_neg. Qed.
  Obligation 31. (* G ⊢a succ M' ⟹ ℕⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ℕ ... *) ob_post. Qed.
  Obligation 32. (* exists i : nat, G ⊢ ℕ : Type@i *) ob_typ_closed. Qed.
  Obligation 33. (* type_check_order M' *) ob_ord. Defined.
  Obligation 34. (* False *) ob_neg. Qed.
  Obligation 35. (* ⊢ G ▹ ℕ *) ob_ctx_ext. Qed.
  Obligation 36. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 37. (* False *) ob_neg. Qed.
  Obligation 38. (* False *) ob_neg. Qed.
  Obligation 39. (* exists j, G ⊢ A'[Id,,zero] : Type@j *)
    clear_defs.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢s Id,,zero : G ▹ ℕ) as Hσ by mauto 3.
    (** [sub_preserves_exp] is applied by hand: unifying its conclusion would
        require solving [?A[?σ] ≟ Type@i], which [eapply] cannot do. *)
    match goal with HA' : G ▹ ℕ ⊢ A' : Type@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 40. (* type_check_order MZ *) ob_ord. Defined.
  Obligation 41. (* False *) ob_neg. Qed.
  Obligation 42. (* exists j, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Type@j *)
    clear_defs.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (⊢ G ▹ ℕ ▹ A') by mauto 2.
    assert (G ▹ ℕ ▹ A' ⊢s Wk ⨟ Wk,,succ #1 : G ▹ ℕ) as Hσ by mauto 3.
    match goal with HA' : G ▹ ℕ ⊢ A' : Type@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 43. (* type_check_order MS *) ob_ord. Defined.
  Obligation 44. (* False *) ob_neg. Qed.
  Obligation 45. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Type@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    match goal with HA' : G ▹ ℕ ⊢ A' : Type@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 46. (* G ⊢a rec M' … end ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    (** The motive at the scrutinee is a type, so its normal form is one too,
        and [level_of_nbe] gives both halves at once. *)
    match goal with HA' : G ▹ ℕ ⊢ A' : Type@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Type@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 47. (* G ⊢a ⊤ ⟹ Typeˢⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 48. (* G ⊢a ⋆ ⟹ ⊤ⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ⊤ ⟹ UA /... *) ob_post. Qed.
  Obligation 49. (* G ⊢a ⊥ ⟹ Typeˢⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 50. (* exists i : nat, G ⊢ ⊥ : Type@i *) ob_typ_closed. Qed.
  Obligation 51. (* type_check_order M' *) ob_ord. Defined.
  Obligation 52. (* False *) ob_neg. Qed.
  Obligation 53. (* ⊢ G ▹ ⊥ *) ob_ctx_ext. Qed.
  Obligation 54. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 55. (* False *) ob_neg. Qed.
  Obligation 56. (* False *) ob_neg. Qed.
  Obligation 57. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Type@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Type@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 58. (* G ⊢a efq M' return A' ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Type@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Type@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 59. Qed.
  Obligation 60. (* type_infer_order B *) ob_ord. Defined.
  Obligation 61. (* False *) ob_neg. Qed.
  Obligation 62. (* False *) ob_neg. Qed.
  Obligation 63. (* ⊢ G ▹ B *) ob_ctx. Qed.
  Obligation 64. (* type_infer_order C *) ob_ord. Defined.
  Obligation 65. (* False *) ob_neg. Qed.
  Obligation 66. (* False *) ob_neg. Qed.
  Obligation 67. (* G ⊢a Π B C ⟹ univ_nf (unf_max u v), and that is a type *)
    clear_defs.
    split; [ eapply ati_pi; [ eassumption | eassumption | eassumption | eassumption
                            | apply is_univ_nf_univ_nf ]
           | univ_is_type_obl u v ].
  Qed.
  Obligation 68. Qed.
  Obligation 69. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 70. (* False *) ob_neg. Qed.
  Obligation 71. (* False *) ob_neg. Qed.
  Obligation 72. (* ⊢ G ▹ A' *) ob_ctx. Qed.
  Obligation 73. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 74. (* False *) ob_neg. Qed.
  Obligation 75. (* nbe_ty_order gc_deps gc_stack G A' *)
    clear_defs.
    saturate_infer_univ.
    match goal with H : G ⊢ A' : Type@?k |- _ =>
      assert (G ⊢ A' : Type@k) as [? []]%soundness_ty by exact H end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 76. (* G ⊢a λ A' M' ⟹ Πⁿ A'' B', and [Π A'' B'] is a type *)
    clear_defs.
    saturate_infer_univ.
    (** The annotation's normal form is a type at the same level, and the
        body's type is one in the context of that normal form. *)
    assert (⊢ G ▹ A') by mauto 2.
    assert (G ⊢ A' ≈ A'' : Type@(unf_large u)) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (G ⊢ A'' : Type@(unf_large u)) by (gen_presups; mauto 2).
    assert (⊢ G ▹ (A'' : exp)) by mauto 2.
    assert (exists l, G ▹ (A'' : exp) ⊢ B' : Type@l) as [l HB'] by (eexists; mauto 4).
    split; [ mauto 3 | split ].
    - destruct (alg_type_infer_typ_complete (user_exp_nf A'') ltac:(eassumption)) as [UA'' [w [? []]]].
      destruct (alg_type_infer_typ_complete (user_exp_nf B') HB') as [UB' [w' [? []]]].
      do 2 eexists; split;
        [ eapply ati_pi; [ eassumption | eassumption | eassumption | eassumption
                         | apply is_univ_nf_univ_nf ]
        | apply is_univ_nf_univ_nf ].
    - exists (max (unf_large u) l); apply wf_pi;
        [ mauto 3 using lift_exp_max_left | mauto 3 using lift_exp_max_right ].
  Qed.
  Obligation 77. Qed.
  Obligation 78. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 79. (* False *) ob_neg. Qed.
  Obligation 80. (* False *) ob_neg. Qed.
  Obligation 81. (* exists i : nat, G ⊢ A : Type@i *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 82. (* type_check_order N' *) ob_ord. Defined.
  Obligation 83. (* False *) ob_neg. Qed.
  Obligation 84. (* nbe_ty_order gc_deps gc_stack G s[Id,,N'] *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    saturate_infer_univ.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    (** The codomain is a type at the large level of the index [ati_pi]'s side
        condition gives it. *)
    assert (G ⊢ s[Id,,N'] : Type@(unf_large v)) as [? []]%soundness_ty by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 85. (* G ⊢a M' $ N' ⟹ B' /\ (B' is a type) *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    split; [mauto 3 |].
    saturate_infer_univ.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ s[Id,,N'] : Type@(unf_large v)) by mauto 3.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 86. Qed.
  Obligation 87. (* False *) ob_neg. Qed.
  Obligation 88. (* nbe_ty_order gc_deps gc_stack G A *)
    clear_defs.
    assert (exists i, G ⊢ A : Type@i) as [? [? []]%soundness_ty] by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 89. (* G ⊢a #x ⟹ A', and [A'] is a type *)
    clear_defs.
    assert (exists i, G ⊢ A : Type@i) as [i] by mauto 3.
    split; [ mauto 3 |].
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 90. Qed.
  Obligation 91. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 92. (* False *) ob_neg. Qed.
  Obligation 93. (* False *) ob_neg. Qed.
  Obligation 94. (* exists i, G ⊢ A' : Type@i *)
    clear_defs.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 95. (* type_check_order M' *) ob_ord. Defined.
  Obligation 96. (* False *) ob_neg. Qed.
  Obligation 97. (* ⊢ G ▸ A' ≔ M' *) ob_ctx. Qed.
  Obligation 98. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 99. (* False *) ob_neg. Qed.
  Obligation 100. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Type@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 101. (* G ⊢a ℓ A' ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Type@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 102. Qed.
  Obligation 103. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 104. (* False *) ob_neg. Qed.
  Obligation 105. (* ⊢ G ▸ A ≔ M' *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    mauto 3.
  Qed.
  Obligation 106. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 107. (* False *) ob_neg. Qed.
  Obligation 108. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Type@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 109. (* G ⊢a ℓ ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Type@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 110. (* unit_order U *) ob_ord. Defined.
  Obligation 111. (* False *) ob_neg. Qed.
  Obligation 112. (* ⊢ G ▹ₘ U *) ob_ctx. Qed.
  Obligation 113. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 114. (* False *) ob_neg. Qed.
  Obligation 115. (* nbe_ty_order gc_deps gc_stack G C[Id ,,ₘ me_lit U] *)
    clear_defs.
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢s Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Type@k) as [? [? []]%soundness_ty]
        by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 116. (* G ⊢a ℓₘ U in B' ⟹ D, and [D] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢s Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Type@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 117. (* nbe_ty_order gc_deps gc_stack G A *) mo_1. Qed.
  Obligation 118. (* G ⊢a a_mem M' x ⟹ C /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_1. Qed.
  Obligation 119. (* modexp_order M' *) ob_ord. Defined.
  Obligation 120. (* False *) ob_mem_neg. Qed.
  Obligation 121. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 122. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M' ≈ M' *) mo_18. Qed.
  Obligation 123. (* False *) ob_mem_neg. Qed.
  Obligation 124. (* nbe_ty_order gc_deps gc_stack G A *) mo_7. Qed.
  Obligation 125. (* G ⊢a a_mem M' x ⟹ B /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_8. Qed.
  Obligation 126. (* modexp_order M' *) ob_ord. Defined.
  Obligation 127. (* False *) ob_mem_neg. Qed.
  Obligation 128. (* type_infer_order (apps (member_ref R (pre ++ x :: nil) $ ... *) ob_ord_apps. Defined.
  Obligation 129. (* False *) ob_mem_neg. Qed.
  Obligation 130. (* G ⊢a a_mem M' x ⟹ A /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_9. Qed.
  Obligation 131. (* G ⊢aˣ ⋅ *) ob_check. Qed.
  Obligation 132. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 133. (* False *) mo_10. Qed.
  Obligation 134. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 135. (* type_infer_order A *) ob_ord. Defined.
  Obligation 136. (* False *) mo_10. Qed.
  Obligation 137. (* False *) mo_10. Qed.
  Obligation 138. (* G ⊢aˣ Ψ ▹ A *) ob_check. Qed.
  Obligation 139. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 140. (* False *) mo_10. Qed.
  Obligation 141. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 142. (* type_infer_order A *) ob_ord. Defined.
  Obligation 143. (* False *) mo_10. Qed.
  Obligation 144. (* False *) mo_10. Qed.
  Obligation 145. (* exists i0 : nat, Ψ ++ G ⊢ A : Type@i0 *) mo_14. Qed.
  Obligation 146. (* type_check_order M *) ob_ord. Defined.
  Obligation 147. (* False *) mo_10. Qed.
  Obligation 148. (* G ⊢aˣ Ψ ▸ A ≔ M *) ob_check. Qed.
  Obligation 149. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 150. (* False *) mo_10. Qed.
  Obligation 151. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 152. (* unit_order U *) ob_ord. Defined.
  Obligation 153. (* False *) mo_10. Qed.
  Obligation 154. (* G ⊢aˣ Ψ ▹ₘ U *) ob_check. Qed.
  Obligation 155. (* ext_order (body_ctx Φ ++ Δ) *) ob_ord. Defined.
  Obligation 156. (* False *) mo_10. Qed.
  Obligation 157. (* False *) mo_10. Qed.
  Obligation 158. (* False *) mo_10. Qed.
  Obligation 159. (* False *) mo_10. Qed.
  Obligation 160. (* G ⊢aᵘ gu_body Δ Φ *) ob_check. Qed.
  Obligation 161. (* ext_order Δ *) ob_ord. Defined.
  Obligation 162. (* False *) mo_10. Qed.
  Obligation 163. (* False *) mo_10. Qed.
  Obligation 164. (* ⊢ Δ ++ G *) ob_ctx. Qed.
  Obligation 165. (* modexp_order E *) ob_ord. Defined.
  Obligation 166. (* False *) mo_10. Qed.
  Obligation 167. (* G ⊢aᵘ gu_mk Δ (md_alias E) *) ob_check. Qed.
  Obligation 168. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 169. (* False *) mo_10. Qed.
  Obligation 170. (* G ⊢aᵐ me_unit fp *) mo_2. Qed.
  Obligation 171. (* G ⊢aᵐ me_var x *) mo_19. Qed.
  Obligation 172. (* False *) mo_20. Qed.
  Obligation 173. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 174. (* False *) mo_3. Qed.
  Obligation 175. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 176. (* modexp_order M *) ob_ord. Defined.
  Obligation 177. (* False *) mo_3. Qed.
  Obligation 178. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 179. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 180. (* False *) mo_10. Qed.
  Obligation 181. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 182. (* modexp_order M *) ob_ord. Defined.
  Obligation 183. (* False *) mo_10. Qed.
  Obligation 184. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 185. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 186. (* False *) mo_10. Qed.
  Obligation 187. (* False *) mo_21. Qed.
  Obligation 188. (* exists i : nat, G ⊢ B : Type@i *) mo_22. Qed.
  Obligation 189. (* type_check_order N *) ob_ord. Defined.
  Obligation 190. (* False *) mo_21. Qed.
  Obligation 191. (* G ⊢aᵐ me_app M N *) ob_check. Qed.
  Obligation 192. (* unit_order U *) ob_ord. Defined.
  Obligation 193. (* False *) mo_10. Qed.
  Obligation 194. (* G ⊢aᵐ me_lit U File "./Extraction/TCprobe2.v", line 1071,... *) ob_check. Qed.


  Extraction Inline type_check_functional type_infer_functional ext_check_functional
    unit_check_functional modexp_check_functional.

  Lemma type_infer_order_soundness : forall G M A,
      G ⊢a M ⟹ A ->
      type_infer_order M.
  Proof. intros; apply type_infer_order_all. Qed.

  Lemma type_check_order_soundness : forall G M A,
      G ⊢a M ⟸ A ->
      type_check_order M.
  Proof. intros; constructor; apply type_infer_order_all. Qed.
End type_check.

#[local]
Hint Resolve type_check_order_soundness type_infer_order_soundness : mctt.

Lemma type_check_complete' : forall G M A (HA : exists i, G ⊢ A : Type@i),
    G ⊢a M ⟸ A ->
    exists H H', type_check G A HA M H = left H'.
Proof.
  intros ? ? ? [] ?.
  assert (Horder : type_check_order M) by mauto.
  exists Horder.
  dec_complete.
Qed.

Lemma type_infer_complete : forall G M A (HG : ⊢ G),
    G ⊢a M ⟹ A ->
    exists H H', type_infer G HG M H = inleft (exist _ A H').
Proof.
  intros.
  assert (Horder : type_infer_order M) by mauto.
  exists Horder.
  destruct (type_infer G HG M Horder) as [[? []] |].
  - functional_alg_type_infer_rewrite_clear.
    eexists; reflexivity.
  - contradict H; intuition.
Qed.

Lemma ext_check_complete : forall G Ψ (HG : ⊢ G),
    G ⊢aˣ Ψ ->
    exists H H', ext_check G HG Ψ H = left H'.
Proof.
  intros * HΨ.
  assert (Horder : ext_order Ψ).
  { induction Ψ as [| [A | A M | U] Ψ IH]; inversion HΨ; subst; constructor;
      eauto using type_infer_order_all, unit_order_all, tc_ti. }
  exists Horder; destruct (ext_check G HG Ψ Horder); [ eexists; reflexivity | contradiction ].
Qed.

Lemma unit_check_complete : forall G U (HG : ⊢ G),
    G ⊢aᵘ U ->
    exists H H', unit_check G HG U H = left H'.
Proof.
  intros * HU; exists (unit_order_all U).
  destruct (unit_check G HG U (unit_order_all U)); [ eexists; reflexivity | contradiction ].
Qed.

Lemma modexp_check_complete : forall G M (HG : ⊢ G),
    G ⊢aᵐ M ->
    exists H H', modexp_check G HG M H = left H'.
Proof.
  intros * HM; exists (modexp_order_all M).
  destruct (modexp_check G HG M (modexp_order_all M)); [ eexists; reflexivity | contradiction ].
Qed.

Section type_check_closed.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check_closed (Hg : ⊢g gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M) : { ⋅ ⊢ M : A } + { ~ ⋅ ⊢ M : A } :=
  | Hg, A, HA, M, HM =>
      let*o->b (exist _ UA _) := type_infer ⋅ _ A _ while _ in
      let*o->b (exist _ u _) :=  univ_nf_idx_dec UA while _ in
      let*b _ := type_check ⋅ A _ M _ while _ in
      pureb _
  .
  Next Obligation. (* False *)
    assert (⊢ ⋅) by mauto 2.
    assert (exists i, ⋅ ⊢ A : Type@i) as [i] by (gen_presups; eauto 2).
    assert (exists UA' w, ⋅ ⊢a A ⟹ UA' /\ is_univ_nf UA' w /\ unf_le w (unl i)) as [UA' [w [? []]]]
        by mauto 3.
    firstorder.
  Qed.
  Next Obligation. (* False *)
    assert (exists i, ⋅ ⊢ A : Type@i) as [i] by (gen_presups; eauto 2).
    assert (exists UA' w, ⋅ ⊢a A ⟹ UA' /\ is_univ_nf UA' w /\ unf_le w (unl i)) as [UA' [w [? []]]]
        by mauto 3.
    functional_alg_type_infer_rewrite_clear.
    match goal with
    | HN : forall u : unf, ~ is_univ_nf ?UA u, Hu : is_univ_nf ?UA ?w |- _ => exact (HN w Hu)
    end.
  Qed.
  Next Obligation. (* exists i, ⋅ ⊢ A : Type@i *)
    assert (⊢ ⋅) by mauto 2.
    match goal with Hu : is_univ_nf ?UA u |- _ => rewrite (is_univ_nf_eq _ _ Hu) in * end.
    assert (⋅ ⊢ A : (univ_nf u : exp)) by mauto 2 using alg_type_infer_sound.
    rewrite nf_to_exp_univ_nf in *.
    exists (unf_large u); apply wf_exp_unf_large; eassumption.
  Qed.
  Next Obligation. (* ⋅ ⊢ M : A *)
    assert (⊢ ⋅) by mauto 2.
    match goal with Hu : is_univ_nf ?UA u |- _ => rewrite (is_univ_nf_eq _ _ Hu) in * end.
    assert (⋅ ⊢ A : (univ_nf u : exp)) by mauto 3 using alg_type_infer_sound.
    rewrite nf_to_exp_univ_nf in *.
    assert (⋅ ⊢ A : Type@(unf_large u))
      by (apply wf_exp_unf_large; eassumption).
    mauto 3 using alg_type_check_sound.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete : forall (Hg : ⊢g gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M),
    ⋅ ⊢ M : A ->
    exists H', type_check_closed Hg A HA M HM = left H'.
Proof. intros; dec_complete. Qed.

(** What an unascribed [eval] needs: a type for a closed term, rather than a
    type to check it against. *)
Section type_infer_closed.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    destruct_conjs;
    try assert (⊢ ⋅) by mauto 2;
    solve [ mauto 3 using user_exp_to_type_infer_order, alg_type_infer_sound
          | firstorder ].

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_infer_closed (Hg : ⊢g gc_deps ⍮ gc_stack) M (HM : user_exp M) : { A : nf | ⋅ ⊢ M : A } + { forall A, ~ ⋅ ⊢a M ⟹ A } :=
  | Hg, M, HM =>
      let*o (exist _ A _) := type_infer ⋅ _ M _ while _ in
      pureo (exist _ A _)
  .
End type_infer_closed.

(** The same in a well-formed context, for an [eval] inside a module, which
    sees the parameters of its enclosing frames. *)
Section type_infer_at.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    destruct_conjs;
    solve [ mauto 3 using user_exp_to_type_infer_order, alg_type_infer_sound
          | firstorder ].

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_infer_at G (HG : ⊢ G) M (HM : user_exp M) : { A : nf | G ⊢ M : A } + { forall A, ~ G ⊢a M ⟹ A } :=
  | G, HG, M, HM =>
      let*o (exist _ A _) := type_infer G HG M _ while _ in
      pureo (exist _ A _)
  .
End type_infer_at.

End Fixed_GCtx.
