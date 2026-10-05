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
  #[derive(equations=no,eliminator=no)]
  Equations get_level_of_type_nf (A : nf) : { i | A = Typeⁿ@i } + { forall i, A <> Typeⁿ@i } :=
  | Typeⁿ@i => pureo (exist _ i _)
  | _               => inright _
  .

  (** Extraction should set the 9th bit of [Extraction Flag] (for example,
      [Set Extraction Flag 1007.]); otherwise this function introduces
      redundant pair construction and pattern matching. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_subterms_of_pi_nf (A : nf) : { B & { C | A = Πⁿ B C } } + { forall B C, A <> Πⁿ B C } :=
  | Πⁿ B C => pureo (existT _ B (exist _ C _))
  | _              => inright _
  .

  Extraction Inline get_level_of_type_nf get_subterms_of_pi_nf.

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

  (** Whether a name is fresh in a body. *)
  Definition gm_fresh_dec : forall x Φ, { gm_fresh x Φ } + { ~ gm_fresh x Φ }.
  Proof.
    intros x Φ; unfold gm_fresh; destruct (in_dec string_dec x (gm_names Φ)) as [Hin | Hn];
      [ right; intros Hf; exact (Hf Hin) | left; exact Hn ].
  Defined.

  (** ** Deciding Member Types *)

  Definition member_type_dec (Hg : ⊢g gc_ctx) Γ H ch
      (HH : gc_ctx ⍮ Γ ⊢ᵐ H ≈ H) :
      { R | member_type gc_ctx Γ H ch R } + { forall R, ~ member_type gc_ctx Γ H ch R } :=
    member_type_impl gc_ctx (gctx_closed_of_wf _ Hg) Γ H ch (mt_order_of_wf _ _ _ Hg HH ch).

  (** A member type asked for as a definition's type, or as a module's
      arity: member types are unique, so the other sort is none. *)
  Definition mres_term_dec {Γ H ch}
      (d : { R | member_type gc_ctx Γ H ch R } + { forall R, ~ member_type gc_ctx Γ H ch R }) :
      { A | member_type gc_ctx Γ H ch (mr_term A) } +
      { forall A, ~ member_type gc_ctx Γ H ch (mr_term A) }.
  Proof.
    destruct d as [[[A | T] HR] | HN]; [ left; exists A; exact HR | right | right; intros A HA; exact (HN _ HA) ].
    intros A HA; pose proof (proj1 (member_type_functional _) _ _ _ _ HR _ HA); discriminate.
  Defined.

  Definition mres_mod_dec {Γ H ch}
      (d : { R | member_type gc_ctx Γ H ch R } + { forall R, ~ member_type gc_ctx Γ H ch R }) :
      { T | member_type gc_ctx Γ H ch (mr_mod T) } +
      { forall T, ~ member_type gc_ctx Γ H ch (mr_mod T) }.
  Proof.
    destruct d as [[[A | T] HR] | HN]; [ right | left; exists T; exact HR | right; intros T HT; exact (HN _ HT) ].
    intros T HT; pose proof (proj1 (member_type_functional _) _ _ _ _ HR _ HT); discriminate.
  Defined.

  Definition member_term_dec (Hg : ⊢g gc_ctx) Γ H ch (HH : gc_ctx ⍮ Γ ⊢ᵐ H ≈ H) :=
    mres_term_dec (member_type_dec Hg Γ H ch HH).

  Definition member_mod_dec (Hg : ⊢g gc_ctx) Γ H ch (HH : gc_ctx ⍮ Γ ⊢ᵐ H ≈ H) :=
    mres_mod_dec (member_type_dec Hg Γ H ch HH).

  (** The outermost parameter of an arity, if any. *)
  Equations tele_view_dec (T : ctx) : { B : typ & { T1 : ctx | tele_view T = Some (B, T1) } } + { tele_view T = None } :=
  tele_view_dec T with inspect (tele_view T) := {
    | exist _ (Some (B, T1)) E => inleft (existT _ B (exist _ T1 E))
    | exist _ None E => inright E }.

  Extraction Inline member_type_dec member_term_dec member_mod_dec mres_term_dec mres_mod_dec tele_view_dec.

  (** ** Facts the Obligations Use *)

  Lemma nbe_order_of_typ : forall G X i, G ⊢ X : Type@i -> nbe_ty_order gc_ctx G X.
  Proof. intros * HX; destruct (soundness_ty HX) as [W [HW _]]; eauto using nbe_ty_order_sound. Qed.

  Lemma level_of_nbe : forall G X i D, G ⊢ X : Type@i -> nbe_ty_f G X D -> exists j, G ⊢a D ⟹ Typeⁿ@j.
  Proof.
    intros * HX HD.
    assert (G ⊢ X ≈ D : Type@i) by (eapply soundness_ty'; eassumption).
    assert (G ⊢ D : Type@i) by (gen_presups; eassumption).
    destruct (alg_type_infer_typ_complete (user_exp_nf D) ltac:(eassumption)) as [j [Hj _]]; eauto.
  Qed.

  Lemma member_typ_of_alg : forall G M ch R, ⊢ G -> G ⊢aᵐ M ->
      member_type gc_ctx G M ch R -> (mres_kind R = mk_term -> ch <> nil) -> exists i, G ⊢ mres_ty R : Type@i.
  Proof.
    intros * HG HM Hm Hch.
    exact (proj1 (proj1 member_wf _ _ _ _ Hm (alg_modexp_sound HM HG) Hch)).
  Qed.

  Lemma let_mod_typ_of_alg : forall G U C i, ⊢ G -> G ⊢aᵘ U -> G ▹ₘ U ⊢a C ⟹ Typeⁿ@i ->
      G ⊢ C[Id ,,ₘ me_lit U] : Type@i.
  Proof.
    intros * HG HU HC.
    pose proof (alg_unit_sound HU HG) as HU'.
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU').
    assert (HCt : G ▹ₘ U ⊢ C : Typeⁿ@i) by (eapply alg_type_infer_sound; eassumption).
    exact (sub_preserves_exp _ _ _ _ _ _ HCt (wf_sub_single_mod _ _ _ HU')).
  Qed.

  (** The self context of a body the checker accepted is well formed. *)
  Lemma self_ctx_of_alg : forall G Δ Φ, G ⊢aᵘ gu_body Δ Φ -> ⊢ G -> ⊢ self_ent Φ :: Δ ++ G.
  Proof.
    intros * HU HG.
    destruct (unit_parts_of_wf _ _ _ (alg_unit_sound HU HG)) as (HC & _ & Hb).
    exact (self_ctx_wf _ _ _ HC Hb).
  Qed.

  Inductive type_check_order : exp -> Prop :=
  | tc_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order : exp -> Prop :=
  | ti_typ : forall {i}, type_infer_order Type@i
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
  | ti_const : forall {c}, type_infer_order (a_const c)
  with ext_order : ctx -> Prop :=
  | eo_nil : ext_order nil
  | eo_ass : forall {A Ψ}, ext_order Ψ -> type_infer_order A -> ext_order (Ψ ▹ A)
  | eo_def : forall {A M Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> ext_order (Ψ ▸ A ≔ M)
  | eo_mod : forall {U Ψ}, ext_order Ψ -> unit_order U -> ext_order (Ψ ▹ₘ U)
  with unit_order : gunit -> Prop :=
  (** A body, entry by entry, as its check runs. *)
  | uo_nil : forall {Δ}, ext_order Δ -> unit_order (gu_body Δ gm_nil)
  | uo_def : forall {Δ Φ x pv A oM}, unit_order (gu_body Δ Φ) -> type_infer_order A ->
      (forall M, oM = Some M -> type_check_order M) ->
      unit_order (gu_body Δ (gm_ext Φ x (ge_def pv A oM)))
  | uo_mod : forall {Δ Φ x pv U}, unit_order (gu_body Δ Φ) -> unit_order U ->
      unit_order (gu_body Δ (gm_ext Φ x (ge_mod pv U)))
  | uo_open : forall {Δ Φ H oz its}, unit_order (gu_body Δ (gm_open Φ H oz its))
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
           | md_body Φ => forall Δ, ext_order Δ -> unit_order (gu_body Δ Φ)
           | md_alias E => modexp_order E
           end) /\
    (forall Φ Δ, ext_order Δ -> unit_order (gu_body Δ Φ)) /\
    (forall E, match E with
           | ge_def _ A oM => type_infer_order A /\ (forall M, oM = Some M -> type_infer_order M)
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
             | md_body Φ => forall Δ, ext_order Δ -> unit_order (gu_body Δ Φ)
             | md_alias E => modexp_order E
             end)
      (fun Φ => forall Δ, ext_order Δ -> unit_order (gu_body Δ Φ))
      (fun E => match E with
             | ge_def _ A oM => type_infer_order A /\ (forall M, oM = Some M -> type_infer_order M)
             | ge_mod _ U => unit_order U
             end)
      centry_order); intros; cbn in *; destruct_conjs.
    (** Terms. *)
    all: try solve [ eauto 6 with mctt ].
    all: try solve [ match goal with |- type_infer_order (a_let ?b _) =>
        destruct b as [[A |] M | U]; destruct_conjs;
        [ apply ti_let; [ eauto | constructor; assumption | assumption ]
        | apply ti_let_infer; assumption
        | apply ti_let_mod; assumption ] end ].
    all: try solve [ match goal with |- type_infer_order (a_mem _ _) => idtac end;
      constructor; [ assumption |];
      intros R args pre Hs Hne;
      match goal with Hsp : forall R args pre, modexp_spine _ = _ -> _ |- _ => destruct (Hsp _ _ _ Hs) as [HR Hargs] end;
      apply apps_order; [ apply member_ref_order; [ eapply spine_root_self; eassumption | exact HR ] | exact Hargs ] ].
    (** Module expressions, with their spines. *)
    all: try solve [ split; [ constructor | intros * [= <- <- <-]; split; constructor ] ].
    all: try solve [ split; [ constructor; assumption | intros * [= <- <- <-]; split; [ constructor; assumption | constructor ] ] ].
    all: try solve [ match goal with |- modexp_order (me_mem ?H _) /\ _ =>
      split; [ constructor; assumption |];
      intros R args pre Hs;
      destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-; eauto end ].
    all: try solve [ match goal with |- modexp_order (me_app ?H _) /\ _ =>
      split; [ constructor; [ assumption | constructor; assumption ] |];
      intros R args pre Hs;
      destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-;
      match goal with Hsp : forall R args pre, (R0, a0, p0) = _ -> _ |- _ => destruct (Hsp _ _ _ eq_refl) as [? ?] end;
      split; [ assumption | apply Forall_app; split; [ assumption | constructor; [ constructor; assumption | constructor ] ] ] end ].
    (** Units and bodies. *)
    all: try solve [ match goal with |- unit_order (gu_mk _ ?D) =>
      destruct D; eauto using ext_order_of_forall with mctt end ].
    all: try solve [ match goal with |- unit_order (gu_body _ (gm_ext _ _ ?E)) =>
      destruct E; destruct_conjs; constructor; eauto with mctt end ].
    all: try solve [ destruct E as [pv A [M |] | pm U]; destruct_conjs; cbn; eauto with mctt ].
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
                ({ B : nf | G ⊢a M ⟹ B /\ (exists i : nat, G ⊢a (nf_to_exp B) ⟹ Typeⁿ@i) } + { forall C : nf, ~ G ⊢a M ⟹ C }))
        |- _ =>
          clear H
      | H: (forall G : ctx,
               ⊢ G ->
               forall M : typ,
                 type_infer_order M ->
                 ({ B : nf | G ⊢a M ⟹ B /\ (exists i : nat, G ⊢a (nf_to_exp B) ⟹ Typeⁿ@i) } + { forall C : nf, ~ G ⊢a M ⟹ C }))
        |- _ =>
          clear H
    end.

  #[local]
  Ltac impl_obl_tac_helper :=
    match goal with
    | H: type_infer_order _ |- _ => progressive_invert H
    end.

  (** A context the checker extends is well formed by the soundness of the
      check of the extension. *)
  #[local]
  Ltac ctx_wf_tac :=
    match goal with
    | |- ⊢ ?G => assumption
    | |- ⊢ ?G ▹ ?A =>
        match goal with H : G ⊢a A ⟹ Typeⁿ@?i |- _ =>
          assert (G ⊢ A : Type@i) by (eapply alg_type_infer_sound; eassumption); mauto 2 end
    | |- ⊢ ?G ▸ ?A ≔ ?M =>
        match goal with H : G ⊢a A ⟹ Typeⁿ@?i, H' : G ⊢a M ⟸ A |- _ =>
          assert (G ⊢ A : Type@i) by (eapply alg_type_infer_sound; eassumption);
          assert (G ⊢ M : A) by (eapply alg_type_check_sound; eassumption); mauto 2 end
    | |- ⊢ ?G ▹ₘ ?U =>
        match goal with H : G ⊢aᵘ U |- _ => apply wf_ctx_extend_mod; eapply alg_unit_sound; eassumption end
    | |- ⊢ ?Ψ ++ ?G =>
        match goal with H : G ⊢aˣ Ψ |- _ => eapply ext_eq_ctx_left, alg_ext_sound; eassumption end
    | |- ⊢ self_ent ?Φ :: ?Δ ++ ?G =>
        match goal with H : G ⊢aᵘ gu_body Δ Φ |- _ => eapply self_ctx_of_alg; eassumption end
    end.

  #[local]
  Ltac impl_obl_tac :=
    clear_defs;
    try match goal with
      | H: type_check_order _ |- _ => progressive_invert H
      end;
    repeat match goal with
      | H: type_infer_order _ |- _ => progressive_invert H
      | H: ext_order _ |- _ => progressive_invert H
      | H: unit_order _ |- _ => progressive_invert H
      | H: modexp_order _ |- _ => progressive_invert H
      end;
    destruct_conjs;
    match goal with
    | |- ⊢ _ => first [ solve [ ctx_wf_tac ] | solve [ mauto 3 ] ]
    | |- ⊢g _ => eapply ctx_wf_gctx; eassumption
    | |- wf_modexp_eq _ ?G ?M ?M =>
        match goal with H : G ⊢aᵐ M |- _ => eapply alg_modexp_sound; eassumption end
    | |- type_infer_order (apps _ _) =>
        match goal with H : forall R args pre, modexp_spine _ = _ -> _ -> type_infer_order _ |- _ =>
          eapply H; [ eassumption | discriminate ] end
    | |- _ -> forall A : nf, ~ _ ⊢a a_mem _ _ ⟹ A =>
        let HN := fresh "HN" in
        let HA := fresh "HA" in
        intros HN ? HA; inversion HA; subst;
        repeat match goal with
          | H1 : modexp_spine ?M = _, H2 : modexp_spine ?M = _ |- _ =>
              rewrite H1 in H2; injection H2; intros; subst; clear H2
          end;
        first [ solve [ eapply HN; eassumption ]
              | match goal with Hn : me_noargs ?M, Hs : modexp_spine ?M = _ |- _ =>
                  pose proof (me_noargs_spine _ _ _ _ Hn Hs); discriminate end
              | congruence ]
    | H: ?G ⊢ ?A : Type@?i |- ?G ⊢ ?A : Type@(Nat.max ?i ?j) => apply lift_exp_max_left; mautosolve 4
    | H: ?G ⊢ ?A : Type@?j |- ?G ⊢ ?A : Type@(Nat.max ?i ?j) => apply lift_exp_max_right; mautosolve 4
    | |- _ ⊢ _ : _ => gen_presups; mautosolve 4
    | |- _ -> ~ _ ⊢a _ ⟸ _ =>
        let H := fresh "H" in
        intros ? H;
        directed dependent destruction H;
        functional_alg_type_infer_rewrite_clear;
        firstorder
    | |- _ -> (forall A : nf, ~ _ ⊢a _ ⟹ _) =>
        unfold not in *;
        intros;
        progressive_inversion;
        functional_alg_type_infer_rewrite_clear;
        solve [congruence | mautosolve 3]
    | |- type_infer_order _ => eassumption; fail 1
    | |- type_check_order _ => eassumption; fail 1
    | |- ext_order _ => eassumption; fail 1
    | |- unit_order _ => eassumption; fail 1
    | |- modexp_order _ => eassumption; fail 1
    | |- subtyping_order ?G ?A ?B =>
        enough (exists i, G ⊢ A : Typeⁿ@i) as [? [? []]%soundness_ty];
        only 1: enough (exists j, G ⊢ B : Typeⁿ@j) as [? [? []]%soundness_ty];
        only 1: solve [econstructor; eauto 3 using nbe_ty_order_sound];
        solve [mauto 4 using alg_type_infer_sound]
    | _ => try mautosolve 3
    end.

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
    first [ match goal with H : forall i, ?X <> Typeⁿ@i |- _ => exact (H _ eq_refl) end | firstorder ].

  #[local]
  Ltac typ_sound :=
    match goal with
    | |- exists i, ?G ⊢ ?A : Type@i =>
        match goal with H : G ⊢a A ⟹ Typeⁿ@?i |- _ =>
          exists i;
          let Hx := fresh in
          assert (Hx : G ⊢ A : Typeⁿ@i) by (eapply alg_type_infer_sound; [ eassumption | ctx_wf_tac ]);
          exact Hx
        end
    end.

  #[local]
  Ltac ctxp :=
    first [ assumption
          | ctx_wf_tac
          | match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; left; reflexivity end ].

  #[local]
  Ltac mt_unify :=
    repeat match goal with
      | H1 : member_type ?T ?G ?M ?c ?A1, H2 : member_type ?T ?G ?M ?c ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          let E := fresh "E" in
          pose proof (proj1 (member_type_functional _) _ _ _ _ H1 _ H2) as E; try injection E as E; subst; clear H2
      end.

  #[local]
  Ltac mod_obl :=
    clear_defs; destruct_conjs;
    first
      [ solve [ match goal with HG : ⊢ ?G, Ec : gc_const _ _ = Some _ |- _ =>
                  destruct (wf_const_typ _ _ _ _ _ _ HG Ec) as [? ?];
                  first [ eapply nbe_order_of_typ; eassumption
                        | split; [ eapply ati_const; eassumption | eapply level_of_nbe; eassumption ] ] end ]
      | solve [ intros; match goal with Hx : _ ⊢a a_const _ ⟹ _ |- _ => inversion Hx; subst; congruence end ]
      | solve [ match goal with Hx : _ ⊢aᵐ me_mem _ _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
                match goal with HN : forall T, ~ member_type _ _ (me_mem _ _) nil (mr_mod T) |- _ =>
                  first [ eapply HN; eassumption | eapply HN; eapply mt_mem; [ discriminate | eassumption ] ] end ]
      | solve [ match goal with Hx : _ ⊢aᵐ _ |- False => inversion Hx; subst end; congruence ]
      | solve [ eapply nbe_order_of_typ, let_mod_typ_of_alg; eassumption ]
      | solve [ split; [ eapply ati_let_mod; eassumption
                       | eapply level_of_nbe; [ eapply let_mod_typ_of_alg; eassumption | eassumption ] ] ]
      | solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ ?G ?M _ (mr_term ?A) |- nbe_ty_order _ ?G ?A =>
                    destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?];
                    eapply nbe_order_of_typ; eassumption
                end ]
      | solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ ?G ?M _ (mr_term ?A), Hn : nbe_ty_f ?G ?A _ |- _ =>
                    destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?]
                end;
                split; [ eapply ati_mem; [ eapply spine_nil_noargs; eassumption | eassumption | eassumption | eassumption ]
                       | eapply level_of_nbe; eassumption ] ]
      | solve [ split; [ eapply ati_mem_app; [ eassumption | eassumption | discriminate | eassumption ] | eauto ] ]
      | solve [ negc ]
      | solve [ split; intros * [] ]
      | solve [ econstructor; eassumption ]
      | solve [ econstructor; eauto ]
      | solve [ typ_sound ]
      | solve [ ctx_wf_tac ]
      | solve [ intros; match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; right; eassumption end ]
      | solve [ eapply ctx_wf_gctx; ctxp ]
      | solve [ eapply alg_modexp_sound; [ eassumption | ctxp ] ]
      | solve [ econstructor; apply ctx_find_mod_sound; eassumption ]
      | solve [ match goal with Hx : _ ⊢aᵐ me_var _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
                match goal with Hl : ctx_lookup_mod _ _ _ |- _ => apply ctx_find_mod_complete in Hl end; congruence ]
      | solve [ match goal with Hx : _ ⊢aᵐ me_app _ _ |- False => inversion Hx; subst; try (cbn in *; congruence) end;
                mt_unify;
                repeat match goal with
                  | H1 : tele_view ?T = Some _, H2 : tele_view ?T = Some _ |- _ =>
                      rewrite H1 in H2; injection H2; intros; subst; clear H2
                  | H1 : tele_view ?T = Some _, H2 : tele_view ?T = None |- _ => rewrite H1 in H2; discriminate H2
                  end;
                first [ contradiction | eauto ] ]
      | solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ ?G ?M nil (mr_mod ?T),
                  Hv : tele_view ?T = Some (?B, _) |- exists i, ?G ⊢ ?B : Type@i =>
                    let i := fresh "i" in
                    let HA := fresh "HA" in
                    destruct (member_typ_of_alg _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [i HA];
                    cbn [mres_ty] in HA;
                    exists i; exact (proj1 (proj2 (tele_view_wf _ _ _ _ _ HA Hv)))
                end ]
      | solve [ eapply amod_app; eassumption ] ].

  #[local]
  Ltac impl_obl_tac_t := impl_obl_tac.

  #[tactic="impl_obl_tac_t",derive(equations=no,eliminator=no)]
  Equations type_check G A (HA : (exists i, G ⊢ A : Type@i)) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, M, H =>
      let*o->b (exist _ B _) := type_infer G _ M _ while _ in
      let*b _ := subtyping_impl G (B : nf) A _ while _ in
      pureb _
  with type_infer G (HG : ⊢ G) M (H : type_infer_order M) : { A : nf | G ⊢a M ⟹ A /\ (exists i, G ⊢a A ⟹ Typeⁿ@i) } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, M, H with M => {
    | Type@j =>
        pureo (exist _ Typeⁿ@(S j) _)
    | ℕ =>
        pureo (exist _ Typeⁿ@0 _)
    | zero =>
        pureo (exist _ ℕⁿ _)
    | succ M' =>
        let*b->o _ := type_check G ℕ _ M' _ while _ in
        pureo (exist _ ℕⁿ _)
    | rec M' return A' | zero -> MZ | succ -> MS end =>
        let*b->o _ := type_check G ℕ _ M' _ while _ in
        let*o (exist _ UA' _) := type_infer (G ▹ ℕ) _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G A'[Id,,zero] _ MZ _ while _ in
        let*b->o _ := type_check (G ▹ ℕ ▹ A') A'[Wk ⨟ Wk,,succ #1] _ MS _ while _ in
        let (A'', _) := nbe_ty_impl gc_ctx G A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | ⊤ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Typeⁿ@0 _)
    | efq M' return A' =>
        let*b->o _ := type_check G ⊥ _ M' _ while _ in
        let*o (exist _ UA' _) := type_infer (G ▹ ⊥) _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let (A'', _) := nbe_ty_impl gc_ctx G A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | Π B C =>
        let*o (exist _ UB _) := type_infer G _ B _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UB while _ in
        let*o (exist _ UC _) := type_infer (G ▹ B) _ C _ while _ in
        let*o (exist _ j _) :=  get_level_of_type_nf UC while _ in
        pureo (exist _ Typeⁿ@(max i j) _)
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*o (exist _ B' _) := type_infer (G ▹ A') _ M' _ while _ in
        let (A'', _) := nbe_ty_impl gc_ctx G A' _ in
        pureo (exist _ (Πⁿ A'' B') _)
    | M' $ N' =>
        let*o (exist _ C _) := type_infer G _ M' _ while _ in
        let*o (existT _ A (exist _ B _)) := get_subterms_of_pi_nf C while _ in
        let*b->o _ := type_check G (A : nf) _ N' _ while _ in
        let (B', _) := nbe_ty_impl gc_ctx G (B : nf)[Id,,N'] _ in
        pureo (exist _ B' _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer G _ A' _ while _ in
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G A' _ M' _ while _ in
        let*o (exist _ C _) := type_infer (G ▸ A' ≔ M') _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_ctx G (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer G _ M' _ while _ in
        let*o (exist _ C _) := type_infer (G ▸ (A : nf) ≔ M') _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_ctx G (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let*o (exist _ C _) := type_infer (G ▹ₘ U) _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_ctx G (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    (** A member, through its module. *)
    | a_mem M' x with inspect (modexp_spine M') => {
      | exist _ (R, nil, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := member_term_dec _ G M' (x :: nil) _ while _ in
          let (B, _) := nbe_ty_impl gc_ctx G A _ in
          pureo (exist _ B _)
      | exist _ (R, N :: args, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := type_infer G HG (apps (member_ref R (pre ++ x :: nil)) (N :: args)) _ while _ in
          pureo (exist _ A _) }
    | #x =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let (A', _) := nbe_ty_impl gc_ctx G A _ in
        pureo (exist _ A' _)
    (** A constant infers the normal form of its closed type. *)
    | a_const c with inspect (gc_const gc_ctx c) => {
      | exist _ (Some (A, oM, b)) Ec =>
          let (C, _) := nbe_ty_impl gc_ctx G A _ in
          pureo (exist _ C _)
      | exist _ None Ec => inright _ }
    }
  with ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*o->b (exist _ UA _) := type_infer (Ψ ++ G) _ A _ while _ in
      let*o->b (exist _ i _) := get_level_of_type_nf UA while _ in
      pureb _
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*o->b (exist _ UA _) := type_infer (Ψ ++ G) _ A _ while _ in
      let*o->b (exist _ i _) := get_level_of_type_nf UA while _ in
      let*b _ := type_check (Ψ ++ G) A _ M _ while _ in
      pureb _
  | G, HG, ce_mod U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*b _ := unit_check (Ψ ++ G) _ U _ while _ in
      pureb _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body gm_nil), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      pureb _
  (** An entry, in the self context of the body before it. *)
  | G, HG, gu_mk Δ (md_body (gm_ext Φ x (ge_def pv A (Some M)))), H =>
      let*b HΦ := unit_check G HG (gu_body Δ Φ) _ while _ in
      let*b _ := gm_fresh_dec x Φ while _ in
      let*o->b (exist _ UA _) := type_infer (self_ent Φ :: Δ ++ G) _ A _ while _ in
      let*o->b (exist _ i _) := get_level_of_type_nf UA while _ in
      let*b _ := type_check (self_ent Φ :: Δ ++ G) A _ M _ while _ in
      pureb _
  (** A local body has no axioms. *)
  | G, HG, gu_mk Δ (md_body (gm_ext Φ x (ge_def pv A None))), H => right _
  | G, HG, gu_mk Δ (md_body (gm_ext Φ x (ge_mod pv U))), H =>
      let*b HΦ := unit_check G HG (gu_body Δ Φ) _ while _ in
      let*b _ := gm_fresh_dec x Φ while _ in
      let*b _ := unit_check (self_ent Φ :: Δ ++ G) _ U _ while _ in
      pureb _
  (** An open is expanded before typing. *)
  | G, HG, gu_mk Δ (md_body (gm_open Φ E oz its)), H => right _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := modexp_check (Δ ++ G) _ E _ while _ in
      pureb _
  with modexp_check G (HG : ⊢ G) M (H : modexp_order M) : { G ⊢aᵐ M } + { ~ G ⊢aᵐ M } by struct H :=
  | G, HG, me_unit fp, H with inspect (gc_unit gc_ctx fp) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_var x, H with inspect (ctx_find_mod G x) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_lit U, H =>
      let*b _ := unit_check G HG U _ while _ in
      pureb _
  | G, HG, me_mem M y, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ T _) := member_mod_dec _ G M (y :: nil) _ while _ in
      pureb _
  | G, HG, me_app M N, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ T _) := member_mod_dec _ G M nil _ while _ in
      let*o->b (existT _ B (exist _ T1 _)) := tele_view_dec T while _ in
      let*b _ := type_check G B _ N _ while _ in
      pureb _
  .

  Next Obligation. (* G ⊢a succ M' ⟹ ℕⁿ /\ (exists i, G ⊢a ℕ ⟹ Typeⁿ@i) *)
    clear_defs.
    mautosolve 4.
  Qed.

  Next Obligation. (* exists j, G ⊢ A'[Id,,zero] : Type@j *)
    clear_defs.
    exists i.
    assert (G ⊢s Id,,zero : G ▹ ℕ) as Hσ by mauto 3.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    (** [sub_preserves_exp] is applied by hand: unifying its conclusion would
        require solving [?A[?σ] ≟ Type@i], which [eapply] cannot do. *)
    exact (sub_preserves_exp _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* exists j, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Type@i *)
    clear_defs.
    exists i.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▹ ℕ ▹ A') by mauto 2.
    assert (G ▹ ℕ ▹ A' ⊢s Wk ⨟ Wk,,succ #1 : G ▹ ℕ) as Hσ by mauto 3.
    exact (sub_preserves_exp _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeⁿ@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    exists i.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    exact (sub_preserves_exp _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* G ⊢a rec M' return A' | zero -> MZ | succ -> MS end ⟹ A'' /\ (exists j, G ⊢a A'' ⟹ Typeⁿ@j) *)
    clear_defs.
    split; [mauto 3 |].
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    assert (G ⊢ A'[Id,,M'] : Typeⁿ@i) by exact (sub_preserves_exp _ _ _ _ _ _ HA' Hσ).
    assert (G ⊢ A'[Id,,M'] ≈ A'' : Type@i) by (eapply soundness_ty'; mauto 3).
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, G ⊢a A'' ⟹ Typeⁿ@j /\ j <= i) as [? []] by (gen_presups; mauto 3); firstorder.
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeⁿ@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    exists i.
    assert (G ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    assert (G ▹ ⊥ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    exact (sub_preserves_exp _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* G ⊢a efq M' return A' ⟹ A'' /\ (exists j, G ⊢a A'' ⟹ Typeⁿ@j) *)
    clear_defs.
    split; [mauto 3 |].
    assert (G ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    assert (G ▹ ⊥ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    assert (G ⊢ A'[Id,,M'] : Typeⁿ@i) by exact (sub_preserves_exp _ _ _ _ _ _ HA' Hσ).
    assert (G ⊢ A'[Id,,M'] ≈ A'' : Type@i) by (eapply soundness_ty'; mauto 3).
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, G ⊢a A'' ⟹ Typeⁿ@j /\ j <= i) as [? []] by (gen_presups; mauto 3); firstorder.
  Qed.

  Next Obligation. (* ⊢ G ▹ B *)
    clear_defs.
    assert (G ⊢ B : Type@i) by mauto 4 using alg_type_infer_sound.
    mauto 3.
  Qed.

  Next Obligation. (* G ⊢a Π B C ⟹ Typeⁿ@(max i j) /\ (exists k, G ⊢a Type@(max i j) ⟹ Typeⁿ@k) *)
    clear_defs.
    mautosolve 4.
  Qed.

  Next Obligation. (* ⊢ G ▹ A' *)
    clear_defs.
    assert (G ⊢ A' : Type@i) by mauto 4 using alg_type_infer_sound.
    mauto 3.
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G A' *)
    clear_defs.
    assert (G ⊢ A' : Type@i) as [? []]%soundness_ty by mauto 4 using alg_type_infer_sound.
    mauto 3 using nbe_ty_order_sound.
  Qed.

  Next Obligation. (* G ⊢a λ A' M' ⟹ Πⁿ A'' B' /\ (exists j, G ⊢a Π A'' B' ⟹ Typeⁿ@j) *)
    clear_defs.
    assert (G ⊢ A' : Type@i) by mauto 4 using alg_type_infer_sound.
    assert (G ⊢ A' ≈ A'' : Type@i) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (⊢ G ▹ A') by mauto 2.
    assert (G ⊢ A'' : Type@i) by (gen_presups; mauto 2).
    assert (⊢ G ▹ (A'' : exp)) by mauto 2.
    assert (G ▹ A' ⊢ B' : Type@H1) by mauto 4 using alg_type_infer_sound.
    assert (G ▹ (A'' : exp) ⊢ B' : Type@H1) by mauto 4.
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, G ⊢a A'' ⟹ Typeⁿ@j /\ j <= i) as [? []] by (gen_presups; mauto 3).
    assert (user_exp B') by trivial using user_exp_nf.
    assert (exists k, G ▹ (A'' : exp) ⊢a B' ⟹ Typeⁿ@k /\ k <= H1) as [? []] by (gen_presups; mauto 3).
    firstorder mauto 3.
  Qed.

  Next Obligation. (* exists i : nat, G ⊢ A : Type@i *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    eexists; mauto 4 using alg_type_infer_sound.
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G s[Id,,N'] *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    assert (G ⊢ A : Typeⁿ@i) by mauto 4 using alg_type_infer_sound.
    assert (G ▹ (A : exp) ⊢ s : Typeⁿ@j) by mauto 4 using alg_type_infer_sound.
    assert (G ⊢ N' : A) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ s[Id,,N'] : Typeⁿ@j) as [? []]%soundness_ty by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.

  Next Obligation. (* G ⊢a M' $ N' ⟹ B' /\ (exists i, G ⊢a B' ⟹ Typeⁿ@i) *)
    clear_defs.
    functional_alg_type_infer_rewrite_clear.
    progressive_inversion.
    split; [mauto 3 |].
    assert (G ⊢ A : Typeⁿ@i) by mauto 4 using alg_type_infer_sound.
    assert (G ▹ (A : exp) ⊢ s : Typeⁿ@j) by mauto 4 using alg_type_infer_sound.
    assert (G ⊢ s[Id,,N'] ≈ B' : Type@j) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (user_exp B') by trivial using user_exp_nf.
    assert (exists k, G ⊢a B' ⟹ Typeⁿ@k /\ k <= j) as [? []] by (gen_presups; mauto 3).
    firstorder.
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G A *)
    clear_defs.
    assert (exists i, G ⊢ A : Type@i) as [? [? []]%soundness_ty] by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.

  Next Obligation. (* G ⊢a #x ⟹ A' /\ (exists i, G ⊢a A' ⟹ Typeⁿ@i) *)
    clear_defs.
    assert (exists i, G ⊢ A : Type@i) as [i] by mauto 3.
    assert (G ⊢ A ≈ A' : Type@i) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (user_exp A') by trivial using user_exp_nf.
    assert (exists j, G ⊢a A' ⟹ Typeⁿ@j /\ j <= i) as [? []] by (gen_presups; mauto 4); firstorder mauto 3.
  Qed.


  Next Obligation. (* exists i, G ⊢ A' : Type@i *)
    clear_defs.
    eexists; mauto 4 using alg_type_infer_sound.
  Qed.

  Next Obligation. (* ⊢ G ▸ A' ≔ M' *)
    clear_defs.
    assert (G ⊢ A' : Type@i) by mauto 4 using alg_type_infer_sound.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    mauto 3.
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ A' : Type@i) by mauto 4 using alg_type_infer_sound.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (exists j, G ▸ A' ≔ M' ⊢ C : Type@j) as [j] by (eexists; mauto 4 using alg_type_infer_sound).
    assert (G ⊢ C[Id,,M'] : Type@j) as [? []]%soundness_ty by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.

  Next Obligation. (* G ⊢a ℓ A' ≔ M' in B' ⟹ D /\ (exists i, G ⊢a D ⟹ Typeⁿ@i) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ A' : Type@i) by mauto 4 using alg_type_infer_sound.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (exists j, G ▸ A' ≔ M' ⊢ C : Type@j) as [j] by (eexists; mauto 4 using alg_type_infer_sound).
    assert (G ⊢ C[Id,,M'] : Type@j) by mauto 3.
    assert (G ⊢ C[Id,,M'] ≈ D : Type@j) by (eapply soundness_ty'; mauto 3).
    assert (user_exp D) by trivial using user_exp_nf.
    assert (exists k, G ⊢a D ⟹ Typeⁿ@k /\ k <= j) as [? []] by (gen_presups; mauto 3).
    firstorder.
  Qed.

  Next Obligation. (* ⊢ G ▸ A ≔ M' *)
    clear_defs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    mauto 3.
  Qed.

  Next Obligation. (* nbe_ty_order gc_ctx G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (exists i, G ⊢ A : Type@i) as [i] by (gen_presups; eauto 2).
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (exists j, G ▸ A ≔ M' ⊢ C : Type@j) as [j] by (eexists; mauto 4 using alg_type_infer_sound).
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (G ⊢ C[Id,,M'] : Type@j) as [? []]%soundness_ty by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.

  Next Obligation. (* G ⊢a ℓ ≔ M' in B' ⟹ D /\ (exists i, G ⊢a D ⟹ Typeⁿ@i) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (exists i, G ⊢ A : Type@i) as [i] by (gen_presups; eauto 2).
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (exists j, G ▸ A ≔ M' ⊢ C : Type@j) as [j] by (eexists; mauto 4 using alg_type_infer_sound).
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (G ⊢ C[Id,,M'] : Type@j) by mauto 3.
    assert (G ⊢ C[Id,,M'] ≈ D : Type@j) by (eapply soundness_ty'; mauto 3).
    assert (user_exp D) by trivial using user_exp_nf.
    assert (exists k, G ⊢a D ⟹ Typeⁿ@k /\ k <= j) as [? []] by (gen_presups; mauto 3).
    firstorder.
  Qed.

  (** The obligations of the module cases. *)
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.

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
  Equations type_check_closed (Hg : ⊢g gc_ctx) A (HA : user_exp A) M (HM : user_exp M) : { ⋅ ⊢ M : A } + { ~ ⋅ ⊢ M : A } :=
  | Hg, A, HA, M, HM =>
      let*o->b (exist _ UA _) := type_infer ⋅ _ A _ while _ in
      let*o->b (exist _ i _) :=  get_level_of_type_nf UA while _ in
      let*b _ := type_check ⋅ A _ M _ while _ in
      pureb _
  .
  Next Obligation. (* False *)
    assert (⊢ ⋅) by mauto 2.
    assert (exists i, ⋅ ⊢ A : Type@i) as [i] by (gen_presups; eauto 2).
    assert (exists j, ⋅ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    firstorder.
  Qed.
  Next Obligation. (* False *)
    assert (exists i, ⋅ ⊢ A : Type@i) as [i] by (gen_presups; eauto 2).
    assert (exists j, ⋅ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    functional_alg_type_infer_rewrite_clear.
    intuition.
  Qed.
  Next Obligation. (* exists i, ⋅ ⊢ A : Type@i *)
    assert (⊢ ⋅) by mauto 2.
    assert (⋅ ⊢ A : Typeⁿ@i) by mauto 2 using alg_type_infer_sound.
    simpl in *.
    firstorder.
  Qed.
  Next Obligation. (* ⋅ ⊢ M : A *)
    assert (⊢ ⋅) by mauto 2.
    assert (⋅ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound.
    simpl in *.
    mauto 3 using alg_type_check_sound.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete : forall (Hg : ⊢g gc_ctx) A (HA : user_exp A) M (HM : user_exp M),
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
  Equations type_infer_closed (Hg : ⊢g gc_ctx) M (HM : user_exp M) : { A : nf | ⋅ ⊢ M : A } + { forall A, ~ ⋅ ⊢a M ⟹ A } :=
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
