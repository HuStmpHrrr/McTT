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

  Definition entry_shape_dec : forall E E', { entry_shape E E' } + { ~ entry_shape E E' }.
  Proof.
    intros [b pv A [M |] | U] [b' pv' A' [M' |] | U']; cbn; try (right; intros []; fail); try (left; exact I).
    destruct b, b', (Bool.bool_dec pv pv'); try (right; intuition congruence; fail); left; auto.
  Defined.

  Definition check_shape_dec : forall c c', { check_shape c c' } + { ~ check_shape c c' }.
  Proof.
    intros [E ns | M A] [E' ns' | M' A']; cbn; try (right; intros []; fail).
    apply list_eq_dec, string_dec.
  Defined.

  Definition body_shape_dec : forall Φ Φ', { body_shape Φ Φ' } + { ~ body_shape Φ Φ' }.
  Proof.
    induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c']; cbn;
      try (left; exact I); try (right; intros []; fail).
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (string_dec x x') as [H2 | H2]; [| right; intuition ].
      destruct (entry_shape_dec E E') as [H3 | H3]; [ left; auto | right; intuition ].
    - destruct (IH Φ') as [H1 | H1]; [| right; intuition ].
      destruct (check_shape_dec c c') as [H2 | H2]; [ left; auto | right; intuition ].
  Defined.

  (** ** Deciding Member Types *)

  Definition member_type_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ H ch k
      (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
      { A | member_type gc_deps gc_stack Γ H ch k A } + { forall A, ~ member_type gc_deps gc_stack Γ H ch k A } :=
    member_type_impl gc_deps gc_stack (gctx_closed_of_wf _ _ Hg) Γ H ch k (mt_order_of_wf _ _ _ _ Hg HH ch k).

  Definition member_type_path_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ pq :
      { A | member_type gc_deps gc_stack Γ (me_path pq) nil mk_mod A } +
      { forall A, ~ member_type gc_deps gc_stack Γ (me_path pq) nil mk_mod A } :=
    member_type_impl gc_deps gc_stack (gctx_closed_of_wf _ _ Hg) Γ (me_path pq) nil mk_mod
      (mt_order_path _ _ _ _ _ _ Hg).

  Definition member_ok_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ E n
      (HE : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ E ≈ E) :
      { member_ok gc_deps gc_stack Γ E n } + { ~ member_ok gc_deps gc_stack Γ E n }.
  Proof.
    destruct (member_type_dec Hg Γ E (n :: nil) mk_term HE) as [[A HA] | HN1]; [ left; left; eauto |].
    destruct (member_type_dec Hg Γ E (n :: nil) mk_mod HE) as [[A HA] | HN2]; [ left; right; eauto |].
    right; intros [[A HA] | [A HA]]; [ exact (HN1 _ HA) | exact (HN2 _ HA) ].
  Defined.

  Definition names_ok_dec (Hg : ⊢g gc_deps ⍮ gc_stack) Γ E
      (HE : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ E ≈ E) :
      forall ns, { forall n, In n ns -> member_ok gc_deps gc_stack Γ E n } +
                 { ~ (forall n, In n ns -> member_ok gc_deps gc_stack Γ E n) }.
  Proof.
    induction ns as [| n ns IH]; [ left; intros ? [] |].
    destruct (member_ok_dec Hg Γ E n HE) as [Hn | Hn]; [| right; intros Hall; apply Hn, Hall; left; reflexivity ].
    destruct IH as [Hns | Hns]; [ left; intros ? [<- | Hin]; auto | right; intros Hall; apply Hns; intros; apply Hall; right; assumption ].
  Defined.

  Definition imports_ok (G Δ : ctx) (ls : list (gmod * bcheck)) : Prop :=
    (forall Φ0 E ns, In (Φ0, bc_import E ns) ls -> body_ctx Φ0 ++ Δ ++ G ⊢aᵐ E) /\
    (forall Φ0 E ns n, In (Φ0, bc_import E ns) ls -> In n ns ->
       member_ok gc_deps gc_stack (body_ctx Φ0 ++ Δ ++ G) E n).

  Extraction Inline member_type_dec member_type_path_dec.

  (** ** Facts the Obligations Use *)

  Lemma nbe_order_of_typ : forall G X i, G ⊢ X : Type@i -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * HX; destruct (soundness_ty HX) as [W [HW _]]; eauto using nbe_ty_order_sound. Qed.

  Lemma level_of_nbe : forall G X i D, G ⊢ X : Type@i -> nbe_ty_f G X D -> exists j, G ⊢a D ⟹ Typeⁿ@j.
  Proof.
    intros * HX HD.
    assert (G ⊢ X ≈ D : Type@i) by (eapply soundness_ty'; eassumption).
    assert (G ⊢ D : Type@i) by (gen_presups; eassumption).
    destruct (alg_type_infer_typ_complete (user_exp_nf D) ltac:(eassumption)) as [j [Hj _]]; eauto.
  Qed.

  Lemma member_typ_of_alg : forall G M ch k A, ⊢ G -> G ⊢aᵐ M ->
      member_type gc_deps gc_stack G M ch k A -> (k = mk_term -> ch <> nil) -> exists i, G ⊢ A : Type@i.
  Proof.
    intros * HG HM Hm Hch.
    exact (proj1 (proj1 member_wf _ _ _ _ _ Hm (alg_modexp_sound HM HG) Hch)).
  Qed.

  Lemma let_mod_typ_of_alg : forall G U C i, ⊢ G -> G ⊢aᵘ U -> G ▹ₘ U ⊢a C ⟹ Typeⁿ@i ->
      G ⊢ C[Id ,,ₘ me_lit U] : Type@i.
  Proof.
    intros * HG HU HC.
    pose proof (alg_unit_sound HU HG) as HU'.
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU').
    assert (HCt : G ▹ₘ U ⊢ C : Typeⁿ@i) by (eapply alg_type_infer_sound; eassumption).
    exact (sub_preserves_exp _ _ _ _ _ _ _ HCt (wf_sub_single_mod _ _ _ _ HU')).
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
  | ti_let_mod : forall {U B}, unit_order U -> type_infer_order B -> type_infer_order (ℓₘ U in B)
  (** A member of an applied module recurses into its root's member applied,
      which is not a subterm. *)
  | ti_mem : forall {H x}, modexp_order H ->
      (forall R args pre, modexp_spine H = (R, args, pre) -> args <> nil ->
         type_infer_order (apps (member_ref R (pre ++ x :: nil)) args)) ->
      type_infer_order (a_mem H x)
  | ti_vlookup : forall {x}, type_infer_order #x
  (** A global is read off the global context without recursion; the
      obligations obtain the normal form of its resolved type from the
      well-formedness of [G]. *)
  | ti_glob : forall {pth}, type_infer_order (a_glob pth)
  with ext_order : ctx -> Prop :=
  | eo_nil : ext_order nil
  | eo_ass : forall {A Ψ}, ext_order Ψ -> type_infer_order A -> ext_order (Ψ ▹ A)
  | eo_def : forall {A M Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> ext_order (Ψ ▸ A ≔ M)
  | eo_mod : forall {U Ψ}, ext_order Ψ -> unit_order U -> ext_order (Ψ ▹ₘ U)
  with unit_order : gunit -> Prop :=
  | uo_body : forall {Δ Φ}, ext_order (body_ctx Φ ++ Δ) -> imports_order (gm_checks Φ) -> unit_order (gu_body Δ Φ)
  | uo_alias : forall {Δ E}, ext_order Δ -> modexp_order E -> unit_order (gu_mk Δ (md_alias E))
  with imports_order : list (gmod * bcheck) -> Prop :=
  | io_nil : imports_order nil
  | io_import : forall {Φ0 E ns ls}, modexp_order E -> imports_order ls -> imports_order ((Φ0, bc_import E ns) :: ls)
  | io_eval : forall {Φ0 M A ls}, imports_order ls -> imports_order ((Φ0, bc_eval M A) :: ls)
  with modexp_order : modexp -> Prop :=
  | mo_path : forall {pq}, modexp_order (me_path pq)
  | mo_var : forall {x}, modexp_order (me_var x)
  | mo_lit : forall {U}, unit_order U -> modexp_order (me_lit U)
  | mo_mem : forall {H y}, modexp_order H -> modexp_order (me_mem H y)
  | mo_app : forall {H N}, modexp_order H -> type_check_order N -> modexp_order (me_app H N)
  .

  #[local]
  Hint Constructors type_check_order type_infer_order ext_order unit_order imports_order modexp_order : mctt.

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
    (forall b, match b with b_def A M => type_infer_order A /\ type_infer_order M | b_mod U => unit_order U end) /\
    (forall U, unit_order U) /\
    (forall D, match D with
           | md_body Φ => List.Forall centry_order (body_ctx Φ) /\ imports_order (gm_checks Φ)
           | md_alias E => modexp_order E
           end) /\
    (forall Φ, List.Forall centry_order (body_ctx Φ) /\ imports_order (gm_checks Φ)) /\
    (forall c, match c with bc_import E _ => modexp_order E | bc_eval _ _ => True end) /\
    (forall E, match E with
           | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
           | ge_mod U => unit_order U
           end) /\
    (forall e, centry_order e).
  Proof.
    apply (syn_mut_ind type_infer_order
      (fun H => modexp_order H /\
         forall R args pre, modexp_spine H = (R, args, pre) -> modexp_order R /\ List.Forall type_check_order args)
      (fun b => match b with b_def A M => type_infer_order A /\ type_infer_order M | b_mod U => unit_order U end)
      unit_order
      (fun D => match D with
             | md_body Φ => List.Forall centry_order (body_ctx Φ) /\ imports_order (gm_checks Φ)
             | md_alias E => modexp_order E
             end)
      (fun Φ => List.Forall centry_order (body_ctx Φ) /\ imports_order (gm_checks Φ))
      (fun c => match c with bc_import E _ => modexp_order E | bc_eval _ _ => True end)
      (fun E => match E with
             | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
             | ge_mod U => unit_order U
             end)
      centry_order); intros; cbn in *; destruct_conjs; eauto 6 with mctt.
    - (* a local binding *)
      destruct b; destruct_conjs; [ apply ti_let; [| constructor |]; assumption | apply ti_let_mod; assumption ].
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
    - destruct E as [b pv A [M |] | U]; destruct_conjs; (split; [| assumption ]); constructor; cbn; eauto with mctt.
    - split; [ assumption | destruct c; constructor; assumption ].
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
    destruct syn_orders_all as (_ & _ & _ & _ & _ & _ & _ & _ & Hc); apply Hc.
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
    | |- ⊢ body_ctx ?Φ0 ++ ?Δ ++ ?G =>
        match goal with Hls : forall Φ c, In (Φ, c) _ -> ⊢ body_ctx Φ ++ Δ ++ G |- _ =>
          eapply Hls; left; reflexivity end
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
      | H: imports_order _ |- _ => progressive_invert H
      | H: modexp_order _ |- _ => progressive_invert H
      end;
    destruct_conjs;
    match goal with
    | |- ⊢ _ => first [ solve [ ctx_wf_tac ] | solve [ mauto 3 ] ]
    | |- ⊢g _ ⍮ _ => eapply ctx_wf_gctx; eassumption
    | |- wf_modexp_eq _ _ ?G ?M ?M =>
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
    | |- imports_order _ => eassumption; fail 1
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
    | Hx : _ ⊢aᵐ (_ _) |- False => inversion Hx; subst
    | Hx : _ ⊢aᵐ (_ _ _) |- False => inversion Hx; subst
    end;
    functional_alg_type_infer_rewrite_clear;
    first [ match goal with H : forall i, ?X <> Typeⁿ@i |- _ => exact (H _ eq_refl) end | firstorder ].

  #[local]
  Ltac imp_neg :=
    match goal with Hi : imports_ok _ _ _ |- False => destruct Hi end;
    match goal with
    | HN : ~ _ ⊢aᵐ _, Hi1 : forall Φ0 E ns, In _ _ -> _ |- _ => apply HN; eapply Hi1; left; reflexivity
    | HN : ~ (forall n, In n _ -> _), Hi2 : forall Φ0 E ns n, In _ _ -> In n ns -> _ |- _ =>
        apply HN; intros; eapply Hi2; [ left; reflexivity | eassumption ]
    | HN : ~ imports_ok _ _ _, Hi1 : forall Φ0 E ns, In _ _ -> _, Hi2 : forall Φ0 E ns n, In _ _ -> In n ns -> _ |- _ =>
        apply HN; split; intros; [ eapply Hi1; right; eassumption | eapply Hi2; [ right; eassumption | eassumption ] ]
    end.

  #[local]
  Ltac imp_pos :=
    match goal with Hr : imports_ok _ _ _ |- imports_ok _ _ _ => destruct Hr end;
    split;
    let Hin := fresh "Hin" in
    let Heq := fresh "Heq" in
    intros * Hin; destruct Hin as [Heq | Hin]; try (injection Heq; intros; subst); eauto; try discriminate.

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
      | H1 : member_type ?T ?X ?G ?M ?c ?k ?A1, H2 : member_type ?T ?X ?G ?M ?c ?k ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (member_type_functional _ _) _ _ _ _ _ H1 _ H2); subst; clear H2
      end.

  #[local]
  Ltac mod_obl :=
    clear_defs; destruct_conjs;
    first
      [ solve [ eapply nbe_order_of_typ, let_mod_typ_of_alg; eassumption ]
      | solve [ split; [ eapply ati_let_mod; eassumption
                       | eapply level_of_nbe; [ eapply let_mod_typ_of_alg; eassumption | eassumption ] ] ]
      | solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M _ _ ?A |- nbe_ty_order _ _ ?G ?A =>
                    destruct (member_typ_of_alg _ _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?];
                    eapply nbe_order_of_typ; eassumption
                end ]
      | solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M _ _ ?A, Hn : nbe_ty_f ?G ?A _ |- _ =>
                    destruct (member_typ_of_alg _ _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [? ?]
                end;
                split; [ eapply ati_mem; [ eapply spine_nil_noargs; eassumption | eassumption | eassumption | eassumption ]
                       | eapply level_of_nbe; eassumption ] ]
      | solve [ split; [ eapply ati_mem_app; [ eassumption | eassumption | discriminate | eassumption ] | eauto ] ]
      | solve [ negc ]
      | solve [ imp_neg ]
      | solve [ imp_pos ]
      | solve [ split; intros * [] ]
      | solve [ match goal with Hi : imports_ok _ _ _ |- _ ⊢aᵘ _ => destruct Hi end; eapply aunit_body; eassumption ]
      | solve [ econstructor; eassumption ]
      | solve [ econstructor; eauto ]
      | solve [ typ_sound ]
      | solve [ ctx_wf_tac ]
      | solve [ intros; match goal with Hls : forall Φ c, _ \/ _ -> _ |- _ => eapply Hls; right; eassumption end ]
      | solve [ eapply ctx_wf_gctx; ctxp ]
      | solve [ eapply alg_modexp_sound; [ eassumption | ctxp ] ]
      | solve [ econstructor; apply ctx_find_mod_sound; eassumption ]
      | solve [ match goal with Hx : _ ⊢aᵐ me_var _ |- False => inversion Hx; subst end;
                match goal with Hl : ctx_lookup_mod _ _ _ |- _ => apply ctx_find_mod_complete in Hl end; congruence ]
      | solve [ match goal with
                | HG : ⊢ ?G, Hin : In (?Φ0, _) (gm_checks ?Φ), Ha : ?G ⊢aˣ body_ctx ?Φ ++ ?Δ |- _ =>
                    let Ψ0 := fresh "Ψ0" in
                    let HΨ0 := fresh "HΨ0" in
                    let HC := fresh "HC" in
                    destruct (gm_checks_body_ctx _ _ _ Hin) as [Ψ0 HΨ0];
                    pose proof (ext_eq_ctx_left _ _ _ _ _ (alg_ext_sound Ha HG)) as HC;
                    rewrite HΨ0, <- !app_assoc in HC; exact (ctx_app_wf_right _ _ _ _ HC)
                end ]
      | solve [ match goal with Hx : _ ⊢aᵐ me_app _ _ |- False => inversion Hx; subst end;
                mt_unify; functional_nbe_rewrite_clear;
                first [ match goal with H0 : forall B C, _ <> Πⁿ B C |- _ => eapply H0; reflexivity end
                      | match goal with Heq : Πⁿ _ _ = Πⁿ _ _ |- _ => injection Heq; intros; subst end; eauto ] ]
      | solve [ match goal with
                | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : member_type _ _ ?G ?M nil mk_mod ?A,
                  Hn : nbe_ty_f ?G ?A (Πⁿ ?B ?s) |- exists i, ?G ⊢ _ : Type@i =>
                    let i := fresh "i" in
                    let HA := fresh "HA" in
                    destruct (member_typ_of_alg _ _ _ _ _ HG HM Hm ltac:(intros; discriminate)) as [i HA];
                    assert (G ⊢ A ≈ Πⁿ B s : Type@i) by (eapply soundness_ty'; eassumption);
                    let HΠ := fresh "HΠ" in
                    assert (HΠ : G ⊢ Π B s : Type@i) by (gen_presups; eassumption);
                    let HB := fresh "HB" in
                    destruct (wf_pi_inversion' HΠ) as [HB _]; eauto
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
        let (A'', _) := nbe_ty_impl gc_deps gc_stack G A'[Id,,M'] _ in
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
        let (A'', _) := nbe_ty_impl gc_deps gc_stack G A'[Id,,M'] _ in
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
        let*o (exist _ i _) :=  get_level_of_type_nf UA' while _ in
        let*b->o _ := type_check G A' _ M' _ while _ in
        let*o (exist _ C _) := type_infer (G ▸ A' ≔ M') _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_deps gc_stack G (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let*o (exist _ C _) := type_infer (G ▹ₘ U) _ B' _ while _ in
        let (D, _) := nbe_ty_impl gc_deps gc_stack G (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    | a_mem M' x with inspect (modexp_spine M') => {
      | exist _ (R, nil, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := member_type_dec _ G M' (x :: nil) mk_term _ while _ in
          let (B, _) := nbe_ty_impl gc_deps gc_stack G A _ in
          pureo (exist _ B _)
      | exist _ (R, N :: args, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := type_infer G HG (apps (member_ref R (pre ++ x :: nil)) (N :: args)) _ while _ in
          pureo (exist _ A _) }
    | #x =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let (A', _) := nbe_ty_impl gc_deps gc_stack G A _ in
        pureo (exist _ A' _)
    (** A global infers the closed type that resolution returns for it,
        normalized at [G]. *)
    | a_glob pth with inspect (gc_resolve gc_deps gc_stack pth) => {
      | exist _ (Some (ge_def b pv A B)) _ =>
          let (C, _) := nbe_ty_impl gc_deps gc_stack G A _ in
          pureo (exist _ C _)
      | exist _ _ _ => inright _
      }
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
  | G, HG, gu_mk Δ (md_body Φ), H =>
      let*b _ := ext_check G HG (body_ctx Φ ++ Δ) _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      let*b _ := imports_check G Δ (gm_checks Φ) _ _ while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := modexp_check (Δ ++ G) _ E _ while _ in
      pureb _
  with imports_check G Δ ls (Hls : forall Φ0 c, In (Φ0, c) ls -> ⊢ body_ctx Φ0 ++ Δ ++ G) (H : imports_order ls) :
      { imports_ok G Δ ls } + { ~ imports_ok G Δ ls } by struct H :=
  | G, Δ, nil, Hls, H => left _
  | G, Δ, (Φ0, bc_import E ns) :: ls, Hls, H =>
      let*b _ := modexp_check (body_ctx Φ0 ++ Δ ++ G) _ E _ while _ in
      let*b _ := names_ok_dec _ (body_ctx Φ0 ++ Δ ++ G) E _ ns while _ in
      let*b _ := imports_check G Δ ls _ _ while _ in
      pureb _
  | G, Δ, (Φ0, bc_eval M A) :: ls, Hls, H =>
      let*b _ := imports_check G Δ ls _ _ while _ in
      pureb _
  with modexp_check G (HG : ⊢ G) M (H : modexp_order M) : { G ⊢aᵐ M } + { ~ G ⊢aᵐ M } by struct H :=
  | G, HG, me_path pq, H =>
      let*o->b (exist _ A _) := member_type_path_dec _ G pq while _ in
      pureb _
  | G, HG, me_var x, H with inspect (ctx_find_mod G x) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_lit U, H =>
      let*b _ := unit_check G HG U _ while _ in
      pureb _
  | G, HG, me_mem M y, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ A _) := member_type_dec _ G M (y :: nil) mk_mod _ while _ in
      pureb _
  | G, HG, me_app M N, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ A _) := member_type_dec _ G M nil mk_mod _ while _ in
      let (W, _) := nbe_ty_impl gc_deps gc_stack G A _ in
      let*o->b (existT _ B (exist _ C _)) := get_subterms_of_pi_nf W while _ in
      let*b _ := type_check G (B : nf) _ N _ while _ in
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
    exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* exists j, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Type@i *)
    clear_defs.
    exists i.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▹ ℕ ▹ A') by mauto 2.
    assert (G ▹ ℕ ▹ A' ⊢s Wk ⨟ Wk,,succ #1 : G ▹ ℕ) as Hσ by mauto 3.
    exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeⁿ@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    exists i.
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* G ⊢a rec M' return A' | zero -> MZ | succ -> MS end ⟹ A'' /\ (exists j, G ⊢a A'' ⟹ Typeⁿ@j) *)
    clear_defs.
    split; [mauto 3 |].
    assert (G ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    assert (G ▹ ℕ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    assert (G ⊢ A'[Id,,M'] : Typeⁿ@i) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ).
    assert (G ⊢ A'[Id,,M'] ≈ A'' : Type@i) by (eapply soundness_ty'; mauto 3).
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, G ⊢a A'' ⟹ Typeⁿ@j /\ j <= i) as [? []] by (gen_presups; mauto 3); firstorder.
  Qed.

  Next Obligation. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeⁿ@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    exists i.
    assert (G ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    assert (G ▹ ⊥ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ).
  Qed.

  Next Obligation. (* G ⊢a efq M' return A' ⟹ A'' /\ (exists j, G ⊢a A'' ⟹ Typeⁿ@j) *)
    clear_defs.
    split; [mauto 3 |].
    assert (G ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    assert (G ▹ ⊥ ⊢ A' : Typeⁿ@i) as HA' by mauto 3 using alg_type_infer_sound.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    assert (G ⊢ A'[Id,,M'] : Typeⁿ@i) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ).
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

  Next Obligation. (* nbe_ty_order gc_deps gc_stack G A' *)
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

  Next Obligation. (* nbe_ty_order gc_deps gc_stack G s[Id,,N'] *)
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

  Next Obligation. (* nbe_ty_order gc_deps gc_stack G A *)
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

  (** ** The Global Cases

      The obligations of [a_glob] reduce to one fact, that the type
      resolution returns is a type at [G], or, when nothing resolves, to an
      inversion.  [glob_obl] does not depend on the order in which [Equations]
      presents them. *)

  #[local]
  Ltac resolved_typ :=
    match goal with
    | Hr : gc_resolve _ _ _ = Some (ge_def _ _ _ _) |- _ =>
        eapply wf_glob_typ; [ eassumption | exact Hr ]
    end.

  #[local]
  Ltac glob_obl :=
    clear_defs;
    first
      [ match goal with
        | |- nbe_ty_order _ _ ?G ?X =>
            enough (exists i, G ⊢ X : Type@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
              by eauto 3 using nbe_ty_order_sound;
            resolved_typ
        end
      | match goal with
        | |- _ /\ _ =>
            split; [ mauto 3 |];
            match goal with
            | _ : nbe_ty gc_deps gc_stack ?G ?X ?C |- _ =>
                assert (exists i, G ⊢ X : Type@i) as [i HX] by resolved_typ;
                assert (G ⊢ X ≈ C : Type@i) by (eapply soundness_ty'; mauto 3);
                assert (user_exp C) by trivial using user_exp_nf;
                assert (exists j, G ⊢a C ⟹ Typeⁿ@j /\ j <= i) as [? []] by (gen_presups; mauto 3);
                firstorder
            end
        end
      | (* nothing resolves, so nothing is inferred *)
        repeat intro;
        match goal with
        | H : _ ⊢a a_glob _ ⟹ _ |- _ => inversion H; subst; congruence
        end ].

  Next Obligation. glob_obl. Qed.
  Next Obligation. glob_obl. Qed.
  Next Obligation. glob_obl. Qed.
  Next Obligation. glob_obl. Qed.

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

  Next Obligation. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
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
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.
  Next Obligation. mod_obl. Qed.

  Extraction Inline type_check_functional type_infer_functional ext_check_functional
    unit_check_functional imports_check_functional modexp_check_functional.

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
