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
    destruct A as [ i | c xs | | ? ? | | | | ? ? | ? ? | ? ? | ? ? ? | ? | ? ? | ? ? ? ? ];
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
    intros [b pv A [M |] | pm U | pvi Di Φi | ? ? ? ? | ? ? ?] [b' pv' A' [M' |] | pm' U' | pvi' Di' Φi' | ? ? ? ? | ? ? ?]; cbn;
      try (right; intros []; fail); try (left; exact I).
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

  (** ** Deciding What Module Expressions Denote

      What a module expression denotes is computed by [mdenote_impl], at
      the order a well-formed module expression, or a selection from one,
      has ([dn_order_of_wf], [dn_order_mem_of_wf]); a path has one
      outright.  The checker reads off the description what the rules ask
      for: a member's type ([ds_ty]), a module's telescope ([ds_mtele]) and
      module part ([ds_mod]). *)

  Definition mdenote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
      { R | mdenote gc_deps gc_stack Γ H R } + { forall R, ~ mdenote gc_deps gc_stack Γ H R } :=
    mdenote_impl gc_deps gc_stack Hg Γ H (dn_order_of_wf _ _ Hg _ _ _ HH).

  Definition mem_denote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H y (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
      { R | mdenote gc_deps gc_stack Γ (me_mem H y) R } + { forall R, ~ mdenote gc_deps gc_stack Γ (me_mem H y) R } :=
    mdenote_impl gc_deps gc_stack Hg Γ (me_mem H y) (dn_order_mem_of_wf _ _ Hg _ _ _ y HH).

  Definition path_denote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ fp :
      { R | mdenote gc_deps gc_stack Γ (me_unit fp) R } + { forall R, ~ mdenote gc_deps gc_stack Γ (me_unit fp) R } :=
    mdenote_impl gc_deps gc_stack Hg Γ (me_unit fp) (dno_path _ _ Γ fp).

  (** What a local open of a module generates. *)
  Definition items_gen_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H its (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
      { gs | items_gen gc_deps gc_stack false Γ H its gs } + { forall gs, ~ items_gen gc_deps gc_stack false Γ H its gs } :=
    items_gen_impl gc_deps gc_stack Hg false Γ H its (ig_order_of_wf _ _ Hg _ _ _ its HH).

  Equations ds_ty_dec (R : mdesc) : { A | ds_ty gc_deps gc_stack R = Some A } + { ds_ty gc_deps gc_stack R = None } :=
  ds_ty_dec R with inspect (ds_ty gc_deps gc_stack R) := {
    | exist _ (Some A) E => inleft (exist _ A E)
    | exist _ None E => inright E }.

  Equations ds_mtele_dec (R : mdesc) : { T | ds_mtele gc_deps gc_stack R = Some T } + { ds_mtele gc_deps gc_stack R = None } :=
  ds_mtele_dec R with inspect (ds_mtele gc_deps gc_stack R) := {
    | exist _ (Some T) E => inleft (exist _ T E)
    | exist _ None E => inright E }.

  Equations ds_mod_dec (R : mdesc) : { Rm | ds_mod gc_deps gc_stack R = Some Rm } + { ds_mod gc_deps gc_stack R = None } :=
  ds_mod_dec R with inspect (ds_mod gc_deps gc_stack R) := {
    | exist _ (Some Rm) E => inleft (exist _ Rm E)
    | exist _ None E => inright E }.

  (** The outermost parameter of an arity, if any. *)
  Equations tele_view_dec (T : ctx) : { B : typ & { T1 : ctx | tele_view T = Some (B, T1) } } + { tele_view T = None } :=
  tele_view_dec T with inspect (tele_view T) := {
    | exist _ (Some (B, T1)) E => inleft (existT _ B (exist _ T1 E))
    | exist _ None E => inright E }.

  Extraction Inline mdenote_dec mem_denote_dec path_denote_dec items_gen_dec ds_ty_dec ds_mtele_dec ds_mod_dec
    tele_view_dec.

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

  (** The type a member of a checked module expression is read at is a
      type ([member_wf]). *)
  Lemma member_typ_of_alg : forall G M x R A, ⊢ G -> G ⊢aᵐ M ->
      mdenote gc_deps gc_stack G (me_mem M x) R -> ds_ty gc_deps gc_stack R = Some A -> exists i, G ⊢ A : Typeω@i.
  Proof.
    intros * HG HM Hm Ht.
    exact (proj1 (member_wf _ _ _ _ _ (alg_modexp_sound HM HG) Hm Ht)).
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

  (** The reference value of the unit a module slot adds. *)
  Lemma tenv_ref_mod : forall G U p, ⊢ G ▹ₘ U -> initial_env gc_deps gc_stack G p ->
      exists h, ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ p ↘ h.
  Proof.
    intros * HGU Hp.
    assert (G ▹ₘ U ⊢ ⊤ : Typeω@0) as [W [HW _]]%soundness_ty by mauto 2.
    inversion HW as [? ? Hi _ _]; subst.
    inversion Hi; subst; functional_initial_env_rewrite_clear; eauto.
  Qed.

  Lemma tenv_eval_order_mod : forall G U p', ⊢ G ▹ₘ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      feval_modexp_order gc_deps gc_stack (me_lit U) p'.
  Proof.
    intros * HGU (p & Hp & Hag); destruct (tenv_ref_mod _ _ _ HGU Hp) as [h Hh].
    eapply (feval_modexp_of_ref _ _ _ _ _ _ Hh), agree_all, Hag.
  Qed.

  Lemma tenv_mod_sim : forall G U p' h', ⊢ G ▹ₘ U ->
      (exists p, initial_env gc_deps gc_stack G p /\ env_agree (fun _ => True) p p') ->
      ⟦ me_lit U ⟧ᵐᶠ gc_deps ⍮ gc_stack ⍮ p' ↘ h' ->
      exists p, initial_env gc_deps gc_stack (G ▹ₘ U) p /\ env_agree (fun _ => True) p (p' ↦ᵐ h').
  Proof.
    intros * HGU (p & Hp & Hag) Hh'; destruct (tenv_ref_mod _ _ _ HGU Hp) as [h Hh].
    pose proof (proj2 (feval_modexp_of_ref _ _ _ _ _ _ Hh (agree_all _ _ _ Hag)) _ Hh').
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ exact Hag | constructor; assumption | intros; exact I ].
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

  Definition tenv_mod G (P : tenv G) U (HGU : ⊢ G ▹ₘ U) : tenv (G ▹ₘ U) :=
    let (p, Hp) := P in
    let (h, Hh) := feval_modexp_impl gc_deps gc_stack (me_lit U) p (tenv_eval_order_mod G U p HGU Hp) in
    exist _ (p ↦ᵐ h) (tenv_mod_sim _ _ _ _ HGU Hp Hh).

  (** The initial environment of an extension [Ψ ++ G], from that of [G]:
      one entry more per entry of [Ψ], rather than all of [G]'s again. *)
  Fixpoint tenv_ext G (P : tenv G) (Ψ : ctx) {struct Ψ} : ⊢ Ψ ++ G -> tenv (Ψ ++ G) :=
    match Ψ as Ψ0 return ⊢ Ψ0 ++ G -> tenv (Ψ0 ++ G) with
    | nil => fun _ => P
    | ce_ass A :: Ψ' => fun H => tenv_ass (Ψ' ++ G) (tenv_ext G P Ψ' (ctx_decomp_tail H)) A H
    | ce_def A M :: Ψ' => fun H => tenv_def (Ψ' ++ G) (tenv_ext G P Ψ' (ctx_decomp_tail H)) A M H
    | ce_mod U :: Ψ' => fun H => tenv_mod (Ψ' ++ G) (tenv_ext G P Ψ' (ctx_decomp_tail H)) U H
    end.

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
  | ti_indty : forall {p k}, type_infer_order (a_ind p k)
  | ti_con : forall {p k c}, type_infer_order (a_con p k c)
  (** A numeral is expanded before it is checked; it has no type. *)
  | ti_nlit : forall {n}, type_infer_order (a_nlit n)
  | ti_ntok : type_infer_order a_ntok
  (** An eliminator: its scrutinee and the annotations and motives of its
      blocks infer, its uniform parameters and the branches are checked. *)
  | ti_elim : forall {oq Us m Bks M}, type_infer_order M ->
      (forall U, List.In U Us -> type_check_order U) ->
      (forall b Z, List.In b Bks -> eb_ann b = Some Z -> type_infer_order Z) ->
      (forall b, List.In b Bks -> type_infer_order (eb_motive b)) ->
      (forall b br, List.In b Bks -> List.In br (eb_brs b) -> type_check_order (snd br)) ->
      type_infer_order (a_elim oq Us m Bks M)
  | ti_pi : forall {A B}, type_infer_order A -> type_infer_order B -> type_infer_order Π A B
  | ti_fn : forall {A M}, type_infer_order A -> type_infer_order M -> type_infer_order λ A M
  | ti_app : forall {M N}, app_order M N -> type_infer_order (M $ N)
  | ti_let : forall {A M B}, type_infer_order A -> type_check_order M -> type_infer_order B -> type_infer_order (ℓ A ≔ M in B)
  | ti_let_infer : forall {M B}, type_infer_order M -> type_infer_order B -> type_infer_order (ℓ ≔ M in B)
  | ti_let_mod : forall {U B}, unit_order U -> type_infer_order B -> type_infer_order (ℓₘ U in B)
  | ti_mem : forall {H x}, modexp_order H -> type_infer_order (a_mem H x)
  | ti_vlookup : forall {x}, type_infer_order #x
  (** A record's type former recurses on nothing *)
  | ti_record : forall {p}, type_infer_order (a_record p)
  (** A tuple infers its annotation and checks its fields *)
  | ti_tuple : forall {T fs}, type_infer_order T -> (forall fm, List.In fm fs -> type_check_order (snd fm)) ->
      type_infer_order (a_tuple T fs)
  (** A projection infers its element *)
  | ti_proj : forall {f M}, type_infer_order M -> type_infer_order (a_proj f M)
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
  | uo_body : forall {Δ sm Φ}, ext_order Δ -> body_order Φ -> unit_order (gu_mk Δ (md_body sm Φ))
  | uo_alias : forall {Δ E}, ext_order Δ -> modexp_order E -> unit_order (gu_mk Δ (md_alias E))
  (** A body, entry by entry; an entry no body may hold has nothing to
      check. *)
  with body_order : gmod -> Prop :=
  | bo_nil : body_order gm_nil
  | bo_def : forall {Φ x b pv A M}, body_order Φ -> type_infer_order A -> type_check_order M ->
      body_order (gm_ext Φ x (ge_def b pv A (Some M)))
  | bo_mod : forall {Φ x pm U}, body_order Φ -> unit_order U -> body_order (gm_ext Φ x (ge_mod pm U))
  | bo_axiom : forall {Φ x b pv A}, body_order Φ -> body_order (gm_ext Φ x (ge_def b pv A None))
  | bo_ind : forall {Φ x pv p k D Φi}, body_order Φ -> body_order (gm_ext Φ x (ge_ind pv p k D Φi))
  (** A definition with a module part: filed only, held by no body *)
  | bo_def_mod : forall {Φ x pv A M U}, body_order Φ -> body_order (gm_ext Φ x (ge_def_mod pv A M U))
  (** A record declaration: as written in no local body, only the entries
      before it *)
  | bo_record : forall {Φ x pv pr R Φr}, body_order Φ -> body_order (gm_ext Φ x (ge_record pv pr R Φr))
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

  (** Every term has an order. *)
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
           | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
           | ge_mod _ U => unit_order U
           | ge_ind _ _ _ _ _ | ge_def_mod _ _ _ _ | ge_record _ _ _ _ => True
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
             | ge_def _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
             | ge_mod _ U => unit_order U
             | ge_ind _ _ _ _ _ | ge_def_mod _ _ _ _ | ge_record _ _ _ _ => True
             end)
      centry_order); intros; cbn in *; destruct_conjs; eauto 6 with mctt.
    (* a tuple: its fields are checked *)
    all: try match goal with HF : List.Forall _ ?fs |- type_infer_order (a_tuple _ ?fs) =>
           rewrite List.Forall_forall in HF; constructor; [ assumption | intros fm Hfm; apply tc_ti; auto ] end.
    - (* an eliminator: its uniform parameters and branches are checked *)
      match goal with
      | HU : List.Forall _ ?Us, HB : List.Forall _ ?Bks |- type_infer_order (a_elim _ ?Us _ ?Bks _) =>
          rewrite List.Forall_forall in HU, HB
      end.
      constructor; [ assumption | intros U HU'; apply tc_ti; auto
                   | intros b Z Hb HZ; match goal with HB : forall x, List.In x _ -> _ |- _ => exact (proj1 (HB b Hb) Z HZ) end
                   | intros b Hb; match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ => exact (proj1 (proj2 (HB b Hb))) end
                   | intros b br Hb Hbr; apply tc_ti;
                     match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ =>
                       exact (proj1 (List.Forall_forall _ _) (proj2 (proj2 (HB b Hb))) br Hbr) end ].
    - (* a local binding *)
      destruct b as [[A |] M | U]; destruct_conjs;
        [ apply ti_let; [ eauto | constructor; assumption | assumption ]
        | apply ti_let_infer; assumption
        | apply ti_let_mod; assumption ].
    - destruct D; destruct_conjs; constructor; auto using ext_order_of_forall.
    - destruct E as [b pv A [M |] | pm U | pvi pk ki Di Φi | ? ? ? ? | ? ? ?]; destruct_conjs;
        first [ apply bo_def; eauto with mctt | apply bo_mod; assumption
              | apply bo_axiom; assumption | apply bo_ind; assumption | apply bo_def_mod; assumption
              | apply bo_record; assumption ].
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
        let T := constr:(G ⊢ A : a_typ (unf_large u)) in
        assert_fails (assert T by assumption);
        assert (G ⊢ A : unf_tm u)
          by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              eapply alg_type_infer_sound; [ exact Ha | ctx_wf_tac ]);
        assert T by (apply wf_exp_unf_large; eassumption)
    | HnC : nbe_ty _ _ (?G ▹ ?A) _ ?UB', Hv : is_univ_nf ?UB' ?v,
      HC : ?G ▹ ?A ⊢a ?B ⟹ ?UB, HB : ?G ⊢a ?A ⟹ ?UA, Hu : is_univ_nf ?UA _ |- _ =>
        (** A codomain whose universe was normalised ([ati_pi]): its
            typing at the large level of the normal form's index. *)
        let T := constr:(G ▹ A ⊢ B : a_typ (unf_large v)) in
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

Ltac negc :=
  match goal with
  | Hx : _ ⊢aˣ (_ :: _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵘ (gu_mk _ _) |- False => inversion Hx; subst
  | Hx : _ ⊢aᵐ (_ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
  | Hx : _ ⊢aᵐ (_ _ _) |- False => inversion Hx; subst; try (cbn in *; congruence)
  end;
  functional_alg_type_infer_rewrite_clear;
  md_unify;
  first [ match goal with H : forall u : unf, ?X <> univ_nf u |- _ => exact (H _ eq_refl) end
        | congruence
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ]
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

(** ** The Obligations of the Module Cases

    One tactic per kind of obligation; each obligation below names the one
    that proves it. *)

(** A loaded unit: what it denotes, and that is a module. *)
Ltac mo_2 :=
  clear_defs; destruct_conjs;
  solve [ eapply amod_unit; eassumption ].

(** A failure of a selection or an application: its rule's premises are
    read off what it denotes. *)
Ltac mo_3 :=
  clear_defs; destruct_conjs;
  solve [ negc ].

(** The type a member is read at is a type. *)
Ltac mo_7 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : mdenote _ _ ?G (me_mem ?M _) _, Ht : ds_ty _ _ _ = Some ?A
                |- nbe_ty_order _ _ ?G ?A =>
                  destruct (member_typ_of_alg _ _ _ _ _ HG HM Hm Ht) as [? ?];
                  eapply nbe_order_of_typ; eassumption
              end ].

(** A member infers the normal form of that type. *)
Ltac mo_8 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : mdenote _ _ ?G (me_mem ?M _) _, Ht : ds_ty _ _ _ = Some ?A,
                Hn : nbe_ty_f ?G ?A _ |- _ =>
                  destruct (member_typ_of_alg _ _ _ _ _ HG HM Hm Ht) as [? ?]
              end;
              split; [ eapply ati_mem; eassumption | eapply level_of_nbe; eassumption ] ].

Ltac mo_10 :=
  clear_defs; destruct_conjs;
  solve [ negc ].

Ltac mo_14 :=
  clear_defs; destruct_conjs;
  solve [ typ_sound ].

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
  solve [ negc ].

(** The outermost parameter of a checked module expression is a type
    ([mtele_head_wf]). *)
Ltac mo_22 :=
  clear_defs; destruct_conjs;
  solve [ match goal with
              | HG : ⊢ ?G, HM : ?G ⊢aᵐ ?M, Hm : mdenote _ _ ?G ?M _, Ht : ds_mtele _ _ _ = Some ?T,
                Hv : tele_view ?T = Some (?B, _) |- exists i, ?G ⊢ ?B : Typeω@i =>
                  exact (mtele_head_wf _ _ _ _ _ _ (alg_modexp_sound HM HG) Hm Ht Hv)
              end ].

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

(** The orders of the parts of an eliminator: its scrutinee, a uniform
    parameter, and an annotation, a motive or a branch of a block. *)
Ltac ob_ord_elim :=
  clear_defs;
  match goal with H : type_infer_order (a_elim _ _ _ _ _) |- _ => progressive_invert H end;
  first
    [ eassumption
    | match goal with Hall : forall _ : _, _ |- _ => solve [ eapply Hall; eassumption ] end ].

(** The orders of the parts of a tuple and of a projection: the annotation
    or a field, the element. *)
Ltac ob_ord_record :=
  clear_defs;
  match goal with
  | H : type_infer_order (a_tuple _ _) |- _ => progressive_invert H
  | H : type_infer_order (a_proj _ _) |- _ => progressive_invert H
  end;
  first
    [ eassumption
    | match goal with Hall : forall _ : _, _ |- _ => solve [ eapply Hall; eassumption ] end ].

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
  simpl_let_guards;
  destruct_conjs;
  functional_alg_type_infer_rewrite_clear;
  first [ contradiction | solve [ eauto 2 ] | congruence | solve [ firstorder ] ].

(** A failure branch of a member: the member's inference is inverted, and
    each rule it could come from contradicts the branch's premises. *)
Ltac ob_mem_neg :=
  clear_defs;
  lazymatch goal with H : _ ⊢a a_mem _ _ ⟹ _ |- False => inversion H; subst; clear H end;
  md_unify;
  first [ contradiction
        | congruence
        | solve [ match goal with HN : forall _, ~ _ |- _ => eapply HN; eassumption end ] ].

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
    | Hu : _ ⊢aᵘ gu_mk _ (md_body _ _) |- _ => inversion Hu; subst; clear Hu
    end;
  repeat match goal with
    | H1 : ?G ⊢aᵇ ?Φ ⇝ ?X, H2 : ?G ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
        assert_fails constr_eq X Y; pose proof (alg_body_functional ltac:(gctx_wf_tac) H1 H2); subst Y; clear H2
    end;
  functional_alg_type_infer_rewrite_clear;
  md_unify;
  first [ contradiction
        | solve [ firstorder ]
        | congruence
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
