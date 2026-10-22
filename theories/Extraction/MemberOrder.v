(** * Every Module Expression Has a Termination Order

    [MemberType.mdenote_impl] decides what a module expression [H]
    denotes in a context [Γ], by recursion on a termination order
    [dn_order Θ Ξ Γ H].  Typing gives that order ([dn_order_of_wf]), but
    the resolution of an eliminator's annotation ([site_resolves], in
    [Core.Syntactic.Builtin]) reads module expressions that are not typed:
    the binders of the terms around are holes.  This file proves that,
    in a well-formed global context, *every* module expression has the
    order, in *every* context ([dn_order_all]), with no condition on the
    context and no typing, and so discharges the interface [site_search]
    of [Extraction.Command].

    The measure.  What [mdenote] produces at an open module is a
    description [ds_open Δ Φw Φx] whose entries it later reads.  Each such
    description is one of three kinds ([denotation_classified]):
    - it comes from a stored (filed, closed) module: the validity of the
      global context gives each of its entries a finite derivation, so an
      order ([stored_entry_order]);
    - it is a typed open description ([typed_open]): its module entries
      are typed units moved along a substitution that keeps module slots,
      and a typed unit denotes, so it has an order
      ([typed_instance_order]);
    - otherwise it is no bigger than the module expression it came from,
      for the unfolded size [modexp_size] of module syntax, in which terms
      count 0, a slot counts as the unit the context gives it, and an open
      as the entries it generates.  Substitution does not grow the size
      ([sizes_sub]): it puts terms (size 0) or module expressions no bigger
      than the slot for slots.

    The order is then by induction on the size ([order_bounded]). *)

From Stdlib Require Import Lia String List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Builtin.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths DescTyping Presup.
From Mctt.Extraction Require Import MemberType.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Unfolded Size of Module Syntax

    Sizes are read in a list of slot sizes [ρ], innermost first:
    [nth x ρ 0] is the size of the unit in the slot [x] (0 for a term
    slot).  Terms count 0. *)

(** The size of a module expression: a slot is as big as its unit. *)
Fixpoint modexp_size (ρ : list nat) (H : modexp) {struct H} : nat :=
  match H with
  | me_unit _ => 1
  | me_var x => S (nth x ρ 0)
  | me_mem H _ => S (modexp_size ρ H)
  | me_app H _ => S (modexp_size ρ H)
  | me_lit U => S (unit_size ρ U)
  end
(** The size of a unit: its definition's, under its telescope. *)
with unit_size (ρ : list nat) (U : gunit) {struct U} : nat :=
  match U with
  | gu_mk Δ D =>
      S (moddef_size ((fix tele_sizes (Δ : list centry) : list nat :=
                 match Δ with
                 | nil => nil
                 | e :: Δ' => centry_size (tele_sizes Δ' ++ ρ) e :: tele_sizes Δ'
                 end) Δ ++ ρ) D)
  end
(** The size of a context entry: a module slot's unit's, 0 otherwise. *)
with centry_size (ρ : list nat) (e : centry) {struct e} : nat :=
  match e with
  | ce_mod U => unit_size ρ U
  | _ => 0
  end
(** The size of a module definition: its body's, or its target's. *)
with moddef_size (ρ : list nat) (D : moddef) {struct D} : nat :=
  match D with
  | md_body _ Φ => fst (body_size ρ Φ)
  | md_alias E => modexp_size ρ E
  end
(** The size of a body, with the slot sizes of its binders (innermost
    first): an open counts as its target once per item it opens, each item
    one entry of the target's size and two more. *)
with body_size (ρ : list nat) (Φ : gmod) {struct Φ} : prod nat (list nat) :=
  match Φ with
  | gm_nil => (0, nil)
  | gm_ext Φ _ E =>
      (fst (body_size ρ Φ) + S (gentry_size (snd (body_size ρ Φ) ++ ρ) E),
       gentry_size (snd (body_size ρ Φ) ++ ρ) E :: snd (body_size ρ Φ))
  | gm_open Φ H its =>
      (fst (body_size ρ Φ) + S (length its) * S (S (S (modexp_size (snd (body_size ρ Φ) ++ ρ) H))),
       repeat (S (S (modexp_size (snd (body_size ρ Φ) ++ ρ) H))) (length its) ++ snd (body_size ρ Φ))
  end
(** The size of an entry: a module's unit's, 0 otherwise. *)
with gentry_size (ρ : list nat) (E : gentry) {struct E} : nat :=
  match E with
  | ge_mod _ U => unit_size ρ U
  | _ => 0
  end.

(** The slot sizes of a telescope, innermost first, each entry read under
    those before it. *)
Fixpoint tele_sizes (ρ : list nat) (Δ : list centry) : list nat :=
  match Δ with
  | nil => nil
  | e :: Δ' => centry_size (tele_sizes ρ Δ' ++ ρ) e :: tele_sizes ρ Δ'
  end.

Lemma unit_size_mk : forall ρ Δ D, unit_size ρ (gu_mk Δ D) = S (moddef_size (tele_sizes ρ Δ ++ ρ) D).
Proof. intros; cbn; do 3 f_equal; induction Δ; cbn; congruence. Qed.

(** The slot sizes of a context. *)
Definition ctx_sizes (Γ : ctx) : list nat := tele_sizes nil Γ.

Lemma tele_sizes_app : forall ρ Δ Γ, tele_sizes ρ (Δ ++ Γ) = tele_sizes (tele_sizes ρ Γ ++ ρ) Δ ++ tele_sizes ρ Γ.
Proof. induction Δ as [| e Δ IH]; intros; cbn; [ reflexivity | rewrite IH, <- app_assoc; reflexivity ]. Qed.

Lemma ctx_sizes_app : forall Δ Γ, ctx_sizes (Δ ++ Γ) = tele_sizes (ctx_sizes Γ) Δ ++ ctx_sizes Γ.
Proof. intros; unfold ctx_sizes; rewrite tele_sizes_app, app_nil_r; reflexivity. Qed.

Lemma ctx_sizes_cons : forall e Γ, ctx_sizes (e :: Γ) = centry_size (ctx_sizes Γ) e :: ctx_sizes Γ.
Proof. intros; unfold ctx_sizes; cbn; rewrite app_nil_r; reflexivity. Qed.

Lemma length_tele_sizes : forall ρ Δ, length (tele_sizes ρ Δ) = length Δ.
Proof. induction Δ; cbn; auto. Qed.

Lemma length_body_size : forall ρ Φ, length (snd (body_size ρ Φ)) = gm_binders Φ.
Proof.
  induction Φ; cbn; auto.
  rewrite length_app, repeat_length; auto.
Qed.

(** ** The Pointwise Order on Slot Sizes *)

(** Each slot of [a] is no bigger than the same slot of [b]. *)
Definition sizes_le (a b : list nat) : Prop := forall x, nth x a 0 <= nth x b 0.

Lemma sizes_le_app : forall a' a ρ' ρ, Forall2 le a' a -> sizes_le ρ' ρ -> sizes_le (a' ++ ρ') (a ++ ρ).
Proof.
  induction 1 as [| s' s a' a Hs Ha IH]; intros Hρ; cbn; [ exact Hρ |].
  intros [| x]; cbn; [ exact Hs | apply IH; exact Hρ ].
Qed.

Lemma Forall2_le_repeat : forall n a b, a <= b -> Forall2 le (repeat a n) (repeat b n).
Proof. induction n; cbn; constructor; auto. Qed.

Lemma sizes_le_refl : forall ρ, sizes_le ρ ρ.
Proof. intros ? ?; reflexivity. Qed.

(** ** Weakening Does Not Grow Sizes *)

(** The weakening [φ], from the slot sizes [ρ] to [ρ'], sends each slot to
    one no bigger. *)
Definition wk_keeps_sizes (ρ' ρ : list nat) (φ : wk) : Prop := forall x, nth (φ x) ρ' 0 <= nth x ρ 0.

Lemma wk_keeps_sizes_q : forall ρ' ρ φ s' s, wk_keeps_sizes ρ' ρ φ -> s' <= s ->
    wk_keeps_sizes (s' :: ρ') (s :: ρ) (wk_q φ).
Proof. intros * Hφ Hs [| x]; cbn; [ exact Hs | apply Hφ ]. Qed.

Lemma wk_keeps_sizes_qn : forall a' a ρ' ρ φ, Forall2 le a' a -> wk_keeps_sizes ρ' ρ φ ->
    wk_keeps_sizes (a' ++ ρ') (a ++ ρ) (wk_qn (length a) φ).
Proof.
  induction 1 as [| s' s a' a Hs Ha IH]; intros Hφ; cbn; [ exact Hφ |].
  apply wk_keeps_sizes_q; auto.
Qed.

Lemma wk_keeps_sizes_id : forall ρ' ρ, sizes_le ρ' ρ -> wk_keeps_sizes ρ' ρ wk_id.
Proof. intros * H x; apply H. Qed.

Theorem sizes_wk :
  (forall H ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> modexp_size ρ' (modexp_wk H φ) <= modexp_size ρ H) /\
  (forall U ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> unit_size ρ' (gunit_wk U φ) <= unit_size ρ U) /\
  (forall D ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> moddef_size ρ' (moddef_wk D φ) <= moddef_size ρ D) /\
  (forall Φ ρ' ρ φ, wk_keeps_sizes ρ' ρ φ ->
     fst (body_size ρ' (gmod_wk Φ φ)) <= fst (body_size ρ Φ) /\
     Forall2 le (snd (body_size ρ' (gmod_wk Φ φ))) (snd (body_size ρ Φ))) /\
  (forall E ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> gentry_size ρ' (gentry_wk E φ) <= gentry_size ρ E) /\
  (forall e ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> centry_size ρ' (centry_wk e φ) <= centry_size ρ e).
Proof.
  destruct (syn_mut_ind (fun _ => True)
    (fun H => forall ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> modexp_size ρ' (modexp_wk H φ) <= modexp_size ρ H)
    (fun _ => True)
    (fun U => forall ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> unit_size ρ' (gunit_wk U φ) <= unit_size ρ U)
    (fun D => forall ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> moddef_size ρ' (moddef_wk D φ) <= moddef_size ρ D)
    (fun Φ => forall ρ' ρ φ, wk_keeps_sizes ρ' ρ φ ->
       fst (body_size ρ' (gmod_wk Φ φ)) <= fst (body_size ρ Φ) /\
       Forall2 le (snd (body_size ρ' (gmod_wk Φ φ))) (snd (body_size ρ Φ)))
    (fun E => forall ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> gentry_size ρ' (gentry_wk E φ) <= gentry_size ρ E)
    (fun e => forall ρ' ρ φ, wk_keeps_sizes ρ' ρ φ -> centry_size ρ' (centry_wk e φ) <= centry_size ρ e))
    as (_ & Hm & _ & Hu & Hd & Hg & He & Hc); try solve [ intros; exact I ].
  all: intros.
  - cbn; lia.
  - cbn; specialize (H k); lia.
  - cbn; apply le_n_S; auto.
  - cbn; apply le_n_S; auto.
  - cbn; apply le_n_S; auto.
  - rewrite gunit_wk_mk, !unit_size_mk; apply le_n_S.
    assert (HT : Forall2 le (tele_sizes ρ' (tele_wk Δ φ)) (tele_sizes ρ Δ)).
    { clear H0; induction H as [| e Δ He HΔ IH]; cbn; constructor; [| exact IH ].
      apply He; rewrite <- (length_tele_sizes ρ Δ); apply wk_keeps_sizes_qn; [ exact IH | exact H1 ]. }
    apply H0; rewrite <- (length_tele_sizes ρ Δ); apply wk_keeps_sizes_qn; assumption.
  - cbn; apply H; auto.
  - cbn; apply H; auto.
  - cbn; split; [ lia | constructor ].
  - cbn [body_size gmod_wk fst snd].
    destruct (H _ _ _ H1) as [H2 H3].
    assert (Hw' : wk_keeps_sizes (snd (body_size ρ' (gmod_wk Φ φ)) ++ ρ') (snd (body_size ρ Φ) ++ ρ)
                    (wk_qn (gm_binders Φ) φ))
      by (rewrite <- (length_body_size ρ Φ); apply wk_keeps_sizes_qn; assumption).
    specialize (H0 _ _ _ Hw'); split; [ lia | constructor; assumption ].
  - cbn [body_size gmod_wk fst snd].
    destruct (H0 _ _ _ H2) as [H3 H4].
    assert (Hw' : wk_keeps_sizes (snd (body_size ρ' (gmod_wk Φ φ)) ++ ρ') (snd (body_size ρ Φ) ++ ρ)
                    (wk_qn (gm_binders Φ) φ))
      by (rewrite <- (length_body_size ρ Φ); apply wk_keeps_sizes_qn; assumption).
    specialize (H1 _ _ _ Hw'); split; [ nia | apply Forall2_app; [ apply Forall2_le_repeat; lia | assumption ] ].
  - cbn; lia.
  - cbn; auto.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - cbn; auto.
  - exact (conj Hm (conj Hu (conj Hd (conj Hg (conj He Hc))))).
Qed.

Corollary modexp_size_shift : forall s ρ H, modexp_size (s :: ρ) (modexp_wk H wk_shift) <= modexp_size ρ H.
Proof. intros; apply (proj1 sizes_wk); intros x; reflexivity. Qed.

Lemma modexp_size_mono : forall H ρ' ρ, sizes_le ρ' ρ -> modexp_size ρ' H <= modexp_size ρ H.
Proof. intros; rewrite <- (modexp_wk_id H) at 1; apply (proj1 sizes_wk), wk_keeps_sizes_id; assumption. Qed.

Lemma gentry_size_mono : forall E ρ' ρ, sizes_le ρ' ρ -> gentry_size ρ' E <= gentry_size ρ E.
Proof.
  intros; rewrite <- (gentry_wk_id E) at 1.
  apply (proj1 (proj2 (proj2 (proj2 (proj2 sizes_wk))))), wk_keeps_sizes_id; assumption.
Qed.

(** ** Substitution Does Not Grow Sizes *)

(** The size of what a substitution puts for a slot: a term counts 1. *)
Definition sentry_size (ρ : list nat) (e : sentry) : nat :=
  match e with
  | se_var y => S (nth y ρ 0)
  | se_exp _ => 1
  | se_mod H => modexp_size ρ H
  end.

(** The substitution [σ], from the slot sizes [ρ'] to [ρ], puts for each
    slot something no bigger. *)
Definition sub_keeps_sizes (ρ' ρ : list nat) (σ : sub) : Prop := forall x, sentry_size ρ' (σ x) <= S (nth x ρ 0).

Lemma sentry_size_shift : forall s ρ e, sentry_size (s :: ρ) (sentry_wk e wk_shift) <= sentry_size ρ e.
Proof. intros s ρ [y | M | H]; cbn; [ reflexivity | reflexivity | apply modexp_size_shift ]. Qed.

Lemma sub_keeps_sizes_q : forall ρ' ρ σ s' s, sub_keeps_sizes ρ' ρ σ -> s' <= s ->
    sub_keeps_sizes (s' :: ρ') (s :: ρ) (q σ).
Proof.
  intros * Hσ Hs [| x]; rewrite ?sb_q_zero, ?sb_q_succ; cbn; [ lia |].
  etransitivity; [ apply sentry_size_shift | apply Hσ ].
Qed.

Lemma sub_keeps_sizes_qn : forall a' a ρ' ρ σ, Forall2 le a' a -> sub_keeps_sizes ρ' ρ σ ->
    sub_keeps_sizes (a' ++ ρ') (a ++ ρ) (sb_qn (length a) σ).
Proof.
  induction 1 as [| s' s a' a Hs Ha IH]; intros Hσ; cbn; [ exact Hσ |].
  apply sub_keeps_sizes_q; auto.
Qed.

Theorem sizes_sub :
  (forall H ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> modexp_size ρ' (modexp_sub H σ) <= modexp_size ρ H) /\
  (forall U ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> unit_size ρ' (gunit_sub U σ) <= unit_size ρ U) /\
  (forall D ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> moddef_size ρ' (moddef_sub D σ) <= moddef_size ρ D) /\
  (forall Φ ρ' ρ σ, sub_keeps_sizes ρ' ρ σ ->
     fst (body_size ρ' (gmod_sub Φ σ)) <= fst (body_size ρ Φ) /\
     Forall2 le (snd (body_size ρ' (gmod_sub Φ σ))) (snd (body_size ρ Φ))) /\
  (forall E ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> gentry_size ρ' (gentry_sub E σ) <= gentry_size ρ E) /\
  (forall e ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> centry_size ρ' (centry_sub e σ) <= centry_size ρ e).
Proof.
  destruct (syn_mut_ind (fun _ => True)
    (fun H => forall ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> modexp_size ρ' (modexp_sub H σ) <= modexp_size ρ H)
    (fun _ => True)
    (fun U => forall ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> unit_size ρ' (gunit_sub U σ) <= unit_size ρ U)
    (fun D => forall ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> moddef_size ρ' (moddef_sub D σ) <= moddef_size ρ D)
    (fun Φ => forall ρ' ρ σ, sub_keeps_sizes ρ' ρ σ ->
       fst (body_size ρ' (gmod_sub Φ σ)) <= fst (body_size ρ Φ) /\
       Forall2 le (snd (body_size ρ' (gmod_sub Φ σ))) (snd (body_size ρ Φ)))
    (fun E => forall ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> gentry_size ρ' (gentry_sub E σ) <= gentry_size ρ E)
    (fun e => forall ρ' ρ σ, sub_keeps_sizes ρ' ρ σ -> centry_size ρ' (centry_sub e σ) <= centry_size ρ e))
    as (_ & Hm & _ & Hu & Hd & Hg & He & Hc); try solve [ intros; exact I ].
  all: intros.
  - cbn; lia.
  - cbn; specialize (H k); destruct (σ k); cbn in *; lia.
  - cbn; apply le_n_S; auto.
  - cbn; apply le_n_S; auto.
  - cbn; apply le_n_S; auto.
  - rewrite gunit_sub_mk, !unit_size_mk; apply le_n_S.
    assert (HT : Forall2 le (tele_sizes ρ' (tele_sub Δ σ)) (tele_sizes ρ Δ)).
    { clear H0; induction H as [| e Δ He HΔ IH]; cbn; constructor; [| exact IH ].
      apply He; rewrite <- (length_tele_sizes ρ Δ); apply sub_keeps_sizes_qn; [ exact IH | exact H1 ]. }
    apply H0; rewrite <- (length_tele_sizes ρ Δ); apply sub_keeps_sizes_qn; assumption.
  - cbn; apply H; auto.
  - cbn; apply H; auto.
  - cbn; split; [ lia | constructor ].
  - cbn [body_size gmod_sub fst snd].
    destruct (H _ _ _ H1) as [H2 H3].
    assert (Hw' : sub_keeps_sizes (snd (body_size ρ' (gmod_sub Φ σ)) ++ ρ') (snd (body_size ρ Φ) ++ ρ)
                    (sb_qn (gm_binders Φ) σ))
      by (rewrite <- (length_body_size ρ Φ); apply sub_keeps_sizes_qn; assumption).
    specialize (H0 _ _ _ Hw'); split; [ lia | constructor; assumption ].
  - cbn [body_size gmod_sub fst snd].
    destruct (H0 _ _ _ H2) as [H3 H4].
    assert (Hw' : sub_keeps_sizes (snd (body_size ρ' (gmod_sub Φ σ)) ++ ρ') (snd (body_size ρ Φ) ++ ρ)
                    (sb_qn (gm_binders Φ) σ))
      by (rewrite <- (length_body_size ρ Φ); apply sub_keeps_sizes_qn; assumption).
    specialize (H1 _ _ _ Hw'); split; [ nia | apply Forall2_app; [ apply Forall2_le_repeat; lia | assumption ] ].
  - cbn; lia.
  - cbn; auto.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - cbn; auto.
  - exact (conj Hm (conj Hu (conj Hd (conj Hg (conj He Hc))))).
Qed.

Corollary tele_sizes_sub : forall Δ ρ' ρ σ, sub_keeps_sizes ρ' ρ σ ->
    Forall2 le (tele_sizes ρ' (tele_sub Δ σ)) (tele_sizes ρ Δ).
Proof.
  induction Δ as [| e Δ IH]; intros * Hσ; cbn; constructor; [| auto ].
  apply (proj2 (proj2 (proj2 (proj2 (proj2 sizes_sub))))).
  rewrite <- (length_tele_sizes ρ Δ); apply sub_keeps_sizes_qn; auto.
Qed.

Lemma sub_keeps_sizes_compose : forall ρ2 ρ1 ρ0 σ τ, sub_keeps_sizes ρ1 ρ0 σ -> sub_keeps_sizes ρ2 ρ1 τ ->
    sub_keeps_sizes ρ2 ρ0 (σ ⨟ τ).
Proof.
  intros * Hσ Hτ x; specialize (Hσ x); cbn [sb_compose].
  destruct (σ x) as [y | M | H]; cbn [sentry_sub sentry_size] in *.
  - specialize (Hτ y); lia.
  - cbn; lia.
  - cbn; etransitivity; [ apply (proj1 sizes_sub); exact Hτ | exact Hσ ].
Qed.

Lemma sub_keeps_sizes_id : forall ρ, sub_keeps_sizes ρ ρ Id.
Proof. intros ρ x; cbn; lia. Qed.

Lemma sub_keeps_sizes_ctx_ext : forall Δ σ ρ' ρ, sub_keeps_sizes ρ' ρ σ ->
    sub_keeps_sizes (tele_sizes ρ' (tele_sub Δ σ) ++ ρ') (tele_sizes ρ Δ ++ ρ) (sb_qn (length Δ) σ).
Proof.
  intros; rewrite <- (length_tele_sizes ρ Δ); apply sub_keeps_sizes_qn; [ apply tele_sizes_sub |]; assumption.
Qed.

(** A term for a term slot keeps sizes. *)
Lemma sub_keeps_sizes_single : forall Γ e N, centry_size (ctx_sizes Γ) e = 0 ->
    sub_keeps_sizes (ctx_sizes Γ) (ctx_sizes (e :: Γ)) (Id,,N).
Proof. intros * He [| x]; rewrite ctx_sizes_cons; cbn; [ lia | reflexivity ]. Qed.

(** A unit for a module slot keeps sizes. *)
Lemma sub_keeps_sizes_single_mod : forall Γ U,
    sub_keeps_sizes (ctx_sizes Γ) (ctx_sizes (ce_mod U :: Γ)) (Id ,,ₘ me_lit U).
Proof. intros * [| x]; rewrite ctx_sizes_cons; cbn; [ reflexivity | reflexivity ]. Qed.

(** Splitting a telescope off at its last assumption keeps sizes. *)
Lemma tele_split_keeps_sizes : forall R Γ,
    match tele_split R with
    | inl (B, T, τ) => sub_keeps_sizes (ctx_sizes (T ++ ce_ass B :: Γ)) (ctx_sizes (rev R ++ Γ)) τ
    | inr τ => sub_keeps_sizes (ctx_sizes Γ) (ctx_sizes (rev R ++ Γ)) τ
    end.
Proof.
  induction R as [| [B0 | B0 N | U] R IH]; intros Γ; cbn [rev tele_split].
  - apply sub_keeps_sizes_id.
  - rewrite <- List.app_assoc; cbn [List.app]; apply sub_keeps_sizes_id.
  - specialize (IH (ce_def B0 N :: Γ)); rewrite <- List.app_assoc; cbn [List.app].
    pose proof (sub_keeps_sizes_single Γ (ce_def B0 N) N eq_refl) as Hs.
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + eapply sub_keeps_sizes_compose; [ exact IH |].
      pose proof (sub_keeps_sizes_ctx_ext (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite <- !ctx_sizes_app, tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia; exact Hx.
    + eapply sub_keeps_sizes_compose; [ exact IH | exact Hs ].
  - specialize (IH (ce_mod U :: Γ)); rewrite <- List.app_assoc; cbn [List.app].
    pose proof (sub_keeps_sizes_single_mod Γ U) as Hs.
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + eapply sub_keeps_sizes_compose; [ exact IH |].
      pose proof (sub_keeps_sizes_ctx_ext (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite <- !ctx_sizes_app, tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia; exact Hx.
    + eapply sub_keeps_sizes_compose; [ exact IH | exact Hs ].
Qed.

(** Filling in the entries before a member keeps sizes. *)
Lemma fill_keeps_sizes : forall Φ σ Γ, gm_fill Φ = Some σ ->
    sub_keeps_sizes (ctx_sizes Γ) (ctx_sizes (body_ctx Φ ++ Γ)) σ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hf; cbn in Hf; try discriminate.
  - injection Hf as <-; apply sub_keeps_sizes_id.
  - destruct E as [b pv A [M |] | pv U | | ]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:E0; cbn in Hf; try discriminate; injection Hf as <-;
      specialize (IH _ Γ eq_refl); cbn [body_ctx List.app]; rewrite ctx_sizes_cons.
    + intros [| x]; cbn; [ lia | apply IH ].
    + intros [| x]; cbn; [| apply IH ].
      apply le_n_S, (proj1 (proj2 sizes_sub)), IH.
Qed.

(** A unit in a slot is no bigger than the slot says. *)
Lemma ctx_find_mod_size : forall Γ x U, ctx_find_mod Γ x = Some U ->
    unit_size (ctx_sizes Γ) U <= nth x (ctx_sizes Γ) 0.
Proof.
  induction Γ as [| e Γ IH]; intros [| y] U Hf; cbn in Hf; try discriminate; rewrite ctx_sizes_cons.
  - destruct e as [| | U0]; try discriminate; injection Hf as <-; cbn [nth centry_size].
    apply (proj1 (proj2 sizes_wk)); intros x; reflexivity.
  - destruct (ctx_find_mod Γ y) as [U0 |] eqn:E; cbn in Hf; [| discriminate ]; injection Hf as <-.
    cbn [nth]; etransitivity; [| exact (IH _ _ E) ].
    apply (proj1 (proj2 sizes_wk)); intros x; reflexivity.
Qed.

(** ** The Size of an Open Description *)

(** The size of an open description over [Γ]: one more than its expanded
    body's, read under its parameters; 0 for the other descriptions. *)
Definition open_size (Γ : ctx) (R : mdesc) : nat :=
  match R with
  | ds_open Δ _ Φx => S (fst (body_size (ctx_sizes (Δ ++ Γ)) Φx))
  | _ => 0
  end.

Lemma body_size_mono : forall Φ ρ' ρ, sizes_le ρ' ρ ->
    fst (body_size ρ' Φ) <= fst (body_size ρ Φ) /\ Forall2 le (snd (body_size ρ' Φ)) (snd (body_size ρ Φ)).
Proof.
  intros * H; pose proof (proj1 (proj2 (proj2 (proj2 sizes_wk))) Φ ρ' ρ wk_id (wk_keeps_sizes_id _ _ H)) as H0.
  rewrite gmod_wk_id in H0; exact H0.
Qed.

(** The slot sizes of the binders of a body with no open. *)
Lemma body_size_noopen_ctx : forall Φ ρ, gm_noopen Φ -> tele_sizes ρ (body_ctx Φ) = snd (body_size ρ Φ).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros ρ Hn; cbn in Hn |- *; [ reflexivity | | contradiction ].
  destruct E as [b pv A [M |] | pv U | | ]; cbn [body_ctx tele_sizes]; rewrite (IH ρ Hn); reflexivity.
Qed.

(** An entry of a body with no open is smaller than the body. *)
Lemma body_size_prefix : forall Φ y Φ' E ρ, gm_noopen Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ' y E) ->
    fst (body_size ρ Φ') + S (gentry_size (tele_sizes ρ (body_ctx Φ') ++ ρ) E) <= fst (body_size ρ Φ).
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hn Hp; cbn in Hn, Hp; [ discriminate | | contradiction ].
  cbn [body_size fst].
  destruct (String.eqb y x).
  - injection Hp as <- <- <-; rewrite (body_size_noopen_ctx _ _ Hn); lia.
  - specialize (IH _ _ _ ρ Hn Hp); lia.
Qed.

Lemma open_size_up : forall Γ Θ' R, open_size Γ (ds_up Θ' R) = open_size (Θ' ++ Γ) R.
Proof. intros * ; destruct R; cbn; rewrite ?app_assoc; reflexivity. Qed.

Lemma open_size_sub : forall Γ1 Γ2 R σ, sub_keeps_sizes (ctx_sizes Γ2) (ctx_sizes Γ1) σ ->
    open_size Γ2 (ds_sub R σ) <= open_size Γ1 R.
Proof.
  intros * Hσ; destruct R as [| Δ Φw Φx | |]; cbn; try lia.
  rewrite !ctx_sizes_app; apply le_n_S.
  apply (proj1 (proj2 (proj2 (proj2 sizes_sub))) Φx), sub_keeps_sizes_ctx_ext, Hσ.
Qed.

Lemma open_size_at : forall Γ R N R', ds_at R N = Some R' -> open_size Γ R' <= open_size Γ R.
Proof.
  intros * Ha; destruct R as [A om | Δ Φw Φx | Θ' p T Φ Ns | Θ' p k Ns]; cbn in Ha.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; cbn; lia.
  - pose proof (tele_split_keeps_sizes (rev Δ) Γ) as Hc; rewrite rev_involutive in Hc.
    destruct (tele_split (rev Δ)) as [[[B Δ'] τ] | τ]; [| discriminate ]; injection Ha as <-; cbn.
    apply le_n_S, (proj1 (proj2 (proj2 (proj2 sizes_sub))) Φx).
    eapply sub_keeps_sizes_compose; [ exact Hc |].
    pose proof (sub_keeps_sizes_ctx_ext Δ' _ _ _ (sub_keeps_sizes_single Γ (ce_ass B) N eq_refl)) as Hx.
    rewrite <- !ctx_sizes_app in Hx; exact Hx.
  - destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha as <-; cbn; lia.
  - destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha as <-; cbn; lia.
Qed.

Lemma open_size_ats : forall Ns Γ R R', ds_ats R Ns = Some R' -> open_size Γ R' <= open_size Γ R.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; lia |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  etransitivity; [ eapply IH; exact Ha | eapply open_size_at; exact E ].
Qed.

(** ** What an Open Generates, and the Expansion of a Body *)

(** The sizes of the body [gens_append Φ k gs] after the generated entries
    [gs], each of size at most [c] read under [B]: [Φ]'s slot sizes are
    [new ++ B], with [k] new ones. *)
#[warnings="-cannot-define-projection"]
Record gens_sizes (ρ : list nat) (Φ : gmod) (k : nat) (gs : list igen) (B new : list nat) (c : nat) : Prop :=
  mk_gens_sizes
  { (** The body grows by at most [S c] per generated entry *)
    gens_total : fst (body_size ρ (gens_append Φ k gs)) <= fst (body_size ρ Φ) + List.length gs * S c
    (** The slot sizes of the generated entries, innermost first *)
  ; gens_new : list nat
    (** They come before [Φ]'s *)
  ; gens_slots : snd (body_size ρ (gens_append Φ k gs)) = gens_new ++ new ++ B
    (** Each is at most [c] *)
  ; gens_bounded : Forall (fun s => s <= c) gens_new
    (** One per generated entry *)
  ; gens_count : List.length gens_new = List.length gs }.

Section Expansion.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** What an open generates, outside a generated group: one entry per
      item, each of size at most the target's and two more. *)
  Lemma items_gen_shape : forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> g = false ->
      List.length gs = List.length its /\
      Forall (fun x => forall ρ, gentry_size ρ (snd (ig_entry x)) <= S (S (modexp_size ρ H))) gs.
  Proof.
    induction 1 as [g Γ H | g Γ H d pv its gs Hig IH | g Γ H n d pv A om its gs Hm Hig IH
                    | g Γ H n d pv R its gs Hm Hmod Hig IH | Γ H n d pv Θ' p k D pm Ns its gs Hm Hl Hp Hml Hig IH];
      intros Hgf; [ split; [ reflexivity | constructor ] | | | | discriminate ].
    all: destruct (IH Hgf) as [IHl IHf]; split; [ cbn; lia | constructor; [ intros ρ; cbn; lia | exact IHf ] ].
  Qed.

  Lemma Forall2_le_repeat_r : forall a c, Forall (fun s => s <= c) a -> Forall2 le a (repeat c (List.length a)).
  Proof. induction 1; cbn; constructor; auto. Qed.

  Lemma gens_append_sizes : forall gs Φ k B ρ new c,
      snd (body_size ρ Φ) = new ++ B -> List.length new = k ->
      Forall (fun g => gentry_size (B ++ ρ) (snd (ig_entry g)) <= c) gs ->
      gens_sizes ρ Φ k gs B new c.
  Proof.
    induction gs as [| g gs IH]; intros * Hs Hk Hgs; cbn [gens_append].
    - apply (mk_gens_sizes ρ Φ k nil B new c ltac:(cbn; lia) nil); cbn; auto.
    - inversion Hgs as [| ? ? Hg Hgs']; subst.
      destruct (ig_entry g) as [d E] eqn:Eg; cbn [snd] in Hg.
      set (s := gentry_size (snd (body_size ρ Φ) ++ ρ) (gentry_wk E (wk_shiftn (List.length new)))).
      assert (Hsc : s <= c).
      { unfold s; rewrite Hs, <- app_assoc; etransitivity; [| exact Hg ].
        apply (proj1 (proj2 (proj2 (proj2 (proj2 sizes_wk))))).
        intros x; cbn; rewrite app_nth2 by lia; replace (x + List.length new - List.length new) with x by lia; reflexivity. }
      destruct (IH (gm_ext Φ d (gentry_wk E (wk_shiftn (List.length new)))) (S (List.length new)) B ρ (s :: new) c)
        as [IH1 new' IH2 IH3 IH4]; [ unfold s; cbn [body_size snd]; rewrite Hs; reflexivity | reflexivity | exact Hgs' |].
      refine (mk_gens_sizes ρ Φ _ (g :: gs) B new c _ (new' ++ s :: nil) _ _ _).
      + cbn [gens_append]; rewrite Eg; cbn [body_size fst] in IH1; fold s in IH1; cbn [List.length]; nia.
      + cbn [gens_append]; rewrite Eg, IH2, <- app_assoc; reflexivity.
      + apply Forall_app; split; [ exact IH3 | constructor; auto ].
      + rewrite length_app; cbn; lia.
  Qed.

  (** Expanding a body does not grow it. *)
  Lemma body_xp_size : forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall ρ,
      fst (body_size ρ Φx) <= fst (body_size ρ Φ) /\ Forall2 le (snd (body_size ρ Φx)) (snd (body_size ρ Φ)).
  Proof.
    induction 1 as [Γ | Γ Φ Φx x E Hx IH | Γ Φ Φx H its R Rm gs Hx IH Hm Hmod Hig Hok]; intros ρ.
    - cbn; split; [ lia | constructor ].
    - destruct (IH ρ) as [IH1 IH2]; cbn [body_size fst snd].
      pose proof (gentry_size_mono E _ _ (sizes_le_app _ _ ρ ρ IH2 (sizes_le_refl ρ))) as He.
      split; [ lia | constructor; assumption ].
    - destruct (IH ρ) as [IH1 IH2].
      destruct (items_gen_shape _ _ _ _ _ Hig eq_refl) as [Hl Hf].
      set (c := S (S (modexp_size (snd (body_size ρ Φx) ++ ρ) H))).
      assert (Hgs : Forall (fun g => gentry_size (snd (body_size ρ Φx) ++ ρ) (snd (ig_entry g)) <= c) gs)
        by (eapply Forall_impl; [| exact Hf ]; intros g Hg; apply Hg).
      destruct (gens_append_sizes gs Φx 0 (snd (body_size ρ Φx)) ρ nil c eq_refl eq_refl Hgs) as [G1 new' G2 G3 G4].
      pose proof (modexp_size_mono H _ _ (sizes_le_app _ _ ρ ρ IH2 (sizes_le_refl ρ))) as Hmo.
      cbn [body_size fst snd]; rewrite G2; cbn [List.app]; split.
      + unfold c in G1; rewrite Hl in G1; nia.
      + apply Forall2_app; [| exact IH2 ].
        rewrite <- Hl, <- G4; apply Forall2_le_repeat_r.
        eapply Forall_impl; [| exact G3 ]; intros s Hs; unfold c in Hs; lia.
  Qed.
End Expansion.

(** ** Typed Open Descriptions

    Descriptions whose module entries are instances of typed units: they
    come from filed aliases; their entries denote, so they have an order,
    and reading them gives such descriptions again. *)

Section Typed.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** [U] over [Γ] is a typed unit of another context, moved along a
      substitution that keeps module slots. *)
  #[warnings="-cannot-define-projection"]
  Record typed_instance (Γ : ctx) (U : gunit) : Prop := mk_typed_instance
    { (** The context the unit is typed in *)
      instance_ctx : ctx
      (** The typed unit *)
    ; instance_unit : gunit
      (** The substitution from [Γ] into that context *)
    ; instance_sub : sub
      (** The unit is typed there *)
    ; instance_typed : Θ ⍮ Ξ ⍮ instance_ctx ⊢ᵘ instance_unit ≈ instance_unit
      (** The substitution keeps module slots *)
    ; instance_compat : sub_mod_compat instance_sub Γ instance_ctx
      (** [U] is the typed unit moved along it *)
    ; instance_eq : U = gunit_sub instance_unit instance_sub }.

  (** Every module entry of an open description over [Γ] is a typed
      instance; other descriptions have no module entry to read. *)
  Definition typed_open (Γ : ctx) (R : mdesc) : Prop :=
    match R with
    | ds_open Δ _ Φx =>
        forall y Φ' pm U, gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm U)) ->
          typed_instance (body_ctx Φ' ++ Δ ++ Γ) U
    | _ => True
    end.

  Lemma typed_instance_sub : forall Γ1 U Γ2 σ, typed_instance Γ1 U -> sub_mod_compat σ Γ2 Γ1 ->
      typed_instance Γ2 (gunit_sub U σ).
  Proof.
    intros * [Γt Ut τ HU Hτ ->] Hσ.
    apply (mk_typed_instance _ _ Γt Ut (τ ⨟ σ) HU); [ eapply sub_mod_compat_compose; eassumption | apply gunit_sub_sub ].
  Qed.

  (** The general move: new parameters, the expanded body substituted. *)
  Lemma typed_open_body_sub : forall Γ1 Δ1 Φw Φx Γ2 Δ2 Φw' σ,
      typed_open Γ1 (ds_open Δ1 Φw Φx) -> sub_mod_compat σ (Δ2 ++ Γ2) (Δ1 ++ Γ1) ->
      typed_open Γ2 (ds_open Δ2 Φw' (gmod_sub Φx σ)).
  Proof.
    intros * HT Hσ; cbn in HT |- *; intros y Φ' pm U Hp.
    rewrite gm_prefix_upto_sub in Hp.
    destruct (gm_prefix_upto Φx y) as [Φ1 |] eqn:Hp1; cbn in Hp; [| discriminate ].
    destruct (gm_prefix_entry _ _ _ Hp1) as (Φ0 & E & -> & _).
    cbn in Hp; injection Hp as <- HE.
    destruct E as [| pm0 U0 | |]; cbn in HE; try discriminate; injection HE as <- <-.
    rewrite body_ctx_sub, List.app_assoc.
    eapply typed_instance_sub; [ apply (HT _ _ _ _ Hp1) |].
    rewrite <- length_body_ctx, <- !List.app_assoc.
    apply sub_mod_compat_ext; exact Hσ.
  Qed.

  Lemma typed_open_sub : forall Γ1 R Γ2 σ, typed_open Γ1 R -> sub_mod_compat σ Γ2 Γ1 -> typed_open Γ2 (ds_sub R σ).
  Proof.
    intros * HT Hσ; destruct R as [| Δ Φw Φx | |]; cbn [ds_sub]; try exact I.
    eapply typed_open_body_sub; [ exact HT |].
    apply sub_mod_compat_ext; exact Hσ.
  Qed.

  Lemma typed_open_up : forall Γ Θ' R, typed_open (Θ' ++ Γ) R -> typed_open Γ (ds_up Θ' R).
  Proof.
    intros * HT; destruct R as [| Δ Φw Φx | |]; cbn in *; try exact I.
    intros * Hp; rewrite <- List.app_assoc; exact (HT _ _ _ _ Hp).
  Qed.

  Lemma typed_open_at : forall Γ R N R', typed_open Γ R -> ds_at R N = Some R' -> typed_open Γ R'.
  Proof.
    intros * HT Ha; destruct R as [A om | Δ Φw Φx | Θ' p T Φ Ns | Θ' p k Ns]; cbn in Ha.
    - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
      destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; exact I.
    - pose proof (tele_split_compat (rev Δ) Γ) as Hc; rewrite rev_involutive in Hc.
      destruct (tele_split (rev Δ)) as [[[B Δ'] τ] | τ]; [| discriminate ]; injection Ha as <-.
      eapply typed_open_body_sub; [ exact HT |].
      eapply sub_mod_compat_compose; [ exact Hc |].
      exact (sub_mod_compat_ext Δ' _ _ _ (sub_mod_compat_single Γ B N)).
    - destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
    - destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
  Qed.

  Lemma typed_open_ats : forall Ns Γ R R', typed_open Γ R -> ds_ats R Ns = Some R' -> typed_open Γ R'.
  Proof.
    induction Ns as [| N Ns IH]; intros * HT Ha; cbn in Ha; [ injection Ha as <-; exact HT |].
    destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
    eapply IH; [ eapply typed_open_at; eassumption | exact Ha ].
  Qed.

  Lemma typed_open_mod : forall Γ R Rm, typed_open Γ R -> ds_mod Θ Ξ R = Some Rm -> typed_open Γ Rm.
  Proof.
    intros * HT Hm; destruct R; cbn in Hm; try discriminate; try (injection Hm as <-; exact HT).
    destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (D & pm & T & Φ & _ & _ & _ & ->); exact I.
  Qed.

  (** A typed open description: its module entries are typed units. *)
  Lemma typed_open_of_desc : forall Γt R, desc_ok Θ Ξ Γt R -> typed_open Γt R.
  Proof.
    intros * Hok; destruct R as [| Δ Φw Φx | |]; cbn; try exact I.
    inversion Hok as [| | ? ? ? ? HΦ Hno Hent |]; subst.
    intros y Φ' pm U Hp.
    destruct (gm_prefix_body_ctx _ _ _ Hno Hp) as (Ψ & HΨ); rewrite HΨ in HΦ; cbn [body_ctx] in HΦ.
    rewrite <- !List.app_assoc in HΦ; apply ctx_app_wf_right in HΦ.
    destruct (ctx_decomp_mod HΦ) as [_ HU].
    apply (mk_typed_instance _ _ (body_ctx Φ' ++ Δ ++ Γt) U Id HU); [| symmetry; apply gunit_sub_id ].
    intros x U0 Hl; right; exists x; split; [ reflexivity | rewrite gunit_sub_id; exact Hl ].
  Qed.

  (** A typed unit moved along a substitution that keeps module slots
      denotes the typed description of the unit, moved along it. *)
  Lemma typed_instance_denote : forall Γ Γt Ut τ, Θ ⍮ Ξ ⍮ Γt ⊢ᵘ Ut ≈ Ut -> sub_mod_compat τ Γ Γt ->
      exists Rt, desc_ok Θ Ξ Γt Rt /\ udenote Θ Ξ Γ None (gunit_sub Ut τ) (ds_sub Rt τ).
  Proof.
    intros * HU Hτ.
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & (Rt & HRt) & _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HU (gctx_valid_syn _ _ Hg))
      as (_ & Hok & _).
    destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΓt & HUs & _).
    exists Rt; split; [ exact (Hok _ HRt) |].
    eapply (proj1 (proj2 (mdenote_sub_all _ _ (wf_gctx_closed _ _ _ (presup_unit_eq_ctx HU))))).
    - exact HRt.
    - exact (slots_ok_ctx _ HΓt).
    - left; exact HUs.
    - exact Hτ.
  Qed.

  (** So a typed instance has an order. *)
  Lemma typed_instance_order : forall Γ U, typed_instance Γ U -> un_order Θ Ξ Γ U.
  Proof.
    intros * [Γt Ut τ HU Hτ ->]; destruct (typed_instance_denote _ _ _ _ HU Hτ) as (Rt & _ & Hd).
    exact (proj1 (proj2 (order_of_denote _ _ Hg)) _ _ _ _ Hd).
  Qed.

  Lemma typed_open_entry_order : forall Γ Δ Φw Φx y Γy E rd,
      typed_open Γ (ds_open Δ Φw Φx) -> ds_entry (ds_open Δ Φw Φx) y = Some (Γy, E, rd) -> en_order Θ Ξ (Γy ++ Γ) E.
  Proof.
    intros * HT He; cbn in He.
    destruct (gm_prefix_upto Φx y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    destruct E0 as [b pv A oM | pm U | | ].
    - destruct b, oM; try discriminate; injection He as <- <- <-; constructor.
    - injection He as <- <- <-; constructor; rewrite <- List.app_assoc.
      apply typed_instance_order; exact (HT _ _ _ _ Hp).
    - discriminate.
    - discriminate.
  Qed.

  (** Reading an entry of a typed open description gives one again. *)
  Lemma typed_open_read : forall Γ Δ Φw Φx y Γy E rd R1 R2,
      typed_open Γ (ds_open Δ Φw Φx) -> ds_entry (ds_open Δ Φw Φx) y = Some (Γy, E, rd) ->
      edenote Θ Ξ (Γy ++ Γ) None E R1 -> ds_read rd R1 = Some R2 -> typed_open Γ R2.
  Proof.
    pose proof (mdenote_functional_all _ _ Hg) as (_ & Fu & _).
    intros * HT He Hd Hr; cbn in He.
    destruct (gm_prefix_upto Φx y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    assert (Hrd : rd = rd_open Δ Φ' /\ Γy = body_ctx Φ' ++ Δ /\ E = E0).
    { destruct E0 as [[|] pv A [M |] | pm U | | ]; try discriminate; injection He as <- <- <-; auto. }
    destruct Hrd as (-> & -> & ->).
    cbn in Hr.
    destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    apply typed_open_up.
    eapply typed_open_sub; [| apply sub_mod_compat_fill; exact Hf ].
    destruct E0 as [b pv A oM | pm U | | ]; try discriminate.
    - inversion Hd; subst; exact I.
    - inversion Hd; subst.
      rewrite <- List.app_assoc in *.
      destruct (HT _ _ _ _ Hp) as [Γt Ut τ HU Hτ ->].
      destruct (typed_instance_denote _ _ _ _ HU Hτ) as (Rt & Hok & Hd').
      match goal with Hu : udenote _ _ _ None _ R1 |- _ => rewrite (Fu _ _ _ _ Hu _ Hd') end.
      eapply typed_open_sub; [ apply typed_open_of_desc; exact Hok | exact Hτ ].
  Qed.
End Typed.

(** ** Stored Modules

    The entries of a stored closed module, read in any context: their
    order and their typed descriptions come from the validity of the
    global context. *)

Lemma ctx_lookup_mod_app_l : forall Δ Γ x U, Δ ∋ #x ≔ₘ U -> Δ ++ Γ ∋ #x ≔ₘ U.
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma sub_mod_compat_id_app : forall Δ Γ, sub_mod_compat Id (Δ ++ Γ) Δ.
Proof.
  intros * x U Hl; right; exists x; split; [ reflexivity |].
  rewrite gunit_sub_id; apply ctx_lookup_mod_app_l; exact Hl.
Qed.

Section Stored.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** A stored alias's target denotes in any context under its telescope,
      a typed description. *)
  Lemma stored_alias_denotes : forall p T Φ y Φ0 pv Δa E',
      loc Θ Ξ p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y (ge_mod pv (gu_mk Δa (md_alias E')))) ->
      exists R0, desc_ok Θ Ξ Δa R0 /\ forall Γ, mdenote Θ Ξ (Δa ++ Γ) E' (ds_sub R0 Id).
  Proof.
    intros * Hloc Hp.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    destruct (loc_valid _ _ _ _ _ Hv Hloc) as [_ HvΦ].
    pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp) as HE0.
    cbn [ge_valid syn_V] in HE0; destruct HE0 as (HE' & HΔ & Hcl).
    destruct (Hcl nil ltac:(rewrite app_nil_r; exact HΔ)) as ((R0 & HR0) & Hok).
    rewrite app_nil_r in HR0, Hok.
    exists R0; split; [ exact (proj1 (Hok _ HR0)) |].
    intros Γ.
    destruct (wf_modexp_eq_scoped _ _ _ _ _ HE') as (HΔs & HEs & _).
    rewrite <- (modexp_sub_id E') at 1.
    eapply (proj1 (mdenote_sub_all _ _ (wf_gctx_closed _ _ _ HΔ))); [ exact HR0 | exact (slots_ok_ctx _ HΔs) | exact HEs |].
    apply sub_mod_compat_id_app.
  Qed.

  (** An entry of a stored module has an order in any context. *)
  Lemma stored_entry_order : forall p T Φ y Φ0 E0 Γ,
      loc Θ Ξ p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) -> en_order Θ Ξ Γ (ge_read T E0).
  Proof.
    intros * Hloc Hp.
    pose proof (loc_closed _ _ Hg _ _ _ Hloc) as [_ HcΦ].
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
    destruct E0 as [b pv A oM | pv [Δ [sm Φy | E']] | ? ? ? ? ? | ? ? ? ? ? ?]; cbn [ge_read];
      try solve [ constructor ].
    - destruct HcE as (-> & _ & HcΦy); cbn [ge_read].
      constructor; constructor; apply bx_order_noopen, (body_closed_noopen _ _ HcΦy).
    - destruct (stored_alias_denotes _ _ _ _ _ _ _ _ Hloc Hp) as (R0 & _ & HR).
      constructor; constructor; exact (proj1 (order_of_denote _ _ Hg) _ _ _ (HR Γ)).
  Qed.

  (** What an entry of a stored module denotes, in any context, is typed. *)
  Lemma stored_entry_typed : forall p T Φ y Φ0 E0 Γ o R,
      loc Θ Ξ p T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) ->
      edenote Θ Ξ Γ o (ge_read T E0) R -> forall Γ', typed_open Θ Ξ Γ' R.
  Proof.
    pose proof (mdenote_functional_all _ _ Hg) as (Fm & _).
    intros * Hloc Hp Hd Γ'.
    pose proof (loc_closed _ _ Hg _ _ _ Hloc) as [_ HcΦ].
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
    destruct E0 as [b pv A oM | pv [Δ [sm Φy | E']] | ? ? ? ? ? | ? ? ? ? ? ?]; cbn [ge_read] in Hd;
      try solve [ inversion Hd; subst; exact I ].
    - destruct HcE as (-> & _ & _); cbn [ge_read] in Hd.
      inversion Hd; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
      match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ =>
        cbn in Hb; destruct o; cbn in Hb; [ injection Hb as <- | discriminate ] end.
      exact I.
    - destruct (stored_alias_denotes _ _ _ _ _ _ _ _ Hloc Hp) as (R0 & Hok & HR).
      inversion Hd; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
      apply typed_open_up.
      match goal with Hm : mdenote _ _ _ E' ?R1, Hmod : ds_mod _ _ ?R1 = Some _ |- _ =>
        rewrite (Fm _ _ _ Hm _ (HR Γ)) in Hmod; eapply typed_open_mod; [| exact Hmod ] end.
      eapply typed_open_sub; [ apply typed_open_of_desc; exact Hok | apply sub_mod_compat_id_app ].
  Qed.
End Stored.

(** ** Every Description Is Typed or Bounded *)

Section Classify.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** [R] over [Γ] is typed, or of size at most [b]. *)
  Definition typed_or_bounded (Γ : ctx) (R : mdesc) (b : nat) : Prop := typed_open Θ Ξ Γ R \/ open_size Γ R <= b.

  Lemma typed_or_bounded_mono : forall Γ R b b', typed_or_bounded Γ R b -> b <= b' -> typed_or_bounded Γ R b'.
  Proof. intros * [H | H] Hb; [ left | right; lia ]; assumption. Qed.

  Lemma open_size_mod : forall Γ R R', ds_mod Θ Ξ R = Some R' -> open_size Γ R' <= open_size Γ R.
  Proof.
    intros * Hm; destruct R; cbn in Hm; try discriminate; try (injection Hm as <-; lia).
    destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (D & pm & T & Φ & _ & _ & _ & ->); cbn; lia.
  Qed.

  Lemma typed_open_self : forall Γ M R, typed_open Θ Ξ Γ R -> typed_open Θ Ξ Γ (ds_self M R).
  Proof. intros * HT; destruct R as [A [] | | |]; cbn in *; exact HT || exact I. Qed.

  Lemma ds_mod_open_inv : forall R Δ Φw Φx, ds_mod Θ Ξ R = Some (ds_open Δ Φw Φx) -> R = ds_open Δ Φw Φx.
  Proof.
    intros * Hm; destruct R; [ cbn in Hm; congruence .. |].
    destruct (ds_mod_ind_inv Θ Ξ _ _ _ _ _ Hm) as (D & pm & T & Φ & _ & _ & _ & ?); discriminate.
  Qed.

  (** Every open description [mdenote] produces is typed or no bigger
      than what it came from. *)
  Theorem denotation_classified :
    (forall Γ H R, mdenote Θ Ξ Γ H R -> typed_or_bounded Γ R (modexp_size (ctx_sizes Γ) H)) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> typed_or_bounded Γ R (unit_size (ctx_sizes Γ) U)) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> typed_or_bounded Γ R (gentry_size (ctx_sizes Γ) E)) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> True).
  Proof.
    apply mdenote_all_ind; intros; try exact I.
    - (* a unit *) right; cbn; lia.
    - (* a slot *)
      eapply typed_or_bounded_mono; [ eassumption |]; cbn [modexp_size].
      match goal with Hl : _ ∋ # _ ≔ₘ _ |- _ =>
        pose proof (ctx_find_mod_size _ _ _ (ctx_find_mod_complete _ _ _ Hl)) end; lia.
    - (* a literal *) eapply typed_or_bounded_mono; [ eassumption | cbn; lia ].
    - (* an application *)
      rename H0 into IH, e into Ha.
      destruct IH as [HT | Hn]; [ left; eapply typed_open_at; eassumption | right ].
      pose proof (open_size_at Γ _ _ _ Ha); cbn [modexp_size]; lia.
    - (* a selection *)
      match goal with
      | Hm0 : mdenote _ _ _ _ R0, Hmod0 : ds_mod _ _ R0 = Some _, He1 : ds_entry _ _ = Some _,
        Hd0 : edenote _ _ _ _ _ R, Hr0 : ds_read _ R = Some _,
        IH1 : typed_or_bounded _ R0 _, IH2 : typed_or_bounded _ R _ |- _ =>
          rename Hm0 into Hm, Hmod0 into Hmod, He1 into He, Hd0 into Hd, Hr0 into Hr, IH1 into IH0, IH2 into IHe
      end.
      destruct R0m as [A om | Δ Φw Φx | Θ' p T Φ Ns | Θ' p k Ns]; try (cbn in He; discriminate).
      + (* an open module *)
        pose proof (ds_mod_open_inv _ _ _ _ Hmod) as ->.
        pose proof He as He0; cbn in He.
        destruct (gm_prefix_upto Φx y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
        assert (Hrd : rd = rd_open Δ Φ' /\ Γy = body_ctx Φ' ++ Δ /\ E = E0).
        { destruct E0 as [[|] pv A [M |] | pm U | | ]; try discriminate; injection He as <- <- <-; auto. }
        destruct Hrd as (-> & -> & ->); cbn [ds_epath] in Hd.
        destruct IH0 as [HT | Hn]; [ left; eapply typed_open_read; eassumption |].
        cbn in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
        destruct IHe as [HTe | Hne].
        * left; apply typed_open_up; eapply typed_open_sub; [| apply sub_mod_compat_fill; exact Hf ].
          rewrite <- app_assoc in HTe; exact HTe.
        * right; rewrite open_size_up.
          pose proof (open_size_sub (body_ctx Φ' ++ Δ ++ Γ) (Δ ++ Γ) R σ (fill_keeps_sizes _ _ _ Hf)) as H1.
          pose proof (mdenote_canon _ _ _ _ _ Hg Hm) as Hc; cbn in Hc.
          pose proof (body_size_prefix _ _ _ _ (ctx_sizes (Δ ++ Γ)) Hc Hp) as H2.
          rewrite <- app_assoc, ctx_sizes_app in Hne.
          cbn [open_size] in Hn; cbn [modexp_size]; lia.
      + (* a closed module *)
        pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hmod) as Hloc; cbn in Hloc.
        pose proof He as He0; cbn in He.
        destruct (gm_prefix_upto Φ y) as [[| Φ0 x E0 | ? ? ?] |] eqn:Hp; try discriminate.
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
        injection He as <- <- <-.
        cbn in Hd; left.
        cbn in Hr; destruct (ds_ats R Ns) as [R1 |] eqn:Ea; cbn in Hr; [ injection Hr as <- | discriminate ].
        apply typed_open_up, ds_named_cases; [| apply typed_open_self ];
          (eapply typed_open_ats; [ eapply stored_entry_typed; eassumption | exact Ea ]).
    - (* a body *)
      match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => rename Hb into Hds end.
      match goal with Hx : body_xp _ _ _ _ _ |- _ => rename Hx into Hbx end.
      destruct sm; cbn in Hds.
      + injection Hds as <-; right; cbn [open_size]; rewrite unit_size_mk; cbn [moddef_size]; rewrite <- ctx_sizes_app.
        destruct (body_xp_size _ _ _ _ _ Hbx (ctx_sizes (Δ ++ Γ))) as [H1 _]; lia.
      + destruct o; cbn in Hds; [ injection Hds as <-; right; cbn; lia | discriminate ].
    - (* an alias *)
      rename H into IH, e into Hmod.
      destruct IH as [HT | Hn]; [ left; apply typed_open_up; eapply typed_open_mod; eassumption | right ].
      rewrite open_size_up, unit_size_mk; cbn [moddef_size]; rewrite <- ctx_sizes_app.
      pose proof (open_size_mod (Δ ++ Γ) _ _ Hmod); lia.
    - (* a definition *) right; cbn; lia.
    - (* a module *) cbn [gentry_size]; assumption.
    - right; cbn; lia.
    - right; cbn; lia.
  Qed.
End Classify.

(** ** The Order *)

Section Order.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** The order at the entries of what a module expression denotes, given
      the order at the smaller entries. *)
  Lemma entries_order_bounded : forall n Γ H,
      (forall Γ E, S (gentry_size (ctx_sizes Γ) E) < n -> en_order Θ Ξ Γ E) ->
      modexp_size (ctx_sizes Γ) H < n ->
      forall y R0 R0m Γy E rd, mdenote Θ Ξ Γ H R0 -> ds_mod Θ Ξ R0 = Some R0m ->
        ds_entry R0m y = Some (Γy, E, rd) -> en_order Θ Ξ (Γy ++ Γ) E.
  Proof.
    intros * IHe Hn * Hm Hmod He.
    destruct R0m as [A om | Δ Φw Φx | Θ' p T Φ Ns | Θ' p k Ns]; try (cbn in He; discriminate).
    - (* an open module *)
      pose proof (ds_mod_open_inv _ _ _ _ _ _ Hmod) as ->.
      destruct (proj1 (denotation_classified _ _ Hg) _ _ _ Hm) as [HT | Hnu];
        [ eapply typed_open_entry_order; eassumption |].
      pose proof He as He0; cbn in He.
      destruct (gm_prefix_upto Φx y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
      assert (Hrd : Γy = body_ctx Φ' ++ Δ /\ E = E0).
      { destruct E0 as [[|] pv A [M |] | pm U | | ]; try discriminate; injection He as <- <- <-; auto. }
      destruct Hrd as (-> & ->).
      apply IHe.
      pose proof (mdenote_canon _ _ _ _ _ Hg Hm) as Hc; cbn in Hc.
      pose proof (body_size_prefix _ _ _ _ (ctx_sizes (Δ ++ Γ)) Hc Hp) as H2.
      rewrite <- app_assoc, ctx_sizes_app; cbn [open_size] in Hnu; lia.
    - (* a closed module *)
      pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hmod) as Hloc; cbn in Hloc.
      cbn in He.
      destruct (gm_prefix_upto Φ y) as [[| Φ0 x E0 | ? ? ?] |] eqn:Hp; try discriminate.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
      injection He as <- <- <-; cbn [List.app].
      eapply stored_entry_order; eassumption.
  Qed.

  (** The order of everything of size below [n]. *)
  Theorem order_bounded : forall n,
      (forall Γ H, modexp_size (ctx_sizes Γ) H < n -> dn_order Θ Ξ Γ H) /\
      (forall Γ U, unit_size (ctx_sizes Γ) U < n -> un_order Θ Ξ Γ U) /\
      (forall Γ E, S (gentry_size (ctx_sizes Γ) E) < n -> en_order Θ Ξ Γ E) /\
      (forall Γ Φ, fst (body_size (ctx_sizes Γ) Φ) < n -> bx_order Θ Ξ Γ Φ) /\
      (forall Γ H its, S (S (modexp_size (ctx_sizes Γ) H)) < n -> ig_order Θ Ξ Γ H its).
  Proof.
    induction n as [| n IH]; [ repeat split; intros; lia |].
    destruct IH as (IHd & IHu & IHe & IHb & IHi).
    split; [| split; [| split; [| split ] ] ].
    - (* module expressions *)
      intros Γ [fp | x | H y | H N | U] Hn; cbn [modexp_size] in Hn.
      + apply dno_path.
      + apply dno_var; intros U Hf; apply IHu.
        pose proof (ctx_find_mod_size _ _ _ Hf); lia.
      + destruct (gc_unit Θ Ξ (me_mem H y)) as [[T Φ] |] eqn:Eu; [ eapply dno_unit; exact Eu |].
        apply dno_mem; [ apply IHd; lia |].
        intros; eapply entries_order_bounded; [ exact IHe | | eassumption .. ]; lia.
      + apply dno_app, IHd; lia.
      + apply dno_lit, IHu; lia.
    - (* units *)
      intros Γ [Δ [sm Φ | E]] Hn; rewrite unit_size_mk in Hn; cbn [moddef_size] in Hn; rewrite <- ctx_sizes_app in Hn.
      + apply uno_body, IHb; lia.
      + apply uno_alias, IHd; lia.
    - (* entries *)
      intros Γ [b pv A oM | pv U | pv p k D Φ | pv Δ pm p k Ns] Hn; cbn [gentry_size] in Hn; try constructor.
      apply IHu; lia.
    - (* bodies *)
      intros Γ [| Φ x E | Φ H its] Hn; cbn [body_size fst] in Hn; [ apply bxo_nil | apply bxo_ext, IHb; lia |].
      assert (Hx : forall Φx, body_xp Θ Ξ Γ Φ Φx ->
                 modexp_size (ctx_sizes (body_ctx Φx ++ Γ)) H
                 <= modexp_size (snd (body_size (ctx_sizes Γ) Φ) ++ ctx_sizes Γ) H).
      { intros Φx Hbx; rewrite ctx_sizes_app, (body_size_noopen_ctx _ _ (body_xp_result_noopen _ _ _ _ _ Hbx)).
        destruct (body_xp_size _ _ _ _ _ Hbx (ctx_sizes Γ)) as [_ H2].
        apply modexp_size_mono, sizes_le_app; [ exact H2 | apply sizes_le_refl ]. }
      apply bxo_open; [ apply IHb; nia | intros Φx Hbx; apply IHd | intros Φx Hbx; apply IHi ];
        pose proof (Hx _ Hbx); nia.
    - (* items *)
      intros Γ H its Hn; induction its as [| [[[m |] d] pv] its IHits].
      + apply igo_nil.
      + apply igo_name; [ apply IHd; cbn [modexp_size]; lia | exact IHits ].
      + apply igo_self; exact IHits.
  Qed.

  (** Every module expression, in every context, has the termination
      order of [mdenote_impl], given a well-formed global context: no
      condition on the context and no typing. *)
  Corollary dn_order_all : forall Γ H, dn_order Θ Ξ Γ H.
  Proof. intros; apply (proj1 (order_bounded (S (modexp_size (ctx_sizes Γ) H)))); lia. Qed.

  (** So [mdenote] is decided on every module expression, typed or not. *)
  Definition mdenote_dec (Γ : ctx) (H : modexp) :
      { R | mdenote Θ Ξ Γ H R } + { forall R, ~ mdenote Θ Ξ Γ H R } :=
    mdenote_impl Θ Ξ Hg Γ H (dn_order_all Γ H).
End Order.

(** ** Resolving a Site of an Eliminator

    The interface [site_search] of [Extraction.Command]: the head of the
    annotation is the type former itself, or a member, resolved by
    [mdenote_dec] in the context with the site's binders as holes. *)

(** Refute [site_resolves] at a head [Eh] that is not the one tried. *)
Local Ltac refute_site Eh :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; inversion Hr; subst; try congruence;
  repeat match goal with Eh' : app_head _ = _ |- _ =>
           rewrite Eh in Eh'; injection Eh' as <- <- end;
  try congruence.

(** A site of an eliminator resolves to a type former and its uniform
    arguments, or to nothing. *)
Definition site_search (Θ : gdeps) (Ξ : gstack) (HΞ : ⊢ᵍ Θ ⍮ Ξ) (s : fill_site) :
    {r | site_resolves Θ Ξ s r} + {forall r, ~ site_resolves Θ Ξ s r}.
Proof.
  destruct s as [[Γ d] Z].
  pose proof (proj1 (mdenote_functional_all _ _ HΞ)) as Fm.
  destruct (app_head Z) as [| | | | | | | | | | | p k | | | | | | | | | H x] eqn:Eh;
    try solve [ right; refute_site Eh ].
  - (* the type former *)
    destruct (ind_lookup Θ Ξ p) as [D |] eqn:El; [| right; refute_site Eh ].
    destruct (img_pats (repeat true d) (firstn (ind_nu D) (app_args Z))) as [Us |] eqn:Ei; [| right; refute_site Eh ].
    left; exists (p, Us); eapply site_resolves_former; eassumption.
  - (* a member *)
    destruct (mdenote_dec Θ Ξ HΞ (ctx_holes d ++ Γ) (me_mem H x)) as [(R & HR) | HN];
      [| right; refute_site Eh; eapply HN; eassumption ].
    assert (Hu : forall Θ' p k Ns, mdenote Θ Ξ (ctx_holes d ++ Γ) (me_mem H x) (ds_ind Θ' p k Ns) -> R = ds_ind Θ' p k Ns)
      by (intros * Hm; exact (Fm _ _ _ HR _ Hm)).
    destruct R as [| | | Θ' p k Ns];
      try solve [ right; refute_site Eh;
                  match goal with Hm : mdenote _ _ _ _ (ds_ind _ _ _ _) |- _ => apply Hu in Hm; discriminate end ].
    destruct (ind_lookup Θ Ξ p) as [D |] eqn:El;
      [| right; refute_site Eh;
         match goal with Hm : mdenote _ _ _ _ (ds_ind _ _ _ _) |- _ =>
           apply Hu in Hm; injection Hm as <- <- <- <-; congruence end ].
    destruct (img_pats (repeat true d) (firstn (ind_nu D) (head_args Θ' Ns (app_args Z)))) as [Us |] eqn:Ei;
      [| right; refute_site Eh;
         match goal with Hm : mdenote _ _ _ _ (ds_ind _ _ _ _) |- _ =>
           apply Hu in Hm; injection Hm as <- <- <- <-; congruence end ].
    left; exists (p, Us); eapply site_resolves_member; eassumption.
Defined.
