(** * Transport along an Opening *)

From Stdlib Require Import List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Scoping.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Transport along an Opening

    A judgment moves to another global context when everything in it is opened
    by the same path [a], provided resolution commutes with that opening and the
    parameters in scope agree.  [E1]/[E2] let parameters move between the local
    context and the stack: pushing a frame takes its parameters [E1] off the local
    context ([E2 = ⋅]), and the three uses below — pushing a frame, reading out of
    a nested module, and growing the global context — are all instances. *)

(** [peel_app X E] finds [Γ] with [X = Γ ++ E] syntactically, [X] being [E]
    under some binders. *)
Ltac peel_app X E :=
  lazymatch X with
  | ?Γ ++ E => Γ
  | ?B :: ?Y => let r := peel_app Y E in constr:(B :: r)
  end.

Section OpenTransport.
  Variables (Θ1 Θ2 : gdeps) (Ξ1 Ξ2 : gstack) (E1 E2 : ctx) (a : path).

  Hypothesis Hres : forall r Δ b A B,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
      Θ2 ⍮ Ξ2 ∋ᵍ r[a]p ⇒ Δ[a]p ⍮ ge_def b A[a]p B[a]p.
  Hypothesis Htele : (E1 ++ gs_tele Ξ1)[a]p = E2 ++ gs_tele Ξ2.
  Hypothesis Hbase : ⊢ Θ2 ⍮ Ξ2 ⍮ E2.

  Lemma open_preserves_wf :
    (forall Θ Ξ Γ0, ⊢ Θ ⍮ Ξ ⍮ Γ0 -> Θ = Θ1 -> Ξ = Ξ1 ->
        forall Γ, Γ0 = Γ ++ E1 -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ[a]p ++ E2) /\
    (forall Θ Ξ Γ0 A M, Θ ⍮ Ξ ⍮ Γ0 ⊢ M : A -> Θ = Θ1 -> Ξ = Ξ1 ->
        forall Γ, Γ0 = Γ ++ E1 -> Θ2 ⍮ Ξ2 ⍮ Γ[a]p ++ E2 ⊢ M[a]p : A[a]p) /\
    (forall Θ Ξ Γ0 A M M', Θ ⍮ Ξ ⍮ Γ0 ⊢ M ≈ M' : A -> Θ = Θ1 -> Ξ = Ξ1 ->
        forall Γ, Γ0 = Γ ++ E1 -> Θ2 ⍮ Ξ2 ⍮ Γ[a]p ++ E2 ⊢ M[a]p ≈ M'[a]p : A[a]p) /\
    (forall Θ Ξ Γ0 A A', Θ ⍮ Ξ ⍮ Γ0 ⊢ A ⊆ A' -> Θ = Θ1 -> Ξ = Ξ1 ->
        forall Γ, Γ0 = Γ ++ E1 -> Θ2 ⍮ Ξ2 ⍮ Γ[a]p ++ E2 ⊢ A[a]p ⊆ A'[a]p).
  Proof.
    apply syntactic_wf_mut_ind; intros; subst.
    (* the two context rules: either the split point is inside [Γ], or [Γ] is
       empty and what is left is [Hbase] *)
    1-2: match goal with
         | H : _ = ?Γ ++ E1 |- _ =>
             destruct Γ as [| ? Γ]; cbn in H |- *; [ exact Hbase |];
             try discriminate; injection H as -> ->
         end.
    (* every other premise is at the same split, possibly under binders *)
    all: repeat match goal with
         | IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl)
         | IH : forall Γ', ?X = Γ' ++ E1 -> _ |- _ =>
             let G := peel_app X E1 in specialize (IH G eq_refl)
         end.
    all: cbn in *; rewrite ?exp_open_sub1, ?exp_open_sub2, ?exp_open_sub_succ,
      ?exp_open_wk, ?ctx_pi_open, ?ctx_fn_open in *.
    all: try solve [ econstructor; eauto ].
    (* a variable: the opened context is the target's, by [Htele] *)
    1-2: match goal with
         | H : (_ ++ E1) ++ gs_tele Ξ1 ∋ # _ : _ |- _ =>
             apply (ctx_lookup_open a) in H;
             rewrite <- List.app_assoc, list_open_app, Htele, List.app_assoc in H
         end; econstructor; eauto.
    (* [δ]: resolution commutes with the opening *)
    match goal with
    | H : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ _ ⍮ _ |- _ => pose proof (Hres _ _ _ _ _ H) as Hr; cbn in Hr
    end; econstructor; eauto.
  Qed.
End OpenTransport.

(** ** Pushing a Frame

    Resolution on [U :: Ξ] of a path shifted by one frame finds what resolution on
    [Ξ] found, shifted likewise: a [qu_rel n] reaches frame [n] of [Ξ] as frame
    [1 + n], and what a filed unit hands back is absolute. *)

Lemma path_open_push_rel : forall n ip, (p_rel n ip)[p_rel 1 nil]p = p_rel (S n) ip.
Proof. intros; cbn; rewrite Nat.sub_0_r; reflexivity. Qed.

Lemma gc_lookup_push : forall Θ U Ξ r Δ b A B,
    Θ ⍮ Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    Θ ⍮ U :: Ξ ∋ᵍ r[p_rel 1 nil]p ⇒ Δ[p_rel 1 nil]p ⍮ ge_def b A[p_rel 1 nil]p B[p_rel 1 nil]p.
Proof.
  intros * Hlk; inversion Hlk; subst.
  - rewrite path_open_push_rel.
    rewrite (list_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ (path_open_shift_shift n))),
      (exp_open_ext_comp _ _ _ (path_open_shift_shift n)),
      (option_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ (path_open_shift_shift n))).
    change (List.skipn n Ξ) with (List.skipn (S n) (U :: Ξ)).
    econstructor; eassumption.
  - rewrite (list_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ (path_open_abs_absorb fp _))),
      (exp_open_ext_comp _ _ _ (path_open_abs_absorb fp _)),
      (option_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ (path_open_abs_absorb fp _))).
    econstructor; eassumption.
Qed.

(** A frame's parameters move from the local context onto the stack. *)
Corollary push_preserves_wf : forall Θ U Ξ,
    ⊢g Θ ⍮ U :: Ξ ->
    (forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ ++ gu_params U -> ⊢ Θ ⍮ U :: Ξ ⍮ Γ[p_rel 1 nil]p) /\
    (forall Γ A M, Θ ⍮ Ξ ⍮ Γ ++ gu_params U ⊢ M : A ->
        Θ ⍮ U :: Ξ ⍮ Γ[p_rel 1 nil]p ⊢ M[p_rel 1 nil]p : A[p_rel 1 nil]p) /\
    (forall Γ A M M', Θ ⍮ Ξ ⍮ Γ ++ gu_params U ⊢ M ≈ M' : A ->
        Θ ⍮ U :: Ξ ⍮ Γ[p_rel 1 nil]p ⊢ M[p_rel 1 nil]p ≈ M'[p_rel 1 nil]p : A[p_rel 1 nil]p) /\
    (forall Γ A A', Θ ⍮ Ξ ⍮ Γ ++ gu_params U ⊢ A ⊆ A' ->
        Θ ⍮ U :: Ξ ⍮ Γ[p_rel 1 nil]p ⊢ A[p_rel 1 nil]p ⊆ A'[p_rel 1 nil]p).
Proof.
  intros * Hg.
  destruct (open_preserves_wf Θ Θ Ξ (U :: Ξ) (gu_params U) nil (p_rel 1 nil))
    as (Hc & He & Hq & Hs);
    [ intros; eapply gc_lookup_push; eassumption | reflexivity | constructor; assumption |].
  repeat split; intros; rewrite <- (List.app_nil_r Γ[p_rel 1 nil]p); eauto.
Qed.
