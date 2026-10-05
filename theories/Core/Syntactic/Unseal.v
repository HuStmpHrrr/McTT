(** * Unsealing a Global Context

    [abstract] only hides a body from conversion: a sealed constant still has
    one.  Unsealing a global context makes every constant transparent; an
    axiom, which has no body, stays stuck.  That only adds the δ-equation of
    [wf_exp_eq_const_unfold], so every judgment of a global context holds of
    its unsealing ([unseal_preserves_wf]), and without axioms the unsealed
    context is transparent ([gc_unseal_transparent]): every well-typed term
    computes to a canonical form there. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import Syntax_Notations GlobalCtx_Notations.

Definition gd_unseal (d : gdecl) : gdecl :=
  match d with
  | gd_unit fp U => gd_unit fp U
  | gd_const c A oM _ => gd_const c A oM true
  end.

Definition gc_unseal (Θ : gctx) : gctx := map gd_unseal Θ.

Lemma gc_unit_unseal : forall Θ fp, gc_unit (gc_unseal Θ) fp = gc_unit Θ fp.
Proof. induction Θ as [| [fq U | c A M b] Θ IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

Lemma gc_const_unseal : forall Θ c,
    gc_const (gc_unseal Θ) c = option_map (fun r => let '(A, M, _) := r in (A, M, true)) (gc_const Θ c).
Proof.
  induction Θ as [| [fq U | c' A M b] Θ IH]; intros; cbn; rewrite ?IH; [ reflexivity | reflexivity |].
  destruct (qname_beq c c'); reflexivity.
Qed.

Lemma gc_const_unseal_some : forall Θ c A oM b,
    gc_const Θ c = Some (A, oM, b) -> gc_const (gc_unseal Θ) c = Some (A, oM, true).
Proof. intros * H; rewrite gc_const_unseal, H; reflexivity. Qed.

Lemma gc_const_unseal_none : forall Θ c, gc_const Θ c = None -> gc_const (gc_unseal Θ) c = None.
Proof. intros * H; rewrite gc_const_unseal, H; reflexivity. Qed.

Lemma gc_unseal_transparent : forall Θ, gc_no_axioms Θ -> gc_transparent (gc_unseal Θ).
Proof.
  intros Θ Hna c A oM b H; rewrite gc_const_unseal in H.
  destruct (gc_const Θ c) as [[[A' oM'] b'] |] eqn:E; cbn in H; [| discriminate ].
  injection H as -> -> ->; split; [ reflexivity | exact (Hna _ _ _ _ E) ].
Qed.

Lemma member_type_unseal : forall Θ,
    (forall Γ H ch R, member_type Θ Γ H ch R -> member_type (gc_unseal Θ) Γ H ch R) /\
    (forall Γ U ch R, unit_member_type Θ Γ U ch R -> unit_member_type (gc_unseal Θ) Γ U ch R).
Proof.
  intros Θ; apply member_type_both_ind; intros; econstructor; eauto.
  rewrite gc_unit_unseal; eassumption.
Qed.

Corollary member_type_unseal_mt : forall Θ Γ H ch R,
    member_type Θ Γ H ch R -> member_type (gc_unseal Θ) Γ H ch R.
Proof. intros Θ; exact (proj1 (member_type_unseal Θ)). Qed.

Lemma member_unfold_unseal : forall Θ Γ H x, member_unfold (gc_unseal Θ) Γ H x = member_unfold Θ Γ H x.
Proof.
  intros; unfold member_unfold; generalize (x :: nil); induction H; intros; cbn; rewrite ?gc_unit_unseal, ?IHmodexp; reflexivity.
Qed.

Theorem unseal_preserves_wf :
  (forall Θ Γ, ⊢ Θ ⍮ Γ -> ⊢ gc_unseal Θ ⍮ Γ) /\
  (forall Θ Γ A M, Θ ⍮ Γ ⊢ M : A -> gc_unseal Θ ⍮ Γ ⊢ M : A) /\
  (forall Θ Γ A M M', Θ ⍮ Γ ⊢ M ≈ M' : A -> gc_unseal Θ ⍮ Γ ⊢ M ≈ M' : A) /\
  (forall Θ Γ A A', Θ ⍮ Γ ⊢ A ⊆ A' -> gc_unseal Θ ⍮ Γ ⊢ A ⊆ A') /\
  (forall Θ Γ Ψ Ψ', Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> gc_unseal Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
  (forall Θ Γ U U', Θ ⍮ Γ ⊢ᵘ U ≈ U' -> gc_unseal Θ ⍮ Γ ⊢ᵘ U ≈ U') /\
  (forall Θ Γ H H', Θ ⍮ Γ ⊢ᵐ H ≈ H' -> gc_unseal Θ ⍮ Γ ⊢ᵐ H ≈ H') /\
  (forall Θ, ⊢g Θ -> ⊢g gc_unseal Θ).
Proof.
  apply wf_mut_ind_all; intros;
    try solve [ econstructor; eauto using gc_const_unseal_some, gc_const_unseal_none,
                  member_type_unseal_mt;
                rewrite ?member_unfold_unseal, ?gc_unit_unseal; eassumption ].
Qed.

Corollary unseal_exp : forall Θ Γ A M, Θ ⍮ Γ ⊢ M : A -> gc_unseal Θ ⍮ Γ ⊢ M : A.
Proof. exact (proj1 (proj2 unseal_preserves_wf)). Qed.

Corollary unseal_exp_eq : forall Θ Γ A M M', Θ ⍮ Γ ⊢ M ≈ M' : A -> gc_unseal Θ ⍮ Γ ⊢ M ≈ M' : A.
Proof. exact (proj1 (proj2 (proj2 unseal_preserves_wf))). Qed.

Corollary unseal_subtyp : forall Θ Γ A A', Θ ⍮ Γ ⊢ A ⊆ A' -> gc_unseal Θ ⍮ Γ ⊢ A ⊆ A'.
Proof. exact (proj1 (proj2 (proj2 (proj2 unseal_preserves_wf)))). Qed.

Corollary unseal_gctx : forall Θ, ⊢g Θ -> ⊢g gc_unseal Θ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 unseal_preserves_wf))))))). Qed.
