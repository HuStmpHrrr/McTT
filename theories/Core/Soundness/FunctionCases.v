(** * The Rules of Functions

    The rules of [Π] in the gluing model: the type former, [λ],
    application, their congruences, [β] and [η].  The lemmas they rest on
    are in [LogicalRelation/Functions.v]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.Lets LogicalRelation.Universes.
From Mctt.Core.Completeness Require LogicalRelation.Levels LogicalRelation.Functions.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Levels
  LogicalRelation.Subtyping LogicalRelation.Variables LogicalRelation.Instance LogicalRelation.Universes
  LogicalRelation.Functions.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Generalizable All Variables.

(** [Π] at a universe ([wf_pi]): at a large universe, or at a small one. *)
Lemma glu_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A : abs_kind_sort κd U ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : (abs_kind_sort κc U)[↑]ʷ ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_pi κd κc A B : abs_kind_sort κc U ).
Proof.
  glu_inst_intro.
  match goal with HU : (exists i, ?U = Typeω@i) \/ _ |- _ => destruct HU as [[? ->] | (L & n & -> & HL)] end.
  - rewrite abs_kind_sort_wk in *; cbn [exp_wk] in *.
    rewrite abs_kind_sort_sub; cbn [exp_sub].
    assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A))
      by (eapply glu_rel_sub_inst_q; [ exact Hτ | eassumption | apply sort_kind_abs_kind_sort ]).
    eapply glu_rel_exp_pi_large; glu_inst_premise.
  - (** The domain, at a large universe, for the lifted instance *)
    match goal with HA : glu_rel_exp_under_sub Γ A _ |- _ => rename HA into HAs end.
    assert (HAl : @glu_rel_exp_under_sub (gc_mk Θ2 Ξ2) Γ A (abs_kind_sort κd Typeω@n)).
    { eapply glu_rel_exp_under_sub_conv_typ; [| exact HAs ].
      intros Γ0 τ0 Hτ0 HA0; rewrite !abs_kind_sort_sub in *; cbn [exp_sub] in *.
      eapply glu_rel_exp_kind_sort_small_large; [ glu_inst | exact HA0 ]. }
    assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A))
      by (eapply glu_rel_sub_inst_q; [ exact Hτ | exact HAl | apply sort_kind_abs_kind_sort ]).
    rewrite abs_kind_sort_sub; cbn [exp_sub].
    eapply glu_rel_exp_pi_small; glu_inst_premise.
Qed.

Lemma glu_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ λ A M : a_pi κd κc A B ).
Proof.
  glu_inst_intro.
  assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A)) by (eapply glu_rel_sub_inst_q; eassumption).
  eapply (glu_rel_exp_fn (A := A[τ]) (Srt := Srt)); glu_inst_premise.
Qed.

Lemma glu_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : a_pi κd κc A B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M $ N : B[Id,,N] ).
Proof.
  glu_inst_intro.
  assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A)) by (eapply glu_rel_sub_inst_q; eassumption).
  (** The codomain's instance at the argument, the witness *)
  assert (Hext : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) Γ' (τ,,N[τ]) (Γ ▹{κd} A)).
  { eapply glu_rel_sub_inst_extend; [ exact Hτ | eapply glu_rel_exp_under_sub_wf; eassumption | eassumption
                                    | eapply glu_rel_exp_under_sub_inst_renaming; eassumption ]. }
  rewrite <- exp_sub_extend_comm.
  eapply (glu_rel_exp_app (A := A[τ]) (Srt := Srt) (B := B[q τ])); try glu_inst_premise.
  rewrite exp_sub_q_extend; glu_inst.
Qed.

(** The equations glue their context, which their domain's premise
    does. *)
Lemma glu_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : abs_kind_sort κd U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
