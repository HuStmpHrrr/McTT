(** * Soundness of Normalization by Evaluation

    The fundamental theorem of the gluing model, instantiated at the identity
    embedding and the identity substitution.  The gluing model compares a
    term with its readback up to proofs: the readback is equal up to its
    proofs to a normal form whose annotation ([nf_annotate_proofs]) is equal
    to the term ([soundness_of_glu]).  Two terms whose normal forms are
    equal up to proofs are then equal ([soundness_upto_proofs]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core Require Import Completeness.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Levels Require Export LevelEq.
From Mctt.Core.Soundness Require Export FundamentalTheorem.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Completeness.Consequences Require Import AnnotatedUpto.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A typed term that glues has a normal form, equal up to its proofs to
    one whose annotation ([nf_annotate_proofs]) is equal to the term: its
    glued value at the initial environment is read back
    ([realize_glu_elem_top]); it is the term's value at an evaluated kind
    and the term kept at a proposition, as [nbe_term] has it. *)
Lemma soundness_of_glu : forall {Γ M A},
    Γ ⊢ M : A ->
    Γ ⊩ M : A ->
    exists W W', nbe_f Γ M A W /\ nf_eq_upto_proofs W W' /\ Γ ⊢ M ≈ nf_annotate_proofs W' : A.
Proof.
  intros * H HG.
  assert (⊢ Γ) by mauto 3.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ]
      by mauto 3 using completeness_fundamental_ctx, rel_ctx_wf_per_ctx_env.
  destruct HG as [Sb ? i ?].
  pose proof (wf_ctx_scoped_exp H) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption) HsΓ HsΓ) as [ρ [? ?]].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (Γ ⊢ˢ Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  pose proof (realize_glu_elem_top _ _ _ _ glu_rel_exp_with_sub_univ _ _ _ _ glu_rel_exp_with_sub_exp) as Htop.
  destruct Htop.
  destruct (glu_elem_top_per (length Γ)) as [W W0 HW _ _].
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  destruct (glu_elem_top_read _ _ _ Hid HW) as (W' & HWW' & HeqW).
  rewrite !exp_wk_id, !exp_sub_id in HeqW.
  exists W, W'; split; [| split; [ exact HWW' | exact HeqW ] ].
  econstructor; [ eassumption | eassumption |].
  (** The term's value at an evaluated kind, the term kept at a proposition *)
  destruct (domain_kind a) eqn:Hk; cbn [glu_term_value] in glu_rel_exp_with_sub_eval.
  - eapply nbe_term_evaluated; [ rewrite Hk; constructor | exact glu_rel_exp_with_sub_eval | exact HW ].
  - subst m; eapply nbe_term_proof; [ exact Hk | exact HW ].
  - eapply nbe_term_evaluated; [ rewrite Hk; constructor | exact glu_rel_exp_with_sub_eval | exact HW ].
Qed.

End Fixed_GCtx.

(** A typed term has a normal form, equal to it: it glues by the
    fundamental theorem of the gluing model, read at the identity
    embedding. *)
Theorem soundness : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists W, nbe Θ Ξ Γ M A W /\ Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ W : A.
Proof.
  (* PENDING M2: the gluing model for the Prop core *)
Admitted.

(** Two terms of one type whose normal forms are equal up to their proofs
    ([nf_eq_upto_proofs]) are equal: completeness compares normal forms
    only up to proofs, and proofs are equal by proof irrelevance wherever
    they occur.  For example, with [f : P → ℕ] and [h1 h2 : P], the normal
    forms of [f h1] and [f h2] are [⇑ⁿ{ak_relevant} (f $ⁿ nf_proof #1)] and
    [⇑ⁿ{ak_relevant} (f $ⁿ nf_proof #0)], related, and [f h1 ≈ f h2 : ℕ] holds by
    proof irrelevance under the application.  Milestone M2 proves it from
    the gluing model. *)
Theorem soundness_upto_proofs : forall {Θ Ξ Γ M M' A W W'},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    nbe Θ Ξ Γ M A W ->
    nbe Θ Ξ Γ M' A W' ->
    nf_eq_upto_proofs W W' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A.
Proof.
  intros * HM HM' Hn Hn' E.
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) as Hg.
  pose proof (glu_gctx_embedding_refl _ _ Hg) as Hμ.
  destruct (@soundness_of_glu (gc_mk Θ Ξ) _ _ _ HM (proj1 (proj2 soundness_fundamental) _ _ _ _ _ HM _ _ Hμ))
    as (W1 & W1' & Hn1 & E1 & HE1).
  destruct (@soundness_of_glu (gc_mk Θ Ξ) _ _ _ HM' (proj1 (proj2 soundness_fundamental) _ _ _ _ _ HM' _ _ Hμ))
    as (W2 & W2' & Hn2 & E2 & HE2).
  pose proof (functional_nbe _ _ _ _ _ Hn Hn1) as <-.
  pose proof (functional_nbe _ _ _ _ _ Hn' Hn2) as <-.
  (** The two annotated normal forms, typed, are equal up to their proofs:
      equal ([nf_annotate_proofs_upto]) *)
  assert (E12 : nf_eq_upto_proofs W1' W2') by (etransitivity; [ symmetry; exact E1 | etransitivity; [ exact E | exact E2 ] ]).
  pose proof (nf_annotate_proofs_upto _ _ _ _ _ _ (presup_exp_eq_right HE1) (ex_intro _ _ (presup_exp_eq_right HE2)) E12) as H12.
  etransitivity; [ exact HE1 | etransitivity; [ exact H12 | symmetry; exact HE2 ] ].
Qed.

(** The normal form NbE computes is equal to the term. *)
Theorem soundness' : forall {Θ Ξ Γ M A W},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    nbe Θ Ξ Γ M A W ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ W : A.
Proof.
  intros * [? []]%soundness ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma soundness_ty : forall {Γ} {i : nat} {A},
    Γ ⊢ A : Typeω@i ->
    exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i.
Proof.
  intros.
  assert (exists W', nbe_f Γ A Typeω@i W' /\ Γ ⊢ A ≈ W' : Typeω@i) as [? [?%nbe_type_to_nbe_ty Heq]] by mauto using soundness.
  firstorder.
Qed.

Lemma soundness_ty' : forall {Γ} {i : nat} {A B},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    Γ ⊢ A ≈ B : Typeω@i.
Proof.
  intros.
  assert (exists B', nbe_ty_f Γ A B' /\ Γ ⊢ A ≈ B' : Typeω@i) as [? [? Heq]] by mauto using soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

(** [nbe] of a type, at a large universe it lives in. *)
Lemma nbe_ty_to_nbe_type : forall Γ T i W, nbe_ty_f Γ T W -> nbe_f Γ T Typeω@i W.
Proof.
  intros * H; inversion_clear H.
  eapply nbe_evaluated_intro; [ eassumption | constructor | eassumption | constructor; eassumption | constructor ].
Qed.

(** [nbe] of a type, at [Prop]: a proposition is a relevant term of
    [Prop], read back as a type. *)
Lemma nbe_ty_to_nbe_prop : forall Γ T W, nbe_ty_f Γ T W -> nbe_f Γ T Propₘ W.
Proof.
  intros * H; inversion_clear H.
  econstructor; [ eassumption | constructor | eapply nbe_term_evaluated; [ constructor | eassumption | constructor; eassumption ] ].
Qed.

(** The same at [LevelSort]: a type of levels is a relevant term of
    [LevelSort], read back as a type. *)
Lemma nbe_ty_to_nbe_level_sort : forall Γ T W, nbe_ty_f Γ T W -> nbe_f Γ T LevelSort W.
Proof.
  intros * H; inversion_clear H.
  econstructor; [ eassumption | constructor | eapply nbe_term_evaluated; [ constructor | eassumption | constructor; eassumption ] ].
Qed.

(** A type of a sort ([type_sort]) is equal there to its normal form. *)
Lemma soundness_ty_at_sort : forall {Γ S A W},
    type_sort S ->
    Γ ⊢ A : S ->
    nbe_ty_f Γ A W ->
    Γ ⊢ A ≈ W : S.
Proof.
  intros * [i | |] HA Hn;
    [ exact (soundness_ty' HA Hn)
    | exact (soundness' HA (nbe_ty_to_nbe_prop _ _ _ Hn))
    | exact (soundness' HA (nbe_ty_to_nbe_level_sort _ _ _ Hn)) ].
Qed.

(** The normal form of a level of sort [n] is a canonical level of sort [n]:
    its constant is of a tier at most [n], and each atom is a level of its
    own sort ([nf_lvl_well_scoped]).  It is read off the gluing of the level,
    whose atoms are glued at their types.  The algorithmic layer needs it to
    trust the sorts an atom of a normal form carries. *)
Theorem soundness_lvl_well_scoped : forall {Γ M n W},
    Γ ⊢ M : Level@n ->
    nbe_f Γ M Level@n W ->
    nf_lvl_well_scoped n Γ W.
Proof.
  intros * H Hn.
  assert (⊢ Γ) by mauto 3.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ]
      by mauto 3 using completeness_fundamental_ctx, rel_ctx_wf_per_ctx_env.
  pose proof (soundness_fundamental_exp _ _ _ H) as HM.
  destruct HM as [Sb HSb _ _].
  pose proof (wf_ctx_scoped_exp H) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption) HsΓ HsΓ) as [ρ [? ?]].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (HId : Γ ⊢ˢ Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct (glu_rel_exp_level_elim (n := n) HSb (soundness_fundamental_exp _ _ _ H) _ _ _ HId)
    as [m [Hev [_ Hglu]]].
  destruct (nbe_evaluated_inv Hn ρ _ ltac:(eassumption) ltac:(econstructor) ltac:(cbn; constructor)) as (m' & Hm' & Hr).
  functional_eval_rewrite_clear.
  assert (Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  exact (proj2 (Hglu _ _ _ ltac:(eassumption) (read_nf_level_sort _ _ 0 _ _ Hr))).
Qed.

(** A neutral is an atom of sort [s] of the normal form of a typed level:
    the atoms whose coherence soundness gives
    ([soundness_nbe_atoms_upto_proofs]).  The atom is one of the list
    ([List.In]), not a neutral equal to one up to proofs. *)
#[warnings="-cannot-define-projection"]
Record nbe_level_atom (Γ : ctx) (s : nat) (a : ne) : Prop := mk_nbe_level_atom
  { (** The level *)
    nbe_level_atom_exp : exp
    (** Its sort *)
  ; nbe_level_atom_level_sort : nat
    (** The constant of its normal form *)
  ; nbe_level_atom_constant : o2
    (** The atoms of its normal form *)
  ; nbe_level_atom_atoms : list level_atom
    (** The offset of the atom *)
  ; nbe_level_atom_offset : nat
    (** The level is a level of its sort *)
  ; nbe_level_atom_typed : Γ ⊢ nbe_level_atom_exp : Level@nbe_level_atom_level_sort
    (** Its normal form *)
  ; nbe_level_atom_nbe : nbe_f Γ nbe_level_atom_exp Level@nbe_level_atom_level_sort
                           (nf_lvl nbe_level_atom_constant nbe_level_atom_atoms)
    (** The atom is one of its atoms, at sort [s] *)
  ; nbe_level_atom_in : List.In (mk_level_atom nbe_level_atom_offset s a) nbe_level_atom_atoms }.

(** Two atoms of normal forms of levels, of one sort and equal up to their
    proofs, are equal levels: a canonical form keeps one of them in place
    of the other ([level_atoms_coherent]).  Typed levels hold no proofs
    ([nbe_level_proof_free]), so the two atoms are the same neutral, a
    level of its sort ([soundness_lvl_well_scoped]).  For example, the atom
    [g (λ x : F h. x)] with a proof [h] in an annotation cannot occur:
    [F : P → LevelSort] is not typable, [LevelSort] being in no universe. *)
Theorem soundness_nbe_atoms_upto_proofs : forall {Γ s a b},
    nbe_level_atom Γ s a ->
    nbe_level_atom Γ s b ->
    ne_eq_upto_proofs a b ->
    Γ ⊢ (a : exp) ≈ (b : exp) : Level@s.
Proof.
  intros * [Ma na ca xsa ja Hta Hnbea Hina] [Mb nb cb xsb jb Htb Hnbeb Hinb] Hab.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  (** The atom holds no proof: it is the other one *)
  pose proof (nbe_level_proof_free Hta (wf_level _ _ _ _ HΓ) Hnbea) as Hpf.
  pose proof (ne_proof_free_eq _ _ (level_atoms_proof_free_In _ _ _ _ _ Hpf Hina) Hab) as <-.
  (** a level of its sort *)
  destruct (soundness_lvl_well_scoped Hta Hnbea) as [_ Hws].
  exact (wf_exp_eq_refl (level_atoms_well_scoped_In _ _ _ _ _ _ Hws Hina)).
Qed.

(** The atoms of the normal forms of typed levels are coherent. *)
Lemma level_atoms_coherent_of_nbe : forall {Γ} xs,
    (forall j s a, List.In (mk_level_atom j s a) xs -> nbe_level_atom Γ s a) ->
    @level_atoms_coherent gc_deps gc_stack Γ xs.
Proof.
  intros * Hxs j s a j' b Ha Hb Hab.
  exact (soundness_nbe_atoms_upto_proofs (Hxs _ _ _ Ha) (Hxs _ _ _ Hb) Hab).
Qed.

(** The atoms of the normal form of a typed level are atoms of normal
    forms of typed levels. *)
Lemma nbe_level_atom_of_nbe : forall {Γ M n c xs},
    Γ ⊢ M : Level@n ->
    nbe_f Γ M Level@n (nf_lvl c xs) ->
    forall j s a, List.In (mk_level_atom j s a) xs -> nbe_level_atom Γ s a.
Proof. intros * HM Hnbe j s a Hin; exact (mk_nbe_level_atom _ _ _ _ _ _ _ _ HM Hnbe Hin). Qed.

End Fixed_GCtx.
