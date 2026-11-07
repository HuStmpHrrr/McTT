(** * Checking an Application Spine Against the Value of the Head's Type

    The checker infers the type of an application [M N] by normalizing the
    instance [B[Id,,N]] of the codomain of the head's type, once per
    argument.  The value-based spine instead keeps the type as a value: the
    codomain closure applied to the argument's value, as an application or
    a local definition binds it, with no substitution and no normal form in
    between.  The one step behind it ([app_step_readback_upto_proofs]): that
    value reads back to the normal form of [B[Id,,N]], up to proofs.  The
    proofs may differ: [B[Id,,N]] keeps a proof [P] of [B] that reads its
    variable as [P[Id,,N]], the value as [P] under a definition of the
    variable. *)
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Completeness Soundness.
From Mctt.Core.Semantic.PER Require Import CoreTactics.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness Require Import LetCases.
From Mctt.Core.Completeness.Modules Require Import Values.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic.System Require Import Structural.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The value an argument [N] is bound to at a domain of the value [a],
    in the environment [ρ], as an application ([eval_exp_app],
    [eval_exp_app_proof]) and a local definition ([eval_exp_let],
    [eval_exp_let_proof]) bind it. *)
Inductive bound_value (a : domain) (N : exp) (ρ : env) : domain -> Prop :=
(** At a domain of an evaluated kind: the value of [N] *)
| bound_value_evaluated : forall n,
    evaluated_kind (domain_kind a) -> ⟦ N ⟧ ρ ↘ n -> bound_value a N ρ n
(** At a proposition: [N] kept as it is *)
| bound_value_proof :
    domain_kind a = ak_propositional -> bound_value a N ρ ⋆ᵈ⟨N, ρ⟩.

(** The codomain [B] of a [Π] over [A], a type of a large universe or a
    proposition, at the value [n] [N] is bound to, reads back to the normal
    form of [B[Id,,N]] up to proofs.  The value is that of the local
    definition [ℓ A ≔ N in B], which is [B[Id,,N]] by [ζ]
    ([wf_exp_eq_let_zeta]); completeness relates their normal forms. *)
Lemma app_step_readback_upto_proofs : forall Γ κd A B N SA S ρ a n b W W',
    Γ ⊢ A : SA -> sort_kind SA κd ->
    Γ ▹{κd} A ⊢ B : S -> module_body_sort S ->
    Γ ⊢ N : A ->
    initial_env_f Γ ρ ->
    ⟦ A ⟧ ρ ↘ a ->
    bound_value a N ρ n ->
    ⟦ B ⟧ ρ ↦ n ⦂ entry_type_value a ↘ b ->
    Rtyp b in List.length Γ ↘ W' ->
    nbe_ty_f Γ B[Id,,N] W ->
    nf_eq_upto_proofs W' W.
Proof.
  intros * HA HSk HB HS HN Hρ Ha Hn Hb Hr HW.
  pose proof (sort_kind_type_sort _ _ HSk) as HSA.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  (** [B] in the context of the definition [A ≔ N] *)
  assert (HId : Γ ▸ A ≔ N ⊢ˢ Id : Γ ▹{κd} A).
  { eapply wf_sub_id_forget; [ apply wf_sub_id; exact HΓ | exact HA | exact HSk | exact HA | exact HSA | | exact HN ].
    eapply wf_subtyp_refl; [ exact HA | exact HSA | apply wf_exp_eq_refl; exact HA ]. }
  assert (HΓd : ⊢ Γ ▸ A ≔ N) by (eapply wf_ctx_extend_def; [ exact HA | exact HSA | exact HN ]).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB HId) as HB'.
  assert (HSt : type_sort S) by (destruct HS; constructor).
  rewrite !exp_sub_id in HB'.
  (** The sort, a type of a large universe *)
  assert (HSS : exists k, Γ ▸ A ≔ N ⊢ S : Typeω@k).
  { destruct HS as [i |].
    - exists (Datatypes.S i); apply wf_typ; exact HΓd.
    - exists 0; exact (wf_prop_large HΓd). }
  destruct HSS as [k HSk'].
  assert (Hlc : level_closed_sort SA Typeω@k) by constructor.
  assert (Heq : Γ ⊢ ℓ A ≔ N in B ≈ B[Id,,N] : S[Id,,N])
    by (eapply wf_exp_eq_let_zeta; [ exact HA | exact HSA | exact HN | exact HSk' | exact Hlc | exact HB' ]).
  rewrite (type_sort_sub _ _ HSt) in Heq.
  destruct (completeness_ty_sort HSt Heq) as (W1 & W2 & HW1 & HW2 & HE).
  pose proof (functional_nbe_ty _ _ _ _ HW2 HW) as <-.
  inversion HW1 as [ρ1 a1 Hρ1 Ha1 Hr1]; subst.
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  inversion Ha1; subst; functional_eval_rewrite_clear;
    destruct Hn as [n' Hk Hn' | Hk]; functional_eval_rewrite_clear;
    try (exfalso; match goal with H : evaluated_kind ?k, E : ?k = ak_propositional |- _ => rewrite E in H; inversion H end);
    try (exfalso; match goal with H : evaluated_kind (domain_kind ?x), E : domain_kind ?x = ak_propositional |- _ =>
                    rewrite E in H; inversion H end).
  all: functional_eval_rewrite_clear; functional_read_rewrite_clear; exact HE.
Qed.

(** ** The Spine Invariant

    The spine keeps the type of [M N₁ … Nᵢ] as a value [v]; the reference
    keeps its normal form [Wᵢ].  The invariant is that [v] is related, in a
    universe, to the value of [Wᵢ] at the initial environment.  Its proofs
    read a normal form back as a type equal to the one it normalizes
    ([soundness_ty_at_sort]), so they rest on soundness (PENDING M2), as
    the algorithmic soundness the checker's postconditions rest on. *)


(** The type of a normal form, at the initial environment, is related to
    the value of the type it normalizes. *)
Lemma per_univ_of_nbe_ty : forall Γ S T W ρ t,
    type_sort S -> Γ ⊢ T : S -> nbe_ty_f Γ T W -> initial_env_f Γ ρ -> ⟦ T ⟧ ρ ↘ t ->
    exists w (i : nat), ⟦ nf_to_exp W ⟧ ρ ↘ w /\ Dom t ≈ w ∈ per_univ i.
Proof.
  intros * HS HT HW Hρ Ht.
  destruct (rel_typ_sort_at_initial_env HS (soundness_ty_at_sort HS HT HW)) as (ρ1 & t1 & w & i & Hρ1 & Ht1 & Hw & Htw).
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  functional_eval_rewrite_clear.
  exists w, i; split; assumption.
Qed.

(** What one step of the spine gives: the codomain at the argument's
    value, related to the value of the reference's next normal form. *)
#[warnings="-cannot-define-projection"]
Record spine_step_result (ρ' : env) (B' : exp) (a n : domain) (ρ : env) (W1 : nf) : Prop := mk_spine_step_result
  { (** The codomain's value at the argument *)
    spine_step_value : domain
    (** It is the value of the codomain closure at the argument's value *)
  ; spine_step_eval : ⟦ B' ⟧ ρ' ↦ n ⦂ entry_type_value a ↘ spine_step_value
    (** The value of the reference's normal form *)
  ; spine_step_reference : domain
    (** It is that normal form's value at the initial environment *)
  ; spine_step_reference_eval : ⟦ nf_to_exp W1 ⟧ ρ ↘ spine_step_reference
    (** The universe they are related in *)
  ; spine_step_index : nat
    (** They are related there *)
  ; spine_step_related_types : Dom spine_step_value ≈ spine_step_reference ∈ per_univ spine_step_index }.

(** One step of the spine at a relevant codomain and a domain of an
    evaluated kind: if the spine's value [v] of the head's type is related
    to the value of its normal form [Π A. B], then the codomain closure of
    [v] at the value of [N] is related to the value of the normal form [W1]
    of [B[Id,,N]], which is the reference's next type.  Rests on soundness
    ([soundness_ty_at_sort], PENDING M2) through [per_univ_of_nbe_ty]. *)
Lemma spine_step_related : forall Γ κd A B N (k : nat) ρ c a ρ' B' n (i : nat) W1,
    Γ ⊢ a_pi κd ak_relevant (nf_to_exp A) (nf_to_exp B) : Typeω@k ->
    Γ ⊢ N : nf_to_exp A ->
    initial_env_f Γ ρ ->
    ⟦ a_pi κd ak_relevant (nf_to_exp A) (nf_to_exp B) ⟧ ρ ↘ c ->
    Dom d_pi κd ak_relevant a ρ' B' ≈ c ∈ per_univ i ->
    evaluated_kind (domain_kind a) ->
    ⟦ N ⟧ ρ ↘ n ->
    nbe_ty_f Γ (nf_to_exp B)[Id,,N] W1 ->
    spine_step_result ρ' B' a n ρ W1.
Proof.
  intros * HT HN Hρ Hc [R Hv] Hk Hn HW1.
  inversion Hc; subst.
  match goal with Ha0 : ⟦ nf_to_exp A ⟧ ρ ↘ ?x |- _ => rename x into a0 end.
  (** The domains are related, and the codomains at related arguments *)
  destruct (per_univ_elem_pi_inv evaluated_kind_relevant Hv) as (in_rel & out_rel & Hdom & Hcod & _).
  (** The argument's value is related to itself in the domain *)
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ (wf_exp_eq_refl HN)) as HNs.
  pose proof HNs as [env_relΓ HΓr _ _].
  destruct (rel_exp_under_ctx_simple_full_at HΓr HNs) as [kN HNat].
  pose proof (per_ctx_then_per_env_initial_env HΓr (wf_ctx_scoped_exp HN) (wf_ctx_scoped_exp HN)) as [ρ1 [ρ1' [Hρ1 [Hρ1' Hrel]]]].
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ1' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HNat _ _ Hrel) as (a1 & a1' & RA & Ha1 & Ha1' & HRA & HNe).
  functional_eval_rewrite_clear.
  pose proof (per_univ_elem_kind _ _ _ _ Hdom) as Ekd.
  destruct HNe as [Hp | (m & m' & Hm & Hm' & Hmm)]; [ rewrite Ekd, Hp in Hk; inversion Hk |].
  functional_eval_rewrite_clear.
  assert (Ein : in_rel <~> RA)
    by (eapply per_univ_elem_right_irrel; [ exact (proj1 (per_univ_elem_sym _ _ _ _ Hdom)) | exact HRA ]).
  assert (Hnn : in_rel n n) by (apply Ein; exact Hmm).
  destruct (Hcod _ _ Hnn) as [b b0 Hb Hb0 Hbb].
  (** The codomain at the argument is the value of the local definition,
      which is the instance by ζ *)
  pose proof (wf_pi_parts_at _ _ _ _ _ _ _ _ HT) as [SA iU HSk HA HB _].
  cbn [abs_kind_sort] in HB.
  pose proof (sort_kind_type_sort _ _ HSk) as HSA.
  assert (Hlet : ⟦ ℓ (nf_to_exp A) ≔ N in nf_to_exp B ⟧ ρ ↘ b0)
    by (eapply eval_exp_let; [ eassumption | rewrite <- Ekd; exact Hk | exact Hn | exact Hb0 ]).
  assert (HId : Γ ▸ nf_to_exp A ≔ N ⊢ˢ Id : Γ ▹{κd} nf_to_exp A).
  { eapply wf_sub_id_forget; [ apply wf_sub_id; exact HΓ | exact HA | exact HSk | exact HA | exact HSA | | exact HN ].
    eapply wf_subtyp_refl; [ exact HA | exact HSA | apply wf_exp_eq_refl; exact HA ]. }
  assert (HΓd : ⊢ Γ ▸ nf_to_exp A ≔ N) by (eapply wf_ctx_extend_def; [ exact HA | exact HSA | exact HN ]).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB HId) as HB'; rewrite !exp_sub_id in HB'.
  assert (Heq : Γ ⊢ ℓ (nf_to_exp A) ≔ N in nf_to_exp B ≈ (nf_to_exp B)[Id,,N] : Typeω@iU[Id,,N])
    by (eapply wf_exp_eq_let_zeta;
        [ exact HA | exact HSA | exact HN | apply wf_typ; exact HΓd | constructor | exact HB' ]).
  cbn [exp_sub] in Heq.
  destruct (rel_typ_sort_at_initial_env (type_sort_universe iU) Heq) as (ρ2 & a2 & a3 & i2 & Hρ2 & Ha2 & Ha3 & H23).
  assert (ρ2 = ρ) as -> by (eapply functional_initial_env; eassumption).
  functional_eval_rewrite_clear.
  assert (HBN : Γ ⊢ (nf_to_exp B)[Id,,N] : Typeω@iU) by (gen_presups; assumption).
  destruct (per_univ_of_nbe_ty _ _ _ _ _ _ (type_sort_universe iU) HBN HW1 Hρ Ha3) as (w & i3 & Hw & H3w).
  apply (mk_spine_step_result _ _ _ _ _ _ b Hb w Hw i).
  eapply per_univ_trans'; [ exists (out_rel n n Hnn); exact Hbb |].
  eapply per_univ_trans'; eassumption.
Qed.

(** The start of the spine: the value of a normal form of a type at the
    initial environment is related to itself. *)
Lemma spine_start_related : forall Γ S W ρ t,
    type_sort S -> Γ ⊢ nf_to_exp W : S -> initial_env_f Γ ρ -> ⟦ nf_to_exp W ⟧ ρ ↘ t ->
    exists (i : nat), Dom t ≈ t ∈ per_univ i.
Proof.
  intros * HS HW Hρ Ht.
  destruct (rel_typ_sort_at_initial_env HS (wf_exp_eq_refl HW)) as (ρ1 & t1 & t2 & i & Hρ1 & Ht1 & Ht2 & Htt).
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  functional_eval_rewrite_clear.
  exists i; exact Htt.
Qed.

(** The end of the spine: a value related to the value of the normal form
    [W] of a type [T] reads back to [W] up to proofs.  Rests on soundness
    through [idempotent_nbe_ty_sort] (PENDING M2). *)
Lemma spine_readback_upto_proofs : forall Γ S T W ρ t v (i : nat) W',
    type_sort S -> Γ ⊢ T : S -> nbe_ty_f Γ T W -> initial_env_f Γ ρ ->
    ⟦ nf_to_exp W ⟧ ρ ↘ t -> Dom v ≈ t ∈ per_univ i ->
    Rtyp v in List.length Γ ↘ W' ->
    nf_eq_upto_proofs W' W.
Proof.
  intros * HS HT HW Hρ Ht [R Hvt] Hv.
  destruct (per_univ_then_per_top_typ Hvt (List.length Γ)) as [X1 X2 HX1 HX2 HX].
  functional_read_rewrite_clear.
  assert (HWX : nbe_ty_f Γ (nf_to_exp W) X2) by (econstructor; eassumption).
  pose proof (idempotent_nbe_ty_sort HS HT HW HWX) as HWX2.
  etransitivity; [ exact HX | symmetry; exact HWX2 ].
Qed.

End Fixed_GCtx.
