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
From Mctt.Core Require Import Base Completeness.
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

End Fixed_GCtx.
