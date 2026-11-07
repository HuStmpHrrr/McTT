(** * Deciding Type Formers

    Whether a term of a normal type is a type former of an inductive type
    ([ind_former_dec]) or of a record type ([record_former_dec]), as an
    alias command and a local alias of a type require ([Core.TypedElab.Fill]),
    with what the decisions read: the [Π]s of a normal type
    ([nf_pi_tele_spec]), the term at the variables they bind
    ([applied_vars_typed]), and whether a normal type is a universe
    ([nf_is_universe_dec]). *)

From Stdlib Require Import List Lia.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness Completeness.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core Require Import TypedElab.
From Mctt.Core.Syntactic.System.Inductives Require Import Runs IndCong.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import Lookup NbE IndDecl.
Import Syntax_Notations GlobalCtx_Notations.

(** A normal type is the [Π] over its domains ([nf_pi_tele]), a telescope
    of assumptions, of its codomain. *)
Lemma nf_pi_tele_spec : forall W Ds C, nf_pi_tele W = (Ds, C) -> nf_to_exp W = ctx_pi Ds (nf_to_exp C) /\ all_assumptions Ds.
Proof.
  induction W; intros * E; cbn [nf_pi_tele] in E;
    try (injection E as <- <-; split; [ reflexivity | constructor ]).
  destruct a0; try (injection E as <- <-; split; [ reflexivity | constructor ]).
  destruct (nf_pi_tele W2) as [Ds' C'] eqn:E2; injection E as <- <-.
  destruct (IHW2 _ _ eq_refl) as [HW Ha].
  cbn [nf_to_exp]; rewrite ctx_pi_snoc, <- HW; split; [ reflexivity |].
  apply List.Forall_app; split; [ exact Ha | constructor; [ do 2 eexists; reflexivity | constructor ] ].
Qed.

(** A [Π] into a relevant codomain typed at a sort is a type of a large
    universe: its value at the initial environment is a [Π] of that kind
    ([typed_at_sort_of_initial_kind]). *)
Lemma relevant_pi_large : forall Θ Ξ Γ κ A B S, type_sort S -> Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κ ak_relevant A B : S ->
    exists j : nat, Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κ ak_relevant A B : Typeω@j.
Proof.
  intros * HS HT.
  pose proof (@completeness_fundamental_exp (gc_mk Θ Ξ) _ _ _ HT) as HTs.
  destruct (@rel_exp_under_ctx_at_initial_env (gc_mk Θ Ξ) _ _ _ _ (wf_ctx_scoped_exp HT) (wf_exp_scoped_term _ _ _ _ _ HT)
              (wf_exp_scoped_term _ _ _ _ _ HT) HTs) as [ρ a W W' Hρ Ea HW _ _].
  destruct HW as [w Hp _ | m w _ Em _].
  - exfalso; destruct HS; inversion Ea; subst; cbn in Hp; discriminate Hp.
  - destruct (@typed_at_sort_of_initial_kind (gc_mk Θ Ξ) _ _ _ _ _ HS HT Hρ Em) as [k Hk].
    inversion Em; subst; exists k; exact Hk.
Qed.

(** A term of a normal type, at the variables of the type's domains, is of
    its codomain past them: a relevant [Π]'s, at a large universe. *)
Lemma applied_vars_typed : forall Θ Ξ Γ M W Ds C, Θ ⍮ Ξ ⍮ Γ ⊢ M : nf_to_exp W -> nf_pi_tele W = (Ds, C) ->
    Θ ⍮ Ξ ⍮ Ds ++ Γ ⊢ exp_applied_to_vars M (List.length Ds) : nf_to_exp C.
Proof.
  intros * HM Ep; destruct (nf_pi_tele_spec _ _ _ Ep) as [HW Ha]; rewrite HW in HM.
  destruct Ds as [| e Ds0] using List.rev_ind.
  - cbn in HM |- *; unfold exp_applied_to_vars; cbn.
    rewrite exp_wk_id_ext by (intros x; cbn; lia); exact HM.
  - assert (He : exists κ A, e = ce_ass κ A)
      by (unfold all_assumptions in Ha; apply List.Forall_app in Ha as [_ He]; inversion He as [| ? ? He0]; exact He0).
    destruct He as (κ & A & ->).
    pose proof (presup_exp_typ HM) as Hty; rewrite ctx_pi_snoc in Hty.
    inversion Hty as [? S HS HT | ]; subst.
    destruct (relevant_pi_large _ _ _ _ _ _ _ HS HT) as [i HT'].
    rewrite <- ctx_pi_snoc in HT'.
    pose proof (ctx_pi_inv_outer _ _ _ _ Ha HT') as HC.
    exact (wf_apps_vars _ _ _ _ _ _ _ Ha (presup_exp_ctx HC) HC HM).
Qed.

(** Whether a normal type is a universe. *)
Definition nf_is_universe_dec (W : nf) : {nf_is_universe W} + {~ nf_is_universe W} :=
  match W as W0 return {nf_is_universe W0} + {~ nf_is_universe W0} with
  | nf_typ _ => left I
  | nf_univ _ _ => left I
  | _ => right (fun H => H)
  end.

(** A typed term has the termination order of its normalization. *)
Lemma typed_nbe_order {Θ Ξ Γ M A} : Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe_order Θ Ξ Γ M A.
Proof. intros H; destruct (soundness H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

(** Whether a term of a normal type is a type former of an inductive type
    ([ind_former]): its normal form at the variables of the type's
    domains, computed once, is decisive, since normal forms are unique. *)
Definition ind_former_dec (F : FCtx) (Γ : ctx) (M : exp) (W : nf)
    (HM : fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ M : nf_to_exp W) :
    {ind_former (fc_deps F) (fc_stack F) Γ M W} + {~ ind_former (fc_deps F) (fc_stack F) Γ M W}.
Proof.
  unfold ind_former.
  destruct (nf_pi_tele W) as [Ds C] eqn:Ep.
  destruct (nf_is_universe_dec C) as [Hu | Hu]; [| right; intros [Hu' _]; contradiction ].
  destruct (nbe_impl F (Ds ++ Γ) (exp_applied_to_vars M (List.length Ds)) (nf_to_exp C)
              (typed_nbe_order (applied_vars_typed _ _ _ _ _ _ _ HM Ep))) as [W' HW'].
  destruct W';
    try (right; intros (_ & p0 & k0 & Rs0 & Hn); pose proof (functional_nbe _ _ _ _ _ HW' Hn) as E; discriminate E).
  left; split; [ exact Hu | do 3 eexists; exact HW' ].
Defined.

(** Likewise of a record type ([record_former]). *)
Definition record_former_dec (F : FCtx) (Γ : ctx) (M : exp) (W : nf)
    (HM : fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ M : nf_to_exp W) :
    {record_former (fc_deps F) (fc_stack F) Γ M W} + {~ record_former (fc_deps F) (fc_stack F) Γ M W}.
Proof.
  unfold record_former.
  destruct (nf_pi_tele W) as [Ds C] eqn:Ep.
  destruct (nf_is_universe_dec C) as [Hu | Hu]; [| right; intros [Hu' _]; contradiction ].
  destruct (nbe_impl F (Ds ++ Γ) (exp_applied_to_vars M (List.length Ds)) (nf_to_exp C)
              (typed_nbe_order (applied_vars_typed _ _ _ _ _ _ _ HM Ep))) as [W' HW'].
  destruct W';
    try (right; intros (_ & p0 & Rs0 & Hn); pose proof (functional_nbe _ _ _ _ _ HW' Hn) as E; discriminate E).
  left; split; [ exact Hu | do 2 eexists; exact HW' ].
Defined.

(** Being a type former of an inductive type, a normal form, moves along an
    equivalence. *)
Lemma equiv_ind_former : forall Θ Θ' Ξ Γ M W, gds_equiv Θ Θ' -> ind_former Θ Ξ Γ M W -> ind_former Θ' Ξ Γ M W.
Proof.
  intros * He; unfold ind_former; destruct (nf_pi_tele W) as [Ds C].
  intros (Hu & p & k & Rs & Hn); split; [ exact Hu | exists p, k, Rs; exact (equiv_nbe _ _ _ He _ _ _ _ Hn) ].
Qed.

(** Likewise of a record type. *)
Lemma equiv_record_former : forall Θ Θ' Ξ Γ M W, gds_equiv Θ Θ' -> record_former Θ Ξ Γ M W -> record_former Θ' Ξ Γ M W.
Proof.
  intros * He; unfold record_former; destruct (nf_pi_tele W) as [Ds C].
  intros (Hu & p & Rs & Hn); split; [ exact Hu | exists p, Rs; exact (equiv_nbe _ _ _ He _ _ _ _ Hn) ].
Qed.
