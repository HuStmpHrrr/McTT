(** * Consequences of Completeness: types are rigid

    Distinct type constructors are never judgmentally equal, and [Typeω@i ≈ Typeω@j]
    forces [i = j].  Each proof reads the judgment at the initial environment and
    inverts the resulting [per_univ]; only the variable-against-variable case needs
    work, since there the values are neutrals whose levels must be turned back
    into indices. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [x] is bound by an assumption of [Γ], not by a definition. *)
Definition ctx_ass (Γ : ctx) (x : nat) : Prop :=
  exists A, List.nth_error Γ x = Some (ce_ass A).

(** A variable bound by an assumption evaluates, in the initial environment of
    its context, to the neutral at its own level. *)
Lemma eval_var_at_initial_env : forall {Γ x} {i : nat} {ρ a},
    ctx_ass Γ x ->
    initial_env_f Γ ρ ->
    ⟦ #x ⟧ ρ ↘ a ->
    Γ ⊢ #x : Typeω@i ->
    x < length Γ /\ exists b, a = ⇑! b (length Γ - x - 1).
Proof.
  intros * [A Hlookup] Hρ Hev Hx.
  pose proof (initial_env_spec _ _ _ _ Hρ Hlookup) as [b Heq].
  split.
  - apply List.nth_error_Some; congruence.
  - exists b.
    eapply functional_eval_exp; [ exact Hev | apply eval_exp_var_eq; exact Heq ].
Qed.

Lemma exp_eq_typ_implies_eq_level : forall {Γ} {i : nat} {j k},
    Γ ⊢ Typeω@i ≈ Typeω@j : Typeω@k ->
    i = j.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = 𝕌ω@i) as ->
      by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ]).
  assert (a' = 𝕌ω@j) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  invert_per_univ_elem HR; congruence.
Qed.

Hint Resolve exp_eq_typ_implies_eq_level : mctt.

(** The same at either tier, and across them: the universes at two different
    indices are never equal, since their values are not related. *)
Lemma exp_eq_ulvl_tm_implies_eq : forall {Γ} {u v : uidx} {k},
    Γ ⊢ ulvl_tm u ≈ ulvl_tm v : Typeω@k ->
    u = v.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = ulvl_val u) as ->
      by (eapply functional_eval_exp; [ exact Ha | apply eval_ulvl_tm ]).
  assert (a' = ulvl_val v) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_ulvl_tm ]).
  destruct u as [n | n], v as [m | m]; cbn in HR;
    invert_per_univ_elem HR; try congruence.
  (** Two small universes at literal levels: their levels are related, so
      they have the same realiser, which is the literal. *)
  match goal with H : per_lvl _ _ |- _ => apply per_lvl_real in H; cbn in H end.
  congruence.
Qed.

Corollary exp_eq_univ_implies_eq_level : forall {Γ} {n m k},
    Γ ⊢ Type⟨𝕃ᵒ n⟩ ≈ Type⟨𝕃ᵒ m⟩ : Typeω@k ->
    n = m.
Proof.
  intros * H.
  assert (us n = us m) as Heq by (eapply (exp_eq_ulvl_tm_implies_eq (u := us n) (v := us m)); exact H).
  injection Heq; trivial.
Qed.

Hint Resolve exp_eq_univ_implies_eq_level : mctt.

(** A type headed by a type constructor, or a variable. *)
Inductive is_typ_constr : typ -> Prop :=
(** A large universe *)
| typ_is_typ_constr : forall i, is_typ_constr Typeω@i
(** A small universe at any level term: in a context with an axiom of type
    [Level] a closed type may be the universe at that axiom. *)
| univ_is_typ_constr : forall t, is_typ_constr Type⟨t⟩
(** A type of levels *)
| level_is_typ_constr : forall n, is_typ_constr Level@n
(** The unit type *)
| True_is_typ_constr : is_typ_constr ⊤
(** The empty type *)
| False_is_typ_constr : is_typ_constr ⊥
(** A [Π] *)
| pi_is_typ_constr : forall A B, is_typ_constr Π A B
(** A variable *)
| var_is_typ_constr : forall x, is_typ_constr #x
(** An inductive type at its parameters. *)
| ind_is_typ_constr : forall p k Ms, is_typ_constr (apps_exp (a_ind p k) Ms)
(** A record type at its parameters. *)
| record_is_typ_constr : forall p Ms, is_typ_constr (apps_exp (a_record p) Ms)
.
Hint Constructors is_typ_constr : mctt.

(** A type is rigid in [Γ] when it is a type constructor or a variable bound
    by an assumption.  A variable bound by a definition is not rigid, since it
    is equal to its body. *)
Inductive rigid_typ (Γ : ctx) : typ -> Prop :=
(** A large universe *)
| typ_is_rigid : forall i, rigid_typ Γ Typeω@i
(** A small universe at a literal level *)
| univ_is_rigid : forall n, rigid_typ Γ Type⟨𝕃ᵒ n⟩
(** A type of levels *)
| level_is_rigid : forall n, rigid_typ Γ Level@n
(** The unit type *)
| True_is_rigid : rigid_typ Γ ⊤
(** The empty type *)
| False_is_rigid : rigid_typ Γ ⊥
(** A [Π] *)
| pi_is_rigid : forall A B, rigid_typ Γ (Π A B)
(** A variable bound by an assumption *)
| var_is_rigid : forall x, ctx_ass Γ x -> rigid_typ Γ #x
(** An inductive type at its parameters *)
| ind_is_rigid : forall p k Ms, rigid_typ Γ (apps_exp (a_ind p k) Ms)
(** A record type at its parameters *)
| record_is_rigid : forall p Ms, rigid_typ Γ (apps_exp (a_record p) Ms)
.
Hint Constructors rigid_typ : mctt.

(** An inductive type evaluates to an inductive type value. *)
Lemma eval_apps_ind_inv : forall p k xs ys r, $*| d_ind p k xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_ind p k (xs ++ ys).
Proof.
  intros p k xs ys; revert xs; induction ys as [| y ys IH]; intros xs r H; inversion H; subst.
  - rewrite List.app_nil_r; reflexivity.
  - match goal with H1 : $| d_ind _ _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
    match goal with H2 : $*| _ & ys | _ ⍮ _ ↘ _ |- _ => apply IH in H2 end.
    subst; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma eval_ind_value : forall p k Ms ρ a, ⟦ apps_exp (a_ind p k) Ms ⟧ ρ ↘ a -> exists ms, a = d_ind p k ms.
Proof.
  intros * H; apply eval_apps_exp in H as (f & ms & Hf & _ & Hap).
  inversion Hf; subst; apply eval_apps_ind_inv in Hap; eauto.
Qed.

(** A record type evaluates to a record type value. *)
Lemma eval_apps_record_inv : forall p xs ys r, $*| d_record p xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_record p (xs ++ ys).
Proof.
  intros p xs ys; revert xs; induction ys as [| y ys IH]; intros xs r H; inversion H; subst.
  - rewrite List.app_nil_r; reflexivity.
  - match goal with H1 : $| d_record _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
    match goal with H2 : $*| _ & ys | _ ⍮ _ ↘ _ |- _ => apply IH in H2 end.
    subst; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma eval_record_value : forall p Ms ρ a, ⟦ apps_exp (a_record p) Ms ⟧ ρ ↘ a -> exists ms, a = d_record p ms.
Proof.
  intros * H; apply eval_apps_exp in H as (f & ms & Hf & _ & Hap).
  inversion Hf; subst; apply eval_apps_record_inv in Hap; eauto.
Qed.

(** A universe as a term: a large one, or a small one at any level term. *)
Inductive univ_term : exp -> Prop :=
| univ_term_typ : forall i, univ_term Typeω@i
| univ_term_suniv : forall t, univ_term Type⟨t⟩.
Hint Constructors univ_term : mctt.

Theorem is_typ_constr_and_exp_eq_var_implies_eq_var : forall Γ A x i,
    rigid_typ Γ A ->
    ctx_ass Γ x ->
    Γ ⊢ A ≈ #x : Typeω@i ->
    A = #x.
Proof.
  intros * Histyp Hx H.
  assert (Γ ⊢ A : Typeω@i) by mauto 2.
  assert (Γ ⊢ #x : Typeω@i) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_var_at_initial_env Hx Hρ Ha' ltac:(eassumption)) as [Hxlt [b ->]].
  (** Only the variable case survives: [⇑! b _] has no other constructor to be
      related to. *)
  destruct Histyp;
    [ assert (a = 𝕌ω@i0) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(dlvl_lit n)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  - (** [Π A B] evaluates to a [Π]-value once its domain does. *)
    match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
  - (** Two neutral variables related in [per_bot]: read both back at
        [length Γ] and compare the indices they produce. *)
    f_equal.
    enough (length Γ - x0 - 1 = length Γ - x - 1) by lia.
    match_by_head1 per_bot ltac:(fun H => destruct (H (length Γ)) as [? []]).
    match_by_head read_ne ltac:(fun H => directed dependent destruction H).
    lia.
Qed.

Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.

Theorem is_typ_constr_and_exp_eq_typ_implies_eq_typ : forall Γ A i j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Typeω@i : Typeω@j ->
    A = Typeω@i.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = 𝕌ω@i) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  destruct Histyp;
    [ assert (a = 𝕌ω@i0) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(dlvl_lit n)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  - congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.

Theorem is_typ_constr_and_exp_eq_univ_implies_eq_univ : forall Γ A n j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Type⟨𝕃ᵒ n⟩ : Typeω@j ->
    A = Type⟨𝕃ᵒ n⟩.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = 𝕌@(dlvl_lit n)) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_univ, eval_exp_llit ]).
  destruct Histyp;
    [ assert (a = 𝕌ω@i) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(dlvl_lit n0)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  - (** The two levels are related, so the two literals are the same
        realiser. *)
    match goal with H : per_lvl _ _ |- _ => apply per_lvl_real in H; cbn in H end.
    congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_univ_implies_eq_univ : mctt.


(** ** Universe Terms

    A universe as a term: a large one, or a small one at any level term.  The
    small ones at a level term are not [rigid_typ] — their level is a term —
    so these lemmas state what a judgment with a universe term on one side
    says about the other. *)

Lemma univ_term_ulvl_tm : forall u, univ_term (ulvl_tm u).
Proof. intros []; constructor. Qed.
Hint Resolve univ_term_ulvl_tm : mctt.

Lemma pi_not_univ_term : forall A B, ~ univ_term (Π A B).
Proof. intros * H; inversion H. Qed.

(** A rigid type equal to a small universe at a level term is a universe: its
    value is related to a small universe's, and only a small universe's is. *)
Theorem is_typ_constr_and_exp_eq_suniv_tm : forall Γ A t j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    univ_term A.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha'; subst.
  destruct Histyp; try solve [ constructor ];
    [ inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Corollary rigid_typ_eq_univ_term : forall Γ A U k,
    rigid_typ Γ A ->
    univ_term U ->
    Γ ⊢ A ≈ U : Typeω@k ->
    univ_term A.
Proof.
  intros * HA HU H; destruct HU.
  - assert (A = Typeω@i) as -> by mauto 3; constructor.
  - eapply is_typ_constr_and_exp_eq_suniv_tm; eassumption.
Qed.

(** A [Π] is never a universe term. *)
Corollary pi_univ_term_absurd : forall Γ A B U k,
    univ_term U ->
    Γ ⊢ Π A B ≈ U : Typeω@k ->
    False.
Proof.
  intros * HU H.
  eapply pi_not_univ_term, rigid_typ_eq_univ_term; [ constructor | exact HU | exact H ].
Qed.

(** The two tiers are distinct: a large universe is never a small one. *)
Lemma exp_eq_typ_suniv_absurd : forall Γ i t k,
    Γ ⊢ Typeω@i ≈ Type⟨t⟩ : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = 𝕌ω@i) as -> by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ]).
  inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

(** A rigid type equal to a universe is that universe, at either tier. *)
Corollary rigid_typ_eq_ulvl_tm : forall Γ A (u : uidx) k,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ ulvl_tm u : Typeω@k ->
    A = ulvl_tm u.
Proof. intros * ? H; destruct u as [n | i]; cbn in H |- *; mauto 3. Qed.

(** A type constructor other than a universe is never a universe: the goal is
    closed by inspecting the two tiers. *)
Lemma var_neq_ulvl_tm : forall x (u : uidx), #x <> ulvl_tm u.
Proof. intros ? []; discriminate. Qed.

(** A [Π] is never a universe, at either tier. *)
Corollary pi_ulvl_tm_absurd : forall Γ A B (u : uidx) k,
    Γ ⊢ Π A B ≈ ulvl_tm u : Typeω@k ->
    False.
Proof.
  intros * H; destruct u as [n | i]; cbn in H;
    [ assert (Π A B = Type⟨𝕃ᵒ n⟩) as Heq by mauto 3 | assert (Π A B = Typeω@i) as Heq by mauto 3 ];
    discriminate Heq.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve exp_eq_typ_implies_eq_level exp_eq_univ_implies_eq_level : mctt.
#[export]
Hint Constructors is_typ_constr rigid_typ : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_univ_implies_eq_univ : mctt.
#[export]
Hint Resolve pi_ulvl_tm_absurd rigid_typ_eq_ulvl_tm var_neq_ulvl_tm : mctt.
#[export]
Hint Constructors univ_term : mctt.
#[export]
Hint Resolve univ_term_ulvl_tm : mctt.
(** A concrete type that is not a universe is not a universe term. *)
#[export] Hint Extern 1 (~ univ_term _) =>
  (let Hu := fresh "Hu" in intro Hu; inversion Hu; fail) : mctt.
#[export] Hint Extern 1 (forall _ : uidx, _ <> ulvl_tm _) => (intros []; discriminate) : mctt.
#[export] Hint Extern 1 (_ <> ulvl_tm _) => (destruct_all uidx; discriminate) : mctt.
