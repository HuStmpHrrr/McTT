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
From Mctt.Core.Semantic Require Import Realizability.
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
    Γ ⊢ Type@n ≈ Type@m : Typeω@k ->
    n = m.
Proof.
  intros * H.
  assert (us n = us m) as Heq by (eapply (exp_eq_ulvl_tm_implies_eq (u := us n) (v := us m)); exact H).
  injection Heq; trivial.
Qed.

Hint Resolve exp_eq_univ_implies_eq_level : mctt.

Inductive is_typ_constr : typ -> Prop :=
| typ_is_typ_constr : forall i, is_typ_constr Typeω@i
(** A small universe at any level term: in a context with an axiom of type
    [Level] a closed type may be the universe at that axiom. *)
| univ_is_typ_constr : forall t, is_typ_constr Type⟨t⟩
| level_is_typ_constr : is_typ_constr Level
| nat_is_typ_constr : is_typ_constr ℕ
| True_is_typ_constr : is_typ_constr ⊤
| False_is_typ_constr : is_typ_constr ⊥
| pi_is_typ_constr : forall A B, is_typ_constr Π A B
| var_is_typ_constr : forall x, is_typ_constr #x
.
Hint Constructors is_typ_constr : mctt.

(** A type is rigid in [Γ] when it is a type constructor or a variable bound
    by an assumption.  A variable bound by a definition is not rigid, since it
    is equal to its body. *)
Inductive rigid_typ (Γ : ctx) : typ -> Prop :=
| typ_is_rigid : forall i, rigid_typ Γ Typeω@i
| univ_is_rigid : forall n, rigid_typ Γ Type@n
| level_is_rigid : rigid_typ Γ Level
| nat_is_rigid : rigid_typ Γ ℕ
| True_is_rigid : rigid_typ Γ ⊤
| False_is_rigid : rigid_typ Γ ⊥
| pi_is_rigid : forall A B, rigid_typ Γ (Π A B)
| var_is_rigid : forall x, ctx_ass Γ x -> rigid_typ Γ #x
.
Hint Constructors rigid_typ : mctt.

(** A universe as a term: a large one, or a small one at any level term. *)
Inductive univ_term : exp -> Prop :=
| univ_term_typ : forall i, univ_term Typeω@i
| univ_term_suniv : forall t, univ_term Type⟨t⟩.
Hint Constructors univ_term : mctt.

(** A well-formed type constructor is rigid in a context whose variables are
    all bound by assumptions, unless it is a universe: a small universe at a
    level term is not rigid, its level being a term. *)
Lemma rigid_typ_of_is_typ_constr : forall Γ A i,
    (forall x B, Γ ∋ #x : B -> ctx_ass Γ x) ->
    is_typ_constr A ->
    Γ ⊢ A : Typeω@i ->
    rigid_typ Γ A \/ univ_term A.
Proof.
  intros * HΓ HA HAi.
  destruct HA; try solve [ left; mauto 2 | right; constructor ].
  left.
  destruct (wf_vlookup_inversion HAi) as [B [Hlookup _]].
  constructor; eapply HΓ; eassumption.
Qed.

(** The context of [consistency]. *)
Lemma ctx_ass_of_lookup_typ : forall i x B,
    ⋅ ▹ Typeω@i ∋ #x : B ->
    ctx_ass (⋅ ▹ Typeω@i) x.
Proof.
  intros * H.
  dependent destruction H; [ eexists; reflexivity |].
  inversion H.
Qed.

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
    | assert (a = Levelᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_level ])
    | assert (a = ℕᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
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
    | assert (a = Levelᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_level ])
    | assert (a = ℕᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
    invert_per_univ_elem HR.
  - congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.

Theorem is_typ_constr_and_exp_eq_univ_implies_eq_univ : forall Γ A n j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Type@n : Typeω@j ->
    A = Type@n.
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
    | assert (a = Levelᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_level ])
    | assert (a = ℕᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
    invert_per_univ_elem HR.
  - (** The two levels are related, so the two literals are the same
        realiser. *)
    match goal with H : per_lvl _ _ |- _ => apply per_lvl_real in H; cbn in H end.
    congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_univ_implies_eq_univ : mctt.

Theorem is_typ_constr_and_exp_eq_nat_implies_eq_nat : forall Γ A j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ ℕ : Typeω@j ->
    A = ℕ.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = ℕᵈ) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_nat ]).
  destruct Histyp;
    [ assert (a = 𝕌ω@i) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(dlvl_lit n)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | assert (a = Levelᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_level ])
    | reflexivity
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
    invert_per_univ_elem HR.
  match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mctt.

(** ** Universe Terms

    A universe as a term: a large one, or a small one at any level term.  The
    small ones at a level term are not [rigid_typ] — their level is a term —
    so these lemmas state what a judgment with a universe term on one side
    says about the other. *)

Lemma univ_term_ulvl_tm : forall u, univ_term (ulvl_tm u).
Proof. intros []; constructor. Qed.
Hint Resolve univ_term_ulvl_tm : mctt.

Lemma var_not_univ_term : forall x, ~ univ_term #x.
Proof. intros x H; inversion H. Qed.

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
    [ assert (a = Levelᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_level ])
    | assert (a = ℕᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
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
    [ assert (Π A B = Type@n) as Heq by mauto 3 | assert (Π A B = Typeω@i) as Heq by mauto 3 ];
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
Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mctt.
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
