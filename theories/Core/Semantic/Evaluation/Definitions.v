From Stdlib Require Import Morphisms.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations.

Reserved Notation "'⟦' M '⟧' ρ '↘' r" (at level 70, M at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|↘' r" (at level 70, m at level 69, n at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' ρ '↘' ρσ" (at level 70, σ at level 69, ρ at level 69, ρσ at level 69).

Generalizable All Variables.

(** * Evaluation of Weakenings

    A weakening only renames variables, so evaluating one needs no recursion and
    can fail nowhere: it is the total function on environments that looks up the
    renamed variable.  [drop_env] is the special case [φ = ↑], recorded
    below.
 *)
Definition eval_wk (φ : wk) (ρ : env) : env := fun x => ρ (φ x).
Arguments eval_wk _ _ _ /.
Transparent eval_wk.

Notation "'⟪' φ '⟫' ρ" := (eval_wk φ ρ) (at level 2, φ constr at level 60, ρ at level 0) : mctt_scope.

Proposition eval_wk_shift : forall ρ,
    ⟪↑⟫ ρ = ρ↯.
Proof.
  reflexivity.
Qed.

Proposition eval_wk_id : forall ρ,
    ⟪wk_id⟫ ρ = ρ.
Proof.
  reflexivity.
Qed.

(** Unlike the substitution case below, this one *is* an equation, because
    [eval_wk] is a function: weakenings compose diagrammatically on the syntax
    and contravariantly on environments. *)
Proposition eval_wk_compose : forall φ ψ ρ,
    ⟪φ ⊙ ψ⟫ ρ = ⟪φ⟫ (⟪ψ⟫ ρ).
Proof.
  reflexivity.
Qed.

(** A lifted weakening acts on an environment exactly the way its name suggests:
    it leaves the head alone and applies the underlying weakening to the tail.
    Both are conversions — [wk_q] is a [match] on the index, and both [drop_env]
    and [eval_wk] are [fun]s — which is why the corresponding completeness case
    has no work to do beyond naming them. *)
Proposition eval_wk_q_tail : forall φ ρ,
    (⟪(wk_q φ)⟫ ρ)↯ = ⟪φ⟫ (ρ↯).
Proof.
  reflexivity.
Qed.

Proposition eval_wk_q_zero : forall φ ρ,
    ⟪(wk_q φ)⟫ ρ 0 = ρ 0.
Proof.
  reflexivity.
Qed.

#[export]
Instance eval_wk_Proper : Proper (wk_eq ==> env_eq ==> env_eq) eval_wk.
Proof.
  intros φ φ' Hφ ρ ρ' Hρ x. unfold eval_wk. rewrite Hφ. apply Hρ.
Qed.

(** * Evaluation of Expressions

    Three mutually defined relations: evaluation proper, its
    [ℕ]-eliminator case, and semantic application.  There is no [eval_exp_sub]
    clause: [M[σ]] is not a form of expression any more, so there is nothing to
    give a rule for.
 *)
Inductive eval_exp : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( ⟦ Type@i ⟧ ρ ↘ 𝕌@i )
| eval_exp_var :
  `( ⟦ #x ⟧ ρ ↘ (ρ x) )
| eval_exp_nat :
  `( ⟦ ℕ ⟧ ρ ↘ ℕᵈ )
| eval_exp_zero :
  `( ⟦ zero ⟧ ρ ↘ zeroᵈ )
| eval_exp_succ :
  `( ⟦ M ⟧ ρ ↘ m ->
     ⟦ succ M ⟧ ρ ↘ succᵈ m )
| eval_exp_natrec :
  `( ⟦ M ⟧ ρ ↘ m ->
     ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r )
| eval_exp_pi :
  `( ⟦ A ⟧ ρ ↘ a ->
     ⟦ Π A B ⟧ ρ ↘ Πᵈ a ρ B )
| eval_exp_fn :
  `( ⟦ λ A M ⟧ ρ ↘ λᵈ ρ M )
| eval_exp_app :
  `( ⟦ M ⟧ ρ ↘ m ->
     ⟦ N ⟧ ρ ↘ n ->
     $| m & n |↘ r ->
     ⟦ M $ N ⟧ ρ ↘ r )
where "'⟦' e '⟧' ρ '↘' r" := (eval_exp e ρ r)
with eval_natrec : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( ⟦ MZ ⟧ ρ ↘ mz ->
     ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ mz )
| eval_natrec_succ :
  `( ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r ->
     ⟦ MS ⟧ ρ ↦ b ↦ r ↘ ms ->
     ⟦rec succᵈ b return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ ms )
| eval_natrec_neut :
  `( ⟦ MZ ⟧ ρ ↘ mz ->
     ⟦ A ⟧ ρ ↦ ⇑ b m ↘ a ->
     ⟦rec ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ ⇑ a recᵈ m under ρ return A | zero -> mz | succ -> MS end )
where "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' ρ '↘' r" := (eval_natrec A MZ MS m ρ r)
with eval_app : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( ⟦ M ⟧ ρ ↦ n ↘ m ->
     $| λᵈ ρ M & n |↘ m )
| eval_app_neut :
  `( ⟦ B ⟧ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n |↘ ⇑ b (m $ᵈ ⇓ a n) )
where "'$|' m '&' n '|↘' r" := (eval_app m n r)
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app : mctt.

(** [eval_exp_var] up to conversion.  Its own conclusion carries the value
    [(ρ x)], a *flexible application*, so unifying it with a goal whose value is
    some other application — [ρσ x], say, which is the shape [eval_sub_intro]
    always leaves — makes unification read [ρ] and [x] off the wrong term and
    fail.  Since substitution is now an operation, those goals are everywhere:
    every pointwise evaluation of a concrete substitution reduces to a variable
    on the left and to an environment lookup on the right, and the two are
    convertible but not syntactically equal.  Naming the index and discharging
    the lookup by conversion is what this is for. *)
Proposition eval_exp_var_eq : forall x ρ m,
    ρ x = m ->
    ⟦ #x ⟧ ρ ↘ m.
Proof.
  intros * <-. apply eval_exp_var.
Qed.

(** * Evaluation of Substitutions

    A substitution is a function from variables to expressions, and its
    evaluation is defined pointwise: [ρσ] is the environment that assigns
    to each variable the value of the expression [σ] sends it to.  This is a
    [Definition], not a fourth clause of the induction above, for the same
    reason [wf_sub] is a record rather than an inductive family — there is no
    grammar of substitutions left to recurse on.
 *)
Definition eval_sub (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, eval_exp (σ x) ρ (ρσ x).
Arguments eval_sub : simpl never.

Notation "'⟦' σ '⟧s' ρ '↘' ρσ" := (eval_sub σ ρ ρσ) : mctt_scope.

(** Its introduction and elimination principles.  Everything below, and
    everything downstream, goes through these rather than unfolding
    [eval_sub]. *)
Proposition eval_sub_intro : forall σ ρ ρσ,
    (forall x, ⟦ (σ x) ⟧ ρ ↘ (ρσ x)) ->
    ⟦ σ ⟧s ρ ↘ ρσ.
Proof.
  intros * H. exact H.
Qed.

Proposition eval_sub_index : forall σ ρ ρσ,
    ⟦ σ ⟧s ρ ↘ ρσ ->
    forall x, ⟦ (σ x) ⟧ ρ ↘ (ρσ x).
Proof.
  intros * H. exact H.
Qed.

(** Both arguments that [eval_sub] inspects pointwise may be replaced by
    pointwise-equal ones.  The *input* environment may not — evaluation does not
    respect [env_eq], see the closing comment of this section. *)
#[export]
Instance eval_sub_Proper : Proper (sb_eq ==> eq ==> env_eq ==> iff) eval_sub.
Proof.
  intros σ σ' Hσ ρ ρ0 <- ρσ ρσ' Hρσ.
  split; intros H; apply eval_sub_intro; intros x;
    [ rewrite <- (Hσ x), <- (Hρσ x) | rewrite (Hσ x), (Hρσ x) ];
    apply eval_sub_index; assumption.
Qed.

(** ** The Substitutions that Compute

    The substitutions whose evaluation *can* be computed: the image of a
    weakening under [ι], the identity, and an extension.  These four facts are
    the whole bridge between substitution as an operation on terms and as a
    transformation of environments.
 *)
Lemma eval_sub_of_wk : forall φ ρ,
    ⟦ (ι φ) ⟧s ρ ↘ ⟪φ⟫ ρ.
Proof.
  intros. apply eval_sub_intro. intros. simpl. apply eval_exp_var.
Qed.

Lemma eval_sub_id : forall ρ,
    ⟦ Id ⟧s ρ ↘ ρ.
Proof.
  intros. apply eval_sub_intro. intros. simpl. apply eval_exp_var.
Qed.

Lemma eval_sub_shift : forall ρ,
    ⟦ Wk ⟧s ρ ↘ ρ↯.
Proof.
  intros. apply eval_sub_of_wk.
Qed.

Lemma eval_sub_extend : forall σ ρ ρσ M m,
    ⟦ σ ⟧s ρ ↘ ρσ ->
    ⟦ M ⟧ ρ ↘ m ->
    ⟦ σ,,M ⟧s ρ ↘ ρσ ↦ m.
Proof.
  intros * ? ?. apply eval_sub_intro.
  intros [| x]; simpl; [ assumption | apply eval_sub_index; assumption ].
Qed.

(** The weakening of an extension, which is the shape every four-value pattern
    about a substitution extension needs for its two *outer* environments.
    [sb_wk_extend] pushes the weakening into both components, so this is
    [eval_sub_extend] modulo that equation — but the equation is a [sb_eq], not an
    [eq], so using it means going through [eval_sub_Proper].  Doing so once here
    keeps the completeness substitution cases free of setoid rewriting. *)
Lemma eval_sub_wk_extend : forall σ M φ ρ ρσ m,
    ⟦ (sb_wk σ φ) ⟧s ρ ↘ ρσ ->
    ⟦ M⟨φ⟩ ⟧ ρ ↘ m ->
    ⟦ (sb_wk (σ,,M) φ) ⟧s ρ ↘ ρσ ↦ m.
Proof.
  intros * ? ?.
  rewrite sb_wk_extend.
  apply eval_sub_extend; assumption.
Qed.

(** The two evaluations of a *lifted* substitution, which are the only reason
    [sb_wk_q] exists.  [q σ] is the extension of [σ⟨↑⟩] by [#0], so evaluating it
    extends the evaluation of [σ⟨↑⟩] by the head of the environment; postcomposing
    by [φ] reads index [φ 0] instead.  Both heads are values *already in* [ρ] —
    nothing is evaluated for them — which is why the completeness case for [q σ]
    has only two head values to relate rather than four. *)
Lemma eval_sub_q : forall σ ρ ρσ,
    ⟦ (sb_wk σ ↑) ⟧s ρ ↘ ρσ ->
    ⟦ q σ ⟧s ρ ↘ ρσ ↦ (ρ 0).
Proof.
  intros * ?.
  apply eval_sub_extend; [ assumption | apply eval_exp_var ].
Qed.

Lemma eval_sub_wk_q : forall σ φ ρ ρσ,
    ⟦ (sb_wk (sb_wk σ ↑) φ) ⟧s ρ ↘ ρσ ->
    ⟦ (sb_wk (q σ) φ) ⟧s ρ ↘ ρσ ↦ (ρ (φ 0)).
Proof.
  intros * ?.
  rewrite sb_wk_q.
  apply eval_sub_extend; [| apply eval_exp_var ].
  rewrite <- sb_wk_wk.
  assumption.
Qed.

(** The single substitution [Id ,, M]. *)
Corollary eval_sub_single : forall ρ M m,
    ⟦ M ⟧ ρ ↘ m ->
    ⟦ Id,,M ⟧s ρ ↘ ρ ↦ m.
Proof.
  intros. apply eval_sub_extend; [ apply eval_sub_id | assumption ].
Qed.

(** *Pre*composition by a weakening, on the other hand, does compute: [ι φ ⨟ σ]
    sends [x] to [σ (φ x)], so evaluating it only reindexes the environment [σ]
    already evaluates to.  No expression is transported across the weakening —
    every [(ι φ) x] is a variable — which is exactly what fails in the three
    equations below.  [eval_sub_shift_pre] is the instance at [φ := ↑]. *)
Lemma eval_sub_wk_pre : forall φ σ ρ ρσ,
    ⟦ σ ⟧s ρ ↘ ρσ ->
    ⟦ (ι φ) ⨟ σ ⟧s ρ ↘ ⟪φ⟫ ρσ.
Proof.
  intros * H. apply eval_sub_intro.
  intros x. exact (eval_sub_index _ _ _ H (φ x)).
Qed.

Corollary eval_sub_shift_pre : forall σ ρ ρσ,
    ⟦ σ ⟧s ρ ↘ ρσ ->
    ⟦ Wk ⨟ σ ⟧s ρ ↘ ρσ↯.
Proof.
  intros. apply (eval_sub_wk_pre wk_shift). assumption.
Qed.

(** No such lemma exists for [q σ], for a general [σ ⨟ τ], or for [σ⟨φ⟩], and
    none can:

      ⟦σ⟨φ⟩⟧(ρ) = ⟦σ⟧(⟪φ⟫ ρ),  ⟦M[σ]⟧(ρ) = ⟦M⟧(⟦σ⟧(ρ)),  ⟦σ ⨟ τ⟧(ρ) = ⟦σ⟧(⟦τ⟧(ρ))

    all *fail* as equations once substitution is an operation rather than a
    delayed constructor, because a closure [λ ρ M] captures both an environment
    and a syntactic body and the two sides capture different ones.  They hold
    only as relations in the PER model, which is what the four-value pattern of
    [Core/Semantic/PER/Chain.v] is for. *)

#[export]
Hint Resolve eval_sub_of_wk eval_sub_id eval_sub_shift eval_sub_extend eval_sub_wk_extend
             eval_sub_q eval_sub_wk_q
             eval_sub_single eval_sub_wk_pre eval_sub_shift_pre : mctt.
#[export]
Hint Resolve eval_sub_index : mctt.
