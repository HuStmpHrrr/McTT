From Stdlib Require Import Lia List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution GlobalCtx.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρσ at level 69).

Generalizable All Variables.

(** * Evaluation of Expressions

    Three mutually defined relations: evaluation proper, its
    [ℕ]-eliminator case, and semantic application.  All three are relative to
    the global context [Θ ⍮ Ξ], which does not change during NbE.  A global is
    looked up there ([gc_resolve], which follows names and nothing else): a
    transparent definition unfolds to its body — stored closed, so evaluated in
    the empty environment — and anything else is a neutral at its stored type.
    A parameter is a neutral at the type its frame stores for it.  No rule
    applies a substitution, a weakening or a module substitution to a term, or
    builds one. *)
Inductive eval_exp (Θ : gdeps) (Ξ : gstack) : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( ⟦ Type@i ⟧ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌@i )
| eval_exp_var :
  `( ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρ x )
| eval_exp_nat :
  `( ⟦ ℕ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ℕᵈ )
| eval_exp_zero :
  `( ⟦ zero ⟧ Θ ⍮ Ξ ⍮ ρ ↘ zeroᵈ )
| eval_exp_succ :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ succᵈ m )
| eval_exp_natrec :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ a ρ B )
| eval_exp_fn :
  `( ⟦ λ A M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ ρ M )
| eval_exp_app :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** δ: a transparent definition is its body. *)
| eval_exp_glob_delta :
  `( gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M)) ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ m ->
     ⟦ a_glob p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m )
(** An opaque definition or an axiom stays a neutral at its type. *)
| eval_exp_glob_neut :
  `( gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
     ⟦ a_glob p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_glob p) )
(** A module parameter is a neutral at its type, which mentions no
    λ-variable. *)
| eval_exp_param :
  `( gs_param Ξ lp = Some T ->
     ⟦ T ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
     ⟦ a_param lp ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_param lp) )
where "'⟦' e '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_exp Θ Ξ e ρ r)
with eval_natrec (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz )
| eval_natrec_succ :
  `( ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ MS ⟧ Θ ⍮ Ξ ⍮ ρ ↦ b ↦ r ↘ ms ->
     ⟦rec succᵈ b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ms )
| eval_natrec_neut :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦rec ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a recᵈ m under ρ return A | zero -> mz | succ -> MS end )
where "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_natrec Θ Ξ A MZ MS m ρ r)
with eval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ ρ M & n | Θ ⍮ Ξ ↘ m )
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
where "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (eval_app Θ Ξ m n r)
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

(** [eval_exp_var] up to conversion: its value [ρ x] is a flexible
    application, which unification would read [ρ] and [x] off the wrong term
    of. *)
Proposition eval_exp_var_eq : forall {Θ Ξ} x (ρ : env) m,
    ρ x = m ->
    ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m.
Proof. intros * <-; apply eval_exp_var. Qed.

(** * Evaluation of Substitutions

    Pointwise, at every variable: each value of [ρσ] is what the substitution
    computes from [ρ].  A list ends, so past its end [ρσ] reads [zeroᵈ]; a result
    therefore exists only when [σ] is, far enough out, a variable past [ρ]. *)
Definition eval_sub (Θ : gdeps) (Ξ : gstack) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρσ x.
Arguments eval_sub : simpl never.

Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" := (eval_sub Θ Ξ σ ρ ρσ) : mctt_scope.

Lemma eval_sub_id : forall {Θ Ξ} ρ, ⟦ Id ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ.
Proof. intros * x; constructor. Qed.

Lemma eval_sub_shift : forall {Θ Ξ} ρ, ⟦ Wk ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ↯.
Proof. intros * x; rewrite env_var_drop; constructor. Qed.

Lemma eval_sub_extend : forall {Θ Ξ} σ ρ ρσ M m,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ σ,,M ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H HM [| x]; [ assumption | apply H ].
Qed.

Corollary eval_sub_single : forall {Θ Ξ} ρ M m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ Id,,M ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ m.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id | assumption ].
Qed.

Proposition eval_sub_intro : forall {Θ Ξ} σ (ρ ρσ : env),
    (forall x, ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρσ x) ->
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ.
Proof. intros * H. exact H. Qed.

Proposition eval_sub_index : forall {Θ Ξ} σ (ρ ρσ : env),
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    forall x, ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρσ x.
Proof. intros * H. exact H. Qed.

(** Both arguments that [eval_sub] inspects pointwise may be replaced by
    pointwise-equal ones; the input environment may not — a closure captures
    it. *)
#[export]
Instance eval_sub_Proper : forall {Θ Ξ}, Proper (sb_eq ==> eq ==> env_eq ==> iff) (eval_sub Θ Ξ).
Proof.
  intros Θ Ξ σ σ' Hσ ρ ρ0 <- ρσ ρσ' Hρσ.
  split; intros H x; [ rewrite <- (Hσ x), <- (Hρσ x) | rewrite (Hσ x), (Hρσ x) ]; apply H.
Qed.

(** ** The Substitutions that Compute

    The image of a weakening under [ι] — one that moves no variable down, so
    that [⟪φ⟫ ρ] is [ρ ∘ φ] everywhere — the identity, and an extension. *)
Lemma eval_sub_of_wk : forall {Θ Ξ} φ ρ `{Hφ : WkMono φ},
    ⟦ ι φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ⟪φ⟫ ρ.
Proof.
  intros Θ Ξ φ ρ Hφ x; cbn; rewrite (eval_wk_eq _ _ Hφ x); apply eval_exp_var.
Qed.

(** The weakening of an extension. *)
Lemma eval_sub_wk_extend : forall {Θ Ξ} σ M φ ρ ρσ m,
    ⟦ sb_wk σ φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ M[φ]ʷ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ sb_wk (σ,,M) φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof. intros * ? ? [| x]; [ assumption | apply H ]. Qed.

(** The two evaluations of a lifted substitution: [q σ] extends [σ[↑]] by
    [#0], so its head is a value already in [ρ]. *)
Lemma eval_sub_q : forall {Θ Ξ} σ ρ ρσ,
    ⟦ sb_wk σ ↑ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ q σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ ρ 0.
Proof.
  intros * H [| x]; [ cbn; apply eval_exp_var |].
  rewrite sb_q_succ; exact (H x).
Qed.

Lemma eval_sub_wk_q : forall {Θ Ξ} σ φ ρ ρσ,
    ⟦ sb_wk (sb_wk σ ↑) φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ sb_wk (q σ) φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ ρ (φ 0).
Proof.
  intros * H [| x]; cbn [sb_wk]; [ rewrite sb_q_zero; cbn; apply eval_exp_var |].
  rewrite sb_q_succ; exact (H x).
Qed.

(** Precomposition by a weakening reindexes the environment [σ] evaluates to. *)
Lemma eval_sub_wk_pre : forall {Θ Ξ} φ σ ρ ρσ `{Hφ : WkMono φ},
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ (ι φ) ⨟ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ⟪φ⟫ ρσ.
Proof.
  intros Θ Ξ φ σ ρ ρσ Hφ H x; rewrite (eval_wk_eq _ _ Hφ x); exact (H (φ x)).
Qed.

Corollary eval_sub_shift_pre : forall {Θ Ξ} σ ρ ρσ,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ Wk ⨟ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ↯.
Proof. intros * H x; rewrite env_var_drop; exact (H (S x)). Qed.

#[export]
Hint Resolve eval_sub_id eval_sub_shift eval_sub_extend eval_sub_single eval_sub_wk_extend
             eval_sub_q eval_sub_wk_q eval_sub_shift_pre : mctt.
#[export]
Hint Resolve eval_sub_index : mctt.
