From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String Morphisms Relation_Definitions RelationClasses.

From Mctt.Core.Syntactic Require Export Syntax.

(** * The Semantic Domain

    An environment is the list of values of the λ-variables in scope, indexed
    by de Bruijn index; for [Θ ⍮ Ξ ⍮ Γ] these are the variables of [Γ].  The
    global context does not change during NbE, so it is not part of the
    environment; evaluation takes it as a separate argument.  Module parameters
    are λ-variables and so live in the environment. *)

Inductive domain : Set :=
| d_nat : domain
| d_pi : domain -> list domain -> exp -> domain
| d_univ : nat -> domain
| d_zero : domain
| d_succ : domain -> domain
| d_True : domain
| d_true : domain
| d_False : domain
| d_fn : list domain -> exp -> domain
| d_neut : domain -> domain_ne -> domain
with domain_ne : Set :=
(** [x] is a de Bruijn level, not an index: it names a variable absolutely and
    does not change under binders. *)
| d_var : forall (x : nat), domain_ne
| d_app : domain_ne -> domain_nf -> domain_ne
| d_natrec : list domain -> typ -> domain -> exp -> domain_ne -> domain_ne
(** The [⊥]-eliminator on a neutral, with its motive as a closure. *)
| d_exfalso : list domain -> typ -> domain_ne -> domain_ne
(** An opaque definition or an axiom. *)
| d_glob : path -> domain_ne
with domain_nf : Set :=
| d_dom : domain -> domain -> domain_nf.

Notation env := (list domain).

Derive NoConfusion for domain domain_ne domain_nf.

(** The value of the variable [#x], or [zeroᵈ] past the end of the list.  A
    well-typed term only reads the variables in its context, so it never sees
    the default.  As a coercion, it lets an environment be applied as a
    function, [ρ x]. *)
Fixpoint env_var (ρ : env) (x : nat) : domain :=
  match x with
  | 0 => List.hd d_zero ρ
  | S x' => env_var (List.tl ρ) x'
  end.
#[warning="-uniform-inheritance"]
Coercion env_var : list >-> Funclass.

(** [env_var] is [nth], but defined by recursion on the index so that [ρ↯ x]
    is [ρ (S x)] by conversion. *)
Lemma env_var_nth : forall ρ x, env_var ρ x = List.nth x ρ d_zero.
Proof. intros ρ x; revert ρ; induction x; intros [| d ρ]; cbn; auto; rewrite IHx; destruct x; reflexivity. Qed.

Definition extend_env (ρ : env) (d : domain) : env := d :: ρ.
Arguments extend_env _ _ /.

Definition drop_env (ρ : env) : env := List.tl ρ.
Arguments drop_env _ /.

#[global] Bind Scope mctt_scope with domain.

(** ** Semantic Notations

    Value notations share [constr] with expression notations, so the
    spellings the two would otherwise share ([ℕ], [zero], [succ], [⊤], [⋆],
    [⊥], [Π] and the closure's [λ]) carry a superscript [ᵈ].  Notations specific to values
    ([↦], [↯], [𝕌@n], [⇑], [⇓], [⇑!], [#ᵈ n]) follow the paper. *)
Module Domain_Notations.
  Export Syntax_Notations.

  (** Declared first so that level 1 is left associative, as for [M[σ]] in
      [Syntax_Notations]. *)
  Notation "ρ '↯'" := (drop_env ρ) (at level 1, left associativity) : mctt_scope.
  Notation "'𝕌' @ n" := (d_univ n) (at level 1, n at level 0, format "'𝕌' @ n") : mctt_scope.
  Notation "'#ᵈ' n" := (d_var n) (at level 1, n at level 0, format "'#ᵈ' n") : mctt_scope.
  Notation "'ℕᵈ'" := d_nat : mctt_scope.
  Notation "'zeroᵈ'" := d_zero : mctt_scope.
  Notation "'succᵈ' m" := (d_succ m) (at level 2, m at level 1) : mctt_scope.
  Notation "'⊤ᵈ'" := d_True : mctt_scope.
  Notation "'⋆ᵈ'" := d_true : mctt_scope.
  Notation "'⊥ᵈ'" := d_False : mctt_scope.
  Notation "'λᵈ' ρ M" := (d_fn ρ M) (at level 2, ρ at level 1, M at level 9) : mctt_scope.
  Notation "'Πᵈ' a ρ B" := (d_pi a ρ B) (at level 2, a at level 1, ρ at level 0, B at level 9) : mctt_scope.
  Notation "'⇑' a m" := (d_neut a m) (at level 2, a at level 1, m at level 1) : mctt_scope.
  Notation "'⇓' a m" := (d_dom a m) (at level 2, a at level 1, m at level 1) : mctt_scope.
  Notation "'⇑!' a n" := (d_neut a (d_var n)) (at level 2, a at level 1, n at level 0) : mctt_scope.
  Notation "m '$ᵈ' n" := (d_app m n) (at level 10, left associativity, format "m  $ᵈ  n") : mctt_scope.
  Notation "'recᵈ' m 'under' ρ 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec ρ P mz MS m) (at level 0, m at level 60, ρ at level 60, P at level 60, mz at level 60, MS at level 60) : mctt_scope.
  Notation "'efqᵈ' m 'under' ρ 'return' P" := (d_exfalso ρ P m) (at level 2, m at level 60, ρ at level 60, P at level 60) : mctt_scope.

  Notation "ρ ↦ m" := (extend_env ρ m) (at level 20, left associativity) : mctt_scope.
End Domain_Notations.

Import Domain_Notations.

(** The two projections of an extended environment. *)
Proposition drop_env_extend_env_cancel : forall ρ a,
    (ρ ↦ a)↯ = ρ.
Proof. reflexivity. Qed.

Proposition extend_env_zero_cancel : forall ρ a,
    env_var (ρ ↦ a) 0 = a.
Proof. reflexivity. Qed.

Proposition extend_env_succ : forall ρ a x,
    env_var (ρ ↦ a) (S x) = env_var ρ x.
Proof. reflexivity. Qed.

Proposition env_var_drop : forall ρ x, env_var ρ↯ x = env_var ρ (S x).
Proof. reflexivity. Qed.

(** ** Pointwise Equality

    Two environments are equal when they agree at every index.  Evaluating a
    substitution determines its result only up to this equality, since a list
    can end in any number of [zeroᵈ]s.  Evaluation does not respect it, because
    [λᵈ ρ M] carries its environment; values from pointwise-equal environments
    are related by the PER model instead. *)
Definition env_eq : relation env := fun ρ ρ' => forall x, env_var ρ x = env_var ρ' x.

#[export]
Instance env_eq_Equivalence : Equivalence env_eq.
Proof. split; [ intros ? ? | intros ? ? ? ? | intros ? ? ? ? ? ? ]; congruence. Qed.

#[export]
Instance extend_env_Proper : Proper (env_eq ==> eq ==> env_eq) extend_env.
Proof. intros ρ ρ' Hρ d d' <- [| n]; [ reflexivity | apply Hρ ]. Qed.

#[export]
Instance drop_env_Proper : Proper (env_eq ==> env_eq) drop_env.
Proof. intros ρ ρ' Hρ n. rewrite !env_var_drop; apply Hρ. Qed.

Import Wk_Notations.

(** ** Weakening an Environment

    A weakening renames variables, so [(⟪φ⟫ ρ) x] is [ρ (φ x)].  The list
    [⟪φ⟫ ρ] has one entry for each [x] with [φ x] among the variables of [ρ].
    For weakenings built from [↑] and [wk_q], which are strictly increasing,
    those [x] form an initial segment.  Hence [⟪φ⟫ ρ] is [ρ ∘ φ] at every
    index, and as lists [⟪↑⟫ ρ] is [ρ↯] and [⟪wk_id⟫ ρ] is [ρ]. *)

Fixpoint wk_count (φ : wk) (n m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => wk_count φ n m' + (if φ m' <? n then 1 else 0)
  end.

(** How many variables [φ] keeps among [n]. *)
Definition wk_len (φ : wk) (n : nat) : nat := wk_count φ n n.

Definition eval_wk (φ : wk) (ρ : env) : env :=
  List.map (fun x => env_var ρ (φ x)) (List.seq 0 (wk_len φ (List.length ρ))).

Notation "'⟪' φ '⟫' ρ" := (eval_wk φ ρ) (at level 2, φ constr at level 60, ρ at level 0) : mctt_scope.

(** A weakening that preserves the order of variables.  [WkMono] is a class so
    that lemmas needing it obtain it by instance resolution. *)
Definition wk_mono (φ : wk) : Prop := forall x y, x < y -> φ x < φ y.

Class WkMono (φ : wk) : Prop := wk_mono_of : wk_mono φ.

Lemma wk_mono_id : wk_mono wk_id.
Proof.
  intros x y; cbn; lia.
Qed.

Lemma wk_mono_shift : wk_mono ↑.
Proof.
  intros x y; cbn; lia.
Qed.

Lemma wk_mono_q : forall φ, wk_mono φ -> wk_mono (wk_q φ).
Proof.
  intros φ H [| x] [| y] ?; cbn; try lia; specialize (H x y); lia.
Qed.

Lemma wk_mono_compose : forall φ ψ, wk_mono φ -> wk_mono ψ -> wk_mono (φ ⊙ ψ).
Proof.
  intros * Hφ Hψ x y ?; cbn; apply Hψ, Hφ; assumption.
Qed.

Lemma wk_mono_ge : forall φ, wk_mono φ -> forall x, x <= φ x.
Proof.
  intros φ H; induction x; [ lia |].
  specialize (H x (S x) ltac:(lia)); lia.
Qed.

Lemma nat_eq_of_lt_iff : forall a b, (forall x, x < a <-> x < b) -> a = b.
Proof.
  intros a b H; destruct (Nat.lt_trichotomy a b) as [Hlt | [? | Hgt]]; [ | assumption |].
  - specialize (H a); lia.
  - specialize (H b); lia.
Qed.

Lemma wk_count_le : forall φ n m m', m <= m' -> wk_count φ n m <= wk_count φ n m'.
Proof.
  intros * H; induction H; [ lia |]; cbn [wk_count]; lia.
Qed.

(** The variables kept form an initial segment: those below the first variable
    that [φ] sends past [n]. *)
Lemma wk_count_spec : forall φ n m, wk_mono φ ->
    forall x, x < wk_count φ n m <-> x < m /\ φ x < n.
Proof.
  intros φ n m Hφ; induction m as [| m IH]; intros x; cbn [wk_count]; [ lia |].
  destruct (Nat.ltb_spec (φ m) n) as [Hm | Hm].
  - (* every variable below [m] is kept too, so [m] of them are *)
    assert (Hc : wk_count φ n m = m).
    { apply nat_eq_of_lt_iff; intros y; rewrite IH; split; [ intros [? ?]; assumption |].
      intros Hy; split; [ assumption |]. specialize (Hφ y m Hy); lia. }
    rewrite Hc; split; [ intros Hx; split; [ lia |] | lia ].
    destruct (Nat.eq_dec x m) as [-> | ?]; [ assumption |].
    specialize (Hφ x m ltac:(lia)); lia.
  - rewrite Nat.add_0_r, IH; split; intros [? ?]; split; try lia.
    destruct (Nat.eq_dec x m) as [-> | ?]; lia.
Qed.

Lemma wk_len_spec : forall φ n, wk_mono φ -> forall x, x < wk_len φ n <-> φ x < n.
Proof.
  intros; unfold wk_len; rewrite wk_count_spec by assumption.
  split; [ intros [? ?]; assumption | intros Hx; split; [| assumption ] ].
  pose proof (wk_mono_ge φ ltac:(assumption) x); lia.
Qed.



Lemma eval_wk_length : forall φ ρ, List.length (⟪φ⟫ ρ) = wk_len φ (List.length ρ).
Proof.
  intros; unfold eval_wk; rewrite List.length_map, List.length_seq; reflexivity.
Qed.

Lemma eval_wk_var : forall φ ρ x, x < wk_len φ (List.length ρ) -> env_var (⟪φ⟫ ρ) x = env_var ρ (φ x).
Proof.
  intros * Hx; unfold eval_wk; rewrite !env_var_nth.
  rewrite (List.nth_indep _ _ ((fun y => env_var ρ (φ y)) 0))
    by (rewrite List.length_map, List.length_seq; assumption).
  rewrite (List.map_nth (fun y => env_var ρ (φ y)) (List.seq 0 _) 0 x).
  rewrite List.seq_nth, env_var_nth by assumption; reflexivity.
Qed.

Lemma env_var_ge : forall ρ x, List.length ρ <= x -> env_var ρ x = d_zero.
Proof.
  intros; rewrite env_var_nth; apply List.nth_overflow; assumption.
Qed.

(** [⟪φ⟫ ρ] is [ρ ∘ φ] at every index, including past the end of the list. *)
Lemma eval_wk_eq : forall φ ρ, wk_mono φ -> forall x, env_var (⟪φ⟫ ρ) x = env_var ρ (φ x).
Proof.
  intros * Hφ x; destruct (Nat.lt_ge_cases x (wk_len φ (List.length ρ))) as [Hx | Hx].
  - apply eval_wk_var; assumption.
  - rewrite !env_var_ge; [ reflexivity | | rewrite eval_wk_length; assumption ].
    destruct (Nat.lt_ge_cases (φ x) (List.length ρ)) as [Hy | Hy]; [| assumption ].
    exfalso; apply (proj2 (wk_len_spec _ _ Hφ x)) in Hy; lia.
Qed.

(** Two environments of the same length that agree below it are equal. *)
Lemma env_ext : forall ρ ρ', List.length ρ = List.length ρ' ->
    (forall x, x < List.length ρ -> env_var ρ x = env_var ρ' x) -> ρ = ρ'.
Proof.
  intros * Hl H; apply (List.nth_ext _ _ d_zero d_zero); [ assumption |].
  intros; rewrite <- !env_var_nth; auto.
Qed.

Lemma eval_wk_id : forall ρ, ⟪wk_id⟫ ρ = ρ.
Proof.
  intros; assert (Hl : wk_len wk_id (List.length ρ) = List.length ρ)
    by (apply nat_eq_of_lt_iff; intros; rewrite wk_len_spec by apply wk_mono_id; reflexivity).
  apply env_ext; rewrite eval_wk_length, Hl; [ reflexivity |].
  intros x Hx; apply eval_wk_var; rewrite Hl; assumption.
Qed.

Lemma eval_wk_shift : forall ρ, ⟪↑⟫ ρ = ρ↯.
Proof.
  intros; assert (Hl : wk_len ↑ (List.length ρ) = List.length ρ↯).
  { apply nat_eq_of_lt_iff; intros; rewrite wk_len_spec by apply wk_mono_shift.
    destruct ρ; cbn; lia. }
  apply env_ext; rewrite eval_wk_length, Hl; [ reflexivity |].
  intros x Hx; rewrite eval_wk_var by (rewrite Hl; assumption).
  cbn [wk_shift]; rewrite <- env_var_drop; reflexivity.
Qed.

Lemma eval_wk_q_zero : forall φ ρ, env_var (⟪wk_q φ⟫ ρ) 0 = env_var ρ 0.
Proof.
  intros φ [| d ρ]; [ reflexivity |].
  rewrite eval_wk_var; [ reflexivity |].
  unfold wk_len; cbn [List.length].
  pose proof (wk_count_le (wk_q φ) (S (List.length ρ)) 1 (S (List.length ρ)) ltac:(lia)); cbn in *; lia.
Qed.

Lemma eval_wk_q_tail : forall φ ρ `{Hφ : WkMono φ}, (⟪wk_q φ⟫ ρ)↯ = ⟪φ⟫ (ρ↯).
Proof.
  intros φ ρ Hφ.
  assert (Hq : wk_mono (wk_q φ)) by (apply wk_mono_q, Hφ).
  (* [wk_q φ] keeps [0] and then what [φ] keeps of the tail *)
  assert (Hl : forall x, x < wk_len (wk_q φ) (List.length ρ) - 1 <-> φ x < List.length ρ - 1).
  { intros x; split; intros Hx.
    - assert (S x < wk_len (wk_q φ) (List.length ρ)) as H' by lia.
      apply (wk_len_spec _ _ Hq) in H'; cbn in H'; lia.
    - assert (wk_q φ (S x) < List.length ρ) as H' by (cbn; lia).
      apply (wk_len_spec _ _ Hq) in H'; lia. }
  apply env_ext.
  - rewrite eval_wk_length; cbn [drop_env]; rewrite List.length_tl, eval_wk_length.
    apply nat_eq_of_lt_iff; intros x; rewrite (wk_len_spec _ _ Hφ), List.length_tl; apply Hl.
  - intros x Hx.
    cbn [drop_env] in Hx; rewrite List.length_tl, eval_wk_length in Hx.
    rewrite env_var_drop, !eval_wk_var; cbn [wk_q].
    + rewrite <- env_var_drop; reflexivity.
    + rewrite (wk_len_spec _ _ Hφ); cbn [drop_env]; rewrite List.length_tl; apply Hl; assumption.
    + lia.
Qed.

Lemma eval_wk_compose : forall φ ψ ρ `{Hφ : WkMono φ} `{Hψ : WkMono ψ}, ⟪φ ⊙ ψ⟫ ρ = ⟪φ⟫ (⟪ψ⟫ ρ).
Proof.
  intros φ ψ ρ Hφ Hψ.
  assert (Hc : wk_mono (φ ⊙ ψ)) by (apply wk_mono_compose; assumption).
  assert (Hl : wk_len (φ ⊙ ψ) (List.length ρ) = wk_len φ (wk_len ψ (List.length ρ))).
  { apply nat_eq_of_lt_iff; intros x.
    rewrite (wk_len_spec _ _ Hc), (wk_len_spec _ _ Hφ), (wk_len_spec _ _ Hψ); reflexivity. }
  apply env_ext; rewrite !eval_wk_length; [ assumption |].
  intros x Hx.
  rewrite eval_wk_var by assumption.
  rewrite eval_wk_var by (rewrite eval_wk_length, <- Hl; assumption).
  rewrite eval_wk_var; [ reflexivity |].
  rewrite Hl in Hx; apply (wk_len_spec _ _ Hφ) in Hx; assumption.
Qed.

#[export] Instance WkMono_id : WkMono wk_id := wk_mono_id.
#[export] Instance WkMono_shift : WkMono ↑ := wk_mono_shift.
#[export] Instance WkMono_q φ `{WkMono φ} : WkMono (wk_q φ) := wk_mono_q φ wk_mono_of.
#[export] Instance WkMono_compose φ ψ `{WkMono φ} `{WkMono ψ} : WkMono (φ ⊙ ψ) :=
  wk_mono_compose φ ψ (@wk_mono_of φ _) (@wk_mono_of ψ _).

#[export] Hint Extern 1 (WkMono _) => typeclasses eauto : mctt core.

(** [eval_wk_eq], with monotonicity found by instance resolution. *)
Lemma eval_wk_app : forall φ `{Hφ : WkMono φ} ρ x, env_var (⟪φ⟫ ρ) x = env_var ρ (φ x).
Proof. intros φ Hφ ρ x; exact (eval_wk_eq φ ρ Hφ x). Qed.
