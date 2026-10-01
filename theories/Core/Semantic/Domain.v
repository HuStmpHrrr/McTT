From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String Morphisms Relation_Definitions RelationClasses.

From Mctt.Core.Syntactic Require Export Syntax.

(** * The Semantic Domain

    An environment is the list of the values of the λ-variables in scope,
    indexed by de Bruijn index; for [Θ ⍮ Ξ ⍮ Γ] those are [Γ].  The global
    context is not part of it: it does not change during NbE, so evaluation
    takes it as a separate argument.

    Where evaluation is in the global context is a *module environment*
    [menv]: the frames in scope, innermost first.  A closed frame
    [me_frame a args κ] is a module (at the address [a], a path into the global
    context whose members are its module chain) applied to the values [args]
    of its parameters, innermost parameter first; [me_base j] is the open frames
    of the stack from [j] outward, whose parameters are neutrals ([d_param]).
    Module parameters are not variables of the environment: they are read off
    the module environment, which every closure captures.  A global needing
    the parameters of a closed frame is the value [d_gfn κ a c args ip]: the
    frame at [a], outside of which is [κ], with [c] parameters of which [args]
    are given, and the member chain [ip] still to resolve in it. *)

Inductive domain : Set :=
| d_nat : domain
| d_pi : domain -> menv -> list domain -> exp -> domain
| d_univ : nat -> domain
| d_zero : domain
| d_succ : domain -> domain
| d_fn : menv -> list domain -> exp -> domain
| d_neut : domain -> domain_ne -> domain
| d_gfn : menv -> path -> nat -> list domain -> list string -> domain
with domain_ne : Set :=
(** Notice that the number x here is not a de Bruijn index but an absolute
    representation of names.  That is, this number does not change relative to the
    binding structure it currently exists in.
 *)
| d_var : forall (x : nat), domain_ne
| d_app : domain_ne -> domain_nf -> domain_ne
| d_natrec : menv -> list domain -> typ -> domain -> exp -> domain_ne -> domain_ne
(** An opaque definition or an axiom, named from the top level. *)
| d_glob : path -> domain_ne
(** A parameter of an open module, named from the top level. *)
| d_param : lpath -> domain_ne
with domain_nf : Set :=
| d_dom : domain -> domain -> domain_nf
with menv : Set :=
| me_base : nat -> menv
| me_frame : path -> list domain -> menv -> menv.

Notation env := (list domain).

Derive NoConfusion for Ascii.ascii String.string.
Derive NoConfusion for qual path lpath.
Derive NoConfusion for domain domain_ne domain_nf menv.

(** The value of the variable [#x], [zeroᵈ] past the end: a well-typed term
    only reads the variables its context has, so the default is never seen by
    one.  As a coercion it lets an environment be applied like the function it
    stands for, [ρ x]. *)
Fixpoint env_var (ρ : env) (x : nat) : domain :=
  match x with
  | 0 => List.hd d_zero ρ
  | S x' => env_var (List.tl ρ) x'
  end.
Coercion env_var : list >-> Funclass.

(** By recursion on the index, so that [ρ↯ x] is [ρ (S x)] by conversion. *)
Lemma env_var_nth : forall ρ x, env_var ρ x = List.nth x ρ d_zero.
Proof. intros ρ x; revert ρ; induction x; intros [| d ρ]; cbn; auto; rewrite IHx; destruct x; reflexivity. Qed.

Definition extend_env (ρ : env) (d : domain) : env := d :: ρ.
Arguments extend_env _ _ /.

Definition drop_env (ρ : env) : env := List.tl ρ.
Arguments drop_env _ /.

#[global] Bind Scope mctt_scope with domain.

(** ** Semantic Notations

    Values live in ordinary [constr] alongside the expressions, so the four
    spellings the two sorts would otherwise share — [ℕ], [zero], [succ], [Π]
    and the closure's [λ] — carry a superscript [ᵈ] here.  Everything that is
    specific to values ([↦], [↯], [𝕌@n], [⇑], [⇓], [⇑!], [#ᵈ n]) keeps the
    spelling of the paper. *)
Module Domain_Notations.
  Export Syntax_Notations.

  (** Declared before the value constructors so that level 1 is left
      associative, as [M[σ]] does in [Syntax_Notations]. *)
  Notation "ρ '↯'" := (drop_env ρ) (at level 1, left associativity) : mctt_scope.
  Notation "'𝕌' @ n" := (d_univ n) (at level 1, n at level 0, format "'𝕌' @ n") : mctt_scope.
  Notation "'#ᵈ' n" := (d_var n) (at level 1, n at level 0, format "'#ᵈ' n") : mctt_scope.
  Notation "'ℕᵈ'" := d_nat : mctt_scope.
  Notation "'zeroᵈ'" := d_zero : mctt_scope.
  Notation "'succᵈ' m" := (d_succ m) (at level 2, m at level 1) : mctt_scope.
  Notation "'λᵈ' κ ρ M" := (d_fn κ ρ M) (at level 2, κ at level 1, ρ at level 1, M at level 9) : mctt_scope.
  Notation "'Πᵈ' a κ ρ B" := (d_pi a κ ρ B) (at level 2, a at level 1, κ at level 0, ρ at level 0, B at level 9) : mctt_scope.
  Notation "'⇑' a m" := (d_neut a m) (at level 2, a at level 1, m at level 1) : mctt_scope.
  Notation "'⇓' a m" := (d_dom a m) (at level 2, a at level 1, m at level 1) : mctt_scope.
  Notation "'⇑!' a n" := (d_neut a (d_var n)) (at level 2, a at level 1, n at level 0) : mctt_scope.
  Notation "m '$ᵈ' n" := (d_app m n) (at level 10, left associativity, format "m  $ᵈ  n") : mctt_scope.
  Notation "'recᵈ' m 'under' κ ρ 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec κ ρ P mz MS m) (at level 0, m at level 60, κ at level 0, ρ at level 60, P at level 60, mz at level 60, MS at level 60) : mctt_scope.

  Notation "ρ ↦ m" := (extend_env ρ m) (at level 20, left associativity) : mctt_scope.
End Domain_Notations.

Import Domain_Notations.

(** ** Module Environments

    Frame [n] of a module environment is what [me_drop n] leaves on top: a
    closed frame, or the open stack frame [j + n'] when only [me_base j] is
    left.  So [me_drop] is the semantic counterpart of [↑ₘ n]: arithmetic on
    the frame index, nothing done to any term. *)
Abbreviation me_top := (me_base 0).

Fixpoint me_drop (n : nat) (κ : menv) : menv :=
  match n, κ with
  | 0, _ => κ
  | S n', me_frame _ _ κ' => me_drop n' κ'
  | S n', me_base j => me_base (S n' + j)
  end.

(** The address of the innermost frame. *)
Definition me_addr (κ : menv) : path :=
  match κ with
  | me_base j => p_rel j nil
  | me_frame a _ _ => a
  end.

Lemma me_drop_base : forall n j, me_drop n (me_base j) = me_base (n + j).
Proof. intros [| n] j; reflexivity. Qed.

Lemma me_drop_add : forall n m κ, me_drop n (me_drop m κ) = me_drop (n + m) κ.
Proof.
  intros n m; revert n; induction m as [| m IH]; intros n κ.
  - rewrite Nat.add_0_r; reflexivity.
  - destruct κ as [j | a args κ].
    + change (me_drop (S m) (me_base j)) with (me_base (S m + j)).
      rewrite !me_drop_base; f_equal; lia.
    + rewrite Nat.add_succ_r; cbn [me_drop]; apply IH.
Qed.

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

    Two environments are equal as the functions they stand for: evaluating a
    substitution determines its result only up to this, since a list can end
    in any number of [zeroᵈ]s.  Evaluation does not respect it — [λᵈ ρ M]
    carries its environment — so relating values of pointwise-equal
    environments is the job of the PER model. *)
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

    A weakening renames variables, so evaluating one looks up the renamed
    variable: [(⟪φ⟫ ρ) x] is [ρ (φ x)].  The list stops where the lookups leave
    [ρ]: it has one entry for each [x] with [φ x] among the variables of [ρ].
    For the weakenings built from [↑] and [wk_q] — which are strictly
    increasing — those [x] are an initial segment, so [⟪φ⟫ ρ] is [ρ ∘ φ] at
    every index, and [⟪↑⟫ ρ] is [ρ↯], [⟪wk_id⟫ ρ] is [ρ], as lists. *)

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

(** A weakening that preserves the order of variables.  A class, so that the
    lemmas needing it take it by instance resolution. *)
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

(** The variables kept are an initial segment: those below [φ]'s first
    variable past [n]. *)
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

(** At every index. *)
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

(** [eval_wk_eq] with the order preservation found by instance resolution. *)
Lemma eval_wk_app : forall φ `{Hφ : WkMono φ} ρ x, env_var (⟪φ⟫ ρ) x = env_var ρ (φ x).
Proof. intros φ Hφ ρ x; exact (eval_wk_eq φ ρ Hφ x). Qed.
