From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String Morphisms Relation_Definitions RelationClasses.

From Mctt.Core.Syntactic Require Export Syntax.

(** * The Semantic Domain

    An environment is the list of the values of the variables in scope,
    indexed by de Bruijn index; for [Θ ⍮ Ξ ⍮ Γ] these are the variables of
    [Γ].  A term variable holds a term value and a module slot a module value
    ([dentry]).  The global context does not change during NbE, so it is not
    part of the environment; evaluation takes it as a separate argument.
    Module parameters are λ-variables and so live in the environment.

    Module values are their own sort ([dmod]), closures like [λ]:

    - [dm_global p args]: the global body module at [p], applied to [args],
      outermost first;
    - [dm_local ρ U args]: the unit [U] over the environment [ρ], applied to
      [args];
    - [dm_member m ch]: the submodule at the chain [ch] of a module [m] still
      lacking arguments.

    [d_member m ch] is the term member at the chain [ch] of such a module: the
    semantic [λ] of a member of a module that is not yet applied to all its
    parameters. *)

Inductive domain : Set :=
(** [ℕ] *)
| d_nat : domain
(** [d_pi a ρ B]: a [Π] with domain [a], its codomain [B] a closure in [ρ] *)
| d_pi : domain -> list dentry -> exp -> domain
(** A large universe *)
| d_univ : nat -> domain
(** A small universe *)
| d_suniv : nat -> domain
(** [zero] *)
| d_zero : domain
(** [succ] *)
| d_succ : domain -> domain
(** [⊤] *)
| d_True : domain
(** Its element *)
| d_true : domain
(** [⊥] *)
| d_False : domain
(** [d_fn ρ M]: a function, its body a closure in [ρ] *)
| d_fn : list dentry -> exp -> domain
(** [d_neut a m]: a neutral [m] at the type [a] *)
| d_neut : domain -> domain_ne -> domain
(** A term member of a module still lacking arguments (see above) *)
| d_member : dmod -> list string -> domain
with domain_ne : Set :=
(** [x] is a de Bruijn level, not an index: it names a variable absolutely and
    does not change under binders. *)
| d_var : forall (x : nat), domain_ne
(** A neutral applied to a normal argument *)
| d_app : domain_ne -> domain_nf -> domain_ne
(** The [ℕ]-eliminator on a neutral, with its motive and successor case as
    closures. *)
| d_natrec : list dentry -> typ -> domain -> exp -> domain_ne -> domain_ne
(** The [⊥]-eliminator on a neutral, with its motive as a closure. *)
| d_exfalso : list dentry -> typ -> domain_ne -> domain_ne
(** An opaque definition or an axiom. *)
| d_glob : qname -> domain_ne
with domain_nf : Set :=
(** [d_dom a m]: the value [m] at the type [a], to be read back *)
| d_dom : domain -> domain -> domain_nf
with dmod : Set :=
(** A global module and the arguments it has *)
| dm_global : qname -> list domain -> dmod
(** The closure of a unit and the arguments it has *)
| dm_local : list dentry -> gunit -> list domain -> dmod
(** A submodule of a module still lacking arguments *)
| dm_member : dmod -> list string -> dmod
with dentry : Set :=
(** A term variable's value *)
| de_term : domain -> dentry
(** A module slot's value *)
| de_mod : dmod -> dentry.

Abbreviation env := (list dentry).

Derive NoConfusion for domain domain_ne domain_nf dmod dentry.

(** The entry of the variable [#x], or the term [zeroᵈ] past the end of the
    list.  [env_entry] is [nth], but defined by recursion on the index so that
    [ρ↯ x] is [ρ (S x)] by conversion. *)
Fixpoint env_entry (ρ : env) (x : nat) : dentry :=
  match x with
  | 0 => List.hd (de_term d_zero) ρ
  | S x' => env_entry (List.tl ρ) x'
  end.

(** The value of the variable [#x] as a term, and as a module.  A well-typed
    term only reads variables of its sort in its context, so it never sees
    the defaults, which are the values of the defaults of [sentry_exp] and
    [sentry_modexp].  As a coercion, [env_var] lets an environment be applied
    as a function, [ρ x]. *)
Definition dm_default : dmod := dm_global (q_abs nil nil) nil.

Definition env_var (ρ : env) (x : nat) : domain :=
  match env_entry ρ x with
  | de_term d => d
  | de_mod _ => d_zero
  end.
#[warning="-uniform-inheritance"]
Coercion env_var : list >-> Funclass.

Definition env_mod (ρ : env) (x : nat) : dmod :=
  match env_entry ρ x with
  | de_mod m => m
  | de_term _ => dm_default
  end.

Lemma env_entry_nth : forall ρ x, env_entry ρ x = List.nth x ρ (de_term d_zero).
Proof. intros ρ x; revert ρ; induction x; intros [| d ρ]; cbn; auto; rewrite IHx; destruct x; reflexivity. Qed.

Lemma env_var_nth : forall ρ x, env_var ρ x = match List.nth x ρ (de_term d_zero) with de_term d => d | de_mod _ => d_zero end.
Proof. intros; unfold env_var; rewrite env_entry_nth; reflexivity. Qed.

Definition extend_env (ρ : env) (d : domain) : env := de_term d :: ρ.
Arguments extend_env _ _ /.

Definition extend_env_mod (ρ : env) (m : dmod) : env := de_mod m :: ρ.
Arguments extend_env_mod _ _ /.

(** The environment extended by arguments, outermost first, as a unit's
    parameters are. *)
Definition env_args (ρ : env) (args : list domain) : env :=
  List.fold_left extend_env args ρ.

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
  Notation "'𝕌ˢ' @ n" := (d_suniv n) (at level 1, n at level 0, format "'𝕌ˢ' @ n") : mctt_scope.
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
  Notation "ρ '↦ᵐ' m" := (extend_env_mod ρ m) (at level 20, left associativity) : mctt_scope.
End Domain_Notations.

(** The value of the universe at an index, at either tier. *)
Definition univ_val (u : uidx) : domain :=
  match u with us n => d_suniv n | ul n => d_univ n end.


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

Proposition env_var_cons_succ : forall e ρ x, env_var (e :: ρ) (S x) = env_var ρ x.
Proof. reflexivity. Qed.

Proposition env_entry_cons_succ : forall e ρ x, env_entry (e :: ρ) (S x) = env_entry ρ x.
Proof. reflexivity. Qed.

Proposition env_entry_drop : forall ρ x, env_entry ρ↯ x = env_entry ρ (S x).
Proof. reflexivity. Qed.

Proposition env_mod_drop : forall ρ x, env_mod ρ↯ x = env_mod ρ (S x).
Proof. reflexivity. Qed.

Proposition extend_env_mod_zero : forall ρ m, env_mod (ρ ↦ᵐ m) 0 = m.
Proof. reflexivity. Qed.

Proposition extend_env_mod_succ : forall ρ m x, env_entry (ρ ↦ᵐ m) (S x) = env_entry ρ x.
Proof. reflexivity. Qed.

(** ** Pointwise Equality

    Two environments are equal when they agree at every index, entry by entry.  Evaluating a
    substitution determines its result only up to this equality, since a list
    can end in any number of [zeroᵈ]s.  Evaluation does not respect it, because
    [λᵈ ρ M] carries its environment; values from pointwise-equal environments
    are related by the PER model instead. *)
Definition env_eq : relation env := fun ρ ρ' => forall x, env_entry ρ x = env_entry ρ' x.

Lemma env_eq_var : forall ρ ρ', env_eq ρ ρ' -> forall x, env_var ρ x = env_var ρ' x.
Proof. intros * H x; unfold env_var; rewrite H; reflexivity. Qed.

Lemma env_eq_mod : forall ρ ρ', env_eq ρ ρ' -> forall x, env_mod ρ x = env_mod ρ' x.
Proof. intros * H x; unfold env_mod; rewrite H; reflexivity. Qed.

#[export]
Instance env_eq_Equivalence : Equivalence env_eq.
Proof. split; [ intros ? ? | intros ? ? ? ? | intros ? ? ? ? ? ? ]; congruence. Qed.

#[export]
Instance extend_env_Proper : Proper (env_eq ==> eq ==> env_eq) extend_env.
Proof. intros ρ ρ' Hρ d d' <- [| n]; [ reflexivity | apply Hρ ]. Qed.

#[export]
Instance extend_env_mod_Proper : Proper (env_eq ==> eq ==> env_eq) extend_env_mod.
Proof. intros ρ ρ' Hρ d d' <- [| n]; [ reflexivity | apply Hρ ]. Qed.

#[export]
Instance drop_env_Proper : Proper (env_eq ==> env_eq) drop_env.
Proof. intros ρ ρ' Hρ n. rewrite !env_entry_drop; apply Hρ. Qed.

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
  List.map (fun x => env_entry ρ (φ x)) (List.seq 0 (wk_len φ (List.length ρ))).

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

Lemma eval_wk_var : forall φ ρ x, x < wk_len φ (List.length ρ) -> env_entry (⟪φ⟫ ρ) x = env_entry ρ (φ x).
Proof.
  intros * Hx; unfold eval_wk; rewrite !env_entry_nth.
  rewrite (List.nth_indep _ _ ((fun y => env_entry ρ (φ y)) 0))
    by (rewrite List.length_map, List.length_seq; assumption).
  rewrite (List.map_nth (fun y => env_entry ρ (φ y)) (List.seq 0 _) 0 x).
  rewrite List.seq_nth, env_entry_nth by assumption; reflexivity.
Qed.

Lemma env_entry_ge : forall ρ x, List.length ρ <= x -> env_entry ρ x = de_term d_zero.
Proof.
  intros; rewrite env_entry_nth; apply List.nth_overflow; assumption.
Qed.

Lemma env_var_ge : forall ρ x, List.length ρ <= x -> env_var ρ x = d_zero.
Proof.
  intros; unfold env_var; rewrite env_entry_ge; [ reflexivity | assumption ].
Qed.

(** [⟪φ⟫ ρ] is [ρ ∘ φ] at every index, including past the end of the list. *)
Lemma eval_wk_entry : forall φ ρ, wk_mono φ -> forall x, env_entry (⟪φ⟫ ρ) x = env_entry ρ (φ x).
Proof.
  intros * Hφ x; destruct (Nat.lt_ge_cases x (wk_len φ (List.length ρ))) as [Hx | Hx].
  - apply eval_wk_var; assumption.
  - rewrite !env_entry_ge; [ reflexivity | | rewrite eval_wk_length; assumption ].
    destruct (Nat.lt_ge_cases (φ x) (List.length ρ)) as [Hy | Hy]; [| assumption ].
    exfalso; apply (proj2 (wk_len_spec _ _ Hφ x)) in Hy; lia.
Qed.

Lemma eval_wk_eq : forall φ ρ, wk_mono φ -> forall x, env_var (⟪φ⟫ ρ) x = env_var ρ (φ x).
Proof. intros * Hφ x; unfold env_var; rewrite eval_wk_entry by assumption; reflexivity. Qed.

Lemma eval_wk_mod : forall φ ρ, wk_mono φ -> forall x, env_mod (⟪φ⟫ ρ) x = env_mod ρ (φ x).
Proof. intros * Hφ x; unfold env_mod; rewrite eval_wk_entry by assumption; reflexivity. Qed.

(** Two environments of the same length that agree below it are equal. *)
Lemma env_ext : forall ρ ρ', List.length ρ = List.length ρ' ->
    (forall x, x < List.length ρ -> env_entry ρ x = env_entry ρ' x) -> ρ = ρ'.
Proof.
  intros * Hl H; apply (List.nth_ext _ _ (de_term d_zero) (de_term d_zero)); [ assumption |].
  intros; rewrite <- !env_entry_nth; auto.
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
  cbn [wk_shift]; rewrite <- env_entry_drop; reflexivity.
Qed.

Lemma eval_wk_q_zero_entry : forall φ ρ, env_entry (⟪wk_q φ⟫ ρ) 0 = env_entry ρ 0.
Proof.
  intros φ [| d ρ]; [ reflexivity |].
  rewrite eval_wk_var; [ reflexivity |].
  unfold wk_len; cbn [List.length].
  pose proof (wk_count_le (wk_q φ) (S (List.length ρ)) 1 (S (List.length ρ)) ltac:(lia)); cbn in *; lia.
Qed.

Lemma eval_wk_q_zero : forall φ ρ, env_var (⟪wk_q φ⟫ ρ) 0 = env_var ρ 0.
Proof. intros; unfold env_var; rewrite eval_wk_q_zero_entry; reflexivity. Qed.

Lemma eval_wk_q_zero_mod : forall φ ρ, env_mod (⟪wk_q φ⟫ ρ) 0 = env_mod ρ 0.
Proof. intros; unfold env_mod; rewrite eval_wk_q_zero_entry; reflexivity. Qed.

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
    rewrite env_entry_drop, !eval_wk_var; cbn [wk_q].
    + rewrite <- env_entry_drop; reflexivity.
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

Lemma eval_wk_app_entry : forall φ `{Hφ : WkMono φ} ρ x, env_entry (⟪φ⟫ ρ) x = env_entry ρ (φ x).
Proof. intros φ Hφ ρ x; exact (eval_wk_entry φ ρ Hφ x). Qed.

Lemma eval_wk_app_mod : forall φ `{Hφ : WkMono φ} ρ x, env_mod (⟪φ⟫ ρ) x = env_mod ρ (φ x).
Proof. intros φ Hφ ρ x; exact (eval_wk_mod φ ρ Hφ x). Qed.
