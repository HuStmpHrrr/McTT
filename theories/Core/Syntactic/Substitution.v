(** * The Algebra of Weakenings and Substitutions

    Weakenings and substitutions are meta-level operations on [exp] (see
    [Core.Syntactic.Syntax]), so the laws that a calculus of explicit
    substitutions postulates as definitional equalities are, here, theorems.
    This file proves them.

    Two conventions are worth repeating.

    - Composition is *diagrammatic*: [σ ⨟ τ] applies [σ] first and then [τ].
    - Weakenings and substitutions are functions, so a law the paper states as
      an equality of substitutions is here an equality of the pointwise
      relation [sb_eq] (respectively [wk_eq]) rather than a Leibniz equality.
      This keeps the development free of functional extensionality.  The
      congruence lemmas [exp_wk_wk_eq] and [exp_sub_sb_eq], together with the
      [Proper] instances registered below, let ordinary [rewrite] cross the
      boundary between the two.

    Most laws come in two forms: a general one taking the relevant pointwise
    equation as a hypothesis (suffix [_ext]), and the specialisation that
    matches the paper.  The general form is what makes the inductions go
    through, because it is what survives passing under a binder; the
    specialisation is what the rest of the development uses.  In particular it
    is what lets us dispense with an induction over the number of enclosing
    binders. *)

From Stdlib Require Import Lia Morphisms Relation_Definitions RelationClasses Setoid.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Wk_Notations.

(** ** Computing with the Operations

    Every one of these is definitional.  They exist so that the index-level
    behaviour of the operations can be reached by rewriting instead of by
    [simpl], which would also unfold [sb_q] and make goals unreadable.
    Together they form a complete rewriting system for expressions of the form
    [σ x], so [reduce_index] below fully normalises any pointwise goal. *)

Create Rewrite HintDb sb_index.
Create Rewrite HintDb sb.

Section computation.
  Variable (σ τ : sub) (φ ψ : wk) (M : exp) (x : nat).

  Fact wk_id_var : wk_id x = x.                                    Proof. reflexivity. Qed.
  Fact wk_shift_var : wk_shift x = S x.                            Proof. reflexivity. Qed.
  Fact wk_q_zero : wk_q φ 0 = 0.                                   Proof. reflexivity. Qed.
  Fact wk_q_succ : wk_q φ (S x) = S (φ x).                         Proof. reflexivity. Qed.
  Fact wk_compose_var : (φ ⊙ ψ) x = ψ (φ x).                       Proof. reflexivity. Qed.
  Fact wk_shiftn_var : forall n, wk_shiftn n x = x + n.            Proof. reflexivity. Qed.

  Fact sb_id_var : {{{ Id }}} x = {{{ #x }}}.                      Proof. reflexivity. Qed.
  Fact sb_shift_var : {{{ Wk }}} x = {{{ #(S x) }}}.               Proof. reflexivity. Qed.
  Fact sb_extend_zero : {{{ σ ,, M }}} 0 = M.                      Proof. reflexivity. Qed.
  Fact sb_extend_succ : {{{ σ ,, M }}} (S x) = σ x.                Proof. reflexivity. Qed.
  Fact sb_wk_var : sb_wk σ φ x = {{{ ^(σ x)⟨φ⟩ }}}.                Proof. reflexivity. Qed.
  Fact sb_of_wk_var : {{{ ^(ι φ) }}} x = {{{ #(φ x) }}}.           Proof. reflexivity. Qed.
  Fact sb_compose_var : {{{ σ ⨟ τ }}} x = {{{ ^(σ x)[τ] }}}.       Proof. reflexivity. Qed.
  Fact sb_q_zero : {{{ q σ }}} 0 = {{{ #0 }}}.                     Proof. reflexivity. Qed.
  Fact sb_q_succ : {{{ q σ }}} (S x) = {{{ ^(σ x)⟨wk_shift⟩ }}}.   Proof. reflexivity. Qed.

  Fact exp_wk_var : {{{ #x⟨φ⟩ }}} = {{{ #(φ x) }}}.                Proof. reflexivity. Qed.
  Fact exp_sub_var : {{{ #x[σ] }}} = σ x.                          Proof. reflexivity. Qed.
End computation.

#[export]
Hint Rewrite -> wk_id_var wk_shift_var wk_q_zero wk_q_succ
                wk_compose_var wk_shiftn_var
                sb_id_var sb_shift_var sb_extend_zero sb_extend_succ
                sb_wk_var sb_of_wk_var sb_compose_var
                sb_q_zero sb_q_succ
                exp_wk_var exp_sub_var : sb_index.

Ltac reduce_index := autorewrite with sb_index in *.

(** The heads an operation passes through without meeting a binder.  [Π], [λ],
    application and the eliminator are deliberately absent: pushing an operation
    through those introduces a [q], which is not a simplification.  These are
    stated outside the section above only to fix the argument order. *)

Fact exp_wk_typ : forall φ i, {{{ Type@i⟨φ⟩ }}} = {{{ Type@i }}}.       Proof. reflexivity. Qed.
Fact exp_wk_nat : forall φ, {{{ ℕ⟨φ⟩ }}} = {{{ ℕ }}}.                   Proof. reflexivity. Qed.
Fact exp_wk_zero : forall φ, {{{ zero⟨φ⟩ }}} = {{{ zero }}}.            Proof. reflexivity. Qed.
Fact exp_wk_succ : forall φ M, {{{ (succ M)⟨φ⟩ }}} = {{{ succ M⟨φ⟩ }}}. Proof. reflexivity. Qed.
Fact exp_sub_typ : forall σ i, {{{ Type@i[σ] }}} = {{{ Type@i }}}.      Proof. reflexivity. Qed.
Fact exp_sub_nat : forall σ, {{{ ℕ[σ] }}} = {{{ ℕ }}}.                  Proof. reflexivity. Qed.
Fact exp_sub_zero : forall σ, {{{ zero[σ] }}} = {{{ zero }}}.           Proof. reflexivity. Qed.
Fact exp_sub_succ : forall σ M, {{{ (succ M)[σ] }}} = {{{ succ M[σ] }}}. Proof. reflexivity. Qed.

(** The heads that do meet a binder.  Kept out of the databases above: pushing
    an operation inside a [Π] or a [λ] replaces it by a [q], which none of the
    laws below can then cancel against an extension.  They are here so that a
    transported [Π]-type can be *recognised* as one by [rewrite]. *)

Fact exp_wk_pi : forall φ A B, {{{ (Π A B)⟨φ⟩ }}} = {{{ Π A⟨φ⟩ B⟨wk_q φ⟩ }}}.
Proof. reflexivity. Qed.

Fact exp_wk_fn : forall φ A M, {{{ (λ A M)⟨φ⟩ }}} = {{{ λ A⟨φ⟩ M⟨wk_q φ⟩ }}}.
Proof. reflexivity. Qed.

Fact exp_wk_app : forall φ M N, {{{ (M N)⟨φ⟩ }}} = {{{ M⟨φ⟩ N⟨φ⟩ }}}.
Proof. reflexivity. Qed.

Fact exp_sub_pi : forall σ A B, {{{ (Π A B)[σ] }}} = {{{ Π A[σ] B[q σ] }}}.
Proof. reflexivity. Qed.

Fact exp_sub_fn : forall σ A M, {{{ (λ A M)[σ] }}} = {{{ λ A[σ] M[q σ] }}}.
Proof. reflexivity. Qed.

Fact exp_sub_app : forall σ M N, {{{ (M N)[σ] }}} = {{{ M[σ] N[σ] }}}.
Proof. reflexivity. Qed.

(** *** Two Shared Tactics

    Almost every proof below is one of two shapes, so they are worth naming
    once instead of being spelled out each time.

    [pointwise] opens a goal about weakenings or substitutions at index [0] and
    at index [S _] and normalises both; [pointwise_solve] additionally closes
    the resulting arithmetic.  [exp_ind_ext] runs the induction on expressions
    used by every law in [_ext] form. *)

(** Every operation but [sb_q] is a one-line definition, so [cbv delta] puts a
    pointwise statement into a normal form in which the only remaining opaque
    applications are of [exp_wk], [exp_sub] and [sb_q].  Unlike rewriting, this
    reaches *under* the [forall] of a pointwise hypothesis, which is why
    [reduce_index] alone is not enough. *)
Ltac unfold_ops :=
  cbv beta delta [ wk_eq sb_eq pointwise_relation
                   wk_id wk_shift wk_compose wk_shiftn
                   sb_id sb_shift sb_of_wk sb_wk sb_extend sb_compose ] in *.

Ltac pointwise :=
  let x := fresh "x" in
  intro x; destruct x; reduce_index.

(** [pointwise_solve] closes a pointwise goal outright, so it can afford to
    normalise the hypotheses with [unfold_ops] first; [pointwise] leaves the
    operations folded, which is what the proofs that go on to rewrite with the
    laws below need. *)
Ltac pointwise_solve :=
  unfold_ops; pointwise; solve [ reflexivity | lia | f_equal; auto | auto ].

(** One case of an induction over [exp] for a law in [_ext] form.  The variable
    case is precisely the hypothesis [Heq]; every other case is a congruence
    whose subgoals follow from the induction hypotheses once [Heq] has been
    lifted under the binders by [lift].  The [a_natrec] successor branch binds
    two variables, so [lift] may have to be applied twice — [auto] takes care
    of that. *)
Ltac exp_ind_ext H lift :=
  simpl;
  try apply H; try (symmetry; apply H);
  f_equal;
  solve [ apply H | symmetry; apply H | auto using lift ].

(** ** Weakenings *)

Lemma wk_q_cong : forall φ ψ, wk_eq φ ψ -> wk_eq (wk_q φ) (wk_q ψ).
Proof. intros * Heq; pointwise_solve. Qed.

Lemma wk_compose_cong : forall φ φ' ψ ψ',
    wk_eq φ φ' -> wk_eq ψ ψ' -> wk_eq (φ ⊙ ψ) (φ' ⊙ ψ').
Proof. intros * Heq Heq'; pointwise; rewrite Heq; apply Heq'. Qed.

#[export]
Instance wk_q_Proper : Proper (wk_eq ==> wk_eq) wk_q.
Proof. intros ? ? ?; now apply wk_q_cong. Qed.

#[export]
Instance wk_compose_Proper : Proper (wk_eq ==> wk_eq ==> wk_eq) wk_compose.
Proof. intros ? ? ? ? ? ?; now apply wk_compose_cong. Qed.

Lemma exp_wk_wk_eq : forall M φ ψ,
    wk_eq φ ψ ->
    {{{ M⟨φ⟩ }}} = {{{ M⟨ψ⟩ }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq wk_q_cong. Qed.

#[export]
Instance exp_wk_Proper : Proper (eq ==> wk_eq ==> eq) exp_wk.
Proof. intros M M' <- ? ? ?; now apply exp_wk_wk_eq. Qed.

#[export]
Instance wk_qn_Proper n : Proper (wk_eq ==> wk_eq) (wk_qn n).
Proof.
  induction n; intros φ ψ Heq; simpl; auto.
  now apply wk_q_cong, IHn.
Qed.

(** Weakenings form a category. *)

Lemma wk_compose_id_left : forall φ, wk_eq (wk_id ⊙ φ) φ.
Proof. intros ?; pointwise_solve. Qed.

Lemma wk_compose_id_right : forall φ, wk_eq (φ ⊙ wk_id) φ.
Proof. intros ?; pointwise_solve. Qed.

Lemma wk_compose_assoc : forall φ ψ χ, wk_eq ((φ ⊙ ψ) ⊙ χ) (φ ⊙ (ψ ⊙ χ)).
Proof. intros *; pointwise_solve. Qed.

(** The identity weakening. *)

Lemma wk_q_id_ext : forall φ, wk_eq φ wk_id -> wk_eq (wk_q φ) wk_id.
Proof. intros * Heq; pointwise_solve. Qed.

Lemma exp_wk_id_ext : forall M φ,
    wk_eq φ wk_id ->
    {{{ M⟨φ⟩ }}} = M.
Proof. induction M; intros * Heq; exp_ind_ext Heq wk_q_id_ext. Qed.

Corollary wk_q_id : wk_eq (wk_q wk_id) wk_id.
Proof. now apply wk_q_id_ext. Qed.

Corollary exp_wk_id : forall M, {{{ M⟨wk_id⟩ }}} = M.
Proof. intros; now apply exp_wk_id_ext. Qed.

(** Weakening application respects composition. *)

Lemma wk_q_compose_ext : forall φ ψ χ,
    wk_eq (φ ⊙ ψ) χ ->
    wk_eq (wk_q φ ⊙ wk_q ψ) (wk_q χ).
Proof. intros * Heq; pointwise_solve. Qed.

Lemma exp_wk_wk_ext : forall M φ ψ χ,
    wk_eq (φ ⊙ ψ) χ ->
    {{{ M⟨φ⟩⟨ψ⟩ }}} = {{{ M⟨χ⟩ }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq wk_q_compose_ext. Qed.

Corollary wk_q_compose : forall φ ψ, wk_eq (wk_q φ ⊙ wk_q ψ) (wk_q (φ ⊙ ψ)).
Proof. intros; now apply wk_q_compose_ext. Qed.

Corollary exp_wk_wk : forall M φ ψ, {{{ M⟨φ⟩⟨ψ⟩ }}} = {{{ M⟨φ ⊙ ψ⟩ }}}.
Proof. intros; now apply exp_wk_wk_ext. Qed.

Lemma wk_qn_compose : forall n φ ψ,
    wk_eq (wk_qn n φ ⊙ wk_qn n ψ) (wk_qn n (φ ⊙ ψ)).
Proof.
  induction n; intros; simpl; [ reflexivity | ].
  now apply wk_q_compose_ext, IHn.
Qed.

(** The action of [q^n] on indices. *)

Lemma wk_qn_lt : forall n φ x, x < n -> wk_qn n φ x = x.
Proof.
  induction n; intros * Hlt; [ lia | ].
  destruct x; simpl; auto.
  f_equal; apply IHn; lia.
Qed.

Lemma wk_qn_ge : forall n φ x, n <= x -> wk_qn n φ x = φ (x - n) + n.
Proof.
  induction n; intros * Hle; simpl.
  - replace (x - 0) with x by lia; lia.
  - destruct x; [ lia | ].
    simpl; rewrite IHn by lia; lia.
Qed.

(** The [n]-fold shift, and its interaction with lifting. *)

Lemma wk_shiftn_zero : wk_eq (wk_shiftn 0) wk_id.
Proof. pointwise_solve. Qed.

Lemma wk_shiftn_succ : forall n, wk_eq (wk_shiftn n ⊙ wk_shift) (wk_shiftn (S n)).
Proof. intros ?; pointwise_solve. Qed.

Lemma wk_shiftn_qn_shift : forall n,
    wk_eq (wk_shiftn n ⊙ wk_qn n wk_shift) (wk_shiftn (S n)).
Proof.
  intros n x; simpl.
  rewrite wk_qn_ge by lia.
  replace (x + n - n) with x by lia; simpl; lia.
Qed.

(** ** Substitutions *)

Lemma sb_wk_cong : forall σ τ φ φ',
    sb_eq σ τ -> wk_eq φ φ' -> sb_eq (sb_wk σ φ) (sb_wk τ φ').
Proof.
  intros * Heq Heq' x; simpl.
  rewrite Heq; now apply exp_wk_wk_eq.
Qed.

Lemma sb_q_cong : forall σ τ, sb_eq σ τ -> sb_eq (sb_q σ) (sb_q τ).
Proof. intros * Heq; pointwise; [ reflexivity | now rewrite Heq ]. Qed.

Lemma exp_sub_sb_eq : forall M σ τ,
    sb_eq σ τ ->
    {{{ M[σ] }}} = {{{ M[τ] }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_cong. Qed.

Lemma sb_extend_cong : forall σ τ M,
    sb_eq σ τ -> sb_eq {{{ σ ,, M }}} {{{ τ ,, M }}}.
Proof. intros * Heq; pointwise_solve. Qed.

Lemma sb_of_wk_cong : forall φ ψ, wk_eq φ ψ -> sb_eq {{{ ^(ι φ) }}} {{{ ^(ι ψ) }}}.
Proof. intros * Heq; pointwise_solve. Qed.

#[export]
Instance sb_wk_Proper : Proper (sb_eq ==> wk_eq ==> sb_eq) sb_wk.
Proof. intros ? ? ? ? ? ?; now apply sb_wk_cong. Qed.

#[export]
Instance sb_q_Proper : Proper (sb_eq ==> sb_eq) sb_q.
Proof. intros ? ? ?; now apply sb_q_cong. Qed.

#[export]
Instance sb_of_wk_Proper : Proper (wk_eq ==> sb_eq) sb_of_wk.
Proof. intros ? ? ?; now apply sb_of_wk_cong. Qed.

#[export]
Instance sb_extend_Proper : Proper (sb_eq ==> eq ==> sb_eq) sb_extend.
Proof. intros σ τ Heq M M' <-; now apply sb_extend_cong. Qed.

#[export]
Instance exp_sub_Proper : Proper (eq ==> sb_eq ==> eq) exp_sub.
Proof. intros M M' <- ? ? ?; now apply exp_sub_sb_eq. Qed.

#[export]
Instance sb_qn_Proper n : Proper (sb_eq ==> sb_eq) (sb_qn n).
Proof.
  induction n; intros σ τ Heq; simpl; auto.
  now apply sb_q_cong, IHn.
Qed.

#[export]
Instance sb_compose_Proper : Proper (sb_eq ==> sb_eq ==> sb_eq) sb_compose.
Proof.
  intros σ σ' Heq τ τ' Heq' x; simpl.
  rewrite Heq; now apply exp_sub_sb_eq.
Qed.

(** The embedding [ι] of weakenings into
    substitutions is faithful, and preserves every operation.  From here on the
    development may treat a weakening as a substitution. *)

Lemma sb_q_of_wk_ext : forall φ σ,
    sb_eq {{{ ^(ι φ) }}} σ ->
    sb_eq {{{ ^(ι (wk_q φ)) }}} {{{ q σ }}}.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite <- Heq; reduce_index; reflexivity.
Qed.

Lemma exp_sub_of_wk_ext : forall M φ σ,
    sb_eq {{{ ^(ι φ) }}} σ ->
    {{{ M[σ] }}} = {{{ M⟨φ⟩ }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_of_wk_ext. Qed.

Corollary exp_sub_of_wk : forall M φ, {{{ M[^(ι φ)] }}} = {{{ M⟨φ⟩ }}}.
Proof. intros; now apply exp_sub_of_wk_ext. Qed.

Corollary sb_q_of_wk : forall φ, sb_eq {{{ ^(ι (wk_q φ)) }}} {{{ q ^(ι φ) }}}.
Proof. intros; now apply sb_q_of_wk_ext. Qed.

Lemma sb_of_wk_id : sb_eq {{{ ^(ι wk_id) }}} {{{ Id }}}.
Proof. pointwise_solve. Qed.

Lemma sb_of_wk_shift : sb_eq {{{ ^(ι wk_shift) }}} {{{ Wk }}}.
Proof. pointwise_solve. Qed.

Lemma sb_of_wk_compose : forall φ ψ,
    sb_eq {{{ ^(ι (φ ⊙ ψ)) }}} {{{ ^(ι φ) ⨟ ^(ι ψ) }}}.
Proof. intros *; pointwise_solve. Qed.

(** The identity substitution. *)

Lemma sb_q_id_ext : forall σ, sb_eq σ {{{ Id }}} -> sb_eq {{{ q σ }}} {{{ Id }}}.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite Heq; reduce_index; reflexivity.
Qed.

Lemma exp_sub_id_ext : forall M σ,
    sb_eq σ {{{ Id }}} ->
    {{{ M[σ] }}} = M.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_id_ext. Qed.

Corollary sb_q_id : sb_eq {{{ q Id }}} {{{ Id }}}.
Proof. now apply sb_q_id_ext. Qed.

Corollary exp_sub_id : forall M, {{{ M[Id] }}} = M.
Proof. intros; now apply exp_sub_id_ext. Qed.

(** Postcomposing with a weakening. *)

Lemma sb_q_wk_ext : forall σ φ τ,
    sb_eq (sb_wk σ φ) τ ->
    sb_eq (sb_wk {{{ q σ }}} (wk_q φ)) {{{ q τ }}}.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite <- Heq; reduce_index.
  do 2 rewrite exp_wk_wk.
  apply exp_wk_wk_eq; pointwise_solve.
Qed.

Lemma exp_wk_sub_ext : forall M σ φ τ,
    sb_eq (sb_wk σ φ) τ ->
    {{{ M[σ]⟨φ⟩ }}} = {{{ M[τ] }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_wk_ext. Qed.

Corollary sb_q_wk : forall σ φ,
    sb_eq (sb_wk {{{ q σ }}} (wk_q φ)) {{{ q ^(sb_wk σ φ) }}}.
Proof. intros; now apply sb_q_wk_ext. Qed.

Corollary exp_wk_sub : forall M σ φ, {{{ M[σ]⟨φ⟩ }}} = {{{ M[^(sb_wk σ φ)] }}}.
Proof. intros; now apply exp_wk_sub_ext. Qed.

(** The two instances a Kripke weakening of a [natrec] produces: its motive sits
    under [q] and its scrutinee's type under an extension. *)
Corollary exp_wk_sub_q : forall M σ φ,
    {{{ M[q σ]⟨wk_q φ⟩ }}} = {{{ M[q ^(sb_wk σ φ)] }}}.
Proof. intros; apply exp_wk_sub_ext, sb_q_wk. Qed.

Corollary exp_wk_sub_extend_head : forall M σ N φ,
    {{{ M[σ ,, N]⟨φ⟩ }}} = {{{ M[^(sb_wk σ φ) ,, N⟨φ⟩] }}}.
Proof. intros; apply exp_wk_sub_ext; intros [| y]; reflexivity. Qed.

(** The successor branch sits under two [q]s. *)
Corollary sb_q_wk2 : forall σ φ,
    sb_eq (sb_wk {{{ q (q σ) }}} (wk_q (wk_q φ))) {{{ q (q ^(sb_wk σ φ)) }}}.
Proof. intros; rewrite sb_q_wk, sb_q_wk; reflexivity. Qed.

Corollary exp_wk_sub_q2 : forall M σ φ,
    {{{ M[q (q σ)]⟨wk_q (wk_q φ)⟩ }}} = {{{ M[q (q ^(sb_wk σ φ))] }}}.
Proof. intros; apply exp_wk_sub_ext, sb_q_wk2. Qed.

(** Precomposing with a weakening. *)

Lemma sb_q_wk_pre_ext : forall φ σ τ,
    (forall x, σ (φ x) = τ x) ->
    forall x, {{{ q σ }}} (wk_q φ x) = {{{ q τ }}} x.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  now rewrite Heq.
Qed.

Lemma exp_sub_wk_ext : forall M φ σ τ,
    (forall x, σ (φ x) = τ x) ->
    {{{ M⟨φ⟩[σ] }}} = {{{ M[τ] }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_wk_pre_ext. Qed.

Corollary exp_sub_wk : forall M φ σ, {{{ M⟨φ⟩[σ] }}} = {{{ M[^(ι φ) ⨟ σ] }}}.
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.

(** The two instances at [↑], spelled with [Wk] instead of [ι ↑].  [Wk] *is*
    [ι ↑] by definition, but [rewrite] matches syntactically, and it is [Wk] that
    the semantic shift lemmas speak of — so these are the
    spellings a context lookup needs in order to move its [A⟨↑⟩] along a
    substitution. *)

Corollary exp_sub_shift : forall M σ, {{{ M⟨↑⟩[σ] }}} = {{{ M[Wk ⨟ σ] }}}.
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.

Corollary exp_sub_of_shift : forall M, {{{ M[Wk] }}} = {{{ M⟨↑⟩ }}}.
Proof. intros; apply exp_sub_of_wk_ext, sb_of_wk_shift. Qed.

(** Instantiating the codomain of a *weakened* [Π]-type.  This is the shape the
    gluing model states its [Π] clauses in: the elimination rule
    produces [OT⟨q φ⟩[Id ,, N]] and the clause speaks of [OT[ι φ ,, N]]. *)
Corollary exp_sub_wk_q_extend : forall M φ N,
    {{{ M⟨wk_q φ⟩[Id ,, N] }}} = {{{ M[^(ι φ) ,, N] }}}.
Proof. intros; apply exp_sub_wk_ext; intros [|?]; reflexivity. Qed.

(** The same with the identity replaced by a second weakening: this is what a
    [Π]-clause of the gluing model turns into when it is itself transported along
    a Kripke weakening. *)
Corollary exp_sub_wk_q_extend_wk : forall M φ ψ N,
    {{{ M⟨wk_q φ⟩[^(ι ψ) ,, N] }}} = {{{ M[^(ι (φ ⊙ ψ)) ,, N] }}}.
Proof. intros; apply exp_sub_wk_ext; intros [|?]; reflexivity. Qed.

(** [ι (q φ)] read as an extension.  This is the converse direction of the two
    above: instantiating a clause about [OT[ι ψ ,, M]] at the canonical variable
    of an extended context has to land back on the [OT⟨q φ⟩] that
    [(Π IT OT)⟨φ⟩] exposes. *)
Lemma sb_of_wk_q_extend : forall φ,
    sb_eq {{{ ^(ι (φ ⊙ ↑)) ,, #0 }}} {{{ ^(ι (wk_q φ)) }}}.
Proof. intros *; pointwise; reflexivity. Qed.

Corollary exp_sub_of_wk_q_extend : forall M φ,
    {{{ M[^(ι (φ ⊙ ↑)) ,, #0] }}} = {{{ M⟨wk_q φ⟩ }}}.
Proof.
  intros; rewrite (exp_sub_sb_eq _ _ _ (sb_of_wk_q_extend φ)).
  apply exp_sub_of_wk.
Qed.

(** The degenerate instance of the above, at [φ := wk_id]: extending [ι ↑] by
    the canonical variable is the identity.  This is the shape a [Π]-clause of
    the gluing model takes when it is instantiated at the shift out of its own
    extended context. *)
Corollary exp_sub_of_shift_extend_zero : forall M, {{{ M[^(ι ↑) ,, #0] }}} = M.
Proof. intros; apply exp_sub_id_ext; pointwise; reflexivity. Qed.

(** Transporting an instantiated [Π]-codomain along a further weakening: the
    two weakenings fuse and the argument is weakened in place.  This is what the
    readback clauses of the gluing model need in order to iterate. *)
Corollary exp_wk_sub_of_wk_extend : forall M φ ψ N,
    {{{ M[^(ι φ) ,, N]⟨ψ⟩ }}} = {{{ M[^(ι (φ ⊙ ψ)) ,, N⟨ψ⟩] }}}.
Proof. intros; apply exp_wk_sub_ext; pointwise; reflexivity. Qed.

(** Weakening and substitution commute.  Stating the hypothesis pointwise is
    what removes the induction over the number of enclosing binders: the hypothesis is exactly what survives being lifted. *)

Lemma sb_q_comm_ext : forall φ σ τ ψ,
    (forall x, σ (φ x) = {{{ ^(τ x)⟨ψ⟩ }}}) ->
    forall x, {{{ q σ }}} (wk_q φ x) = {{{ ^({{{ q τ }}} x)⟨wk_q ψ⟩ }}}.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite Heq; do 2 rewrite exp_wk_wk.
  apply exp_wk_wk_eq; pointwise_solve.
Qed.

Lemma exp_wk_sub_comm_ext : forall M φ σ τ ψ,
    (forall x, σ (φ x) = {{{ ^(τ x)⟨ψ⟩ }}}) ->
    {{{ M⟨φ⟩[σ] }}} = {{{ M[τ]⟨ψ⟩ }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_comm_ext. Qed.

(** The instances the rest of the development needs: the commutation above at
    [n = 0], once for a lifted substitution and once for a lifted weakening.  Together with
    [exp_sub_shift_extend] below, these three are what push the [A⟨↑⟩] produced
    by a context lookup past a lifted operation, and hence what every
    [q]-preservation lemma reduces to. *)

Corollary exp_wk_shift_sub_q : forall M σ,
    {{{ M⟨↑⟩[q σ] }}} = {{{ M[σ]⟨↑⟩ }}}.
Proof. intros; apply exp_wk_sub_comm_ext; intros; reflexivity. Qed.

Corollary exp_wk_shift_wk_q : forall M φ,
    {{{ M⟨↑⟩⟨wk_q φ⟩ }}} = {{{ M⟨φ⟩⟨↑⟩ }}}.
Proof.
  intros; do 2 rewrite exp_wk_wk.
  apply exp_wk_wk_eq; pointwise_solve.
Qed.

(** "[⇑] cancels an extension" at the level of expressions: an extension is
    invisible to an expression that has just been weakened. *)
Corollary exp_sub_shift_extend : forall M σ N,
    {{{ M⟨↑⟩[σ ,, N] }}} = {{{ M[σ] }}}.
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.

(** Substitution application respects
    composition. *)

Lemma sb_q_compose_ext : forall σ τ δ,
    sb_eq {{{ σ ⨟ τ }}} δ ->
    sb_eq {{{ (q σ) ⨟ (q τ) }}} {{{ q δ }}}.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite <- Heq; reduce_index.
  apply exp_wk_shift_sub_q.
Qed.

Lemma exp_sub_sub_ext : forall M σ τ δ,
    sb_eq {{{ σ ⨟ τ }}} δ ->
    {{{ M[σ][τ] }}} = {{{ M[δ] }}}.
Proof. induction M; intros * Heq; exp_ind_ext Heq sb_q_compose_ext. Qed.

Corollary sb_q_compose : forall σ τ,
    sb_eq {{{ (q σ) ⨟ (q τ) }}} {{{ q (σ ⨟ τ) }}}.
Proof. intros; now apply sb_q_compose_ext. Qed.

Corollary exp_sub_sub : forall M σ τ, {{{ M[σ][τ] }}} = {{{ M[σ ⨟ τ] }}}.
Proof. intros; now apply exp_sub_sub_ext. Qed.

(** Substitutions form a category. *)

Lemma sb_compose_id_left : forall σ, sb_eq {{{ Id ⨟ σ }}} σ.
Proof. intros ? ?; reflexivity. Qed.

Lemma sb_compose_id_right : forall σ, sb_eq {{{ σ ⨟ Id }}} σ.
Proof. intros ? ?; simpl; apply exp_sub_id. Qed.

Lemma sb_compose_assoc : forall σ τ δ,
    sb_eq {{{ (σ ⨟ τ) ⨟ δ }}} {{{ σ ⨟ (τ ⨟ δ) }}}.
Proof. intros * x; simpl; apply exp_sub_sub. Qed.

(** [σ[φ]] is just [σ ⨟ ι φ]; this is [exp_sub_of_wk] read pointwise. *)
Lemma sb_wk_compose : forall σ φ, sb_eq (sb_wk σ φ) {{{ σ ⨟ ^(ι φ) }}}.
Proof. intros * x; simpl; symmetry; apply exp_sub_of_wk. Qed.

(** [exp_wk_wk] pointwise: postcomposing twice is postcomposing by the
    composite.  This is what makes the two instantiations of the semantic
    weakening lemma speak about the same substitution. *)
Lemma sb_wk_wk : forall σ ψ φ, sb_eq (sb_wk (sb_wk σ ψ) φ) (sb_wk σ (ψ ⊙ φ)).
Proof. intros * x; simpl; apply exp_wk_wk. Qed.

(** Postcomposition by a weakening slides past *pre*composition by a weakening:
    both sides send [x] to [(σ (ψ x))⟨φ⟩].  Nothing has to be transported across
    [ψ], because [(ι ψ) x] is a variable — the same reason [eval_sub_wk_pre]
    exists while its analogue for a general composition does not.  The semantic
    weakening lemma needs the general form; [sb_wk_shift_pre] below is the
    instance at [ψ := ⇑]. *)
Lemma sb_wk_wk_pre : forall σ ψ φ,
    sb_eq (sb_wk {{{ ^(ι ψ) ⨟ σ }}} φ) {{{ ^(ι ψ) ⨟ ^(sb_wk σ φ) }}}.
Proof. intros * x; reflexivity. Qed.

Corollary sb_wk_shift_pre : forall σ φ,
    sb_eq (sb_wk {{{ Wk ⨟ σ }}} φ) {{{ Wk ⨟ ^(sb_wk σ φ) }}}.
Proof. intros. apply (sb_wk_wk_pre σ wk_shift). Qed.

(** Postcomposition by a weakening distributes over an extension, read at
    [σ ,, M].  Completeness uses it in the other direction: a semantic
    substitution judgment about [σ ,, t] has to produce the evaluation of
    [(σ ,, t)[ψ]], and [eval_sub_extend] only speaks about a syntactic
    extension. *)
Lemma sb_wk_extend : forall σ M φ,
    sb_eq (sb_wk {{{ σ ,, M }}} φ) {{{ ^(sb_wk σ φ) ,, M⟨φ⟩ }}}.
Proof. intros *; pointwise_solve. Qed.

(** The instance of the above at [q σ], with the two heads computed: [q σ] is
    an extension by [#0], and [(#0)⟨φ⟩] is [#(φ 0)].  This is the identity
    the completeness substitution cases need in order to see [(q σ)[ψ]] as an
    extension. *)
Lemma sb_wk_q : forall σ φ,
    sb_eq (sb_wk {{{ q σ }}} φ) {{{ ^(sb_wk σ (↑ ⊙ φ)) ,, #(φ 0) }}}.
Proof. intros *; pointwise; [ reflexivity | apply exp_wk_wk ]. Qed.

(** [⇑] cancels an extension. *)
Lemma sb_shift_extend : forall σ M, sb_eq {{{ Wk ⨟ (σ ,, M) }}} σ.
Proof. intros * x; reflexivity. Qed.

(** Composition distributes over extension. *)
Lemma sb_extend_compose : forall σ τ M,
    sb_eq {{{ (σ ,, M) ⨟ τ }}} {{{ (σ ⨟ τ) ,, M[τ] }}}.
Proof. intros *; pointwise_solve. Qed.

(** Every substitution is its own expansion. *)
Lemma sb_expand : forall σ, sb_eq σ {{{ (Wk ⨟ σ) ,, #0[σ] }}}.
Proof. intros *; pointwise_solve. Qed.

(** A lifted substitution meeting an extension.
    These are the equations behind the [β]-rule and the elimination rules. *)

(** The general form — the old [sub_decompose_q], now an equation.  The two
    lemmas below are its instances at [τ := ι φ] and [τ := Id]; both are stated
    separately because the head of the right-hand side differs, and it is the
    head that the rewrite databases match on. *)
Lemma sb_q_compose_extend : forall σ τ M,
    sb_eq {{{ (q σ) ⨟ (τ ,, M) }}} {{{ (σ ⨟ τ) ,, M }}}.
Proof.
  intros *; pointwise; [ reflexivity | apply exp_sub_shift_extend ].
Qed.

Corollary exp_sub_q_compose_extend : forall M σ τ N,
    {{{ M[q σ][τ ,, N] }}} = {{{ M[(σ ⨟ τ) ,, N] }}}.
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_compose_extend.
Qed.

Lemma sb_q_extend_wk : forall σ φ M,
    sb_eq {{{ (q σ) ⨟ (^(ι φ) ,, M) }}} {{{ ^(sb_wk σ φ) ,, M }}}.
Proof.
  intros *; pointwise; [ reflexivity | ].
  rewrite exp_sub_wk_ext with (τ := sb_of_wk φ) by reflexivity.
  apply exp_sub_of_wk.
Qed.

Corollary exp_sub_q_extend_wk : forall M σ φ N,
    {{{ M[q σ][^(ι φ) ,, N] }}} = {{{ M[^(sb_wk σ φ) ,, N] }}}.
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_extend_wk.
Qed.

Lemma sb_q_extend : forall σ M, sb_eq {{{ (q σ) ⨟ (Id ,, M) }}} {{{ σ ,, M }}}.
Proof.
  intros *; pointwise; [ reflexivity | ].
  rewrite exp_sub_wk_ext with (τ := sb_id) by reflexivity.
  apply exp_sub_id.
Qed.

Corollary exp_sub_q_extend : forall M σ N,
    {{{ M[q σ][Id ,, N] }}} = {{{ M[σ ,, N] }}}.
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_extend.
Qed.

(** A single substitution commutes past a lifted one. *)
Corollary exp_sub_extend_comm : forall M σ N,
    {{{ M[q σ][Id ,, N[σ]] }}} = {{{ M[Id ,, N][σ] }}}.
Proof.
  intros.
  rewrite exp_sub_q_extend, exp_sub_sub.
  apply exp_sub_sb_eq; pointwise_solve.
Qed.

(** The form the completeness proof uses it in: an instantiated type or term,
    substituted, is the instantiation *along* the substitution.  Every rule whose
    type is an [M[Id ,, N]] reads its two outer values through this equation,
    because those are values at [ρ] and [ρ'] of the substituted expression while
    the judgment about [M] can only produce values along a substitution into the
    extended context. *)
Corollary exp_sub_extend_sub : forall M σ N,
    {{{ M[Id ,, N][σ] }}} = {{{ M[σ ,, N[σ]] }}}.
Proof.
  intros.
  rewrite <- exp_sub_extend_comm.
  apply exp_sub_q_extend.
Qed.

(** ** The Instances the Typing Rules Need

    Every type appearing in an elimination rule is of one of three
    shapes: [A[Id ,, N]] (application, [ℕ]-elimination), [A[Id ,, N ,, N']] (the
    [ℕ]-[β] rule for [succ]) or [A[Wk⨟Wk ,, succ #1]] (the successor branch of the
    eliminator).  [wk_preserves_wf] and [sub_preserves_wf] have to push a
    weakening, respectively a
    substitution, past each of them, and the six corollaries below are exactly
    the equations that come up.  Each one is an instance of
    [exp_wk_sub_comm_ext] or of [exp_sub_sub_ext] whose side condition holds by
    computation, so [intros <pattern>; reflexivity] discharges it.

    The single-substitution case for [exp_sub] is [exp_sub_extend_comm] above. *)

(** [Wk ⨟ Wk] is the weakening [↑ ⊙ ↑] in disguise. *)
Lemma sb_shift_shift : sb_eq {{{ Wk ⨟ Wk }}} {{{ ^(ι (↑ ⊙ ↑)) }}}.
Proof. intros ?; reflexivity. Qed.

Corollary exp_sub_shift_shift : forall M, {{{ M[Wk ⨟ Wk] }}} = {{{ M⟨↑⟩⟨↑⟩ }}}.
Proof.
  intros; rewrite sb_shift_shift, exp_sub_of_wk.
  symmetry; apply exp_wk_wk.
Qed.

Corollary exp_wk_sub_extend : forall M N φ,
    {{{ (M[Id ,, N])⟨φ⟩ }}} = {{{ M⟨wk_q φ⟩[Id ,, N⟨φ⟩] }}}.
Proof.
  intros; symmetry.
  apply exp_wk_sub_comm_ext; intros [| y]; reflexivity.
Qed.

Corollary exp_wk_sub_extend2 : forall M N N' φ,
    {{{ (M[Id ,, N ,, N'])⟨φ⟩ }}} = {{{ M⟨wk_q (wk_q φ)⟩[Id ,, N⟨φ⟩ ,, N'⟨φ⟩] }}}.
Proof.
  intros; symmetry.
  apply exp_wk_sub_comm_ext; intros [| [| y]]; reflexivity.
Qed.

(** The motive of the successor branch is stable under a doubly lifted
    weakening. *)
Corollary exp_wk_sub_natrec : forall M φ,
    {{{ (M[Wk⨟Wk ,, succ #1])⟨wk_q (wk_q φ)⟩ }}} = {{{ M⟨wk_q φ⟩[Wk⨟Wk ,, succ #1] }}}.
Proof.
  intros; symmetry.
  apply exp_wk_sub_comm_ext; intros [| y]; reflexivity.
Qed.

Corollary exp_sub_sub_extend2 : forall M σ N N',
    {{{ (M[Id ,, N ,, N'])[σ] }}} = {{{ M[q (q σ)][Id ,, N[σ] ,, N'[σ]] }}}.
Proof.
  intros.
  do 2 rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| [| y]]; reduce_index; try reflexivity.
  do 2 rewrite exp_sub_shift_extend.
  symmetry; apply exp_sub_id.
Qed.

Corollary exp_sub_sub_natrec : forall M σ,
    {{{ (M[Wk⨟Wk ,, succ #1])[q (q σ)] }}} = {{{ M[q σ][Wk⨟Wk ,, succ #1] }}}.
Proof.
  intros.
  do 2 rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; [ reflexivity | ].
  rewrite exp_sub_shift_extend.
  symmetry; apply exp_sub_shift_shift.
Qed.

(** The type of the [ℕ]-[β] rule for [succ]: the successor branch's motive,
    instantiated at [N] and the recursive call, is the motive at [succ N].  Stated
    along an arbitrary [σ] and not just [Id], because the semantic rule reads this
    type at *two* substitutions — [Id ,, M ,, E] out of [Γ] for its two inner
    values and [σ ,, M[σ] ,, E[σ]] out of the caller's [Γ'] for its two outer
    ones — and both instances have to be the *same* equation for the two
    four-value patterns to be identified with one another. *)
Corollary exp_sub_natrec_step : forall M σ N N',
    {{{ (M[Wk⨟Wk ,, succ #1])[σ ,, N ,, N'] }}} = {{{ M[σ ,, succ N] }}}.
Proof.
  intros.
  rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; reflexivity.
Qed.

(** The two-argument analogue of [exp_sub_extend_sub], which is what the
    right-hand side of that rule — an [MS[Id ,, M ,, E]] — is read through. *)
Corollary exp_sub_extend_sub2 : forall M σ N N',
    {{{ M[Id ,, N ,, N'][σ] }}} = {{{ M[σ ,, N[σ] ,, N'[σ]] }}}.
Proof.
  intros.
  rewrite exp_sub_sub_extend2, exp_sub_sub.
  apply exp_sub_sb_eq; intros [| [| y]]; reduce_index; try reflexivity.
  do 2 rewrite exp_sub_shift_extend.
  apply exp_sub_id.
Qed.

(** [zero[σ]] is [zero], so the zero branch's type is an instance of
    [exp_sub_extend_sub] with the right-hand side already reduced. *)
Corollary exp_sub_extend_sub_zero : forall M σ,
    {{{ M[Id ,, zero][σ] }}} = {{{ M[σ ,, zero] }}}.
Proof. intros; apply exp_sub_extend_sub. Qed.

Corollary exp_sub_q_extend2 : forall M σ N N',
    {{{ M[q (q σ)][Id ,, N ,, N'] }}} = {{{ M[σ ,, N ,, N'] }}}.
Proof.
  intros.
  rewrite exp_sub_q_compose_extend.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; [ reflexivity | apply sb_q_extend ].
Qed.

(** [exp_sub_natrec_step] along an arbitrary substitution: [τ] need not be a
    literal extension, because [sb_expand] makes every substitution one. *)
Corollary exp_sub_natrec_step_gen : forall M τ,
    {{{ (M[Wk⨟Wk ,, succ #1])[τ] }}} = {{{ M[(Wk ⨟ (Wk ⨟ τ)) ,, succ (#0[Wk ⨟ τ])] }}}.
Proof.
  intros.
  rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; reflexivity.
Qed.

(** ** The Generic Recursor

    An eliminator whose scrutinee is [#0] and whose three other components have
    been weakened past that binder.  If [E] is the eliminator at [M] in [Γ], this
    is a term of [Γ, ℕ] which the extension [Id ,, M] sends back to [E], and it
    exists for one reason: the recursive call of the [ℕ]-[β] rule for [succ]
    appears in the *substitution* [Id ,, M ,, E], and the only way to validate an
    extension semantically ([rel_sub_under_ctx_extend_sub_double]) is by a term of
    the context being extended.  [E] itself is a term of [Γ], one context too
    short; its generic form is the term of [Γ, ℕ] that is asked for. *)
Corollary exp_sub_natrec_generic : forall A MZ MS σ N,
    {{{ (rec #0 return A⟨wk_q ↑⟩ | zero -> MZ⟨↑⟩ | succ -> MS⟨wk_q (wk_q ↑)⟩ end)[σ ,, N] }}}
    = {{{ rec N return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}.
Proof.
  intros; cbn [exp_sub]; f_equal;
    try apply exp_sub_shift_extend;
    try reflexivity;
    rewrite exp_sub_wk; apply exp_sub_sb_eq;
    intros [| [| y]]; reduce_index; reflexivity.
Qed.

(** Its defining property: substituting the generic recursor along [σ ,, M[σ]]
    is substituting the eliminator at [M] along [σ]. *)
Corollary exp_sub_natrec_generic_self : forall A MZ MS σ M,
    {{{ (rec #0 return A⟨wk_q ↑⟩ | zero -> MZ⟨↑⟩ | succ -> MS⟨wk_q (wk_q ↑)⟩ end)[σ ,, M[σ]] }}}
    = {{{ (rec M return A | zero -> MZ | succ -> MS end)[σ] }}}.
Proof.
  intros; apply exp_sub_natrec_generic.
Qed.

(** The type of the [η]-rule: a codomain weakened under one more binder and
    then applied to [#0] is the codomain itself. *)
Corollary exp_wk_q_shift_single : forall M, {{{ M⟨wk_q ↑⟩[Id ,, #0] }}} = M.
Proof.
  intros.
  rewrite exp_sub_wk.
  transitivity {{{ M[Id] }}}; [ apply exp_sub_sb_eq | apply exp_sub_id ].
  intros [| y]; reduce_index; reflexivity.
Qed.

(** The action of [q^n] on indices. *)

Lemma sb_qn_lt : forall n σ x, x < n -> sb_qn n σ x = {{{ #x }}}.
Proof.
  induction n; intros * Hlt; [ exfalso; lia | ].
  destruct x; [ reflexivity | ].
  simpl; reduce_index; rewrite IHn by lia; reflexivity.
Qed.

Lemma sb_qn_ge : forall n σ x,
    n <= x ->
    sb_qn n σ x = {{{ ^(σ (x - n))⟨wk_shiftn n⟩ }}}.
Proof.
  induction n; intros * Hle; simpl.
  - replace (x - 0) with x by lia.
    symmetry; apply exp_wk_id_ext, wk_shiftn_zero.
  - destruct x; [ exfalso; lia | ].
    reduce_index; rewrite IHn by lia.
    rewrite exp_wk_wk.
    replace (S x - S n) with (x - n) by lia.
    apply exp_wk_wk_eq, wk_shiftn_succ.
Qed.

(** ** Automation

    The [sb] rewrite database normalises a substitution expression: it computes
    the operations at concrete indices and fuses nested applications via the
    composition laws.  Prefer extending it over unfolding these definitions by
    hand. *)

#[export]
Hint Rewrite -> wk_id_var wk_shift_var wk_q_zero wk_q_succ
                wk_compose_var wk_shiftn_var
                sb_id_var sb_shift_var sb_extend_zero sb_extend_succ
                sb_wk_var sb_of_wk_var sb_compose_var
                sb_q_zero sb_q_succ
                exp_wk_var exp_sub_var
                exp_wk_typ exp_wk_nat exp_wk_zero
                exp_sub_typ exp_sub_nat exp_sub_zero
                exp_wk_id exp_sub_id exp_wk_wk exp_sub_sub
                exp_wk_sub exp_sub_of_wk
                exp_sub_shift_extend
                exp_sub_q_extend exp_sub_q_extend_wk exp_sub_q_compose_extend : sb.

Ltac simpl_sub := autorewrite with sb in *.

(** The laws are useful to [mauto] as rewrites; adding them as resolution hints
    instead would let [eauto] loop through the composition laws. *)
#[export]
Hint Rewrite -> exp_sub_id exp_sub_sub exp_sub_shift_extend
                exp_sub_q_extend exp_sub_q_compose_extend : mctt.
