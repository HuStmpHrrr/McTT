(** * The Algebra of Weakenings and Substitutions

    Weakenings and substitutions are meta-level operations on [exp] (see
    [Core.Syntactic.Syntax]), so the laws that a calculus of explicit
    substitutions postulates as definitional equalities are theorems here.

    Two conventions:

    - Composition is diagrammatic: [σ ⨟ τ] applies [σ] first and then [τ].
    - Weakenings and substitutions are functions, so a law the paper states as
      an equality of substitutions is an equality of the pointwise relation
      [sb_eq] (respectively [wk_eq]), which avoids functional
      extensionality.  The congruence lemmas [exp_wk_wk_eq] and
      [exp_sub_sb_eq], with the [Proper] instances registered below, let
      [rewrite] cross between the two.

    Most laws come in two forms: a general one taking the relevant pointwise
    equation as a hypothesis (suffix [_ext]), and the specialisation that
    matches the paper.  The general form makes the inductions go through,
    because it survives passing under a binder, so no induction over the
    number of enclosing binders is needed; the rest of the development uses
    the specialisation. *)

From Stdlib Require Import Lia Morphisms Relation_Definitions RelationClasses Setoid.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Wk_Notations.


Create Rewrite HintDb sb_index.
Create Rewrite HintDb sb.
Create Rewrite HintDb syn_ops.

Section computation.
  Variable (σ τ : sub) (φ ψ : wk) (M : exp) (H : modexp) (e : sentry) (x : nat).

  Fact wk_id_var : wk_id x = x.                                    Proof. reflexivity. Qed.
  Fact wk_shift_var : wk_shift x = S x.                            Proof. reflexivity. Qed.
  Fact wk_q_zero : wk_q φ 0 = 0.                                   Proof. reflexivity. Qed.
  Fact wk_q_succ : wk_q φ (S x) = S (φ x).                         Proof. reflexivity. Qed.
  Fact wk_compose_var : (φ ⊙ ψ) x = ψ (φ x).                       Proof. reflexivity. Qed.
  Fact wk_shiftn_var : forall n, wk_shiftn n x = x + n.            Proof. reflexivity. Qed.

  Fact sb_id_var : Id x = se_var x.                        Proof. reflexivity. Qed.
  Fact sb_shift_var : Wk x = se_var (S x).                 Proof. reflexivity. Qed.
  Fact sb_extend_zero : (sb_extend σ e) 0 = e.             Proof. reflexivity. Qed.
  Fact sb_extend_succ : (sb_extend σ e) (S x) = σ x.       Proof. reflexivity. Qed.
  Fact sb_wk_var : sb_wk σ φ x = sentry_wk (σ x) φ.        Proof. reflexivity. Qed.
  Fact sb_of_wk_var : (ι φ) x = se_var (φ x).              Proof. reflexivity. Qed.
  Fact sb_compose_var : (σ ⨟ τ) x = sentry_sub (σ x) τ.    Proof. reflexivity. Qed.
  Fact sb_q_zero : (q σ) 0 = se_var 0.                     Proof. reflexivity. Qed.
  Fact sb_q_succ : (q σ) (S x) = sentry_wk (σ x) wk_shift. Proof. reflexivity. Qed.

  Fact sentry_wk_var : sentry_wk (se_var x) φ = se_var (φ x).        Proof. reflexivity. Qed.
  Fact sentry_wk_exp : sentry_wk (se_exp M) φ = se_exp M[φ]ʷ.        Proof. reflexivity. Qed.
  Fact sentry_wk_mod : sentry_wk (se_mod H) φ = se_mod (modexp_wk H φ). Proof. reflexivity. Qed.
  Fact sentry_sub_var : sentry_sub (se_var x) σ = σ x.               Proof. reflexivity. Qed.
  Fact sentry_sub_exp : sentry_sub (se_exp M) σ = se_exp M[σ].       Proof. reflexivity. Qed.
  Fact sentry_sub_mod : sentry_sub (se_mod H) σ = se_mod H[σ]ᵐ.      Proof. reflexivity. Qed.

  Fact sentry_exp_var : sentry_exp (se_var x) = #x.             Proof. reflexivity. Qed.
  Fact sentry_exp_exp : sentry_exp (se_exp M) = M.               Proof. reflexivity. Qed.
  Fact sentry_modexp_var : sentry_modexp (se_var x) = me_var x.  Proof. reflexivity. Qed.
  Fact sentry_modexp_mod : sentry_modexp (se_mod H) = H.         Proof. reflexivity. Qed.
  Fact exp_wk_var : #x[φ]ʷ = #(φ x).                       Proof. reflexivity. Qed.
  Fact exp_sub_var : #x[σ] = sentry_exp (σ x).             Proof. reflexivity. Qed.
  Fact modexp_wk_var : modexp_wk (me_var x) φ = me_var (φ x). Proof. reflexivity. Qed.
  Fact modexp_sub_var : (me_var x)[σ]ᵐ = sentry_modexp (σ x). Proof. reflexivity. Qed.
End computation.

#[export]
Hint Rewrite -> wk_id_var wk_shift_var wk_q_zero wk_q_succ
                wk_compose_var wk_shiftn_var
                sb_id_var sb_shift_var sb_extend_zero sb_extend_succ
                sb_wk_var sb_of_wk_var sb_compose_var
                sb_q_zero sb_q_succ
                sentry_wk_var sentry_wk_exp sentry_wk_mod
                sentry_sub_var sentry_sub_exp sentry_sub_mod
                sentry_exp_var sentry_exp_exp sentry_modexp_var sentry_modexp_mod
                exp_wk_var exp_sub_var modexp_wk_var modexp_sub_var : sb_index.

Ltac reduce_index := autorewrite with sb_index in *.

(** The projections of an entry commute with the operations: an entry of the
    wrong sort projects to a closed default, which every operation fixes. *)
Lemma sentry_exp_wk : forall e φ, (sentry_exp e)[φ]ʷ = sentry_exp (sentry_wk e φ).
Proof. intros [] ?; reflexivity. Qed.

Lemma sentry_modexp_wk : forall e φ, modexp_wk (sentry_modexp e) φ = sentry_modexp (sentry_wk e φ).
Proof. intros [] ?; reflexivity. Qed.

Lemma sentry_exp_sub : forall e σ, (sentry_exp e)[σ] = sentry_exp (sentry_sub e σ).
Proof. intros [] ?; reflexivity. Qed.

Lemma sentry_modexp_sub : forall e σ, (sentry_modexp e)[σ]ᵐ = sentry_modexp (sentry_sub e σ).
Proof. intros [] ?; reflexivity. Qed.

(** A unit's telescope and definition, read off the fold. *)
Lemma gunit_wk_mk : forall Δ D φ,
    gunit_wk (gu_mk Δ D) φ = gu_mk (tele_wk Δ φ) (moddef_wk D (wk_qn (List.length Δ) φ)).
Proof. intros; simpl; f_equal; induction Δ; simpl; congruence. Qed.

Lemma gunit_sub_mk : forall Δ D σ,
    gunit_sub (gu_mk Δ D) σ = gu_mk (tele_sub Δ σ) (moddef_sub D (sb_qn (List.length Δ) σ)).
Proof. intros; simpl; f_equal; induction Δ; simpl; congruence. Qed.

Lemma length_tele_wk : forall Δ φ, List.length (tele_wk Δ φ) = List.length Δ.
Proof. induction Δ; simpl; auto. Qed.

Lemma length_tele_sub : forall Δ σ, List.length (tele_sub Δ σ) = List.length Δ.
Proof. induction Δ; simpl; auto. Qed.

Lemma gm_binders_wk : forall Φ φ, gm_binders (gmod_wk Φ φ) = gm_binders Φ.
Proof. induction Φ; simpl; auto. Qed.

Lemma gm_binders_sub : forall Φ σ, gm_binders (gmod_sub Φ σ) = gm_binders Φ.
Proof. induction Φ; simpl; auto. Qed.

#[export]
Hint Rewrite -> gunit_wk_mk gunit_sub_mk length_tele_wk length_tele_sub gm_binders_wk gm_binders_sub : syn_ops.

(** The heads an operation passes through without meeting a binder.  [Π], [λ],
    application and the eliminator are deliberately absent: pushing an operation
    through those introduces a [q], which is not a simplification.  These are
    stated outside the section above only to fix the argument order. *)

Fact exp_wk_typ : forall φ i, Type@i[φ]ʷ = Type@i.       Proof. reflexivity. Qed.
Fact exp_wk_nat : forall φ, ℕ[φ]ʷ = ℕ.                   Proof. reflexivity. Qed.
Fact exp_wk_zero : forall φ, zero[φ]ʷ = zero.            Proof. reflexivity. Qed.
Fact exp_wk_succ : forall φ M, (succ M)[φ]ʷ = succ M[φ]ʷ. Proof. reflexivity. Qed.
Fact exp_sub_typ : forall σ i, Type@i[σ] = Type@i.      Proof. reflexivity. Qed.
Fact exp_sub_nat : forall σ, ℕ[σ] = ℕ.                  Proof. reflexivity. Qed.
Fact exp_sub_zero : forall σ, zero[σ] = zero.           Proof. reflexivity. Qed.
Fact exp_sub_succ : forall σ M, (succ M)[σ] = succ M[σ]. Proof. reflexivity. Qed.
Fact exp_wk_True : forall φ, ⊤[φ]ʷ = ⊤.                  Proof. reflexivity. Qed.
Fact exp_wk_true : forall φ, ⋆[φ]ʷ = ⋆.                  Proof. reflexivity. Qed.
Fact exp_wk_False : forall φ, ⊥[φ]ʷ = ⊥.                 Proof. reflexivity. Qed.
Fact exp_sub_True : forall σ, ⊤[σ] = ⊤.                 Proof. reflexivity. Qed.
Fact exp_sub_true : forall σ, ⋆[σ] = ⋆.                 Proof. reflexivity. Qed.
Fact exp_sub_False : forall σ, ⊥[σ] = ⊥.                Proof. reflexivity. Qed.

(** The heads that do meet a binder.  Kept out of the databases above: pushing
    an operation inside a [Π] or a [λ] replaces it by a [q], which none of the
    laws below can then cancel against an extension.  They are here so that a
    transported [Π]-type can be recognised as one by [rewrite]. *)

Fact exp_wk_pi : forall φ A B, (Π A B)[φ]ʷ = Π A[φ]ʷ B[wk_q φ]ʷ.
Proof. reflexivity. Qed.

Fact exp_wk_fn : forall φ A M, (λ A M)[φ]ʷ = λ A[φ]ʷ M[wk_q φ]ʷ.
Proof. reflexivity. Qed.

Fact exp_wk_app : forall φ M N, (M $ N)[φ]ʷ = M[φ]ʷ $ N[φ]ʷ.
Proof. reflexivity. Qed.

Fact exp_sub_pi : forall σ A B, (Π A B)[σ] = Π A[σ] B[q σ].
Proof. reflexivity. Qed.

Fact exp_sub_fn : forall σ A M, (λ A M)[σ] = λ A[σ] M[q σ].
Proof. reflexivity. Qed.

Fact exp_sub_app : forall σ M N, (M $ N)[σ] = M[σ] $ N[σ].
Proof. reflexivity. Qed.

(** *** Shared Tactics

    Almost every proof below has one of two shapes.

    [pointwise] opens a goal about weakenings or substitutions at index [0] and
    at index [S _] and normalises both; [pointwise_solve] additionally closes
    the resulting arithmetic.  [syn_ind_ext] runs the induction on the syntax
    used by every law in [_ext] form. *)

(** Every operation but [sb_q] is a one-line definition, so [cbv delta] puts a
    pointwise statement into a normal form in which the only remaining opaque
    applications are of the syntactic operations and [sb_q].  Unlike
    rewriting, this reaches under the [forall] of a pointwise hypothesis, which
    is why [reduce_index] alone is not enough. *)
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

(** The mutual induction of a law stated for every sort at once. *)
Ltac syn_mut_ind :=
  lazymatch goal with
  | |- (forall M : exp, @?Pe M) /\ (forall H : modexp, @?Pm H) /\ (forall b : bnd, @?Pb b) /\
      (forall U : gunit, @?Pu U) /\ (forall D : moddef, @?Pd D) /\ (forall Φ : gmod, @?Pg Φ) /\
      (forall c : bcheck, @?Pk c) /\ (forall E : gentry, @?Pn E) /\ (forall e : centry, @?Pc e) =>
      apply (syn_mut_ind Pe Pm Pb Pu Pd Pg Pk Pn Pc)
  end.

(** One case of the induction for a law in [_ext] form.  The variable cases
    are the hypothesis [Heq], read through the lemmas [vars]; every other case
    is a congruence whose subgoals follow from the induction hypotheses once
    [Heq] has been lifted under the binders by [lift] (one binder) or [liftn]
    (a telescope or a body prefix). *)
Ltac syn_ext_tele lift liftn :=
  match goal with
  | HF : List.Forall _ _ |- _ =>
      induction HF; cbn [tele_wk tele_sub]; autorewrite with syn_ops;
      f_equal; eauto using lift, liftn
  end.

Ltac syn_ext_case_with lift liftn vars :=
  intros; autorewrite with syn_ops; intros;
  cbn [exp_wk modexp_wk bnd_wk moddef_wk gmod_wk bcheck_wk gentry_wk centry_wk
       exp_sub modexp_sub bnd_sub moddef_sub gmod_sub bcheck_sub gentry_sub centry_sub];
  autorewrite with syn_ops;
  repeat match goal with
         | B : option exp |- _ => destruct B; cbn iota
         end;
  f_equal;
  try match goal with |- Some _ = Some _ => f_equal end;
  first [ solve [ eauto using lift, liftn ] | syn_ext_tele lift liftn | solve [ vars ] ].

(** The variable cases of most laws are the pointwise hypothesis read at the
    variable, through the projections of an entry. *)
Ltac syn_ext_vars :=
  unfold_ops;
  match goal with
  | Heq : forall _, _ = _ |- _ =>
      solve [ rewrite ?Heq; reduce_index; rewrite ?sentry_exp_wk, ?sentry_modexp_wk, ?sentry_exp_sub, ?sentry_modexp_sub; congruence
            | rewrite <- ?Heq; reduce_index; rewrite ?sentry_exp_wk, ?sentry_modexp_wk, ?sentry_exp_sub, ?sentry_modexp_sub; congruence ]
  end.

Ltac syn_ext_case lift liftn := syn_ext_case_with lift liftn syn_ext_vars.

(** ** Weakenings *)

Lemma wk_q_cong : forall φ ψ, wk_eq φ ψ -> wk_eq (wk_q φ) (wk_q ψ).
Proof. intros * Heq; pointwise_solve. Qed.

Lemma wk_qn_cong : forall n φ ψ, wk_eq φ ψ -> wk_eq (wk_qn n φ) (wk_qn n ψ).
Proof. induction n; intros; simpl; auto using wk_q_cong. Qed.

Lemma wk_compose_cong : forall φ φ' ψ ψ',
    wk_eq φ φ' -> wk_eq ψ ψ' -> wk_eq (φ ⊙ ψ) (φ' ⊙ ψ').
Proof. intros * Heq Heq'; pointwise; rewrite Heq; apply Heq'. Qed.

#[export]
Instance wk_q_Proper : Proper (wk_eq ==> wk_eq) wk_q.
Proof. intros ? ? ?; now apply wk_q_cong. Qed.

#[export]
Instance wk_compose_Proper : Proper (wk_eq ==> wk_eq ==> wk_eq) wk_compose.
Proof. intros ? ? ? ? ? ?; now apply wk_compose_cong. Qed.

Lemma syn_wk_wk_eq :
  (forall M φ ψ, wk_eq φ ψ -> exp_wk M φ = exp_wk M ψ) /\
  (forall H φ ψ, wk_eq φ ψ -> modexp_wk H φ = modexp_wk H ψ) /\
  (forall b φ ψ, wk_eq φ ψ -> bnd_wk b φ = bnd_wk b ψ) /\
  (forall U φ ψ, wk_eq φ ψ -> gunit_wk U φ = gunit_wk U ψ) /\
  (forall D φ ψ, wk_eq φ ψ -> moddef_wk D φ = moddef_wk D ψ) /\
  (forall Φ φ ψ, wk_eq φ ψ -> gmod_wk Φ φ = gmod_wk Φ ψ) /\
  (forall c φ ψ, wk_eq φ ψ -> bcheck_wk c φ = bcheck_wk c ψ) /\
  (forall E φ ψ, wk_eq φ ψ -> gentry_wk E φ = gentry_wk E ψ) /\
  (forall e φ ψ, wk_eq φ ψ -> centry_wk e φ = centry_wk e ψ).
Proof. syn_mut_ind; syn_ext_case wk_q_cong wk_qn_cong. Qed.

Corollary exp_wk_wk_eq : forall M φ ψ, wk_eq φ ψ -> exp_wk M φ = exp_wk M ψ.
Proof. exact (proj1 syn_wk_wk_eq). Qed.
Corollary modexp_wk_wk_eq : forall H φ ψ, wk_eq φ ψ -> modexp_wk H φ = modexp_wk H ψ.
Proof. exact (proj1 (proj2 syn_wk_wk_eq)). Qed.
Corollary bnd_wk_wk_eq : forall b φ ψ, wk_eq φ ψ -> bnd_wk b φ = bnd_wk b ψ.
Proof. exact (proj1 (proj2 (proj2 syn_wk_wk_eq))). Qed.
Corollary gunit_wk_wk_eq : forall U φ ψ, wk_eq φ ψ -> gunit_wk U φ = gunit_wk U ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_wk_wk_eq)))). Qed.
Corollary moddef_wk_wk_eq : forall D φ ψ, wk_eq φ ψ -> moddef_wk D φ = moddef_wk D ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_eq))))). Qed.
Corollary gmod_wk_wk_eq : forall Φ φ ψ, wk_eq φ ψ -> gmod_wk Φ φ = gmod_wk Φ ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_eq)))))). Qed.
Corollary bcheck_wk_wk_eq : forall c φ ψ, wk_eq φ ψ -> bcheck_wk c φ = bcheck_wk c ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_eq))))))). Qed.
Corollary gentry_wk_wk_eq : forall E φ ψ, wk_eq φ ψ -> gentry_wk E φ = gentry_wk E ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_eq)))))))). Qed.
Corollary centry_wk_wk_eq : forall e φ ψ, wk_eq φ ψ -> centry_wk e φ = centry_wk e ψ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_eq)))))))). Qed.

Lemma sentry_wk_wk_eq : forall e φ ψ, wk_eq φ ψ -> sentry_wk e φ = sentry_wk e ψ.
Proof. intros [] * Heq; simpl; f_equal; auto using exp_wk_wk_eq, modexp_wk_wk_eq. Qed.

Lemma tele_wk_wk_eq : forall Δ φ ψ, wk_eq φ ψ -> tele_wk Δ φ = tele_wk Δ ψ.
Proof. induction Δ; intros; simpl; f_equal; auto using centry_wk_wk_eq, wk_qn_cong. Qed.

#[export]
Instance exp_wk_Proper : Proper (eq ==> wk_eq ==> eq) exp_wk.
Proof. intros M M' <- ? ? ?; now apply exp_wk_wk_eq. Qed.

#[export]
Instance modexp_wk_Proper : Proper (eq ==> wk_eq ==> eq) modexp_wk.
Proof. intros M M' <- ? ? ?; now apply modexp_wk_wk_eq. Qed.

#[export]
Instance gunit_wk_Proper : Proper (eq ==> wk_eq ==> eq) gunit_wk.
Proof. intros M M' <- ? ? ?; now apply gunit_wk_wk_eq. Qed.

#[export]
Instance wk_qn_Proper n : Proper (wk_eq ==> wk_eq) (wk_qn n).
Proof. intros ? ? ?; now apply wk_qn_cong. Qed.

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

Lemma wk_qn_id_ext : forall n φ, wk_eq φ wk_id -> wk_eq (wk_qn n φ) wk_id.
Proof. induction n; intros; simpl; auto using wk_q_id_ext. Qed.

Lemma syn_wk_id_ext :
  (forall M φ, wk_eq φ wk_id -> exp_wk M φ = M) /\
  (forall H φ, wk_eq φ wk_id -> modexp_wk H φ = H) /\
  (forall b φ, wk_eq φ wk_id -> bnd_wk b φ = b) /\
  (forall U φ, wk_eq φ wk_id -> gunit_wk U φ = U) /\
  (forall D φ, wk_eq φ wk_id -> moddef_wk D φ = D) /\
  (forall Φ φ, wk_eq φ wk_id -> gmod_wk Φ φ = Φ) /\
  (forall c φ, wk_eq φ wk_id -> bcheck_wk c φ = c) /\
  (forall E φ, wk_eq φ wk_id -> gentry_wk E φ = E) /\
  (forall e φ, wk_eq φ wk_id -> centry_wk e φ = e).
Proof. syn_mut_ind; syn_ext_case wk_q_id_ext wk_qn_id_ext. Qed.

Corollary exp_wk_id_ext : forall M φ, wk_eq φ wk_id -> exp_wk M φ = M.
Proof. exact (proj1 syn_wk_id_ext). Qed.
Corollary modexp_wk_id_ext : forall H φ, wk_eq φ wk_id -> modexp_wk H φ = H.
Proof. exact (proj1 (proj2 syn_wk_id_ext)). Qed.
Corollary bnd_wk_id_ext : forall b φ, wk_eq φ wk_id -> bnd_wk b φ = b.
Proof. exact (proj1 (proj2 (proj2 syn_wk_id_ext))). Qed.
Corollary gunit_wk_id_ext : forall U φ, wk_eq φ wk_id -> gunit_wk U φ = U.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_wk_id_ext)))). Qed.
Corollary moddef_wk_id_ext : forall D φ, wk_eq φ wk_id -> moddef_wk D φ = D.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_wk_id_ext))))). Qed.
Corollary gmod_wk_id_ext : forall Φ φ, wk_eq φ wk_id -> gmod_wk Φ φ = Φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_id_ext)))))). Qed.
Corollary bcheck_wk_id_ext : forall c φ, wk_eq φ wk_id -> bcheck_wk c φ = c.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_id_ext))))))). Qed.
Corollary gentry_wk_id_ext : forall E φ, wk_eq φ wk_id -> gentry_wk E φ = E.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_id_ext)))))))). Qed.
Corollary centry_wk_id_ext : forall e φ, wk_eq φ wk_id -> centry_wk e φ = e.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_id_ext)))))))). Qed.

Corollary exp_wk_id : forall M, exp_wk M wk_id = M.
Proof. intros; now apply exp_wk_id_ext. Qed.
Corollary modexp_wk_id : forall H, modexp_wk H wk_id = H.
Proof. intros; now apply modexp_wk_id_ext. Qed.
Corollary bnd_wk_id : forall b, bnd_wk b wk_id = b.
Proof. intros; now apply bnd_wk_id_ext. Qed.
Corollary gunit_wk_id : forall U, gunit_wk U wk_id = U.
Proof. intros; now apply gunit_wk_id_ext. Qed.
Corollary moddef_wk_id : forall D, moddef_wk D wk_id = D.
Proof. intros; now apply moddef_wk_id_ext. Qed.
Corollary gmod_wk_id : forall Φ, gmod_wk Φ wk_id = Φ.
Proof. intros; now apply gmod_wk_id_ext. Qed.
Corollary bcheck_wk_id : forall c, bcheck_wk c wk_id = c.
Proof. intros; now apply bcheck_wk_id_ext. Qed.
Corollary gentry_wk_id : forall E, gentry_wk E wk_id = E.
Proof. intros; now apply gentry_wk_id_ext. Qed.
Corollary centry_wk_id : forall e, centry_wk e wk_id = e.
Proof. intros; now apply centry_wk_id_ext. Qed.

Corollary wk_q_id : wk_eq (wk_q wk_id) wk_id.
Proof. now apply wk_q_id_ext. Qed.

(** Weakening application respects composition. *)

Lemma wk_q_compose_ext : forall φ ψ χ,
    wk_eq (φ ⊙ ψ) χ ->
    wk_eq (wk_q φ ⊙ wk_q ψ) (wk_q χ).
Proof. intros * Heq; pointwise_solve. Qed.

Lemma wk_qn_compose_ext : forall n φ ψ χ,
    wk_eq (φ ⊙ ψ) χ ->
    wk_eq (wk_qn n φ ⊙ wk_qn n ψ) (wk_qn n χ).
Proof. induction n; intros; simpl; auto using wk_q_compose_ext. Qed.

Lemma syn_wk_wk_ext :
  (forall M φ ψ χ, wk_eq (φ ⊙ ψ) χ -> exp_wk (exp_wk M φ) ψ = exp_wk M χ) /\
  (forall H φ ψ χ, wk_eq (φ ⊙ ψ) χ -> modexp_wk (modexp_wk H φ) ψ = modexp_wk H χ) /\
  (forall b φ ψ χ, wk_eq (φ ⊙ ψ) χ -> bnd_wk (bnd_wk b φ) ψ = bnd_wk b χ) /\
  (forall U φ ψ χ, wk_eq (φ ⊙ ψ) χ -> gunit_wk (gunit_wk U φ) ψ = gunit_wk U χ) /\
  (forall D φ ψ χ, wk_eq (φ ⊙ ψ) χ -> moddef_wk (moddef_wk D φ) ψ = moddef_wk D χ) /\
  (forall Φ φ ψ χ, wk_eq (φ ⊙ ψ) χ -> gmod_wk (gmod_wk Φ φ) ψ = gmod_wk Φ χ) /\
  (forall c φ ψ χ, wk_eq (φ ⊙ ψ) χ -> bcheck_wk (bcheck_wk c φ) ψ = bcheck_wk c χ) /\
  (forall E φ ψ χ, wk_eq (φ ⊙ ψ) χ -> gentry_wk (gentry_wk E φ) ψ = gentry_wk E χ) /\
  (forall e φ ψ χ, wk_eq (φ ⊙ ψ) χ -> centry_wk (centry_wk e φ) ψ = centry_wk e χ).
Proof. syn_mut_ind; syn_ext_case wk_q_compose_ext wk_qn_compose_ext. Qed.

Corollary exp_wk_wk_ext : forall M φ ψ χ, wk_eq (φ ⊙ ψ) χ -> exp_wk (exp_wk M φ) ψ = exp_wk M χ.
Proof. exact (proj1 syn_wk_wk_ext). Qed.
Corollary modexp_wk_wk_ext : forall H φ ψ χ, wk_eq (φ ⊙ ψ) χ -> modexp_wk (modexp_wk H φ) ψ = modexp_wk H χ.
Proof. exact (proj1 (proj2 syn_wk_wk_ext)). Qed.
Corollary bnd_wk_wk_ext : forall b φ ψ χ, wk_eq (φ ⊙ ψ) χ -> bnd_wk (bnd_wk b φ) ψ = bnd_wk b χ.
Proof. exact (proj1 (proj2 (proj2 syn_wk_wk_ext))). Qed.
Corollary gunit_wk_wk_ext : forall U φ ψ χ, wk_eq (φ ⊙ ψ) χ -> gunit_wk (gunit_wk U φ) ψ = gunit_wk U χ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_wk_wk_ext)))). Qed.
Corollary moddef_wk_wk_ext : forall D φ ψ χ, wk_eq (φ ⊙ ψ) χ -> moddef_wk (moddef_wk D φ) ψ = moddef_wk D χ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_ext))))). Qed.
Corollary gmod_wk_wk_ext : forall Φ φ ψ χ, wk_eq (φ ⊙ ψ) χ -> gmod_wk (gmod_wk Φ φ) ψ = gmod_wk Φ χ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_ext)))))). Qed.
Corollary bcheck_wk_wk_ext : forall c φ ψ χ, wk_eq (φ ⊙ ψ) χ -> bcheck_wk (bcheck_wk c φ) ψ = bcheck_wk c χ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_ext))))))). Qed.
Corollary gentry_wk_wk_ext : forall E φ ψ χ, wk_eq (φ ⊙ ψ) χ -> gentry_wk (gentry_wk E φ) ψ = gentry_wk E χ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_ext)))))))). Qed.
Corollary centry_wk_wk_ext : forall e φ ψ χ, wk_eq (φ ⊙ ψ) χ -> centry_wk (centry_wk e φ) ψ = centry_wk e χ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_wk_ext)))))))). Qed.

Corollary exp_wk_wk : forall M φ ψ, exp_wk (exp_wk M φ) ψ = exp_wk M (φ ⊙ ψ).
Proof. intros; now apply exp_wk_wk_ext. Qed.
Corollary modexp_wk_wk : forall H φ ψ, modexp_wk (modexp_wk H φ) ψ = modexp_wk H (φ ⊙ ψ).
Proof. intros; now apply modexp_wk_wk_ext. Qed.
Corollary bnd_wk_wk : forall b φ ψ, bnd_wk (bnd_wk b φ) ψ = bnd_wk b (φ ⊙ ψ).
Proof. intros; now apply bnd_wk_wk_ext. Qed.
Corollary gunit_wk_wk : forall U φ ψ, gunit_wk (gunit_wk U φ) ψ = gunit_wk U (φ ⊙ ψ).
Proof. intros; now apply gunit_wk_wk_ext. Qed.
Corollary moddef_wk_wk : forall D φ ψ, moddef_wk (moddef_wk D φ) ψ = moddef_wk D (φ ⊙ ψ).
Proof. intros; now apply moddef_wk_wk_ext. Qed.
Corollary gmod_wk_wk : forall Φ φ ψ, gmod_wk (gmod_wk Φ φ) ψ = gmod_wk Φ (φ ⊙ ψ).
Proof. intros; now apply gmod_wk_wk_ext. Qed.
Corollary bcheck_wk_wk : forall c φ ψ, bcheck_wk (bcheck_wk c φ) ψ = bcheck_wk c (φ ⊙ ψ).
Proof. intros; now apply bcheck_wk_wk_ext. Qed.
Corollary gentry_wk_wk : forall E φ ψ, gentry_wk (gentry_wk E φ) ψ = gentry_wk E (φ ⊙ ψ).
Proof. intros; now apply gentry_wk_wk_ext. Qed.
Corollary centry_wk_wk : forall e φ ψ, centry_wk (centry_wk e φ) ψ = centry_wk e (φ ⊙ ψ).
Proof. intros; now apply centry_wk_wk_ext. Qed.

Corollary wk_q_compose : forall φ ψ, wk_eq (wk_q φ ⊙ wk_q ψ) (wk_q (φ ⊙ ψ)).
Proof. intros; now apply wk_q_compose_ext. Qed.

Lemma wk_qn_compose : forall n φ ψ,
    wk_eq (wk_qn n φ ⊙ wk_qn n ψ) (wk_qn n (φ ⊙ ψ)).
Proof. intros; now apply wk_qn_compose_ext. Qed.

Lemma sentry_wk_wk : forall e φ ψ, sentry_wk (sentry_wk e φ) ψ = sentry_wk e (φ ⊙ ψ).
Proof. intros [] * ; simpl; f_equal; auto using exp_wk_wk, modexp_wk_wk. Qed.

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
(** ** Substitutions *)

Lemma sb_wk_cong : forall σ τ φ φ',
    sb_eq σ τ -> wk_eq φ φ' -> sb_eq (sb_wk σ φ) (sb_wk τ φ').
Proof.
  intros * Heq Heq' x; simpl.
  rewrite Heq; now apply sentry_wk_wk_eq.
Qed.

Lemma sb_q_cong : forall σ τ, sb_eq σ τ -> sb_eq (sb_q σ) (sb_q τ).
Proof. intros * Heq; pointwise; [ reflexivity | now rewrite Heq ]. Qed.

Lemma sb_qn_cong : forall n σ τ, sb_eq σ τ -> sb_eq (sb_qn n σ) (sb_qn n τ).
Proof. induction n; intros; simpl; auto using sb_q_cong. Qed.

Lemma syn_sub_sb_eq :
  (forall M σ τ, sb_eq σ τ -> exp_sub M σ = exp_sub M τ) /\
  (forall H σ τ, sb_eq σ τ -> modexp_sub H σ = modexp_sub H τ) /\
  (forall b σ τ, sb_eq σ τ -> bnd_sub b σ = bnd_sub b τ) /\
  (forall U σ τ, sb_eq σ τ -> gunit_sub U σ = gunit_sub U τ) /\
  (forall D σ τ, sb_eq σ τ -> moddef_sub D σ = moddef_sub D τ) /\
  (forall Φ σ τ, sb_eq σ τ -> gmod_sub Φ σ = gmod_sub Φ τ) /\
  (forall c σ τ, sb_eq σ τ -> bcheck_sub c σ = bcheck_sub c τ) /\
  (forall E σ τ, sb_eq σ τ -> gentry_sub E σ = gentry_sub E τ) /\
  (forall e σ τ, sb_eq σ τ -> centry_sub e σ = centry_sub e τ).
Proof. syn_mut_ind; syn_ext_case sb_q_cong sb_qn_cong. Qed.

Corollary exp_sub_sb_eq : forall M σ τ, sb_eq σ τ -> exp_sub M σ = exp_sub M τ.
Proof. exact (proj1 syn_sub_sb_eq). Qed.
Corollary modexp_sub_sb_eq : forall H σ τ, sb_eq σ τ -> modexp_sub H σ = modexp_sub H τ.
Proof. exact (proj1 (proj2 syn_sub_sb_eq)). Qed.
Corollary bnd_sub_sb_eq : forall b σ τ, sb_eq σ τ -> bnd_sub b σ = bnd_sub b τ.
Proof. exact (proj1 (proj2 (proj2 syn_sub_sb_eq))). Qed.
Corollary gunit_sub_sb_eq : forall U σ τ, sb_eq σ τ -> gunit_sub U σ = gunit_sub U τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_sub_sb_eq)))). Qed.
Corollary moddef_sub_sb_eq : forall D σ τ, sb_eq σ τ -> moddef_sub D σ = moddef_sub D τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_sub_sb_eq))))). Qed.
Corollary gmod_sub_sb_eq : forall Φ σ τ, sb_eq σ τ -> gmod_sub Φ σ = gmod_sub Φ τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sb_eq)))))). Qed.
Corollary bcheck_sub_sb_eq : forall c σ τ, sb_eq σ τ -> bcheck_sub c σ = bcheck_sub c τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sb_eq))))))). Qed.
Corollary gentry_sub_sb_eq : forall E σ τ, sb_eq σ τ -> gentry_sub E σ = gentry_sub E τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sb_eq)))))))). Qed.
Corollary centry_sub_sb_eq : forall e σ τ, sb_eq σ τ -> centry_sub e σ = centry_sub e τ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sb_eq)))))))). Qed.

Lemma sentry_sub_sb_eq : forall e σ τ, sb_eq σ τ -> sentry_sub e σ = sentry_sub e τ.
Proof. intros [] * Heq; simpl; f_equal; auto using exp_sub_sb_eq, modexp_sub_sb_eq. Qed.

Lemma tele_sub_sb_eq : forall Δ σ τ, sb_eq σ τ -> tele_sub Δ σ = tele_sub Δ τ.
Proof. induction Δ; intros; simpl; f_equal; auto using centry_sub_sb_eq, sb_qn_cong. Qed.

Lemma sb_extend_cong : forall σ τ e,
    sb_eq σ τ -> sb_eq (sb_extend σ e) (sb_extend τ e).
Proof. intros * Heq; pointwise_solve. Qed.

Lemma sb_of_wk_cong : forall φ ψ, wk_eq φ ψ -> sb_eq (ι φ) (ι ψ).
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
Proof. intros ? ? ? ? ? <-; now apply sb_extend_cong. Qed.

#[export]
Instance exp_sub_Proper : Proper (eq ==> sb_eq ==> eq) exp_sub.
Proof. intros ? ? <- ? ? ?; now apply exp_sub_sb_eq. Qed.

#[export]
Instance modexp_sub_Proper : Proper (eq ==> sb_eq ==> eq) modexp_sub.
Proof. intros ? ? <- ? ? ?; now apply modexp_sub_sb_eq. Qed.

#[export]
Instance gunit_sub_Proper : Proper (eq ==> sb_eq ==> eq) gunit_sub.
Proof. intros ? ? <- ? ? ?; now apply gunit_sub_sb_eq. Qed.

#[export]
Instance sb_qn_Proper n : Proper (sb_eq ==> sb_eq) (sb_qn n).
Proof. intros ? ? ?; now apply sb_qn_cong. Qed.

#[export]
Instance sb_compose_Proper : Proper (sb_eq ==> sb_eq ==> sb_eq) sb_compose.
Proof.
  intros σ σ' Hσ τ τ' Hτ x; simpl.
  rewrite Hσ; now apply sentry_sub_sb_eq.
Qed.

(** The embedding [ι] of weakenings into
    substitutions is faithful, and preserves every operation.  From here on the
    development may treat a weakening as a substitution. *)

Lemma sb_q_of_wk_ext : forall φ σ,
    sb_eq (ι φ) σ ->
    sb_eq (ι (wk_q φ)) (q σ).
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite <- Heq; reduce_index; reflexivity.
Qed.

Lemma sb_qn_of_wk_ext : forall n φ σ,
    sb_eq (ι φ) σ ->
    sb_eq (ι (wk_qn n φ)) (sb_qn n σ).
Proof. induction n; intros; simpl; auto using sb_q_of_wk_ext. Qed.

Lemma syn_sub_of_wk_ext :
  (forall M φ σ, sb_eq (ι φ) σ -> exp_sub M σ = exp_wk M φ) /\
  (forall H φ σ, sb_eq (ι φ) σ -> modexp_sub H σ = modexp_wk H φ) /\
  (forall b φ σ, sb_eq (ι φ) σ -> bnd_sub b σ = bnd_wk b φ) /\
  (forall U φ σ, sb_eq (ι φ) σ -> gunit_sub U σ = gunit_wk U φ) /\
  (forall D φ σ, sb_eq (ι φ) σ -> moddef_sub D σ = moddef_wk D φ) /\
  (forall Φ φ σ, sb_eq (ι φ) σ -> gmod_sub Φ σ = gmod_wk Φ φ) /\
  (forall c φ σ, sb_eq (ι φ) σ -> bcheck_sub c σ = bcheck_wk c φ) /\
  (forall E φ σ, sb_eq (ι φ) σ -> gentry_sub E σ = gentry_wk E φ) /\
  (forall e φ σ, sb_eq (ι φ) σ -> centry_sub e σ = centry_wk e φ).
Proof. syn_mut_ind; syn_ext_case sb_q_of_wk_ext sb_qn_of_wk_ext. Qed.

Corollary exp_sub_of_wk_ext : forall M φ σ, sb_eq (ι φ) σ -> exp_sub M σ = exp_wk M φ.
Proof. exact (proj1 syn_sub_of_wk_ext). Qed.
Corollary modexp_sub_of_wk_ext : forall H φ σ, sb_eq (ι φ) σ -> modexp_sub H σ = modexp_wk H φ.
Proof. exact (proj1 (proj2 syn_sub_of_wk_ext)). Qed.
Corollary bnd_sub_of_wk_ext : forall b φ σ, sb_eq (ι φ) σ -> bnd_sub b σ = bnd_wk b φ.
Proof. exact (proj1 (proj2 (proj2 syn_sub_of_wk_ext))). Qed.
Corollary gunit_sub_of_wk_ext : forall U φ σ, sb_eq (ι φ) σ -> gunit_sub U σ = gunit_wk U φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_sub_of_wk_ext)))). Qed.
Corollary moddef_sub_of_wk_ext : forall D φ σ, sb_eq (ι φ) σ -> moddef_sub D σ = moddef_wk D φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_sub_of_wk_ext))))). Qed.
Corollary gmod_sub_of_wk_ext : forall Φ φ σ, sb_eq (ι φ) σ -> gmod_sub Φ σ = gmod_wk Φ φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_of_wk_ext)))))). Qed.
Corollary bcheck_sub_of_wk_ext : forall c φ σ, sb_eq (ι φ) σ -> bcheck_sub c σ = bcheck_wk c φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_of_wk_ext))))))). Qed.
Corollary gentry_sub_of_wk_ext : forall E φ σ, sb_eq (ι φ) σ -> gentry_sub E σ = gentry_wk E φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_of_wk_ext)))))))). Qed.
Corollary centry_sub_of_wk_ext : forall e φ σ, sb_eq (ι φ) σ -> centry_sub e σ = centry_wk e φ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_of_wk_ext)))))))). Qed.

Corollary exp_sub_of_wk : forall M φ, exp_sub M (ι φ) = exp_wk M φ.
Proof. intros; now apply exp_sub_of_wk_ext. Qed.
Corollary modexp_sub_of_wk : forall H φ, modexp_sub H (ι φ) = modexp_wk H φ.
Proof. intros; now apply modexp_sub_of_wk_ext. Qed.
Corollary bnd_sub_of_wk : forall b φ, bnd_sub b (ι φ) = bnd_wk b φ.
Proof. intros; now apply bnd_sub_of_wk_ext. Qed.
Corollary gunit_sub_of_wk : forall U φ, gunit_sub U (ι φ) = gunit_wk U φ.
Proof. intros; now apply gunit_sub_of_wk_ext. Qed.
Corollary moddef_sub_of_wk : forall D φ, moddef_sub D (ι φ) = moddef_wk D φ.
Proof. intros; now apply moddef_sub_of_wk_ext. Qed.
Corollary gmod_sub_of_wk : forall Φ φ, gmod_sub Φ (ι φ) = gmod_wk Φ φ.
Proof. intros; now apply gmod_sub_of_wk_ext. Qed.
Corollary bcheck_sub_of_wk : forall c φ, bcheck_sub c (ι φ) = bcheck_wk c φ.
Proof. intros; now apply bcheck_sub_of_wk_ext. Qed.
Corollary gentry_sub_of_wk : forall E φ, gentry_sub E (ι φ) = gentry_wk E φ.
Proof. intros; now apply gentry_sub_of_wk_ext. Qed.
Corollary centry_sub_of_wk : forall e φ, centry_sub e (ι φ) = centry_wk e φ.
Proof. intros; now apply centry_sub_of_wk_ext. Qed.

Corollary sb_q_of_wk : forall φ, sb_eq (ι (wk_q φ)) (q (ι φ)).
Proof. intros; now apply sb_q_of_wk_ext. Qed.

Lemma sb_of_wk_id : sb_eq (ι wk_id) Id.
Proof. pointwise_solve. Qed.

Lemma sb_of_wk_shift : sb_eq (ι wk_shift) Wk.
Proof. pointwise_solve. Qed.

Lemma sb_of_wk_compose : forall φ ψ,
    sb_eq (ι (φ ⊙ ψ)) ((ι φ) ⨟ (ι ψ)).
Proof. intros *; pointwise_solve. Qed.

(** The identity substitution. *)

Lemma sb_q_id_ext : forall σ, sb_eq σ Id -> sb_eq (q σ) Id.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite Heq; reduce_index; reflexivity.
Qed.

Lemma sb_qn_id_ext : forall n σ, sb_eq σ Id -> sb_eq (sb_qn n σ) Id.
Proof. induction n; intros; simpl; auto using sb_q_id_ext. Qed.

Lemma syn_sub_id_ext :
  (forall M σ, sb_eq σ Id -> exp_sub M σ = M) /\
  (forall H σ, sb_eq σ Id -> modexp_sub H σ = H) /\
  (forall b σ, sb_eq σ Id -> bnd_sub b σ = b) /\
  (forall U σ, sb_eq σ Id -> gunit_sub U σ = U) /\
  (forall D σ, sb_eq σ Id -> moddef_sub D σ = D) /\
  (forall Φ σ, sb_eq σ Id -> gmod_sub Φ σ = Φ) /\
  (forall c σ, sb_eq σ Id -> bcheck_sub c σ = c) /\
  (forall E σ, sb_eq σ Id -> gentry_sub E σ = E) /\
  (forall e σ, sb_eq σ Id -> centry_sub e σ = e).
Proof. syn_mut_ind; syn_ext_case sb_q_id_ext sb_qn_id_ext. Qed.

Corollary exp_sub_id_ext : forall M σ, sb_eq σ Id -> exp_sub M σ = M.
Proof. exact (proj1 syn_sub_id_ext). Qed.
Corollary modexp_sub_id_ext : forall H σ, sb_eq σ Id -> modexp_sub H σ = H.
Proof. exact (proj1 (proj2 syn_sub_id_ext)). Qed.
Corollary bnd_sub_id_ext : forall b σ, sb_eq σ Id -> bnd_sub b σ = b.
Proof. exact (proj1 (proj2 (proj2 syn_sub_id_ext))). Qed.
Corollary gunit_sub_id_ext : forall U σ, sb_eq σ Id -> gunit_sub U σ = U.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_sub_id_ext)))). Qed.
Corollary moddef_sub_id_ext : forall D σ, sb_eq σ Id -> moddef_sub D σ = D.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_sub_id_ext))))). Qed.
Corollary gmod_sub_id_ext : forall Φ σ, sb_eq σ Id -> gmod_sub Φ σ = Φ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_id_ext)))))). Qed.
Corollary bcheck_sub_id_ext : forall c σ, sb_eq σ Id -> bcheck_sub c σ = c.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_id_ext))))))). Qed.
Corollary gentry_sub_id_ext : forall E σ, sb_eq σ Id -> gentry_sub E σ = E.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_id_ext)))))))). Qed.
Corollary centry_sub_id_ext : forall e σ, sb_eq σ Id -> centry_sub e σ = e.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_id_ext)))))))). Qed.

Corollary exp_sub_id : forall M, exp_sub M Id = M.
Proof. intros; now apply exp_sub_id_ext. Qed.
Corollary modexp_sub_id : forall H, modexp_sub H Id = H.
Proof. intros; now apply modexp_sub_id_ext. Qed.
Corollary bnd_sub_id : forall b, bnd_sub b Id = b.
Proof. intros; now apply bnd_sub_id_ext. Qed.
Corollary gunit_sub_id : forall U, gunit_sub U Id = U.
Proof. intros; now apply gunit_sub_id_ext. Qed.
Corollary moddef_sub_id : forall D, moddef_sub D Id = D.
Proof. intros; now apply moddef_sub_id_ext. Qed.
Corollary gmod_sub_id : forall Φ, gmod_sub Φ Id = Φ.
Proof. intros; now apply gmod_sub_id_ext. Qed.
Corollary bcheck_sub_id : forall c, bcheck_sub c Id = c.
Proof. intros; now apply bcheck_sub_id_ext. Qed.
Corollary gentry_sub_id : forall E, gentry_sub E Id = E.
Proof. intros; now apply gentry_sub_id_ext. Qed.
Corollary centry_sub_id : forall e, centry_sub e Id = e.
Proof. intros; now apply centry_sub_id_ext. Qed.

Corollary sb_q_id : sb_eq (q Id) Id.
Proof. now apply sb_q_id_ext. Qed.

Lemma sentry_sub_id : forall e, sentry_sub e Id = e.
Proof. intros []; simpl; f_equal; auto using exp_sub_id, modexp_sub_id. Qed.

Lemma tele_sub_id : forall Δ, tele_sub Δ Id = Δ.
Proof. induction Δ; simpl; f_equal; auto; apply centry_sub_id_ext, sb_qn_id_ext; reflexivity. Qed.

(** Postcomposing with a weakening. *)

Lemma sb_q_wk_ext : forall σ φ τ,
    sb_eq (sb_wk σ φ) τ ->
    sb_eq (sb_wk (q σ) (wk_q φ)) (q τ).
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite <- Heq; reduce_index.
  do 2 rewrite sentry_wk_wk.
  apply sentry_wk_wk_eq; pointwise_solve.
Qed.

Lemma sb_qn_wk_ext : forall n σ φ τ,
    sb_eq (sb_wk σ φ) τ ->
    sb_eq (sb_wk (sb_qn n σ) (wk_qn n φ)) (sb_qn n τ).
Proof. induction n; intros; simpl; auto using sb_q_wk_ext. Qed.

Lemma syn_wk_sub_ext :
  (forall M σ φ τ, sb_eq (sb_wk σ φ) τ -> exp_wk (exp_sub M σ) φ = exp_sub M τ) /\
  (forall H σ φ τ, sb_eq (sb_wk σ φ) τ -> modexp_wk (modexp_sub H σ) φ = modexp_sub H τ) /\
  (forall b σ φ τ, sb_eq (sb_wk σ φ) τ -> bnd_wk (bnd_sub b σ) φ = bnd_sub b τ) /\
  (forall U σ φ τ, sb_eq (sb_wk σ φ) τ -> gunit_wk (gunit_sub U σ) φ = gunit_sub U τ) /\
  (forall D σ φ τ, sb_eq (sb_wk σ φ) τ -> moddef_wk (moddef_sub D σ) φ = moddef_sub D τ) /\
  (forall Φ σ φ τ, sb_eq (sb_wk σ φ) τ -> gmod_wk (gmod_sub Φ σ) φ = gmod_sub Φ τ) /\
  (forall c σ φ τ, sb_eq (sb_wk σ φ) τ -> bcheck_wk (bcheck_sub c σ) φ = bcheck_sub c τ) /\
  (forall E σ φ τ, sb_eq (sb_wk σ φ) τ -> gentry_wk (gentry_sub E σ) φ = gentry_sub E τ) /\
  (forall e σ φ τ, sb_eq (sb_wk σ φ) τ -> centry_wk (centry_sub e σ) φ = centry_sub e τ).
Proof. syn_mut_ind; syn_ext_case sb_q_wk_ext sb_qn_wk_ext. Qed.

Corollary exp_wk_sub_ext : forall M σ φ τ, sb_eq (sb_wk σ φ) τ -> exp_wk (exp_sub M σ) φ = exp_sub M τ.
Proof. exact (proj1 syn_wk_sub_ext). Qed.
Corollary modexp_wk_sub_ext : forall H σ φ τ, sb_eq (sb_wk σ φ) τ -> modexp_wk (modexp_sub H σ) φ = modexp_sub H τ.
Proof. exact (proj1 (proj2 syn_wk_sub_ext)). Qed.
Corollary bnd_wk_sub_ext : forall b σ φ τ, sb_eq (sb_wk σ φ) τ -> bnd_wk (bnd_sub b σ) φ = bnd_sub b τ.
Proof. exact (proj1 (proj2 (proj2 syn_wk_sub_ext))). Qed.
Corollary gunit_wk_sub_ext : forall U σ φ τ, sb_eq (sb_wk σ φ) τ -> gunit_wk (gunit_sub U σ) φ = gunit_sub U τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_wk_sub_ext)))). Qed.
Corollary moddef_wk_sub_ext : forall D σ φ τ, sb_eq (sb_wk σ φ) τ -> moddef_wk (moddef_sub D σ) φ = moddef_sub D τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_ext))))). Qed.
Corollary gmod_wk_sub_ext : forall Φ σ φ τ, sb_eq (sb_wk σ φ) τ -> gmod_wk (gmod_sub Φ σ) φ = gmod_sub Φ τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_ext)))))). Qed.
Corollary bcheck_wk_sub_ext : forall c σ φ τ, sb_eq (sb_wk σ φ) τ -> bcheck_wk (bcheck_sub c σ) φ = bcheck_sub c τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_ext))))))). Qed.
Corollary gentry_wk_sub_ext : forall E σ φ τ, sb_eq (sb_wk σ φ) τ -> gentry_wk (gentry_sub E σ) φ = gentry_sub E τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_ext)))))))). Qed.
Corollary centry_wk_sub_ext : forall e σ φ τ, sb_eq (sb_wk σ φ) τ -> centry_wk (centry_sub e σ) φ = centry_sub e τ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_ext)))))))). Qed.

Corollary exp_wk_sub : forall M σ φ, exp_wk (exp_sub M σ) φ = exp_sub M (sb_wk σ φ).
Proof. intros; now apply exp_wk_sub_ext. Qed.
Corollary modexp_wk_sub : forall H σ φ, modexp_wk (modexp_sub H σ) φ = modexp_sub H (sb_wk σ φ).
Proof. intros; now apply modexp_wk_sub_ext. Qed.
Corollary bnd_wk_sub : forall b σ φ, bnd_wk (bnd_sub b σ) φ = bnd_sub b (sb_wk σ φ).
Proof. intros; now apply bnd_wk_sub_ext. Qed.
Corollary gunit_wk_sub : forall U σ φ, gunit_wk (gunit_sub U σ) φ = gunit_sub U (sb_wk σ φ).
Proof. intros; now apply gunit_wk_sub_ext. Qed.
Corollary moddef_wk_sub : forall D σ φ, moddef_wk (moddef_sub D σ) φ = moddef_sub D (sb_wk σ φ).
Proof. intros; now apply moddef_wk_sub_ext. Qed.
Corollary gmod_wk_sub : forall Φ σ φ, gmod_wk (gmod_sub Φ σ) φ = gmod_sub Φ (sb_wk σ φ).
Proof. intros; now apply gmod_wk_sub_ext. Qed.
Corollary bcheck_wk_sub : forall c σ φ, bcheck_wk (bcheck_sub c σ) φ = bcheck_sub c (sb_wk σ φ).
Proof. intros; now apply bcheck_wk_sub_ext. Qed.
Corollary gentry_wk_sub : forall E σ φ, gentry_wk (gentry_sub E σ) φ = gentry_sub E (sb_wk σ φ).
Proof. intros; now apply gentry_wk_sub_ext. Qed.
Corollary centry_wk_sub : forall e σ φ, centry_wk (centry_sub e σ) φ = centry_sub e (sb_wk σ φ).
Proof. intros; now apply centry_wk_sub_ext. Qed.

Lemma sentry_wk_sub : forall e σ φ, sentry_wk (sentry_sub e σ) φ = sentry_sub e (sb_wk σ φ).
Proof. intros [] * ; simpl; f_equal; auto using exp_wk_sub, modexp_wk_sub. Qed.

Corollary sb_q_wk : forall σ φ,
    sb_eq (sb_wk (q σ) (wk_q φ)) (q (sb_wk σ φ)).
Proof. intros; now apply sb_q_wk_ext. Qed.

(** The two instances a Kripke weakening of a [natrec] produces: its motive sits
    under [q] and its scrutinee's type under an extension. *)
Corollary exp_wk_sub_q : forall M σ φ,
    M[q σ][wk_q φ]ʷ = M[q (sb_wk σ φ)].
Proof. intros; apply exp_wk_sub_ext, sb_q_wk. Qed.

Corollary exp_wk_sub_extend_head : forall M σ N φ,
    M[σ,,N][φ]ʷ = M[(sb_wk σ φ),,N[φ]ʷ].
Proof. intros; apply exp_wk_sub_ext; intros [| y]; reflexivity. Qed.

(** The successor branch sits under two [q]s. *)
Corollary sb_q_wk2 : forall σ φ,
    sb_eq (sb_wk (q (q σ)) (wk_q (wk_q φ))) (q (q (sb_wk σ φ))).
Proof. intros; rewrite sb_q_wk, sb_q_wk; reflexivity. Qed.

Corollary exp_wk_sub_q2 : forall M σ φ,
    M[q (q σ)][wk_q (wk_q φ)]ʷ = M[q (q (sb_wk σ φ))].
Proof. intros; apply exp_wk_sub_ext, sb_q_wk2. Qed.

(** Precomposing with a weakening. *)

Lemma sb_q_wk_pre_ext : forall φ σ τ,
    (forall x, σ (φ x) = τ x) ->
    forall x, (q σ) (wk_q φ x) = (q τ) x.
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  now rewrite Heq.
Qed.

Lemma sb_qn_wk_pre_ext : forall n φ σ τ,
    (forall x, σ (φ x) = τ x) ->
    forall x, (sb_qn n σ) (wk_qn n φ x) = (sb_qn n τ) x.
Proof. induction n; intros * Heq; simpl; [ exact Heq | apply sb_q_wk_pre_ext; apply IHn; exact Heq ]. Qed.

Lemma syn_sub_wk_ext :
  (forall M φ σ τ, (forall x, σ (φ x) = τ x) -> exp_sub (exp_wk M φ) σ = exp_sub M τ) /\
  (forall H φ σ τ, (forall x, σ (φ x) = τ x) -> modexp_sub (modexp_wk H φ) σ = modexp_sub H τ) /\
  (forall b φ σ τ, (forall x, σ (φ x) = τ x) -> bnd_sub (bnd_wk b φ) σ = bnd_sub b τ) /\
  (forall U φ σ τ, (forall x, σ (φ x) = τ x) -> gunit_sub (gunit_wk U φ) σ = gunit_sub U τ) /\
  (forall D φ σ τ, (forall x, σ (φ x) = τ x) -> moddef_sub (moddef_wk D φ) σ = moddef_sub D τ) /\
  (forall Φ φ σ τ, (forall x, σ (φ x) = τ x) -> gmod_sub (gmod_wk Φ φ) σ = gmod_sub Φ τ) /\
  (forall c φ σ τ, (forall x, σ (φ x) = τ x) -> bcheck_sub (bcheck_wk c φ) σ = bcheck_sub c τ) /\
  (forall E φ σ τ, (forall x, σ (φ x) = τ x) -> gentry_sub (gentry_wk E φ) σ = gentry_sub E τ) /\
  (forall e φ σ τ, (forall x, σ (φ x) = τ x) -> centry_sub (centry_wk e φ) σ = centry_sub e τ).
Proof. syn_mut_ind; syn_ext_case sb_q_wk_pre_ext sb_qn_wk_pre_ext. Qed.

Corollary exp_sub_wk_ext : forall M φ σ τ, (forall x, σ (φ x) = τ x) -> exp_sub (exp_wk M φ) σ = exp_sub M τ.
Proof. exact (proj1 syn_sub_wk_ext). Qed.
Corollary modexp_sub_wk_ext : forall H φ σ τ, (forall x, σ (φ x) = τ x) -> modexp_sub (modexp_wk H φ) σ = modexp_sub H τ.
Proof. exact (proj1 (proj2 syn_sub_wk_ext)). Qed.
Corollary bnd_sub_wk_ext : forall b φ σ τ, (forall x, σ (φ x) = τ x) -> bnd_sub (bnd_wk b φ) σ = bnd_sub b τ.
Proof. exact (proj1 (proj2 (proj2 syn_sub_wk_ext))). Qed.
Corollary gunit_sub_wk_ext : forall U φ σ τ, (forall x, σ (φ x) = τ x) -> gunit_sub (gunit_wk U φ) σ = gunit_sub U τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_sub_wk_ext)))). Qed.
Corollary moddef_sub_wk_ext : forall D φ σ τ, (forall x, σ (φ x) = τ x) -> moddef_sub (moddef_wk D φ) σ = moddef_sub D τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_sub_wk_ext))))). Qed.
Corollary gmod_sub_wk_ext : forall Φ φ σ τ, (forall x, σ (φ x) = τ x) -> gmod_sub (gmod_wk Φ φ) σ = gmod_sub Φ τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_wk_ext)))))). Qed.
Corollary bcheck_sub_wk_ext : forall c φ σ τ, (forall x, σ (φ x) = τ x) -> bcheck_sub (bcheck_wk c φ) σ = bcheck_sub c τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_wk_ext))))))). Qed.
Corollary gentry_sub_wk_ext : forall E φ σ τ, (forall x, σ (φ x) = τ x) -> gentry_sub (gentry_wk E φ) σ = gentry_sub E τ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_wk_ext)))))))). Qed.
Corollary centry_sub_wk_ext : forall e φ σ τ, (forall x, σ (φ x) = τ x) -> centry_sub (centry_wk e φ) σ = centry_sub e τ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_wk_ext)))))))). Qed.

Corollary exp_sub_wk : forall M φ σ, exp_sub (exp_wk M φ) σ = exp_sub M ((ι φ) ⨟ σ).
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.
Corollary modexp_sub_wk : forall H φ σ, modexp_sub (modexp_wk H φ) σ = modexp_sub H ((ι φ) ⨟ σ).
Proof. intros; apply modexp_sub_wk_ext; intros; reflexivity. Qed.
Corollary bnd_sub_wk : forall b φ σ, bnd_sub (bnd_wk b φ) σ = bnd_sub b ((ι φ) ⨟ σ).
Proof. intros; apply bnd_sub_wk_ext; intros; reflexivity. Qed.
Corollary gunit_sub_wk : forall U φ σ, gunit_sub (gunit_wk U φ) σ = gunit_sub U ((ι φ) ⨟ σ).
Proof. intros; apply gunit_sub_wk_ext; intros; reflexivity. Qed.
Corollary moddef_sub_wk : forall D φ σ, moddef_sub (moddef_wk D φ) σ = moddef_sub D ((ι φ) ⨟ σ).
Proof. intros; apply moddef_sub_wk_ext; intros; reflexivity. Qed.
Corollary gmod_sub_wk : forall Φ φ σ, gmod_sub (gmod_wk Φ φ) σ = gmod_sub Φ ((ι φ) ⨟ σ).
Proof. intros; apply gmod_sub_wk_ext; intros; reflexivity. Qed.
Corollary bcheck_sub_wk : forall c φ σ, bcheck_sub (bcheck_wk c φ) σ = bcheck_sub c ((ι φ) ⨟ σ).
Proof. intros; apply bcheck_sub_wk_ext; intros; reflexivity. Qed.
Corollary gentry_sub_wk : forall E φ σ, gentry_sub (gentry_wk E φ) σ = gentry_sub E ((ι φ) ⨟ σ).
Proof. intros; apply gentry_sub_wk_ext; intros; reflexivity. Qed.
Corollary centry_sub_wk : forall e φ σ, centry_sub (centry_wk e φ) σ = centry_sub e ((ι φ) ⨟ σ).
Proof. intros; apply centry_sub_wk_ext; intros; reflexivity. Qed.

Lemma sentry_sub_wk : forall e φ σ, sentry_sub (sentry_wk e φ) σ = sentry_sub e ((ι φ) ⨟ σ).
Proof. intros [] * ; simpl; f_equal; auto using exp_sub_wk, modexp_sub_wk. Qed.

(** The two instances at [↑], spelled with [Wk] instead of [ι ↑].  [Wk] is
    [ι ↑] by definition, but [rewrite] matches syntactically, and the semantic
    shift lemmas speak of [Wk]; a context lookup needs these spellings to move
    its [A[↑]ʷ] along a substitution. *)

Corollary exp_sub_shift : forall M σ, M[↑]ʷ[σ] = M[Wk ⨟ σ].
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.

Corollary exp_sub_of_shift : forall M, M[Wk] = M[↑]ʷ.
Proof. intros; apply exp_sub_of_wk_ext, sb_of_wk_shift. Qed.

(** Instantiating the codomain of a weakened [Π]-type.  This is the shape the
    gluing model states its [Π] clauses in: the elimination rule
    produces [OT[q φ]ʷ[Id ,, N]] and the clause speaks of [OT[ι φ ,, N]]. *)
Corollary exp_sub_wk_q_extend : forall M φ N,
    M[wk_q φ]ʷ[Id,,N] = M[(ι φ),,N].
Proof. intros; apply exp_sub_wk_ext; intros [|?]; reflexivity. Qed.

(** The same with the identity replaced by a second weakening: this is what a
    [Π]-clause of the gluing model turns into when it is itself transported along
    a Kripke weakening. *)
Corollary exp_sub_wk_q_extend_wk : forall M φ ψ N,
    M[wk_q φ]ʷ[(ι ψ),,N] = M[(ι (φ ⊙ ψ)),,N].
Proof. intros; apply exp_sub_wk_ext; intros [|?]; reflexivity. Qed.

(** [ι (q φ)] read as an extension by a variable entry.  This is the converse
    direction of the two above, at the canonical variable of an extended
    context. *)
Lemma sb_of_wk_q_extend : forall φ,
    sb_eq (sb_extend (ι (φ ⊙ ↑)) (se_var 0)) (ι (wk_q φ)).
Proof. intros *; pointwise; reflexivity. Qed.

Corollary exp_sub_of_wk_q_extend : forall M φ,
    M[sb_extend (ι (φ ⊙ ↑)) (se_var 0)] = M[wk_q φ]ʷ.
Proof.
  intros; rewrite (exp_sub_sb_eq _ _ _ (sb_of_wk_q_extend φ)).
  apply exp_sub_of_wk.
Qed.

(** The degenerate instance of the above, at [φ := wk_id]: extending [ι ↑] by
    the canonical variable is the identity. *)
Corollary exp_sub_of_shift_extend_zero : forall M, M[sb_extend (ι ↑) (se_var 0)] = M.
Proof. intros; apply exp_sub_id_ext; pointwise; reflexivity. Qed.

(** Transporting an instantiated [Π]-codomain along a further weakening: the
    two weakenings fuse and the argument is weakened in place.  This is what the
    readback clauses of the gluing model need in order to iterate. *)
Corollary exp_wk_sub_of_wk_extend : forall M φ ψ N,
    M[(ι φ),,N][ψ]ʷ = M[(ι (φ ⊙ ψ)),,N[ψ]ʷ].
Proof. intros; apply exp_wk_sub_ext; pointwise; reflexivity. Qed.

(** Weakening and substitution commute.  The pointwise hypothesis is what
    survives being lifted, so no induction over the number of enclosing
    binders is needed. *)

Lemma sb_q_comm_ext : forall φ σ τ ψ,
    (forall x, σ (φ x) = sentry_wk (τ x) ψ) ->
    forall x, (q σ) (wk_q φ x) = sentry_wk ((q τ) x) (wk_q ψ).
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite Heq; do 2 rewrite sentry_wk_wk.
  apply sentry_wk_wk_eq; pointwise_solve.
Qed.

Lemma sb_qn_comm_ext : forall n φ σ τ ψ,
    (forall x, σ (φ x) = sentry_wk (τ x) ψ) ->
    forall x, (sb_qn n σ) (wk_qn n φ x) = sentry_wk ((sb_qn n τ) x) (wk_qn n ψ).
Proof. induction n; intros * Heq; simpl; [ exact Heq | apply sb_q_comm_ext; apply IHn; exact Heq ]. Qed.

Lemma syn_wk_sub_comm_ext :
  (forall M φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> exp_sub (exp_wk M φ) σ = exp_wk (exp_sub M τ) ψ) /\
  (forall H φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> modexp_sub (modexp_wk H φ) σ = modexp_wk (modexp_sub H τ) ψ) /\
  (forall b φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> bnd_sub (bnd_wk b φ) σ = bnd_wk (bnd_sub b τ) ψ) /\
  (forall U φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> gunit_sub (gunit_wk U φ) σ = gunit_wk (gunit_sub U τ) ψ) /\
  (forall D φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> moddef_sub (moddef_wk D φ) σ = moddef_wk (moddef_sub D τ) ψ) /\
  (forall Φ φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> gmod_sub (gmod_wk Φ φ) σ = gmod_wk (gmod_sub Φ τ) ψ) /\
  (forall c φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> bcheck_sub (bcheck_wk c φ) σ = bcheck_wk (bcheck_sub c τ) ψ) /\
  (forall E φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> gentry_sub (gentry_wk E φ) σ = gentry_wk (gentry_sub E τ) ψ) /\
  (forall e φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> centry_sub (centry_wk e φ) σ = centry_wk (centry_sub e τ) ψ).
Proof. syn_mut_ind; syn_ext_case sb_q_comm_ext sb_qn_comm_ext. Qed.

Corollary exp_wk_sub_comm_ext : forall M φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> exp_sub (exp_wk M φ) σ = exp_wk (exp_sub M τ) ψ.
Proof. exact (proj1 syn_wk_sub_comm_ext). Qed.
Corollary modexp_wk_sub_comm_ext : forall H φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> modexp_sub (modexp_wk H φ) σ = modexp_wk (modexp_sub H τ) ψ.
Proof. exact (proj1 (proj2 syn_wk_sub_comm_ext)). Qed.
Corollary bnd_wk_sub_comm_ext : forall b φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> bnd_sub (bnd_wk b φ) σ = bnd_wk (bnd_sub b τ) ψ.
Proof. exact (proj1 (proj2 (proj2 syn_wk_sub_comm_ext))). Qed.
Corollary gunit_wk_sub_comm_ext : forall U φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> gunit_sub (gunit_wk U φ) σ = gunit_wk (gunit_sub U τ) ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_wk_sub_comm_ext)))). Qed.
Corollary moddef_wk_sub_comm_ext : forall D φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> moddef_sub (moddef_wk D φ) σ = moddef_wk (moddef_sub D τ) ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_comm_ext))))). Qed.
Corollary gmod_wk_sub_comm_ext : forall Φ φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> gmod_sub (gmod_wk Φ φ) σ = gmod_wk (gmod_sub Φ τ) ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_comm_ext)))))). Qed.
Corollary bcheck_wk_sub_comm_ext : forall c φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> bcheck_sub (bcheck_wk c φ) σ = bcheck_wk (bcheck_sub c τ) ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_comm_ext))))))). Qed.
Corollary gentry_wk_sub_comm_ext : forall E φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> gentry_sub (gentry_wk E φ) σ = gentry_wk (gentry_sub E τ) ψ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_comm_ext)))))))). Qed.
Corollary centry_wk_sub_comm_ext : forall e φ σ τ ψ, (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> centry_sub (centry_wk e φ) σ = centry_wk (centry_sub e τ) ψ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_wk_sub_comm_ext)))))))). Qed.

(** The instances the rest of the development needs: the commutation above at
    [n = 0], once for a lifted substitution and once for a lifted weakening.  Together with
    [exp_sub_shift_extend] below, these three are what push the [A[↑]ʷ] produced
    by a context lookup past a lifted operation, and hence what every
    [q]-preservation lemma reduces to. *)

Corollary exp_wk_shift_sub_q : forall M σ, exp_sub (exp_wk M wk_shift) (q σ) = exp_wk (exp_sub M σ) wk_shift.
Proof. intros; apply exp_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary modexp_wk_shift_sub_q : forall H σ, modexp_sub (modexp_wk H wk_shift) (q σ) = modexp_wk (modexp_sub H σ) wk_shift.
Proof. intros; apply modexp_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary bnd_wk_shift_sub_q : forall b σ, bnd_sub (bnd_wk b wk_shift) (q σ) = bnd_wk (bnd_sub b σ) wk_shift.
Proof. intros; apply bnd_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary gunit_wk_shift_sub_q : forall U σ, gunit_sub (gunit_wk U wk_shift) (q σ) = gunit_wk (gunit_sub U σ) wk_shift.
Proof. intros; apply gunit_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary moddef_wk_shift_sub_q : forall D σ, moddef_sub (moddef_wk D wk_shift) (q σ) = moddef_wk (moddef_sub D σ) wk_shift.
Proof. intros; apply moddef_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary gmod_wk_shift_sub_q : forall Φ σ, gmod_sub (gmod_wk Φ wk_shift) (q σ) = gmod_wk (gmod_sub Φ σ) wk_shift.
Proof. intros; apply gmod_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary bcheck_wk_shift_sub_q : forall c σ, bcheck_sub (bcheck_wk c wk_shift) (q σ) = bcheck_wk (bcheck_sub c σ) wk_shift.
Proof. intros; apply bcheck_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary gentry_wk_shift_sub_q : forall E σ, gentry_sub (gentry_wk E wk_shift) (q σ) = gentry_wk (gentry_sub E σ) wk_shift.
Proof. intros; apply gentry_wk_sub_comm_ext; intros; reflexivity. Qed.
Corollary centry_wk_shift_sub_q : forall e σ, centry_sub (centry_wk e wk_shift) (q σ) = centry_wk (centry_sub e σ) wk_shift.
Proof. intros; apply centry_wk_sub_comm_ext; intros; reflexivity. Qed.

Lemma sentry_wk_shift_sub_q : forall e σ,
    sentry_sub (sentry_wk e wk_shift) (q σ) = sentry_wk (sentry_sub e σ) wk_shift.
Proof. intros [] *; simpl; f_equal; auto using exp_wk_shift_sub_q, modexp_wk_shift_sub_q. Qed.

Corollary exp_wk_shift_wk_q : forall M φ,
    M[↑]ʷ[wk_q φ]ʷ = M[φ]ʷ[↑]ʷ.
Proof.
  intros; do 2 rewrite exp_wk_wk.
  apply exp_wk_wk_eq; pointwise_solve.
Qed.

Corollary modexp_wk_shift_wk_q : forall H φ,
    modexp_wk (modexp_wk H ↑) (wk_q φ) = modexp_wk (modexp_wk H φ) ↑.
Proof.
  intros; do 2 rewrite modexp_wk_wk.
  apply modexp_wk_wk_eq; pointwise_solve.
Qed.

Corollary bnd_wk_shift_wk_q : forall b φ,
    bnd_wk (bnd_wk b ↑) (wk_q φ) = bnd_wk (bnd_wk b φ) ↑.
Proof.
  intros; do 2 rewrite bnd_wk_wk.
  apply bnd_wk_wk_eq; pointwise_solve.
Qed.

Corollary gunit_wk_shift_wk_q : forall U φ,
    gunit_wk (gunit_wk U ↑) (wk_q φ) = gunit_wk (gunit_wk U φ) ↑.
Proof.
  intros; do 2 rewrite gunit_wk_wk.
  apply gunit_wk_wk_eq; pointwise_solve.
Qed.

Corollary moddef_wk_shift_wk_q : forall D φ,
    moddef_wk (moddef_wk D ↑) (wk_q φ) = moddef_wk (moddef_wk D φ) ↑.
Proof.
  intros; do 2 rewrite moddef_wk_wk.
  apply moddef_wk_wk_eq; pointwise_solve.
Qed.

Corollary gmod_wk_shift_wk_q : forall Φ φ,
    gmod_wk (gmod_wk Φ ↑) (wk_q φ) = gmod_wk (gmod_wk Φ φ) ↑.
Proof.
  intros; do 2 rewrite gmod_wk_wk.
  apply gmod_wk_wk_eq; pointwise_solve.
Qed.

Corollary bcheck_wk_shift_wk_q : forall c φ,
    bcheck_wk (bcheck_wk c ↑) (wk_q φ) = bcheck_wk (bcheck_wk c φ) ↑.
Proof.
  intros; do 2 rewrite bcheck_wk_wk.
  apply bcheck_wk_wk_eq; pointwise_solve.
Qed.

Corollary gentry_wk_shift_wk_q : forall E φ,
    gentry_wk (gentry_wk E ↑) (wk_q φ) = gentry_wk (gentry_wk E φ) ↑.
Proof.
  intros; do 2 rewrite gentry_wk_wk.
  apply gentry_wk_wk_eq; pointwise_solve.
Qed.

Corollary centry_wk_shift_wk_q : forall e φ,
    centry_wk (centry_wk e ↑) (wk_q φ) = centry_wk (centry_wk e φ) ↑.
Proof.
  intros; do 2 rewrite centry_wk_wk.
  apply centry_wk_wk_eq; pointwise_solve.
Qed.

(** "[⇑] cancels an extension" at the level of expressions: an extension is
    invisible to an expression that has just been weakened. *)
Corollary exp_sub_shift_extend : forall M σ en, exp_sub (exp_wk M wk_shift) (sb_extend σ en) = exp_sub M σ.
Proof. intros; apply exp_sub_wk_ext; intros; reflexivity. Qed.
Corollary modexp_sub_shift_extend : forall H σ en, modexp_sub (modexp_wk H wk_shift) (sb_extend σ en) = modexp_sub H σ.
Proof. intros; apply modexp_sub_wk_ext; intros; reflexivity. Qed.
Corollary bnd_sub_shift_extend : forall b σ en, bnd_sub (bnd_wk b wk_shift) (sb_extend σ en) = bnd_sub b σ.
Proof. intros; apply bnd_sub_wk_ext; intros; reflexivity. Qed.
Corollary gunit_sub_shift_extend : forall U σ en, gunit_sub (gunit_wk U wk_shift) (sb_extend σ en) = gunit_sub U σ.
Proof. intros; apply gunit_sub_wk_ext; intros; reflexivity. Qed.
Corollary moddef_sub_shift_extend : forall D σ en, moddef_sub (moddef_wk D wk_shift) (sb_extend σ en) = moddef_sub D σ.
Proof. intros; apply moddef_sub_wk_ext; intros; reflexivity. Qed.
Corollary gmod_sub_shift_extend : forall Φ σ en, gmod_sub (gmod_wk Φ wk_shift) (sb_extend σ en) = gmod_sub Φ σ.
Proof. intros; apply gmod_sub_wk_ext; intros; reflexivity. Qed.
Corollary bcheck_sub_shift_extend : forall c σ en, bcheck_sub (bcheck_wk c wk_shift) (sb_extend σ en) = bcheck_sub c σ.
Proof. intros; apply bcheck_sub_wk_ext; intros; reflexivity. Qed.
Corollary gentry_sub_shift_extend : forall E σ en, gentry_sub (gentry_wk E wk_shift) (sb_extend σ en) = gentry_sub E σ.
Proof. intros; apply gentry_sub_wk_ext; intros; reflexivity. Qed.
Corollary centry_sub_shift_extend : forall e σ en, centry_sub (centry_wk e wk_shift) (sb_extend σ en) = centry_sub e σ.
Proof. intros; apply centry_sub_wk_ext; intros; reflexivity. Qed.

Lemma sentry_sub_of_wk : forall e φ, sentry_sub e (ι φ) = sentry_wk e φ.
Proof. intros [] *; simpl; f_equal; auto using exp_sub_of_wk, modexp_sub_of_wk. Qed.

Lemma sentry_sub_shift_extend : forall e σ en, sentry_sub (sentry_wk e wk_shift) (sb_extend σ en) = sentry_sub e σ.
Proof. intros [] *; simpl; f_equal; auto using exp_sub_shift_extend, modexp_sub_shift_extend. Qed.

(** Substitution application respects composition. *)

Lemma sb_q_compose_ext : forall σ τ δ,
    sb_eq (σ ⨟ τ) δ ->
    sb_eq ((q σ) ⨟ (q τ)) (q δ).
Proof.
  intros * Heq; pointwise; [ reflexivity | ].
  rewrite <- Heq; reduce_index.
  apply sentry_wk_shift_sub_q.
Qed.

Lemma sb_qn_compose_ext : forall n σ τ δ,
    sb_eq (σ ⨟ τ) δ ->
    sb_eq ((sb_qn n σ) ⨟ (sb_qn n τ)) (sb_qn n δ).
Proof. induction n; intros; simpl; auto using sb_q_compose_ext. Qed.

Lemma syn_sub_sub_ext :
  (forall M σ τ δ, sb_eq (σ ⨟ τ) δ -> exp_sub (exp_sub M σ) τ = exp_sub M δ) /\
  (forall H σ τ δ, sb_eq (σ ⨟ τ) δ -> modexp_sub (modexp_sub H σ) τ = modexp_sub H δ) /\
  (forall b σ τ δ, sb_eq (σ ⨟ τ) δ -> bnd_sub (bnd_sub b σ) τ = bnd_sub b δ) /\
  (forall U σ τ δ, sb_eq (σ ⨟ τ) δ -> gunit_sub (gunit_sub U σ) τ = gunit_sub U δ) /\
  (forall D σ τ δ, sb_eq (σ ⨟ τ) δ -> moddef_sub (moddef_sub D σ) τ = moddef_sub D δ) /\
  (forall Φ σ τ δ, sb_eq (σ ⨟ τ) δ -> gmod_sub (gmod_sub Φ σ) τ = gmod_sub Φ δ) /\
  (forall c σ τ δ, sb_eq (σ ⨟ τ) δ -> bcheck_sub (bcheck_sub c σ) τ = bcheck_sub c δ) /\
  (forall E σ τ δ, sb_eq (σ ⨟ τ) δ -> gentry_sub (gentry_sub E σ) τ = gentry_sub E δ) /\
  (forall e σ τ δ, sb_eq (σ ⨟ τ) δ -> centry_sub (centry_sub e σ) τ = centry_sub e δ).
Proof. syn_mut_ind; syn_ext_case sb_q_compose_ext sb_qn_compose_ext. Qed.

Corollary exp_sub_sub_ext : forall M σ τ δ, sb_eq (σ ⨟ τ) δ -> exp_sub (exp_sub M σ) τ = exp_sub M δ.
Proof. exact (proj1 syn_sub_sub_ext). Qed.
Corollary modexp_sub_sub_ext : forall H σ τ δ, sb_eq (σ ⨟ τ) δ -> modexp_sub (modexp_sub H σ) τ = modexp_sub H δ.
Proof. exact (proj1 (proj2 syn_sub_sub_ext)). Qed.
Corollary bnd_sub_sub_ext : forall b σ τ δ, sb_eq (σ ⨟ τ) δ -> bnd_sub (bnd_sub b σ) τ = bnd_sub b δ.
Proof. exact (proj1 (proj2 (proj2 syn_sub_sub_ext))). Qed.
Corollary gunit_sub_sub_ext : forall U σ τ δ, sb_eq (σ ⨟ τ) δ -> gunit_sub (gunit_sub U σ) τ = gunit_sub U δ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_sub_sub_ext)))). Qed.
Corollary moddef_sub_sub_ext : forall D σ τ δ, sb_eq (σ ⨟ τ) δ -> moddef_sub (moddef_sub D σ) τ = moddef_sub D δ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 syn_sub_sub_ext))))). Qed.
Corollary gmod_sub_sub_ext : forall Φ σ τ δ, sb_eq (σ ⨟ τ) δ -> gmod_sub (gmod_sub Φ σ) τ = gmod_sub Φ δ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sub_ext)))))). Qed.
Corollary bcheck_sub_sub_ext : forall c σ τ δ, sb_eq (σ ⨟ τ) δ -> bcheck_sub (bcheck_sub c σ) τ = bcheck_sub c δ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sub_ext))))))). Qed.
Corollary gentry_sub_sub_ext : forall E σ τ δ, sb_eq (σ ⨟ τ) δ -> gentry_sub (gentry_sub E σ) τ = gentry_sub E δ.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sub_ext)))))))). Qed.
Corollary centry_sub_sub_ext : forall e σ τ δ, sb_eq (σ ⨟ τ) δ -> centry_sub (centry_sub e σ) τ = centry_sub e δ.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_sub_sub_ext)))))))). Qed.

Corollary exp_sub_sub : forall M σ τ, exp_sub (exp_sub M σ) τ = exp_sub M (σ ⨟ τ).
Proof. intros; now apply exp_sub_sub_ext. Qed.
Corollary modexp_sub_sub : forall H σ τ, modexp_sub (modexp_sub H σ) τ = modexp_sub H (σ ⨟ τ).
Proof. intros; now apply modexp_sub_sub_ext. Qed.
Corollary bnd_sub_sub : forall b σ τ, bnd_sub (bnd_sub b σ) τ = bnd_sub b (σ ⨟ τ).
Proof. intros; now apply bnd_sub_sub_ext. Qed.
Corollary gunit_sub_sub : forall U σ τ, gunit_sub (gunit_sub U σ) τ = gunit_sub U (σ ⨟ τ).
Proof. intros; now apply gunit_sub_sub_ext. Qed.
Corollary moddef_sub_sub : forall D σ τ, moddef_sub (moddef_sub D σ) τ = moddef_sub D (σ ⨟ τ).
Proof. intros; now apply moddef_sub_sub_ext. Qed.
Corollary gmod_sub_sub : forall Φ σ τ, gmod_sub (gmod_sub Φ σ) τ = gmod_sub Φ (σ ⨟ τ).
Proof. intros; now apply gmod_sub_sub_ext. Qed.
Corollary bcheck_sub_sub : forall c σ τ, bcheck_sub (bcheck_sub c σ) τ = bcheck_sub c (σ ⨟ τ).
Proof. intros; now apply bcheck_sub_sub_ext. Qed.
Corollary gentry_sub_sub : forall E σ τ, gentry_sub (gentry_sub E σ) τ = gentry_sub E (σ ⨟ τ).
Proof. intros; now apply gentry_sub_sub_ext. Qed.
Corollary centry_sub_sub : forall e σ τ, centry_sub (centry_sub e σ) τ = centry_sub e (σ ⨟ τ).
Proof. intros; now apply centry_sub_sub_ext. Qed.

Corollary sb_q_compose : forall σ τ,
    sb_eq ((q σ) ⨟ (q τ)) (q (σ ⨟ τ)).
Proof. intros; now apply sb_q_compose_ext. Qed.

Lemma sentry_sub_sub : forall e σ τ, sentry_sub (sentry_sub e σ) τ = sentry_sub e (σ ⨟ τ).
Proof. intros [] *; simpl; f_equal; auto using exp_sub_sub, modexp_sub_sub. Qed.

Lemma tele_sub_sub : forall Δ σ τ, tele_sub (tele_sub Δ σ) τ = tele_sub Δ (σ ⨟ τ).
Proof.
  induction Δ; intros; simpl; f_equal; auto.
  rewrite length_tele_sub; apply centry_sub_sub_ext, sb_qn_compose_ext; reflexivity.
Qed.

Lemma tele_wk_sub : forall Δ σ φ, tele_wk (tele_sub Δ σ) φ = tele_sub Δ (sb_wk σ φ).
Proof.
  induction Δ; intros; simpl; f_equal; auto.
  rewrite length_tele_sub; apply centry_wk_sub_ext, sb_qn_wk_ext; reflexivity.
Qed.

Lemma tele_sub_of_wk : forall Δ φ, tele_sub Δ (ι φ) = tele_wk Δ φ.
Proof.
  induction Δ; intros; simpl; f_equal; auto.
  apply centry_sub_of_wk_ext, sb_qn_of_wk_ext; reflexivity.
Qed.

(** Substitutions form a category. *)

Lemma sb_compose_id_left : forall σ, sb_eq (Id ⨟ σ) σ.
Proof. intros ? ?; reflexivity. Qed.

Lemma sb_compose_id_right : forall σ, sb_eq (σ ⨟ Id) σ.
Proof. intros ? ?; simpl; apply sentry_sub_id. Qed.

Lemma sb_compose_assoc : forall σ τ δ,
    sb_eq ((σ ⨟ τ) ⨟ δ) (σ ⨟ τ ⨟ δ).
Proof. intros * x; simpl; apply sentry_sub_sub. Qed.

(** [σ[φ]] is just [σ ⨟ ι φ]. *)
Lemma sb_wk_compose : forall σ φ, sb_eq (sb_wk σ φ) (σ ⨟ (ι φ)).
Proof. intros * x; simpl; destruct (σ x); simpl; f_equal; symmetry; auto using exp_sub_of_wk, modexp_sub_of_wk. Qed.

(** Postcomposing twice is postcomposing by the composite.  This is what makes
    the two instantiations of the semantic weakening lemma speak about the same
    substitution. *)
Lemma sb_wk_wk : forall σ ψ φ, sb_eq (sb_wk (sb_wk σ ψ) φ) (sb_wk σ (ψ ⊙ φ)).
Proof. intros * x; simpl; apply sentry_wk_wk. Qed.

(** Postcomposition by a weakening slides past precomposition by a weakening:
    both sides send [x] to [(σ (ψ x))[φ]ʷ].  Nothing has to be transported across
    [ψ], because [(ι ψ) x] is a variable.  The semantic weakening lemma needs the
    general form; [sb_wk_shift_pre] below is the instance at [ψ := ⇑]. *)
Lemma sb_wk_wk_pre : forall σ ψ φ,
    sb_eq (sb_wk ((ι ψ) ⨟ σ) φ) ((ι ψ) ⨟ (sb_wk σ φ)).
Proof. intros * x; reflexivity. Qed.

Corollary sb_wk_shift_pre : forall σ φ,
    sb_eq (sb_wk (Wk ⨟ σ) φ) (Wk ⨟ (sb_wk σ φ)).
Proof. intros. apply (sb_wk_wk_pre σ wk_shift). Qed.

(** Postcomposition by a weakening distributes over an extension.  Completeness
    uses it in the other direction: a semantic substitution judgment about
    [σ ,, t] has to produce the evaluation of [(σ ,, t)[ψ]], and
    [eval_sub_extend] only speaks about a syntactic extension. *)
Lemma sb_wk_extend_gen : forall σ e φ,
    sb_eq (sb_wk (sb_extend σ e) φ) (sb_extend (sb_wk σ φ) (sentry_wk e φ)).
Proof. intros *; pointwise_solve. Qed.

Lemma sb_wk_extend : forall σ M φ,
    sb_eq (sb_wk (σ,,M) φ) ((sb_wk σ φ),,M[φ]ʷ).
Proof. intros *; pointwise_solve. Qed.

(** The instance of the above at [q σ], with the two heads computed: [q σ] is
    an extension by the variable [0], which [φ] sends to [φ 0]. *)
Lemma sb_wk_q : forall σ φ,
    sb_eq (sb_wk (q σ) φ) (sb_extend (sb_wk σ (↑ ⊙ φ)) (se_var (φ 0))).
Proof. intros *; pointwise; [ reflexivity | apply sentry_wk_wk ]. Qed.

(** [⇑] cancels an extension. *)
Lemma sb_shift_extend : forall σ e, sb_eq (Wk ⨟ (sb_extend σ e)) σ.
Proof. intros * x; reflexivity. Qed.

(** Composition distributes over extension. *)
Lemma sb_extend_compose_gen : forall σ τ e,
    sb_eq ((sb_extend σ e) ⨟ τ) (sb_extend (σ ⨟ τ) (sentry_sub e τ)).
Proof. intros *; pointwise_solve. Qed.

Lemma sb_extend_compose : forall σ τ M,
    sb_eq ((σ,,M) ⨟ τ) (σ ⨟ τ,,M[τ]).
Proof. intros *; pointwise_solve. Qed.

(** Every substitution is its own expansion. *)
Lemma sb_expand : forall σ, sb_eq σ (sb_extend (Wk ⨟ σ) (σ 0)).
Proof. intros *; pointwise_solve. Qed.

(** A lifted substitution meeting an extension.  These are the equations
    behind the [β]-rule and the elimination rules.

    The general form.  The two lemmas below are its instances at [τ := ι φ]
    and [τ := Id], stated separately because the head of the right-hand side
    differs, and the rewrite databases match on that head. *)
Lemma sb_q_compose_extend_gen : forall σ τ e,
    sb_eq ((q σ) ⨟ (sb_extend τ e)) (sb_extend (σ ⨟ τ) e).
Proof.
  intros *; pointwise; [ reflexivity | ].
  rewrite sentry_sub_wk; apply sentry_sub_sb_eq; intros ?; reflexivity.
Qed.

Lemma sb_q_compose_extend : forall σ τ M,
    sb_eq ((q σ) ⨟ (τ,,M)) (σ ⨟ τ,,M).
Proof. intros; apply sb_q_compose_extend_gen. Qed.

Corollary exp_sub_q_compose_extend : forall M σ τ N,
    M[q σ][τ,,N] = M[σ ⨟ τ,,N].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_compose_extend.
Qed.

Lemma sb_q_extend_wk : forall σ φ M,
    sb_eq ((q σ) ⨟ ((ι φ),,M)) ((sb_wk σ φ),,M).
Proof.
  intros; rewrite sb_q_compose_extend.
  apply sb_extend_cong; symmetry; apply sb_wk_compose.
Qed.

Corollary exp_sub_q_extend_wk : forall M σ φ N,
    M[q σ][(ι φ),,N] = M[(sb_wk σ φ),,N].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_extend_wk.
Qed.

Lemma sb_q_extend_gen : forall σ e, sb_eq ((q σ) ⨟ (sb_extend Id e)) (sb_extend σ e).
Proof.
  intros; rewrite sb_q_compose_extend_gen.
  apply sb_extend_cong, sb_compose_id_right.
Qed.

Lemma sb_q_extend : forall σ M, sb_eq ((q σ) ⨟ (Id,,M)) (σ,,M).
Proof. intros; apply sb_q_extend_gen. Qed.

Corollary exp_sub_q_extend : forall M σ N,
    M[q σ][Id,,N] = M[σ,,N].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_extend.
Qed.

(** A single substitution commutes past a lifted one. *)
Corollary exp_sub_extend_comm : forall M σ N,
    M[q σ][Id,,N[σ]] = M[Id,,N][σ].
Proof.
  intros.
  rewrite exp_sub_q_extend, exp_sub_sub.
  apply exp_sub_sb_eq; pointwise_solve.
Qed.

(** The form the completeness proof uses it in: an instantiated type or term,
    substituted, is the instantiation along the substitution.  Every rule whose
    type is an [M[Id ,, N]] reads its two outer values through this equation,
    because those are values at [ρ] and [ρ'] of the substituted expression while
    the judgment about [M] can only produce values along a substitution into the
    extended context. *)
Corollary exp_sub_extend_sub : forall M σ N,
    M[Id,,N][σ] = M[σ,,N[σ]].
Proof.
  intros.
  rewrite <- exp_sub_extend_comm.
  apply exp_sub_q_extend.
Qed.

(** The same for a module extension. *)
Corollary exp_sub_extend_mod_sub : forall M σ H,
    M[Id ,,ₘ H][σ] = M[σ ,,ₘ H[σ]ᵐ].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq; pointwise_solve.
Qed.

Corollary exp_sub_q_extend_mod : forall M σ H,
    M[q σ][Id ,,ₘ H] = M[σ ,,ₘ H].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_q_extend_gen.
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
Lemma sb_shift_shift : sb_eq (Wk ⨟ Wk) (ι (↑ ⊙ ↑)).
Proof. intros ?; reflexivity. Qed.

Corollary exp_sub_shift_shift : forall M, M[Wk ⨟ Wk] = M[↑]ʷ[↑]ʷ.
Proof.
  intros; rewrite sb_shift_shift, exp_sub_of_wk.
  symmetry; apply exp_wk_wk.
Qed.

Corollary exp_wk_sub_extend : forall M N φ,
    M[Id,,N][φ]ʷ = M[wk_q φ]ʷ[Id,,N[φ]ʷ].
Proof.
  intros; symmetry.
  apply exp_wk_sub_comm_ext; intros [| y]; reflexivity.
Qed.

Corollary exp_wk_sub_extend2 : forall M N N' φ,
    M[Id,,N,,N'][φ]ʷ = M[wk_q (wk_q φ)]ʷ[Id,,N[φ]ʷ,,N'[φ]ʷ].
Proof.
  intros; symmetry.
  apply exp_wk_sub_comm_ext; intros [| [| y]]; reflexivity.
Qed.

(** The motive of the successor branch is stable under a doubly lifted
    weakening. *)
Corollary exp_wk_sub_natrec : forall M φ,
    M[Wk ⨟ Wk,,succ #1][wk_q (wk_q φ)]ʷ = M[wk_q φ]ʷ[Wk ⨟ Wk,,succ #1].
Proof.
  intros; symmetry.
  apply exp_wk_sub_comm_ext; intros [| y]; reflexivity.
Qed.

Corollary exp_sub_sub_extend2 : forall M σ N N',
    M[Id,,N,,N'][σ] = M[q (q σ)][Id,,N[σ],,N'[σ]].
Proof.
  intros.
  do 2 rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| [| y]]; reduce_index; try reflexivity.
  do 2 rewrite sentry_sub_shift_extend.
  symmetry; apply sentry_sub_id.
Qed.

Corollary exp_sub_sub_natrec : forall M σ,
    M[Wk ⨟ Wk,,succ #1][q (q σ)] = M[q σ][Wk ⨟ Wk,,succ #1].
Proof.
  intros.
  do 2 rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; [ reflexivity | ].
  rewrite sentry_sub_shift_extend, sentry_wk_wk, (sentry_sub_sb_eq _ _ _ sb_shift_shift), sentry_sub_of_wk.
  reflexivity.
Qed.

(** The type of the [ℕ]-[β] rule for [succ]: the successor branch's motive,
    instantiated at [N] and the recursive call, is the motive at [succ N].  Stated
    along an arbitrary [σ] and not just [Id], because the semantic rule reads
    this type at two substitutions, [Id ,, M ,, E] out of [Γ] for its two inner
    values and [σ ,, M[σ] ,, E[σ]] out of the caller's [Γ'] for its two outer
    ones, and both instances must be the same equation for the two four-value
    patterns to be identified. *)
Corollary exp_sub_natrec_step : forall M σ N N',
    M[Wk ⨟ Wk,,succ #1][σ,,N,,N'] = M[σ,,succ N].
Proof.
  intros.
  rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; reflexivity.
Qed.

(** The two-argument analogue of [exp_sub_extend_sub], which is what the
    right-hand side of that rule — an [MS[Id ,, M ,, E]] — is read through. *)
Corollary exp_sub_extend_sub2 : forall M σ N N',
    M[Id,,N,,N'][σ] = M[σ,,N[σ],,N'[σ]].
Proof.
  intros.
  rewrite exp_sub_sub_extend2, exp_sub_sub.
  apply exp_sub_sb_eq; intros [| [| y]]; reduce_index; try reflexivity.
  do 2 rewrite sentry_sub_shift_extend.
  apply sentry_sub_id.
Qed.

(** [zero[σ]] is [zero], so the zero branch's type is an instance of
    [exp_sub_extend_sub] with the right-hand side already reduced. *)
Corollary exp_sub_extend_sub_zero : forall M σ,
    M[Id,,zero][σ] = M[σ,,zero].
Proof. intros; apply exp_sub_extend_sub. Qed.

Corollary exp_sub_q_extend2 : forall M σ N N',
    M[q (q σ)][Id,,N,,N'] = M[σ,,N,,N'].
Proof.
  intros.
  rewrite exp_sub_q_compose_extend.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; [ reflexivity | apply sb_q_extend ].
Qed.

(** [exp_sub_natrec_step] along an arbitrary substitution: [τ] need not be a
    literal extension, because [sb_expand] makes every substitution one. *)
Corollary exp_sub_natrec_step_gen : forall M τ,
    M[Wk ⨟ Wk,,succ #1][τ] = M[Wk ⨟ Wk ⨟ τ,,succ #0[Wk ⨟ τ]].
Proof.
  intros.
  rewrite exp_sub_sub.
  apply exp_sub_sb_eq; intros [| y]; reduce_index; reflexivity.
Qed.

(** ** The Generic Recursor

    An eliminator whose scrutinee is [#0] and whose three other components have
    been weakened past that binder.  If [E] is the eliminator at [M] in [Γ], this
    is a term of [Γ ▹ ℕ] which the extension [Id ,, M] sends back to [E], and it
    exists for one reason: the recursive call of the [ℕ]-[β] rule for [succ]
    appears in the substitution [Id ,, M ,, E], and the only way to validate an
    extension semantically ([rel_sub_under_ctx_extend_sub_double]) is by a term of
    the context being extended.  [E] itself is a term of [Γ], one context too
    short; its generic form is the term of [Γ ▹ ℕ] that is asked for. *)
Corollary exp_sub_natrec_generic : forall A MZ MS σ N,
    rec #0 return A[wk_q ↑]ʷ | zero -> MZ[↑]ʷ | succ -> MS[wk_q (wk_q ↑)]ʷ end[σ,,N]
    = rec N return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end.
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
    rec #0 return A[wk_q ↑]ʷ | zero -> MZ[↑]ʷ | succ -> MS[wk_q (wk_q ↑)]ʷ end[σ,,M[σ]]
    = rec M return A | zero -> MZ | succ -> MS end[σ].
Proof.
  intros; apply exp_sub_natrec_generic.
Qed.

(** The type of the [η]-rule: a codomain weakened under one more binder and
    then instantiated at the variable [0] is the codomain itself. *)
Corollary exp_wk_q_shift_single : forall M, M[wk_q ↑]ʷ[sb_extend Id (se_var 0)] = M.
Proof.
  intros.
  rewrite exp_sub_wk.
  transitivity M[Id]; [ apply exp_sub_sb_eq | apply exp_sub_id ].
  intros [| y]; reduce_index; reflexivity.
Qed.

(** The action of [q^n] on indices. *)

Lemma sb_qn_lt : forall n σ x, x < n -> sb_qn n σ x = se_var x.
Proof.
  induction n; intros * Hlt; [ exfalso; lia | ].
  destruct x; [ reflexivity | ].
  simpl; reduce_index; rewrite IHn by lia; reflexivity.
Qed.

Lemma sb_qn_ge : forall n σ x,
    n <= x ->
    sb_qn n σ x = sentry_wk (σ (x - n)) (wk_shiftn n).
Proof.
  induction n; intros * Hle; simpl.
  - replace (x - 0) with x by lia.
    symmetry; destruct (σ x); simpl; f_equal; [ | apply exp_wk_id_ext | apply modexp_wk_id_ext ]; apply wk_shiftn_zero.
  - destruct x; [ exfalso; lia | ].
    reduce_index; rewrite IHn by lia.
    rewrite sentry_wk_wk.
    replace (S x - S n) with (x - n) by lia.
    apply sentry_wk_wk_eq, wk_shiftn_succ.
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
                exp_wk_True exp_wk_true exp_wk_False
                exp_sub_True exp_sub_true exp_sub_False
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

(** A unit is moved by its telescope and definition ([gunit_wk_mk],
    [gunit_sub_mk]); [simpl] leaves it folded. *)
#[global] Arguments gunit_wk : simpl never.
#[global] Arguments gunit_sub : simpl never.
