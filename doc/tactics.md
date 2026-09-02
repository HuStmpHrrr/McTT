# McTT tactic reference

This document describes every `Ltac` definition and `Tactic Notation` in
`theories/` — 228 definitions across 35 files — what each one does, why it
exists, and how the families fit together.

The tactics are not incidental to McTT: the metatheory is proved by
*saturating* the proof context with derived facts and then letting `mauto`
close the goal. Almost every tactic below is in service of one of four jobs:

1. **Saturate** — add all consequences of the hypotheses you already have
   (presuppositions, reflexivity instances, escape lemmas).
2. **Identify** — collapse two derivations of the same deterministic judgment,
   or two relations proved equivalent, into one.
3. **Invert** — take apart a hypothesis without accidentally case-splitting the
   goal, including inverting `Equations`-defined relations.
4. **Iterate** — apply one of the above to *every* hypothesis exactly once.

---

## Table of contents

- [Conventions you need first](#conventions-you-need-first)
- [1. `LibTactics.v` — general infrastructure](#1-libtacticsv--general-infrastructure)
- [2. Determinism: the `functional_*` families](#2-determinism-the-functional_-families)
- [3. Syntactic layer: substitutions and presuppositions](#3-syntactic-layer-substitutions-and-presuppositions)
- [4. Semantic layer: PER tactics](#4-semantic-layer-per-tactics)
- [5. Completeness layer: witness skeletons](#5-completeness-layer-witness-skeletons)
- [6. Soundness layer: glue tactics](#6-soundness-layer-glue-tactics)
- [7. Extraction layer: obligation tactics](#7-extraction-layer-obligation-tactics)
- [8. Gotchas](#8-gotchas)
- [9. Index](#9-index)

---

## Conventions you need first

### `mauto` is the workhorse

`theories/LibTactics.v:6` creates a discriminated hint database `mctt`, and
almost every lemma in the development adds itself to it
(`#[export] Hint Resolve ... : mctt`). `mauto` (`LibTactics.v:194`) is just

```coq
eauto with mctt core
```

with `Tactic Notation` overloads for a search depth and for `using` clauses
(up to four lemmas): `mauto`, `mauto 4`, `mauto using foo`,
`mauto 3 using foo, bar`, and so on. The depth argument matters a lot for
compile time — this is why the sources are littered with `mauto 2`, `mauto 3`,
`mauto 4` rather than bare `mauto`.

`mautosolve` (`LibTactics.v:229`) is the "finish the goal or fail" variant:

```coq
Ltac mautosolve_impl pow := unshelve solve [mauto pow]; solve [constructor].
```

`unshelve` brings back the side goals `eauto` shelved (typically typeclass
side conditions), `solve [mauto pow]` must fully close the main goal, and
`solve [constructor]` then discharges whatever was unshelved. Default depth
is 5.

Idiomatically these appear as `Proof with mautosolve.` plus `...` as the
end-tactic — 83 proofs use exactly that, another 62 use `mautosolve 3`/`4`.
Reading `foo; bar...` means `foo; bar; mautosolve`.

### `fail n` counts enclosing `match`es

This idiom is everywhere and is the single most confusing thing in the file.
In Ltac1, `match goal` is a backtracking point: a failure at level 0 makes it
try the next hypothesis or branch, and a failure at level `n > 0` passes
through, arriving one level lower. So `fail 1` raised inside a helper's own
`match goal` is observed as a *level-0* failure by the caller's `match goal`,
which then simply moves on to the next hypothesis.

That is exactly how `fail_if_dup` is used to terminate saturation loops: the
guard fails, the `pose proof` is undone by backtracking, and the enclosing
`repeat match` proceeds to another hypothesis instead of looping forever.
`fail_at_if_dup` takes the level as a parameter because the number of
enclosing `match`es varies by call site.

### `Equations` and `simp`

`per_univ_elem`, `glu_univ_elem` and the extraction functions are defined with
[Equations](https://github.com/mattam82/Coq-Equations). Two consequences:

- You cannot `constructor`/`inversion` such a relation directly. You must
  first `simp <name>` to unfold one equation step, and afterwards
  `rewrite <- <name>_equation_1` to fold the recursive occurrences back up.
  This is precisely the body of `basic_per_univ_elem_econstructor` and friends.
- Obligations are discharged by the tactic named in the
  `#[tactic="..."]` attribute — that is what every `impl_obl_tac` and
  `def_simp` in the tree is for.

### Notation scopes

Every notation lives in ordinary `constr`, in `mctt_scope`, and needs no
delimiter, so tactic patterns read like the judgments on paper:

```coq
| H : ?Γ ⊢ ?M : ?A |- _ => ...
```

Values and normal forms carry a superscript (`ℕᵈ`, `λᵈ`, `#ᵈ n`; `ℕⁿ`, `λⁿ`,
`#ⁿ n`) because one spelling can denote only one sort. Context extension is
`Γ ▹ A` and application is `M $ N`. See
[`../AGENT/notations.md`](../AGENT/notations.md) for the level table and the
parsing traps.

---

## 1. `LibTactics.v` — general infrastructure

73 of the 228 definitions live here. Nothing in this file mentions McTT
judgments; it is reusable Ltac.

### 1.1 Generalization

| Tactic | Line | Description |
| --- | --- | --- |
| `gen x`, `gen x y`, `gen x y z`, `gen x y z w` | 17–17–17–17 | `generalize dependent`, for up to four variables in one go. |

### 1.2 Marking — iterate over each hypothesis exactly once

The trick is a transparent identity wrapper:

```coq
Definition __mark__ (n : nat) A (a : A) : A := a.
```

`mark H` folds `H`'s type into `__mark__ 0 t`, which is *convertible* to `t`
but no longer *syntactically matches* patterns like `?Γ ⊢ ?M : ?A`.
So a `repeat match goal` loop that marks each hypothesis it processes will
visit every hypothesis exactly once and then terminate.

| Tactic | Line | Description |
| --- | --- | --- |
| `mark H` / `unmark H` | 27, 30 | Wrap/unwrap `H`'s type at level 0. |
| `mark_all` / `unmark_all` | 32, 36 | Mark every unmarked hypothesis; unfold all marks. |
| `mark_with H n` / `mark_all_with n` | 38, 41 | Same, at a chosen level, so nested loops don't interfere. |
| `unmark_all_with n` | 45 | Unmark hypotheses carrying level `n`, skipping marks at other levels. |
| `on_all_marked_hyp tac` / `..._rev` | 50, 54, 58, 59 | Repeatedly pick a marked hypothesis, unmark it, run `tac H`. `_rev` walks the context in reverse. |
| `on_all_hyp: tac` | 60 | The one you actually use: mark everything at level 0, run `tac H` on each, clean up. |
| `on_all_hyp_rev: tac`, `on_all_marked_hyp: tac`, `on_all_marked_hyp_rev: tac` | 62, 58, 59 | Variants of the above. |

Typical use:

```coq
(on_all_hyp: fun H => gen_presup H)
```

### 1.3 Context housekeeping

| Tactic | Line | Description |
| --- | --- | --- |
| `destruct_logic` | 67 | Break one conjunction, existential, disjunction, `sumbool`, `sumor`, or `sum` in the context. |
| `destruct_all` | 77 | `repeat destruct_logic`. |
| `not_let_bind name` | 79 | Fail if `name` is a `let`-bound local definition. Guards the duplicate machinery from clearing definitions. |
| `find_dup_hyp tac non` | 89 | Find two hypotheses with the same `Prop` type and run `tac H H' X`; run `non` if there is no such pair. |
| `fail_at_if_dup n` | 100 | Fail at level `n` if a duplicate pair exists. |
| `fail_if_dup` | 104 | `fail_at_if_dup 1` — tuned so the caller's `match` sees a level-0 failure. The standard terminator for saturation loops. |
| `clear_dups` | 106 | Discard redundant duplicate hypotheses. |
| `clear_PER` | 356 | Drop `PER`/`Symmetric`/`Transitive` hypotheses (they clutter and confuse `eauto`). |

### 1.4 Controlled inversion

`inversion` is dangerous in this development: on a dependent judgment it can
split the goal into unrelated cases or generate a swamp of equations.
`directed` is the fix.

| Tactic | Line | Description |
| --- | --- | --- |
| `directed tac` | 110, 116 | Run `tac`, then `guard`s that the goal count did not increase. Fails if `tac` case-split. Also available as `Tactic Notation "directed" tactic2(tac)`. |
| `progressive_invert H` | 118 | `directed dependent destruction H` — `dependent destruction` is more general than `inversion`, and `directed` keeps it from branching. |
| `progressive_invert_once H n` | 123 | One step of the below: skip marked and `∀`-typed hypotheses, require the type to live in `Prop`/`Type`, then `directed inversion` + `simplify_eqs` + `clear_refl_eqs` + `clear_dups`, and mark at level `n`. |
| `progressive_inversion` | 141 | Repeat `progressive_invert_once _ 100` over the whole context. Marks at level 100 so each hypothesis is inverted at most once. |

### 1.5 Matching by head symbol

Judgments are notated, so their head constants (`wf_exp`, `eval_exp`,
`per_univ_elem`, …) are the reliable way to select hypotheses.

| Tactic | Line | Description |
| --- | --- | --- |
| `find_head t` | 161 | Peel applications off `t` and return its head. |
| `unify_by_head_of t head` | 167 | Succeed iff `t`'s head is `head`, for arities up to 10 (hand-unrolled because Ltac1 cannot pattern-match a spine). |
| `match_by_head1 head tac` | 182 | Run `tac H` on one hypothesis whose head is `head`. |
| `match_by_head head tac` | 186 | Run `tac H` on every such hypothesis exactly once (marks as it goes). |
| `inversion_by_head`, `dir_inversion_by_head`, `inversion_clear_by_head`, `dir_inversion_clear_by_head`, `destruct_by_head`, `dir_destruct_by_head` | 188–189–190–191–192–193 | The six obvious combinations of `inversion` / `inversion_clear` / `destruct`, each optionally wrapped in `directed`. |

### 1.6 Rewriting

| Tactic | Line | Description |
| --- | --- | --- |
| `clean_replace_by exp0 exp1 tac`, i.e. `clean replace e0 with e1 by tac` | 149, 158 | Prove `e0 = e1` by `tac`, `subst`, then `try rewrite <-` it everywhere, so the context uses one of the two uniformly. **Fails if `e0` and `e1` are already syntactically equal**, which is what makes it safe inside `repeat`. |
| `bulky_rewrite1` / `bulky_rewrite` | 465, 471 | Rewrite with *any* hypothesis, or with the `mctt` rewrite database, interleaving `mauto 2` to discharge side conditions. |
| `bulky_rewrite_in1 HT` / `bulky_rewrite_in HT` | 473, 479 | Same, targeting hypothesis `HT`. |

### 1.7 Applying a lemma you cannot `apply`

These four are the deepest magic in the file. They exist because many McTT
lemmas end in an `iff` or a conjunction buried under several `∀`s, so plain
`apply`/`rewrite` cannot see the relevant component.

| Tactic | Line | Description |
| --- | --- | --- |
| `exvar T tac` | 250 | Create a fresh evar of type `T` and hand the raw term to `tac`. Uses `unshelve evar` for `Prop`s so the hole stays open. |
| `deepexec lem tac` | 266 | Walk `lem`'s statement down through `∀`s and `∧`s (unfolding `iff`) to its conclusion, instantiating each `∀`-argument with an evar — preferring, for `Prop` arguments, unification with an existing hypothesis — then run `tac` on the fully applied lemma. |
| `cutexec lem C tac` | 286 | Same traversal, but stop at the first `∀`-argument whose type matches `C`'s type, instantiate it with `C`, and run `tac` there. |
| `unify_args H P` | 312 | Given `P = f x₁ … xₙ`, build `H x₁ … xₙ`: apply `H` to the same argument spine. |
| `strong_apply H X` | 321 | Push hypothesis `X` through implication `H` *in place*: line up `H` with `X`'s argument spine, cut-traverse to the slot `X` fits, `pose proof (L X)`, `simpl`, and rename the result back to `X`. |

### 1.8 Relations, PERs, and setoid rewriting

McTT's logical relations are relations-valued, and the metatheory constantly
needs "these two candidate relations are equivalent, so substitute". When
`setoid_rewrite` can do it, it does; when it cannot, `apply_equiv_*` does it
by hand.

| Tactic | Line | Description |
| --- | --- | --- |
| `apply_equiv_left1` / `apply_equiv_left` | 328, 339 | Given `H : R₁ <∙> R₂` (or `relation_equivalence R₁ R₂`), push every hypothesis headed by `R₁` through `H` via `strong_apply`, and `apply H` if the goal is headed by `R₁`. |
| `apply_equiv_right1` / `apply_equiv_right` | 342, 353 | Mirror image, on `R₂`. |
| `saturate_refl` | 379 | For every `H : R a b` with `a ≠ b` syntactically, derive `R a a` and `R b b` from `PER_refl1`/`PER_refl2` (proved at 361/368); terminate with `fail_if_dup`. |
| `saturate_refl_for hd` | 391 | Same, restricted to relations whose head is `hd` — e.g. `saturate_refl_for per_univ_elem`. |
| `solve_refl` | 404 | `solve [reflexivity \|\| apply Equivalence_Reflexive]`. The fallback exists because plain `reflexivity`'s unification occasionally fails on these goals. |

Supporting declarations in the same file, which are not tactics but determine
whether the above work:

- `Typeclasses Transparent arrows` (line 10) and the six `Hint Extern`s at
  408–423, which register the `subrelation` facts generalized rewriting needs
  (`predicate_equivalence`, `relation_equivalence`, `predicate_implication`,
  `subrelation` itself, and both directions of `iff`/`impl`).
- `predicate_implication_equivalence` (426) plus the parametric morphisms for
  `predicate_implication` (431) and `PER` (443), which let you `rewrite` a
  relation equivalence underneath `⊆∙` and underneath `PER`.
- `Hint Extern 1 => eassumption : typeclass_instances` (line 232) — lets
  typeclass resolution use *local* hypotheses, so a locally quantified `PER`
  can drive `setoid_rewrite`.
- `PERElem` / `PERProper` (451–459): a class that converts a `Proper R a` goal
  into a membership check `P a`. Instances are declared for `wf_exp_eq` and
  `wf_sub_eq` in `Core/Syntactic/System/Definitions.v:549,556`, which is what
  makes `rewrite` usable on the syntactic equality judgments.
- `Ltac Tauto.intuition_solver ::= auto with mctt core solve_subterm`
  (line 245) — redefines what `intuition` uses to close leaves, so `intuition`
  is McTT-aware everywhere.

### 1.9 Decision procedures

| Tactic | Line | Description |
| --- | --- | --- |
| `dec_complete` | 483 | For a goal `exists _, L = _` where `L : sumbool _ _`: `destruct L eqn:Heq`, then `eauto`/`contradiction`. The standard one-liner for "this decision procedure is complete". |

---

## 2. Determinism: the `functional_*` families

Every operational judgment in McTT is deterministic in its output, and each
gets a `functional_...` lemma plus a matching pair of tactics. The `…1`
version does one step; the plain version is `repeat …1`. All of them share
one shape:

```coq
Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  ...
```

Two derivations with the same inputs ⇒ identify the outputs and drop the
redundant derivation. Note the deliberate `fail 3` error message: when the
functionality lemma is not in the hint database at depth 2, you get a legible
complaint instead of a silent no-op.

| Tactic | Location | Judgments covered |
| --- | --- | --- |
| `functional_eval_rewrite_clear1` / `…_clear` | `Core/Semantic/Evaluation/Lemmas.v:73, 86` | `⟦M⟧ρ ↘ m`, `$\|m & n\|↘ r`, `rec … end`, `⟦σ⟧s ρ ↘ ρσ` |
| `functional_read_rewrite_clear1` / `…_clear` | `Core/Semantic/Readback/Lemmas.v:58, 68` | `Rnf`, `Rne`, `Rtyp` |
| `functional_initial_env_rewrite_clear1` / `…_clear` | `Core/Semantic/NbE.v:51, 57` | `initial_env` |
| `functional_nbe_rewrite_clear1` / `…_clear` | `Core/Semantic/NbE.v:171, 181` | `nbe`, `nbe_ty` (including the case where the two derivations use different universe levels) |
| `functional_alg_type_infer_rewrite_clear1` / `…_clear` | `Algorithmic/Typing/Lemmas.v:37, 43` | `Γ ⊢a M ⟹ A` (type inference is deterministic) |

Built on top of them:

| Tactic | Location | Description |
| --- | --- | --- |
| `simplify_subs` | `Core/Semantic/Evaluation/Tactics.v:13` | `cbn [exp_sub exp_wk] in *`. Since substitution is an operation, `⟦ Type@i[σ] ⟧ ρ ↘ a` has no constructor head until `exp_sub` is unfolded far enough to expose one. The delta list is restricted to the two recursive functions so that `eval_sub` and `sb_q` (both `simpl never`) stay folded. Not to be confused with `simpl_sub`, which rewrites the substitution algebra. |
| `simplify_evals` | `Core/Semantic/Evaluation/Tactics.v:15` | The standard "clean up the evaluation hypotheses" step: identify duplicate results, then `directed dependent destruction` every `eval_exp` / `eval_app` / `eval_natrec` / `eval_sub` hypothesis that does not branch, then identify again. |

---

## 3. Syntactic layer: substitutions and presuppositions

### 3.1 The substitution algebra (`Core/Syntactic/Substitution.v`)

Weakenings and substitutions are meta-level functions (`wk := nat -> nat`,
`sub := nat -> exp`), so their algebra is a body of *equations* rather than
constructors, and the tactics here are what prove and apply them. Two rewrite
databases and their drivers:

| Tactic | Line | Description |
| --- | --- | --- |
| `reduce_index` | 78 | `autorewrite with sb_index in *`. The `sb_index` database computes an operation *at an index*: `sb_q` at `0` and at `S _`, `exp_wk`/`exp_sub` at a variable. This is what turns a pointwise goal into arithmetic. |
| `simpl_sub` | 904 | `autorewrite with sb in *`. The `sb` database is the algebra proper — identity, composition, and how an operation meets `↑`, `,,` and `q`. The composition laws are registered as **rewrites** rather than resolution hints on purpose: as hints they would let `eauto` loop. |
| `unfold_ops` | 132 | `cbv beta delta` over every operation *and* over `wk_eq`/`sb_eq`/`pointwise_relation`. Unlike rewriting it reaches under the `forall` of a pointwise hypothesis, which is why `reduce_index` alone is not enough. |
| `pointwise` | 137 | `intro x; destruct x; reduce_index` — the two cases every pointwise law splits into, leaving the operations *folded* for proofs that go on to rewrite with the laws. |
| `pointwise_solve` | 145 | Closes a pointwise goal outright, so it can afford `unfold_ops` first; then `reflexivity`/`lia`/`f_equal`. |
| `exp_ind_ext H lift` | 154 | One case of an induction over `exp` for a law in `_ext` (pointwise-premise) form. The variable case *is* the hypothesis `H`; every other case is a congruence closed by the IHs once `H` has been lifted under the binders by `lift`. The `a_natrec` successor branch binds two variables, so `lift` may be needed twice — `auto` handles that. |

### 3.2 Transporting judgments along an operation (`Core/Syntactic/System/Lemmas.v`)

The algebra above is about *equality* of expressions; these are about pushing a
judgment through an operation — `wk_preserves_wf` (weakening preserves the
judgments), `sub_preserves_wf` (substitution does), and `sub_eq_preserves_exp`
(equivalent substitutions do). All three are one `induction 1` followed by the
same pipeline, which is why each family appears three times: `_wk`, `_sub`,
`_sub_eq`.

```coq
induction 1; intros; saturate_sub_eq; push_sub; lift_sub_eq; saturate_sub_eq;
  saturate_sub_typ; saturate_sub_eq_IH; reduce_sub_natrec.
all: mauto 3.
```

| Family | Lines | Description |
| --- | --- | --- |
| `saturate_wk`, `saturate_sub`, `saturate_sub_eq` | 92, 97, 1171 | Add the domain and codomain well-formedness of every operation in the context. `wf_sub_dom`/`wf_sub_cod` are **deliberately not** `mctt` hints, so these are how you get them; the canonical opening of a gluing proof is `assert Δ ⊢s σ : Γ by mauto 3. saturate_sub.` |
| `push_wk_step`, `push_wk_in`, `push_wk_goal`, `push_wk` | 205, 210, 213, 225 | Move an operation **inward**, toward the leaves: the induction hypothesis produces it on the outside, the rule to be applied wants it on the inside. Alternates `simpl` (which distributes over the term formers) with the `Substitution.v` corollaries that move it past a substitution. Uses `setoid_rewrite` throughout, because the induction hypotheses are still quantified over the target context and plain `rewrite` will not descend under a binder. |
| `push_sub_step`, `push_sub_in`, `push_sub_goal`, `push_sub` | 523, 529, 532, 540 | The same for substitutions. |
| `lift_wk_nat`, `lift_wk_step`, `lift_wk` | 245, 253, 262 | Saturate with the **lifted** operations `q φ`, one `assert` per binder. `wf_wk_q` *is* a hint, but reconstructing `q φ` inside the `eauto` search costs three levels on top of the rule application, which puts the wide cases (`λ`-E, `ℕ`-E) out of reach at any terminating depth. `lift_wk_nat` seeds the `ℕ`-eliminator cases separately: their first binder is over the closed type `ℕ`, which has no induction hypothesis of its own for `lift_wk_step` to use. |
| `lift_sub_nat`, `lift_sub_step`, `lift_sub` | 551, 559, 568 | Ditto for substitutions. |
| `lift_sub_eq_nat`, `lift_sub_eq_step`, `lift_sub_eq` | 1292, 1300, 1309 | Ditto for substitution equivalences. |
| `lift_wk_natrec`, `lift_sub_natrec`, `reduce_sub_natrec` | 271, 576, 1339 | The successor branch of the `ℕ`-eliminator, which is typed at the motive under *two* binders and so needs `A[q σ][Wk⨟Wk,,succ #1]` where the IH gives `A[Wk⨟Wk,,succ #1][q (q σ)]`. `push_sub` cannot do it: `exp_sub_sub_natrec` applies only to a doubly lifted substitution, and in the IH the substitution is still quantified. So instantiate at what `lift_sub` built, then rewrite. It also cannot join the `push_sub` set — it rewrites in the opposite direction from `exp_sub_extend_comm` and the two would loop. |
| `saturate_sub_typ`, `saturate_sub_eq_IH` | 1319, 1327 | The counterparts of `push_sub`/`lift_sub` for the *equivalence* induction: transport every type premise along every substitution in context, and instantiate every induction hypothesis at every substitution equivalence in context. Together they leave all premises of the congruence rule literally in the context, so the search never has to guess a domain type through an evar. |

### 3.3 Presuppositions

McTT's judgments are *not* presupposition-free: from `Γ ⊢ M : A` you can
derive `⊢ Γ` and `∃ i, Γ ⊢ A : Type@i`, and so on. Proofs constantly need
those side facts, so there is machinery to add all of them at once.

`Core/Syntactic/System/Tactics.v`:

| Tactic | Line | Description |
| --- | --- | --- |
| `invert_wf_ctx1 H` | 22 | From `⊢ Γ ▹ A` derive `⊢ Γ` and `∃ i, Γ ⊢ A : Type@i` via `ctx_decomp`, but *skip* introducing the level if an equivalent hypothesis (marked or not) is already present. |
| `invert_wf_ctx` | 38 | `invert_wf_ctx1` on every hypothesis, then `clear_dups`. |
| `gen_core_presup H` | 47 | The core presupposition generator, one case per judgment form: `⊢ Γ ≈ Δ` ⇒ `presup_ctx_eq`; `⊢ Γ ⊆ Δ` ⇒ `presup_ctx_sub`; `Γ ⊢ M : A` ⇒ `presup_exp`; `Γ ⊢s σ : Δ` ⇒ `presup_sub`. |
| `gen_lookup_presup H` | 63 | From `Γ ∋ #x : A` derive `∃ i, Γ ⊢ A : Type@i`, unless already known. |
| `gen_core_presups` | 76 | Run `gen_core_presup` on everything, `invert_wf_ctx`, then `gen_lookup_presup` on everything, then dedupe. |

`Core/Syntactic/Presup.v` extends this to the equality judgments, which are
proved by mutual induction, so the induction hypotheses must be passed in
explicitly:

| Tactic | Line | Description |
| --- | --- | --- |
| `gen_presup1 H` | 167 | The equality cases: `Γ ⊢ M ≈ N : A` via `presup_exp_eq`, `Γ ⊢ A ⊆ A'` via `presup_subtyp`, and `wf_sub_eq` via its two projections. The first two then call `gen_core_presup` on the left-hand typing they just produced, so `⊢ Γ` and the type of the equation come along too — which is what the old four-way-conjunction version gave for free. |
| `gen_presup H` | 188 | `first [ gen_presup1 H \| gen_core_presup H ]`. |
| `gen_presups` | 190 | **The one to use in proofs.** Every presupposition of every hypothesis, then `invert_wf_ctx`, lookup presuppositions, `saturate_wk`, `saturate_sub`, `clear_dups`. |

Related:

| Tactic | Location | Description |
| --- | --- | --- |
| `saturate_ctx_sub` | `Core/Syntactic/CtxSub.v:121` | For every `⊢ Γ ⊆ Δ` in the context add its four consequences — `ctx_sub_escape` (the refinement substitution `Γ ⊢s Id : Δ`), `ctx_sub_dom`, `ctx_sub_cod`, `ctx_sub_length` — then dedupe. |
| `impl_opt_constructor` | `Core/Syntactic/SystemOpt.v:68` | `intros; gen_presups; mautosolve 4`. Proves the "optimized" typing rules in `SystemOpt.v` — variants with fewer premises, since the missing premises are recoverable as presuppositions. Each is then swapped into the `mctt` database in place of the original (`Hint Resolve` + `Remove Hints`). |
| `apply_subtyping` | `Algorithmic/Subtyping/Lemmas.v:9` | From `Γ ⊢ M : A` and `Γ ⊢ A ⊆ B`, derive `Γ ⊢ M : B` and clear the original. |

---

## 4. Semantic layer: PER tactics

The semantics is a PER model: `per_univ_elem i R a b` says `a` and `b` are
related types at level `i` whose element relation is `R`. Two facts drive all
the tactics here:

- **Irrelevance.** If two derivations agree on one side, their element
  relations are equivalent (`per_univ_elem_left_irrel`, `_right_irrel`,
  `_cross_irrel`). Since `R` is an output, you constantly end up with two
  names for the same relation and must identify them.
- `per_univ_elem` is defined by `Equations`, so constructing and inverting it
  requires `simp`.

### 4.1 Relation-equivalence plumbing (`Core/Semantic/PER/Lemmas.v`)

| Tactic | Line | Description |
| --- | --- | --- |
| `rewrite_relation_equivalence_left` | 267 | For each `H : R₁ <~> R₂`, `setoid_rewrite H` in the goal and in every *other* hypothesis, then hide `H` behind `fold (id T)` so the `repeat` does not re-select it; `unfold id in *` at the end. |
| `rewrite_relation_equivalence_right` | 276 | Same, rewriting right-to-left. |
| `clear_relation_equivalence` | 285 | Discard `H : R₁ <~> R₂` when it is trivial (`R₁` and `R₂` unify) or when either side is a local variable — clearing the variable too, which effectively substitutes it away. |
| `apply_relation_equivalence` | 291 | The composite you actually call: clear, rewrite right, clear, rewrite left, clear. |
| `use_relation_equivalence` | 303 | Closes `R₁ x y` from `H : R₁ <~> R₂` (or the mirror) by `apply H`. Needed because `apply_relation_equivalence` only ever *rewrites*, and `setoid_rewrite` leaves the conclusion untouched when both sides of the `<~>` are applications — as the head relations `head_rel _ _ D` of a context PER are, for two different witnesses. |

### 4.2 Irrelevance saturation

| Tactic | Line | Description |
| --- | --- | --- |
| `per_univ_elem_right_irrel_assert1` / `…_assert` | 331, 343 | For two derivations sharing *both* domain arguments, assert `R₁ <~> R₂`; skip if `R₁` and `R₂` unify or the equivalence is already known (in either direction). |
| `do_per_univ_elem_irrel_assert1` | 430 | Three cases — shared left argument (`_right_irrel`), shared right argument (`_left_irrel`), left of one equal to right of the other (`_cross_irrel`) — each guarded against re-derivation. |
| `do_per_univ_elem_irrel_assert` | 460 | `repeat` of the above. |
| `handle_per_univ_elem_irrel` | 463 | **The composite.** `functional_eval_rewrite_clear`, saturate irrelevance, `apply_relation_equivalence`, `clear_dups`. In effect: "make all the relation names in my context the same one." |
| `do_per_ctx_env_irrel_assert1` / `…_assert` | 966, 996 | Same three cases for `per_ctx_env` (environment relations). |
| `handle_per_ctx_env_irrel` | 999 | Composite, as above, for contexts. |

### 4.3 Construction and inversion

| Tactic | Location | Description |
| --- | --- | --- |
| `basic_per_univ_elem_econstructor` | `PER/CoreTactics.v:54` | `simp per_univ_elem; econstructor; try rewrite <- per_univ_elem_equation_1 in *` — unfold one `Equations` step, apply a constructor, fold the recursive occurrences back. |
| `basic_invert_per_univ_elem H` | `PER/CoreTactics.v:49` | The dual: `simp` in `H`, `dependent destruction`, fold back. |
| `per_univ_elem_econstructor` | `PER/Lemmas.v:634` | Try the smart `Π` constructor `per_univ_elem_pi'` first (`repeat intro; hnf; eapply …`), else fall back to the basic one. |
| `invert_per_univ_elem H` | `PER/Lemmas.v:675` | Try `per_univ_elem_pi_clean_inversion` — which yields the `out_rel` and the elem-relation equivalence directly, instead of the raw constructor equations — else `basic_invert_per_univ_elem`. |
| `per_ctx_env_econstructor` | `PER/Lemmas.v:1097` | Same pattern for contexts: try `per_ctx_env_cons'`, else `econstructor`. |
| `invert_per_ctx_env H` | `PER/Lemmas.v:1136` | Try `per_ctx_env_cons_clean_inversion`, else plain `inversion H; subst`. |
| `def_simp` | `PER/Definitions.v:215` | `simp per_univ_elem in *; mauto 3` — the `#[tactic="def_simp"]` used to discharge obligations of the hand-rolled induction principle `per_univ_elem_ind`. |

### 4.4 Destructing "for all related arguments" hypotheses

Semantic function types produce hypotheses of shape
`forall c c', in_rel c c' -> rel_mod_eval …`. You almost never want to
instantiate those by hand.

| Tactic | Location | Description |
| --- | --- | --- |
| `destruct_rel_by_assumption in_rel H` | `PER/CoreTactics.v:9` | For every hypothesis `Dom c ≈ c' ∈ in_rel` in the context, specialize `H` to it, destruct the result, and `destruct_all`. Marks at level 1 so each argument pair is used once. |
| `destruct_rel_mod_eval` | `PER/CoreTactics.v:19` | Apply the above to every `rel_mod_eval`-valued hypothesis, and `dependent destruction` any bare `rel_mod_eval`. |
| `destruct_rel_mod_app` | `PER/CoreTactics.v:28` | Same for `rel_mod_app`. |
| `destruct_rel_typ` | `PER/CoreTactics.v:37` | Same for `rel_typ`. |

### 4.5 Relation chains (`Core/Semantic/PER/Chain.v`)

Most of the completeness invariants are naturally stated as a *set* of values all
consecutively related, the four-value pattern
`{⟦t[σ]⟧ρ, ⟦t⟧(⟦σ⟧ρ), ⟦t'⟧(⟦σ'⟧ρ'), ⟦t'[σ']⟧ρ'} ⊆ 𝑅_T` chief among them.
`rel_chain R l` is that, over a `list`. Because `R` is a PER, the order and any
repetition are immaterial — `rel_chain_pairwise` and `rel_chain_merge` are what
make that formal, and these three tactics are the whole intended API of `Chain.v`.

| Tactic | Line | Description |
| --- | --- | --- |
| `pairwise` | 360 | Closes `R x y` from any `rel_chain` hypothesis about `R`, whichever two of its members `x` and `y` are. `first` over the remaining goals rather than a positional `[ \| \| ]`, because the `PER` obligation may or may not survive to become one. The relation is matched in the **goal** first and only failing that left to the `eapply` to unify (`pairwise_from`, line 356): a goal an `eapply` produced before it could fix the universe level or the element PER has a metavariable where `R` should be, which the syntactic match cannot see. |
| `solve_rel_chain` | 371 | Closes a `rel_chain` goal all of whose members occur in **one** hypothesis, by `pairwise` or else `rel_chain_incl`. |
| `merge_rel_chain H1 H2 c` | 388 | Closes a `rel_chain` goal whose members are spread over **two** hypotheses: merge them along the shared value `c`, then select. Everything is positional because nothing can be guessed — `rel_chain_merge` leaves *both* chain premises with a metavariable list, so a search tactic would put the same hypothesis in both and only fail later at the inclusion, and `c` is not determined by the goal at all. |

Two tactics in `Core/Semantic/PER/Lemmas.v` mechanize *weak functionality* — the
paper's `S ⊆_R ↘ R'`, which says a chain in `per_univ i` determines one output
PER on inhabitants, the same for every pair of the chain. `per_univ i` is what a
semantic *type* judgment hands over, with each link carrying its own existential
element PER; these move to the single PER weak functionality promises:

| Tactic | Location | Description |
| --- | --- | --- |
| `functionalize_per_univ_chain H R` | `Core/Semantic/PER/Lemmas.v:635` | Names the element PER of a chain in `per_univ i` and refines the chain to it in place, via `per_univ_chain_functional` (the *existence* half). Takes no anchor and loses nothing: every pair remains available, at `R`, through `pairwise`. |
| `pairwise_univ` | `Core/Semantic/PER/Lemmas.v:640` | `pairwise` at a `per_univ i` goal, whose existential the refined chain no longer carries. |
| `retype_rel_chain Htyp Hanchor H` | `Core/Semantic/PER/Lemmas.v:665` | Moves `H` between the element PER the type chain `Htyp` reported and the one `Hanchor` names, via `per_univ_chain_rel_irrel` (the *uniqueness* half). The two need share only one value, and only `H` says which direction is wanted, so both are tried. `H` may be a chain — `rel_chain_Proper` is what rewrites it — or a bare pair. Replaces the recurring three-step `rel_chain_4_related` / `per_univ_elem_*_irrel` / `rewrite` idiom. |

Three more build on the `Chain.v` tactics for the case the semantic rules
actually need — a chain of *environments*:

| Tactic | Location | Description |
| --- | --- | --- |
| `destruct_per_univ_chain H` | `Core/Semantic/PER/Lemmas.v:1590` | Splits a four-value chain in `per_univ i` into its three links, going through `per_univ_chain_functional` first so the three come out at *one* element PER rather than three independent existential ones. |
| `solve_per_head` | `Core/Semantic/PER/Lemmas.v:1595` | Discharges the head component of `per_env_extend_intro'`: introduce the two extended environments and the `per_univ_elem` relating the two type values, identify its outputs by `functional_eval_rewrite_clear`, let `handle_per_univ_elem_irrel` identify its PER with the one the term chain lives in, then read the pair off that chain with `pairwise`. |
| `solve_per_env_extend_chain` | `Core/Semantic/PER/Lemmas.v:1605` | The whole last step of an extended-context rule: split every link of the goal chain with `per_env_extend_intro'`, take the tails off the chain the underlying substitution arrived with (`pairwise`) and bridge the heads (`solve_per_head`). Length-agnostic, because the four-value pattern wants four environments while the rules with a premise in an extended context want every extension of the four tails by either head. |

Two side-condition solvers in `Chain.v` support all of them: `solve_in` (line 46,
membership in a literal list) and `solve_incl` (line 52,
`forall x, In x L -> In x L'` for literal `L`, `L'`).

**The `PER R` argument is the trap.** Every chain lemma takes one, and `apply`
does *not* reliably resolve it: the relations involved are context and element
PERs whose instances (`per_env_PER`, `per_elem_PER`) must be found from a
*hypothesis*, not from the goal, which the resolution `apply` performs will not
do. Hence `solve_chain_PER` (line 339, `solve [typeclasses eauto]`) and its
appearance in every tactic above. Worse, an `eapply` that cannot resolve the
argument does not fail: it **shelves** it, so the tactic reports success and you
learn about the hole only at `Qed`, as `Attempt to save an incomplete proof` —
which is why `pairwise_from` and `solve_rel_chain` wrap their `eapply` in
`unshelve`, turning the instance back into a goal `solve_chain_PER` must close.
The relations that really are not PERs — `per_pi` at a domain PER, say — are the
ones this catches, and there the PER-free `rel_chain_4_*` projections are what to
use. If you write another chain tactic, do the same.

---

## 5. Completeness layer: witness skeletons

A completeness judgment `Γ ⊨ M ≈ M' : A` unfolds to a nest of existentials:
an environment relation, a `per_ctx_env` derivation for it, a universe level,
then the per-environment body. The `eexists_*` tactics are exactly the
boilerplate for opening that nest — `eexists` for the outputs, `eassumption`
for the `per_ctx_env` premise you already have.

`Core/Completeness/LogicalRelation/Tactics.v`:

| Tactic | Line | Description |
| --- | --- | --- |
| `eexists_rel_exp` | 6 | `eexists; eexists; [eassumption \|]; eexists` — the skeleton for `Γ ⊨ M ≈ M' : A`. |
| `eexists_rel_exp_with i` | 11 | Same, but commits to universe level `i` instead of leaving an evar. |
| `eexists_rel_sub` | 16 | Skeleton for the substitution judgment (two `eassumption` premises). |
| `eexists_rel_wk` | 25 | The same tactic, for `rel_wk_under_ctx`: it has the same outer shape as `rel_sub_under_ctx` — two environment PERs, each with its context witness read off the goal. |
| `eexists_subtyp` / `eexists_subtyp_with i` | 27, 32 | Skeletons for semantic subtyping. |
| `invert_rel_typ_body` | 37 | **The main workhorse of the completeness proofs.** `simplify_evals`, then `directed invert_per_univ_elem` on every `per_univ_elem` hypothesis, `subst`, `clear_dups`, `clear_refl_eqs`, `handle_per_univ_elem_irrel`, `clear_dups`, and fold `per_univ_elem_equation_1` back. |

Case-specific skeletons, each `apply`ing the corresponding "of" lemma before
opening the existentials:

| Tactic | Location |
| --- | --- |
| `eexists_rel_exp_of_typ` | `Core/Completeness/UniverseCases.v:207` |
| `eexists_rel_exp_of_nat` | `Core/Completeness/NatCases.v:146` |

Plus:

| Tactic | Location | Description |
| --- | --- | --- |
| `solve_it` | `Core/Completeness/FundamentalTheorem.v:49` | `pose proof completeness_fundamental; firstorder` — projects each individual fundamental-theorem corollary out of the mutually proved conjunction. |

---

## 6. Soundness layer: glue tactics

Soundness uses a glued (Kripke) logical relation: `glu_univ_elem i P El a`
pairs a *type* predicate `P` with an *element* predicate `El`, and
`glu_ctx_env Sb Γ` gives the substitution predicate for a context. `P`, `El`,
`Sb` are all outputs, so this layer needs the same identify-and-substitute
machinery as the PER layer, with `<∙>` (predicate equivalence) in place of
`<~>`.

### 6.1 Predicate equivalence (`Core/Soundness/LogicalRelation/CoreLemmas.v`)

| Tactic | Line | Description |
| --- | --- | --- |
| `rewrite_predicate_equivalence_left` / `…_right` | 382, 391 | Mirror of the `relation_equivalence` versions, for `H : R₁ <∙> R₂`. |
| `clear_predicate_equivalence` | 400 | Mirror of `clear_relation_equivalence`. |
| `apply_predicate_equivalence` | 406 | Composite: clear, rewrite right, clear, rewrite left, clear. |

### 6.2 Functionality of the glue relations

| Tactic | Line | Description |
| --- | --- | --- |
| `apply_functional_glu_univ_elem1` / `…_elem` | 511, 527 | Two `glu_univ_elem` derivations for the same `a` at the same level ⇒ assert `(P₁ <∙> P₂) /\ (El₁ <∙> El₂)`, guarded against re-derivation. |
| `handle_functional_glu_univ_elem` | 530 | **Composite.** `functional_eval_rewrite_clear`, re-`fold` the `glu_typ_pred`/`glu_exp_pred` abbreviations (needed for the patterns to match after `simp`), saturate functionality, `apply_predicate_equivalence`, `clear_dups`. |
| `apply_functional_glu_ctx_env1` / `…_env` | `Lemmas.v:829, 841` | Same for `glu_ctx_env`: two derivations for the same `Γ` give `Sb₁ <∙> Sb₂`. |
| `handle_functional_glu_ctx_env` | `Lemmas.v:844` | Composite, as above. |

### 6.3 Construction and inversion

| Tactic | Location | Description |
| --- | --- | --- |
| `basic_glu_univ_elem_econstructor` | `CoreTactics.v:12` | `simp glu_univ_elem; econstructor;` fold back. |
| `basic_invert_glu_univ_elem H` | `CoreTactics.v:7` | The dual. |
| `glu_univ_elem_econstructor` | `CoreLemmas.v:369` | Try `glu_univ_elem_core_univ'` first, else the basic constructor. |
| `invert_glu_univ_elem H` | `CoreLemmas.v:632` | Three-way fallback: `glu_univ_elem_pi_clean_inversion2`, then `…1`, then `basic_invert_glu_univ_elem`. The clean inversions hand back `IP`/`IEl`/`OP`/`OEl` and the two predicate equivalences directly. |
| `invert_glu_rel1` | `CoreTactics.v:17` | `progressive_invert` any `pi_glu_typ_pred` / `pi_glu_exp_pred` / `neut_glu_typ_pred` / `neut_glu_exp_pred` hypothesis. |
| `simpl_glu_rel` | `CoreLemmas.v:100` | **The standard opening move for a glue lemma.** `apply_equiv_left`, `repeat invert_glu_rel1`, `apply_equiv_left`, `destruct_all`, `gen_presups`. |
| `invert_glu_ctx_env H` | `Lemmas.v:875` | Try `glu_ctx_env_cons_clean_inversion`, else `dependent destruction`. |

### 6.4 Saturation

| Tactic | Location | Description |
| --- | --- | --- |
| `saturate_glu_by_per1` / `saturate_glu_by_per` | `CoreLemmas.v:684, 696` | Transport a `glu_univ_elem i P El a` along a `per_univ_elem i _ a a'` (in either direction) to get the glue predicate for the other value. |
| `saturate_glu_info1` / `saturate_glu_info` | `CoreLemmas.v:751, 763` | Extract the syntactic consequences of glue membership: from `P Γ A` get `Γ ⊢ A : Type@i` (`glu_univ_elem_univ_lvl`), from `El …` get the typing of the term (`glu_univ_elem_trm_escape`). |
| `saturate_kripke_escape` | `Weakening/Lemmas.v:26` | For every Kripke weakening `Γ ⊢k φ : Δ` add `kripke_escape`, i.e. `Γ ⊢s ι φ : Δ`. Because `wf_sub_dom`/`wf_sub_cod` are not hints, this must be **followed by `saturate_sub`** to get the two contexts. |
| `saturate_kripke` | `Weakening/Lemmas.v:245` | The same for `kripke_dom`/`kripke_cod` directly. Those two are deliberately not hints either — `eauto` would cycle them against the context introduction rules. |

### 6.5 Judgment-level destruction and inversion (`Core/Soundness/LogicalRelation/Lemmas.v`)

| Tactic | Line | Description |
| --- | --- | --- |
| `destruct_glu_rel_by_assumption sub_glu_rel H` | 996 | The `glu` analogue of `destruct_rel_by_assumption`: for every `Δ ⊢s σ ® ρ ∈ Sb` in the context, instantiate `H` and destruct. |
| `destruct_glu_rel_exp_with_sub` | 1006 | Apply it to every `glu_rel_exp_with_sub`-valued hypothesis; also destruct bare ones. |
| `destruct_glu_rel_typ_with_sub` | 1015 | Same for `glu_rel_typ_with_sub`. |
| `invert_glu_rel_exp H` | 1069 | Fallback chain over `glu_rel_exp_clean_inversion2`, `…1`, then `inversion`. The "clean" versions require a `glu_ctx_env` (and for `2` also a typing) premise, which they discharge by `eassumption`, and give back a single universe level instead of an existential. |
| `def_simp` | `Soundness/LogicalRelation/Definitions.v:233` | `simp glu_univ_elem in *; mauto 3`, the obligation tactic for `glu_univ_elem_ind`. |
| `solve_it` | `Core/Soundness/FundamentalTheorem.v:29` | `pose proof soundness_fundamental; firstorder`. |

### 6.6 Two deliberate redefinitions

`invert_glu_rel_exp` is **redefined** (with `::=`, Ltac1's redefinition
syntax) twice as the development proceeds and stronger clean-inversion lemmas
become available:

- `Core/Soundness/UniverseCases.v:56` prepends `glu_rel_exp_clean_inversion2'`,
  which only needs `Γ ⊩ Type@i : Type@(S i)` — automatically available —
  rather than an explicit typing premise.
- `Core/Soundness/NatCases.v:61` prepends `glu_rel_exp_clean_inversion2''`
  for `ℕ`, on top of the universe version.

So the meaning of `invert_glu_rel_exp` at a given point in the file tree
depends on which of these files has been loaded. Both redefinitions only ever
*add* earlier alternatives to the `+` chain, so they strictly strengthen it.

---

## 7. Extraction layer: obligation tactics

The extraction-facing code in `theories/Extraction/` defines the actual
executable functions with `Equations`, indexed by an "order" (accessibility)
predicate that witnesses termination, and returning a subset type carrying the
soundness proof — e.g.

```coq
Equations eval_exp_impl m p (H : eval_exp_order m p) : { d | eval_exp m p d } by struct H
```

Each such definition names an obligation tactic in
`#[tactic="impl_obl_tac"]`. They all follow the same recipe: invert the order
predicate to expose the recursive sub-orders, then `econstructor; mauto`.

| Tactic | Location | Description |
| --- | --- | --- |
| `impl_obl_tac1` / `impl_obl_tac` | `Extraction/Evaluation.v:96, 104` | Inverts `eval_exp_order`, `eval_natrec_order`, `eval_app_order`, `eval_sub_order`; then `try econstructor; eauto`. |
| `impl_obl_tac1` / `impl_obl_tac` | `Extraction/Readback.v:102, 110` | Same for `read_nf_order`, `read_ne_order`, `read_typ_order`. |
| `impl_obl_tac1` / `impl_obl_tac` | `Extraction/NbE.v:35/41`, `123/129`, `181/187` | Three separate copies inside three `Section`s, for `initial_env_order`, `nbe_order`, and `nbe_ty_order` respectively. |
| `subtyping_tac` | `Extraction/Subtyping.v:9` | Obligations of the *decision* procedure `subtyping_nf_impl`: for a positive goal `⊢anf A ⊆ B`, `subst; mauto 4; try congruence; econstructor`; for a negative goal, introduce, `dependent destruction`, and close by `lia`/`congruence`. |
| `subtyping_impl_tac1` / `subtyping_impl_tac` | `Extraction/Subtyping.v:69, 76` | Inverts `subtyping_order` and `nbe_ty_order`; then `econstructor; mauto`. |
| `impl_obl_tac1` / `impl_obl_tac` | `Extraction/TypeCheck.v:14, 23` | For `lookup`: introduce negations, invert `⊢ Γ ▹ A` and impossible `⋅ ∋ #x : A` / `Γ ▹ A ∋ #(S x) : A` hypotheses, then `intuition (mauto 4)`. |
| `clear_defs` | `Extraction/TypeCheck.v:83` | Housekeeping: `Equations` leaves the mutual recursive-call hypotheses and `let H := fixproto in …` bindings in every obligation context, where they confuse `mauto`. This clears them by matching their (spelled-out) types. |
| `impl_obl_tac` | `Extraction/TypeCheck.v:121` | The big one — obligations of `type_check` / `type_infer`. `clear_defs`, invert the order predicates, `destruct_conjs`, then dispatch on the goal: well-formedness and typing goals via `gen_presups; mautosolve 4`; universe-level maxima via `lift_exp_max_left/right`; negative goals by inverting the algorithmic derivation and using `functional_alg_type_infer_rewrite_clear`; `subtyping_order` goals by routing through `soundness_ty` and `nbe_ty_order_sound`. |
| `impl_obl_tac` | `Extraction/TypeCheck.v:394` | Obligations of `type_check_closed`: `unfold not in *; intros; mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order`. |
| `impl_obl_tac` | `Entrypoint.v:31` | `try eassumption` — the top-level `main` needs nothing more. |

Completeness of the extracted functions is proved by a third pattern: assert
the order predicate, run the function, and use functionality to identify the
result.

| Tactic | Location | Description |
| --- | --- | --- |
| `functional_eval_complete` | `Extraction/Evaluation.v:161` | For a goal `exists H H', f x H = exist _ m H'`: `assert` the order predicate by `mauto 3`, `eexists` it, `destruct` the call, `functional_eval_rewrite_clear`, `eexists; reflexivity`. |
| `functional_read_complete` | `Extraction/Readback.v:174` | Same, with `functional_read_rewrite_clear`. |
| `functional_nbe_complete` | `Extraction/NbE.v:75` | Same, with `functional_nbe_rewrite_clear`. |

The `let*b` / `let*o` / `let*b->o` / `let*o->b` / `pureb` / `pureo` notations
these definitions are written in are *not* tactics — they are the
pseudo-monadic notations for `sumbool`/`sumor` in
`Extraction/PseudoMonadic.v`.

---

## 8. Gotchas

- **Marking levels must nest.** `unmark_all_with n` skips marks at other
  levels, so two loops that mark at the same level will interfere. The
  convention is: level 0 for `on_all_hyp:`, level 1 inside
  `destruct_rel_by_assumption` / `destruct_glu_rel_by_assumption`, level 100
  for `progressive_inversion`. Pick a fresh level if you add a new loop.
- **`fail_if_dup` is a loop terminator, not an assertion.** It is meant to
  fail. If you copy a saturation tactic and drop it, you get a
  non-terminating `repeat`.
- **`clean replace` fails on a no-op** by design. Do not "fix" that.
- **`directed` is load-bearing.** Removing it from a `progressive_invert`
  turns a well-behaved inversion into an unpredictable case split.
- **`invert_glu_rel_exp` is not one tactic.** See *Two deliberate
  redefinitions* — its meaning depends
  on whether `Soundness/UniverseCases.v` and `Soundness/NatCases.v` are in
  scope.
- **`Extraction/TypeCheck.v:115` (`impl_obl_tac_helper`) is dead code** — it
  is defined and never referenced. `impl_obl_tac` at line 121 inlines the same
  `type_infer_order` inversion.
- **`clear_defs` hard-codes the types it clears.** If the signature of
  `type_check`/`type_infer` changes, its `lazymatch` patterns silently stop
  matching and the obligations start failing in confusing ways.
- **Rocq 9.2 deprecations.** The sources use `...` as the `Proof with`
  end-tactic in 237 places, which Rocq 9.2 reports as
  `deprecated-end-tac`. It still works; a future cleanup would replace
  `foo...` with `foo; <the end tactic>.`. Note that `...` is an *error*, not a
  warning, in a plain `Proof.` block with no `with` clause.

---

## 9. Index

Alphabetical, with definition sites. Paths are relative to `theories/`.

| Tactic | Location |
| --- | --- |
| `apply_equiv_left`, `apply_equiv_left1` | `LibTactics.v:339, 328` |
| `apply_equiv_right`, `apply_equiv_right1` | `LibTactics.v:353, 342` |
| `apply_functional_glu_ctx_env`, `…1` | `Core/Soundness/LogicalRelation/Lemmas.v:841, 829` |
| `apply_functional_glu_univ_elem`, `…1` | `Core/Soundness/LogicalRelation/CoreLemmas.v:527, 511` |
| `apply_predicate_equivalence` | `Core/Soundness/LogicalRelation/CoreLemmas.v:406` |
| `apply_relation_equivalence` | `Core/Semantic/PER/Lemmas.v:291` |
| `apply_subtyping` | `Algorithmic/Subtyping/Lemmas.v:9` |
| `basic_glu_univ_elem_econstructor` | `Core/Soundness/LogicalRelation/CoreTactics.v:12` |
| `basic_invert_glu_univ_elem` | `Core/Soundness/LogicalRelation/CoreTactics.v:7` |
| `basic_invert_per_univ_elem` | `Core/Semantic/PER/CoreTactics.v:49` |
| `basic_per_univ_elem_econstructor` | `Core/Semantic/PER/CoreTactics.v:54` |
| `bulky_rewrite`, `…1`, `…_in`, `…_in1` | `LibTactics.v:471, 465, 479, 473` |
| `clean replace … with … by …` | `LibTactics.v:158` (impl. `clean_replace_by`, 149) |
| `clear_defs` | `Extraction/TypeCheck.v:83` |
| `clear_dups` | `LibTactics.v:106` |
| `clear_PER` | `LibTactics.v:356` |
| `clear_predicate_equivalence` | `Core/Soundness/LogicalRelation/CoreLemmas.v:400` |
| `clear_relation_equivalence` | `Core/Semantic/PER/Lemmas.v:285` |
| `cutexec` | `LibTactics.v:286` |
| `dec_complete` | `LibTactics.v:483` |
| `deepexec` | `LibTactics.v:266` |
| `def_simp` | `Core/Semantic/PER/Definitions.v:215`; `Core/Soundness/LogicalRelation/Definitions.v:233` |
| `destruct_all`, `destruct_logic` | `LibTactics.v:77, 67` |
| `destruct_by_head`, `dir_destruct_by_head` | `LibTactics.v:192, 193` |
| `destruct_glu_rel_by_assumption` | `Core/Soundness/LogicalRelation/Lemmas.v:996` |
| `destruct_glu_rel_exp_with_sub` | `Core/Soundness/LogicalRelation/Lemmas.v:1006` |
| `destruct_glu_rel_typ_with_sub` | `Core/Soundness/LogicalRelation/Lemmas.v:1015` |
| `destruct_per_univ_chain` | `Core/Semantic/PER/Lemmas.v:1590` |
| `destruct_rel_by_assumption` | `Core/Semantic/PER/CoreTactics.v:9` |
| `destruct_rel_mod_app`, `…_eval`, `destruct_rel_typ` | `Core/Semantic/PER/CoreTactics.v:28, 19, 37` |
| `directed` | `LibTactics.v:110` (notation 116) |
| `do_per_ctx_env_irrel_assert`, `…1` | `Core/Semantic/PER/Lemmas.v:996, 966` |
| `do_per_univ_elem_irrel_assert`, `…1` | `Core/Semantic/PER/Lemmas.v:460, 430` |
| `eexists_rel_exp`, `…_with` | `Core/Completeness/LogicalRelation/Tactics.v:6, 11` |
| `eexists_rel_exp_of_nat` | `Core/Completeness/NatCases.v:146` |
| `eexists_rel_exp_of_typ` | `Core/Completeness/UniverseCases.v:207` |
| `eexists_rel_sub` | `Core/Completeness/LogicalRelation/Tactics.v:16` |
| `eexists_rel_wk` | `Core/Completeness/LogicalRelation/Tactics.v:25` |
| `eexists_subtyp`, `…_with` | `Core/Completeness/LogicalRelation/Tactics.v:27, 32` |
| `exp_ind_ext` | `Core/Syntactic/Substitution.v:154` |
| `exvar` | `LibTactics.v:250` |
| `fail_at_if_dup`, `fail_if_dup` | `LibTactics.v:100, 104` |
| `find_dup_hyp` | `LibTactics.v:89` |
| `find_head` | `LibTactics.v:161` |
| `functional_alg_type_infer_rewrite_clear`, `…1` | `Algorithmic/Typing/Lemmas.v:43, 37` |
| `functional_eval_complete` | `Extraction/Evaluation.v:161` |
| `functionalize_per_univ_chain` | `Core/Semantic/PER/Lemmas.v:635` |
| `functional_eval_rewrite_clear`, `…1` | `Core/Semantic/Evaluation/Lemmas.v:86, 73` |
| `functional_initial_env_rewrite_clear`, `…1` | `Core/Semantic/NbE.v:57, 51` |
| `functional_nbe_complete` | `Extraction/NbE.v:75` |
| `functional_nbe_rewrite_clear`, `…1` | `Core/Semantic/NbE.v:181, 171` |
| `functional_read_complete` | `Extraction/Readback.v:174` |
| `functional_read_rewrite_clear`, `…1` | `Core/Semantic/Readback/Lemmas.v:68, 58` |
| `gen` | `LibTactics.v:17–20` |
| `gen_core_presup`, `gen_core_presups` | `Core/Syntactic/System/Tactics.v:47, 76` |
| `gen_lookup_presup` | `Core/Syntactic/System/Tactics.v:63` |
| `gen_presup`, `gen_presup1`, `gen_presups` | `Core/Syntactic/Presup.v:188, 167, 190` |
| `glu_univ_elem_econstructor` | `Core/Soundness/LogicalRelation/CoreLemmas.v:369` |
| `handle_functional_glu_ctx_env` | `Core/Soundness/LogicalRelation/Lemmas.v:844` |
| `handle_functional_glu_univ_elem` | `Core/Soundness/LogicalRelation/CoreLemmas.v:530` |
| `handle_per_ctx_env_irrel` | `Core/Semantic/PER/Lemmas.v:999` |
| `handle_per_univ_elem_irrel` | `Core/Semantic/PER/Lemmas.v:463` |
| `impl_obl_tac`, `…1` | `Entrypoint.v:31`; `Extraction/Evaluation.v:104, 96`; `Extraction/NbE.v:41/35, 129/123, 187/181`; `Extraction/Readback.v:110, 102`; `Extraction/TypeCheck.v:23/14, 121, 394` |
| `impl_obl_tac_helper` (unused) | `Extraction/TypeCheck.v:115` |
| `impl_opt_constructor` | `Core/Syntactic/SystemOpt.v:68` |
| `inversion_by_head`, `dir_inversion_by_head` | `LibTactics.v:188, 189` |
| `inversion_clear_by_head`, `dir_inversion_clear_by_head` | `LibTactics.v:190, 191` |
| `invert_glu_ctx_env` | `Core/Soundness/LogicalRelation/Lemmas.v:875` |
| `invert_glu_rel1` | `Core/Soundness/LogicalRelation/CoreTactics.v:17` |
| `invert_glu_rel_exp` | `Core/Soundness/LogicalRelation/Lemmas.v:1069`; redefined `Core/Soundness/UniverseCases.v:59`, `Core/Soundness/NatCases.v:57` |
| `invert_glu_univ_elem` | `Core/Soundness/LogicalRelation/CoreLemmas.v:632` |
| `invert_per_ctx_env`, `invert_per_univ_elem` | `Core/Semantic/PER/Lemmas.v:1136, 675` |
| `invert_rel_typ_body` | `Core/Completeness/LogicalRelation/Tactics.v:37` |
| `invert_wf_ctx`, `…1` | `Core/Syntactic/System/Tactics.v:38, 22` |
| `lift_sub`, `lift_sub_nat`, `lift_sub_step` | `Core/Syntactic/System/Lemmas.v:568, 551, 559` |
| `lift_sub_eq`, `lift_sub_eq_nat`, `lift_sub_eq_step` | `Core/Syntactic/System/Lemmas.v:1309, 1292, 1300` |
| `lift_sub_natrec` | `Core/Syntactic/System/Lemmas.v:576` |
| `lift_wk`, `lift_wk_nat`, `lift_wk_step` | `Core/Syntactic/System/Lemmas.v:262, 245, 253` |
| `lift_wk_natrec` | `Core/Syntactic/System/Lemmas.v:271` |
| `mark`, `unmark`, `mark_all`, `unmark_all` | `LibTactics.v:27, 30, 32, 36` |
| `mark_with`, `mark_all_with`, `unmark_all_with` | `LibTactics.v:38, 41, 45` |
| `match_by_head`, `…1` | `LibTactics.v:186, 182` |
| `mauto` (10 overloads) | `LibTactics.v:197–224` |
| `mautosolve`, `mautosolve_impl` | `LibTactics.v:229–230, 227` |
| `merge_rel_chain` | `Core/Semantic/PER/Chain.v:388` |
| `not_let_bind` | `LibTactics.v:79` |
| `on_all_hyp:`, `on_all_hyp_rev:` | `LibTactics.v:60, 62` |
| `on_all_marked_hyp`, `…_rev` (+ notations) | `LibTactics.v:50, 54, 58, 59` |
| `pairwise` | `Core/Semantic/PER/Chain.v:360` |
| `pairwise_from` | `Core/Semantic/PER/Chain.v:356` |
| `pairwise_univ` | `Core/Semantic/PER/Lemmas.v:640` |
| `per_ctx_env_econstructor` | `Core/Semantic/PER/Lemmas.v:1097` |
| `per_univ_elem_econstructor` | `Core/Semantic/PER/Lemmas.v:634` |
| `per_univ_elem_right_irrel_assert`, `…1` | `Core/Semantic/PER/Lemmas.v:343, 331` |
| `pointwise`, `pointwise_solve` | `Core/Syntactic/Substitution.v:137, 145` |
| `progressive_inversion`, `progressive_invert`, `…_once` | `LibTactics.v:141, 118, 123` |
| `push_sub`, `…_step`, `…_in`, `…_goal` | `Core/Syntactic/System/Lemmas.v:540, 523, 529, 532` |
| `push_wk`, `…_step`, `…_in`, `…_goal` | `Core/Syntactic/System/Lemmas.v:225, 205, 210, 213` |
| `reduce_index` | `Core/Syntactic/Substitution.v:78` |
| `reduce_sub_natrec` | `Core/Syntactic/System/Lemmas.v:1339` |
| `retype_rel_chain` | `Core/Semantic/PER/Lemmas.v:665` |
| `rewrite_predicate_equivalence_left`, `…_right` | `Core/Soundness/LogicalRelation/CoreLemmas.v:382, 391` |
| `rewrite_relation_equivalence_left`, `…_right` | `Core/Semantic/PER/Lemmas.v:267, 276` |
| `saturate_ctx_sub` | `Core/Syntactic/CtxSub.v:121` |
| `saturate_glu_by_per`, `…1` | `Core/Soundness/LogicalRelation/CoreLemmas.v:696, 684` |
| `saturate_glu_info`, `…1` | `Core/Soundness/LogicalRelation/CoreLemmas.v:763, 751` |
| `saturate_kripke` | `Core/Soundness/Weakening/Lemmas.v:245` |
| `saturate_kripke_escape` | `Core/Soundness/Weakening/Lemmas.v:26` |
| `saturate_refl`, `saturate_refl_for` | `LibTactics.v:379, 391` |
| `saturate_sub`, `saturate_wk` | `Core/Syntactic/System/Lemmas.v:97, 92` |
| `saturate_sub_eq`, `saturate_sub_eq_IH` | `Core/Syntactic/System/Lemmas.v:1171, 1327` |
| `saturate_sub_typ` | `Core/Syntactic/System/Lemmas.v:1319` |
| `simpl_glu_rel` | `Core/Soundness/LogicalRelation/CoreLemmas.v:100` |
| `simpl_sub` | `Core/Syntactic/Substitution.v:904` |
| `simplify_evals` | `Core/Semantic/Evaluation/Tactics.v:15` |
| `simplify_subs` | `Core/Semantic/Evaluation/Tactics.v:13` |
| `solve_chain_PER` | `Core/Semantic/PER/Chain.v:339` |
| `solve_in`, `solve_incl` | `Core/Semantic/PER/Chain.v:46, 52` |
| `solve_it` | `Core/Completeness/FundamentalTheorem.v:49`; `Core/Soundness/FundamentalTheorem.v:29` |
| `solve_per_env_extend_chain` | `Core/Semantic/PER/Lemmas.v:1605` |
| `solve_per_head` | `Core/Semantic/PER/Lemmas.v:1595` |
| `solve_refl` | `LibTactics.v:404` |
| `solve_rel_chain` | `Core/Semantic/PER/Chain.v:371` |
| `strong_apply` | `LibTactics.v:321` |
| `subtyping_impl_tac`, `…1` | `Extraction/Subtyping.v:76, 69` |
| `subtyping_tac` | `Extraction/Subtyping.v:9` |
| `Tauto.intuition_solver` (redefinition) | `LibTactics.v:248` |
| `unfold_ops` | `Core/Syntactic/Substitution.v:132` |
| `unify_args` | `LibTactics.v:312` |
| `unify_by_head_of` | `LibTactics.v:167` |
| `use_relation_equivalence` | `Core/Semantic/PER/Lemmas.v:303` |
