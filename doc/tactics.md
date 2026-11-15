# McTT tactic reference

This document describes the `Ltac` definitions and `Tactic Notation`s of
`theories/` that the proofs share: what each one does, why it exists, and how
the families fit together.

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

`theories/LibTactics.v` creates a discriminated hint database `mctt`, and
almost every lemma in the development adds itself to it
(`#[export] Hint Resolve ... : mctt`). `mauto` (`LibTactics.v`) is just

```coq
eauto with mctt core
```

with `Tactic Notation` overloads for a search depth and for `using` clauses
(up to four lemmas): `mauto`, `mauto 4`, `mauto using foo`,
`mauto 3 using foo, bar`, and so on. The depth argument matters a lot for
compile time — this is why the sources are littered with `mauto 2`, `mauto 3`,
`mauto 4` rather than bare `mauto`.

`mautosolve` (`LibTactics.v`) is the "finish the goal or fail" variant:

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

The extraction functions are defined with
[Equations](https://github.com/mattam82/Coq-Equations); `per_univ_elem` and
`glu_univ_elem` are plain definitions over the inductive `…_core` relations,
with an `Equations`-style interface. Two consequences:

- You cannot `constructor`/`inversion` `per_univ_elem`/`glu_univ_elem`
  directly. You must first `simp <name>` to unfold one step (to `…_core i
  (…_below i)`), and afterwards `rewrite <- <name>_equation_1` to fold the
  recursive occurrences back up; `rewrite_per_univ_below` /
  `rewrite_glu_univ_below` restate the universes below the level.
  This is precisely the body of `basic_per_univ_elem_econstructor` and friends.
- Obligations are discharged by the tactic named in the
  `#[tactic="..."]` attribute — that is what every `impl_obligation_tac` in
  the tree is for.

### Notation scopes

Every notation lives in ordinary `constr`, in `mctt_scope`, and needs no
delimiter, so tactic patterns read like the judgments on paper:

```coq
| H : ?Γ ⊢ ?M : ?A |- _ => ...
```

Values and normal forms carry a superscript (`λᵈ`, `#ᵈ n`; `λⁿ`, `#ⁿ n`) because one spelling can denote only one sort. Context extension is
`Γ ▹ A` and application is `M $ N`. See
[`../AGENT/notations.md`](../AGENT/notations.md) for the level table and the
parsing traps.

---

## 1. `LibTactics.v` — general infrastructure

Nothing in this file mentions McTT judgments; it is reusable Ltac.

### 1.1 Generalization

| Tactic | Description |
| --- | --- |
| `gen x`, `gen x y`, `gen x y z`, `gen x y z w` | `generalize dependent`, for up to four variables in one go. |

### 1.2 Marking — iterate over each hypothesis exactly once

The trick is a transparent identity wrapper:

```coq
Definition __mark__ (n : nat) A (a : A) : A := a.
```

`mark H` folds `H`'s type into `__mark__ 0 t`, which is *convertible* to `t`
but no longer *syntactically matches* patterns like `?Γ ⊢ ?M : ?A`.
So a `repeat match goal` loop that marks each hypothesis it processes will
visit every hypothesis exactly once and then terminate.

| Tactic | Description |
| --- | --- |
| `mark H` / `unmark H` | Wrap/unwrap `H`'s type at level 0. |
| `mark_all` / `unmark_all` | Mark every unmarked hypothesis; unfold all marks. |
| `unmark_vars` | Unmark the variables (the hypotheses whose type is not a `Prop`), keeping the marks of the hypotheses. Run it before `dependent destruction`: a marked variable makes it simplify a `JMeq`, which needs uniqueness of identity proofs. |
| `mark_with H n` / `mark_all_with n` | Same, at a chosen level, so nested loops don't interfere. |
| `unmark_all_with n` | Unmark hypotheses carrying level `n`, skipping marks at other levels. |
| `on_all_marked_hyp tac` / `..._rev` | Repeatedly pick a marked hypothesis, unmark it, run `tac H`. `_rev` walks the context in reverse. |
| `on_all_hyp: tac` | The one you actually use: mark everything at level 0, run `tac H` on each, clean up. |
| `on_all_hyp_rev: tac`, `on_all_marked_hyp: tac`, `on_all_marked_hyp_rev: tac` | Variants of the above. |

Typical use:

```coq
(on_all_hyp: fun H => gen_presup H)
```

### 1.3 Context housekeeping

| Tactic | Description |
| --- | --- |
| `destruct_logic` | Break one conjunction, existential, disjunction, `sumbool`, `sumor`, or `sum` in the context. |
| `destruct_all` | `repeat destruct_logic`. |
| `not_let_bind name` | Fail if `name` is a `let`-bound local definition. Guards the duplicate machinery from clearing definitions. |
| `find_dup_hyp tac non` | Find two hypotheses with the same `Prop` type and run `tac H H' X`; run `non` if there is no such pair. |
| `fail_at_if_dup n` | Fail at level `n` if a duplicate pair exists. |
| `fail_if_dup` | `fail_at_if_dup 1` — tuned so the caller's `match` sees a level-0 failure. The standard terminator for saturation loops. |
| `clear_dups` | Discard redundant duplicate hypotheses. |
| `clear_PER` | Drop `PER`/`Symmetric`/`Transitive` hypotheses (they clutter and confuse `eauto`). |

### 1.4 Controlled inversion

`inversion` is dangerous in this development: on a dependent judgment it can
split the goal into unrelated cases or generate a swamp of equations.
`directed` is the fix.

| Tactic | Description |
| --- | --- |
| `directed tac` | Run `tac`, then `guard`s that the goal count did not increase. Fails if `tac` case-split. Also available as `Tactic Notation "directed" tactic2(tac)`. |
| `progressive_invert H` | `directed dependent destruction H` — `dependent destruction` is more general than `inversion`, and `directed` keeps it from branching. |
| `progressive_invert_once H n` | One step of the below: skip marked and `∀`-typed hypotheses, require the type to live in `Prop`/`Type`, then `directed inversion` + `simplify_eqs` + `clear_refl_eqs` + `clear_dups`, and mark at level `n`. |
| `progressive_inversion` | Repeat `progressive_invert_once _ 100` over the whole context. Marks at level 100 so each hypothesis is inverted at most once. |

### 1.5 Matching by head symbol

Judgments are notated, so their head constants (`wf_exp`, `eval_exp`,
`per_univ_elem`, …) are the reliable way to select hypotheses.

| Tactic | Description |
| --- | --- |
| `find_head t` | Peel applications off `t` and return its head. |
| `unify_by_head_of t head` | Succeed iff `t`'s head is `head`, for arities up to 10 (hand-unrolled because Ltac1 cannot pattern-match a spine). |
| `match_by_head1 head tac` | Run `tac H` on one hypothesis whose head is `head`. |
| `match_by_head head tac` | Run `tac H` on every such hypothesis exactly once (marks as it goes). |
| `inversion_by_head`, `directed_inversion_by_head`, `inversion_clear_by_head`, `directed_inversion_clear_by_head`, `destruct_by_head`, `directed_destruct_by_head` | The six obvious combinations of `inversion` / `inversion_clear` / `destruct`, each optionally wrapped in `directed`. |

### 1.6 Rewriting

| Tactic | Description |
| --- | --- |
| `clean_replace_by exp0 exp1 tac`, i.e. `clean replace e0 with e1 by tac` | Prove `e0 = e1` by `tac`, `subst`, then `try rewrite <-` it everywhere, so the context uses one of the two uniformly. **Fails if `e0` and `e1` are already syntactically equal**, which is what makes it safe inside `repeat`. |
| `bulky_rewrite1` / `bulky_rewrite` | Rewrite with *any* hypothesis, or with the `mctt` rewrite database, interleaving `mauto 2` to discharge side conditions. |
| `bulky_rewrite_in1 HT` / `bulky_rewrite_in HT` | Same, targeting hypothesis `HT`. |

### 1.7 Applying a lemma you cannot `apply`

These four are the deepest magic in the file. They exist because many McTT
lemmas end in an `iff` or a conjunction buried under several `∀`s, so plain
`apply`/`rewrite` cannot see the relevant component.

| Tactic | Description |
| --- | --- |
| `exvar T tac` | Create a fresh evar of type `T` and hand the raw term to `tac`. Uses `unshelve evar` for `Prop`s so the hole stays open. |
| `deepexec lem tac` | Walk `lem`'s statement down through `∀`s and `∧`s (unfolding `iff`) to its conclusion, instantiating each `∀`-argument with an evar — preferring, for `Prop` arguments, unification with an existing hypothesis — then run `tac` on the fully applied lemma. |
| `cutexec lem C tac` | Same traversal, but stop at the first `∀`-argument whose type matches `C`'s type, instantiate it with `C`, and run `tac` there. |
| `unify_args H P` | Given `P = f x₁ … xₙ`, build `H x₁ … xₙ`: apply `H` to the same argument spine. |
| `strong_apply H X` | Push hypothesis `X` through implication `H` *in place*: line up `H` with `X`'s argument spine, cut-traverse to the slot `X` fits, `pose proof (L X)`, `simpl`, and rename the result back to `X`. |

### 1.8 Relations, PERs, and setoid rewriting

McTT's logical relations are relations-valued, and the metatheory constantly
needs "these two candidate relations are equivalent, so substitute". When
`setoid_rewrite` can do it, it does; when it cannot, `apply_equiv_*` does it
by hand.

| Tactic | Description |
| --- | --- |
| `apply_equiv_left1` / `apply_equiv_left` | Given `H : R₁ <∙> R₂` (or `relation_equivalence R₁ R₂`), push every hypothesis headed by `R₁` through `H` via `strong_apply`, and `apply H` if the goal is headed by `R₁`. |
| `apply_equiv_right1` / `apply_equiv_right` | Mirror image, on `R₂`. |
| `saturate_refl` | For every `H : R a b` with `a ≠ b` syntactically, derive `R a a` and `R b b` from `PER_refl1`/`PER_refl2` (proved at 361/368); terminate with `fail_if_dup`. |
| `saturate_refl_for hd` | Same, restricted to relations whose head is `hd` — e.g. `saturate_refl_for per_univ_elem`. |
| `solve_refl` | `solve [reflexivity \|\| apply Equivalence_Reflexive]`. The fallback exists because plain `reflexivity`'s unification occasionally fails on these goals. |

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
  `wf_sub_eq` in `Core/Syntactic/System/Definitions.v`, which is what
  makes `rewrite` usable on the syntactic equality judgments.
- `Ltac Tauto.intuition_solver ::= auto with mctt core solve_subterm`
  (line 245) — redefines what `intuition` uses to close leaves, so `intuition`
  is McTT-aware everywhere.

### 1.9 Decision procedures

| Tactic | Description |
| --- | --- |
| `decision_complete` | For a goal `exists _, L = _` where `L : sumbool _ _`: `destruct L eqn:Heq`, then `eauto`/`contradiction`. The standard one-liner for "this decision procedure is complete". |

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
| `functional_eval_rewrite_clear1` / `…_clear` | `Core/Semantic/Evaluation/Lemmas.v` | `⟦M⟧ρ ↘ m`, `$\|m & n\|↘ r`, `rec … end`, `⟦σ⟧s ρ ↘ ρσ` |
| `functional_read_rewrite_clear1` / `…_clear` | `Core/Semantic/Readback/Lemmas.v` | `Rnf`, `Rne`, `Rtyp` |
| `functional_initial_env_rewrite_clear1` / `…_clear` | `Core/Semantic/NbE.v` | `initial_env` |
| `functional_nbe_rewrite_clear1` / `…_clear` | `Core/Semantic/NbE.v` | `nbe`, `nbe_ty` (including the case where the two derivations use different universe levels) |
| `functional_alg_type_infer_rewrite_clear1` / `…_clear` | `Algorithmic/Typing/Lemmas.v` | `Γ ⊢a M ⟹ A` (type inference is deterministic) |

Built on top of them:

| Tactic | Location | Description |
| --- | --- | --- |
| `simplify_subs` | `Core/Semantic/Evaluation/Tactics.v` | `cbn [exp_sub exp_wk] in *`. Since substitution is an operation, `⟦ Type@i[σ] ⟧ ρ ↘ a` has no constructor head until `exp_sub` is unfolded far enough to expose one. The delta list is restricted to the two recursive functions so that `eval_sub` and `sb_q` (both `simpl never`) stay folded. Not to be confused with `simpl_sub`, which rewrites the substitution algebra. |
| `simplify_evals` | `Core/Semantic/Evaluation/Tactics.v` | The standard "clean up the evaluation hypotheses" step: identify duplicate results, then `directed dependent destruction` every `eval_exp` / `eval_app` / `eval_natrec` / `eval_sub` hypothesis that does not branch, then identify again. |

---

## 3. Syntactic layer: substitutions and presuppositions

### 3.1 The substitution algebra (`Core/Syntactic/Substitution.v`)

Weakenings and substitutions are meta-level functions (`wk := nat -> nat`,
`sub := nat -> exp`), so their algebra is a body of *equations* rather than
constructors, and the tactics here are what prove and apply them. Two rewrite
databases and their drivers:

| Tactic | Description |
| --- | --- |
| `reduce_index` | `autorewrite with sb_index in *`. The `sb_index` database computes an operation *at an index*: `sb_q` at `0` and at `S _`, `exp_wk`/`exp_sub` at a variable. This is what turns a pointwise goal into arithmetic. |
| `simpl_sub` | `autorewrite with sb in *`. The `sb` database is the algebra proper — identity, composition, and how an operation meets `↑`, `,,` and `q`. The composition laws are registered as **rewrites** rather than resolution hints on purpose: as hints they would let `eauto` loop. |
| `unfold_ops` | `cbv beta delta` over every operation *and* over `wk_eq`/`sb_eq`/`pointwise_relation`. Unlike rewriting it reaches under the `forall` of a pointwise hypothesis, which is why `reduce_index` alone is not enough. |
| `pointwise` | `intro x; destruct x; reduce_index` — the two cases every pointwise law splits into, leaving the operations *folded* for proofs that go on to rewrite with the laws. |
| `pointwise_solve` | Closes a pointwise goal outright, so it can afford `unfold_ops` first; then `reflexivity`/`lia`/`f_equal`. |

### 3.2 Transporting judgments along an operation (`Core/Syntactic/System/Lemmas.v`)

The algebra above is about *equality* of expressions; these are about pushing a
judgment through an operation — `wk_preserves_wf` (weakening preserves the
judgments), `sub_preserves_wf` (substitution does), and `sub_eq_preserves_exp`
(equivalent substitutions do). All three are one `induction 1` followed by the
same pipeline, which is why each family appears three times: `_wk`, `_sub`,
`_sub_eq`.

```coq
induction 1; intros; saturate_sub_eq; push_sub; lift_sub_eq; saturate_sub_eq;
  saturate_sub_typ; saturate_sub_eq_IH.
all: mauto 3.
```

| Family | Description |
| --- | --- |
| `saturate_wk`, `saturate_sub`, `saturate_sub_eq` | Add the domain and codomain well-formedness of every operation in the context. `wf_sub_dom`/`wf_sub_cod` are **deliberately not** `mctt` hints, so these are how you get them; the canonical opening of a gluing proof is `assert Δ ⊢ˢ σ : Γ by mauto 3. saturate_sub.` |
| `push_wk_step`, `push_wk_in`, `push_wk_goal`, `push_wk` | Move an operation **inward**, toward the leaves: the induction hypothesis produces it on the outside, the rule to be applied wants it on the inside. Alternates `simpl` (which distributes over the term formers) with the `Substitution.v` corollaries that move it past a substitution. Uses `setoid_rewrite` throughout, because the induction hypotheses are still quantified over the target context and plain `rewrite` will not descend under a binder. |
| `push_sub_step`, `push_sub_in`, `push_sub_goal`, `push_sub` | The same for substitutions. |
| `lift_wk_step`, `lift_wk` | Saturate with the **lifted** operations `q φ`, one `assert` per binder. `wf_wk_q` *is* a hint, but reconstructing `q φ` inside the `eauto` search costs three levels on top of the rule application, which puts the wide cases (such as `λ`-E) out of reach at any terminating depth. |
| `lift_sub_step`, `lift_sub` | Ditto for substitutions. |
| `lift_sub_eq_step`, `lift_sub_eq` | Ditto for substitution equivalences. |
| `saturate_sub_typ`, `saturate_sub_eq_IH` | The counterparts of `push_sub`/`lift_sub` for the *equivalence* induction: transport every type premise along every substitution in context, and instantiate every induction hypothesis at every substitution equivalence in context. Together they leave all premises of the congruence rule literally in the context, so the search never has to guess a domain type through an evar. |

### 3.3 Presuppositions

McTT's judgments are *not* presupposition-free: from `Γ ⊢ M : A` you can
derive `⊢ Γ` and `∃ i, Γ ⊢ A : Type@i`, and so on. Proofs constantly need
those side facts, so there is machinery to add all of them at once.

`Core/Syntactic/System/Tactics.v`:

| Tactic | Description |
| --- | --- |
| `invert_wf_ctx1 H` | From `⊢ Γ ▹ A` derive `⊢ Γ` and `∃ i, Γ ⊢ A : Type@i` via `ctx_decomp`, but *skip* introducing the level if an equivalent hypothesis (marked or not) is already present. |
| `invert_wf_ctx` | `invert_wf_ctx1` on every hypothesis, then `clear_dups`. |
| `gen_core_presup H` | The core presupposition generator, one case per judgment form: `⊢ Γ ≈ Δ` ⇒ `presup_ctx_eq`; `⊢ Γ ⊆ Δ` ⇒ `presup_ctx_sub`; `Γ ⊢ M : A` ⇒ `presup_exp`; `Γ ⊢ˢ σ : Δ` ⇒ `presup_sub`. |
| `gen_lookup_presup H` | From `Γ ∋ #x : A` derive `∃ i, Γ ⊢ A : Type@i`, unless already known. |
| `gen_core_presups` | Run `gen_core_presup` on everything, `invert_wf_ctx`, then `gen_lookup_presup` on everything, then dedupe. |

`Core/Syntactic/Presup.v` extends this to the equality judgments, which are
proved by mutual induction, so the induction hypotheses must be passed in
explicitly:

| Tactic | Description |
| --- | --- |
| `gen_presup1 H` | The equality cases: `Γ ⊢ M ≈ N : A` via `presup_exp_eq`, `Γ ⊢ A ⊆ A'` via `presup_subtyp`, and `wf_sub_eq` via its two projections. The first two then call `gen_core_presup` on the left-hand typing they just produced, so `⊢ Γ` and the type of the equation come along too — which is what the old four-way-conjunction version gave for free. |
| `gen_presup H` | `first [ gen_presup1 H \| gen_core_presup H ]`. |
| `gen_presups` | **The one to use in proofs.** Every presupposition of every hypothesis, then `invert_wf_ctx`, lookup presuppositions, `saturate_wk`, `saturate_sub`, `clear_dups`. |

Related:

| Tactic | Location | Description |
| --- | --- | --- |
| `saturate_ctx_sub` | `Core/Syntactic/CtxSub.v` | For every `⊢ Γ ⊆ Δ` in the context add its four consequences — `ctx_sub_escape` (the refinement substitution `Γ ⊢ˢ Id : Δ`), `ctx_sub_dom`, `ctx_sub_cod`, `ctx_sub_length` — then dedupe. |
| `impl_opt_constructor` | `Core/Syntactic/SystemOpt.v` | `intros; gen_presups; mautosolve 4`. Proves the "optimized" typing rules in `SystemOpt.v` — variants with fewer premises, since the missing premises are recoverable as presuppositions. Each is then swapped into the `mctt` database in place of the original (`Hint Resolve` + `Remove Hints`). |
| `apply_subtyping` | `Algorithmic/Subtyping/Lemmas.v` | From `Γ ⊢ M : A` and `Γ ⊢ A ⊆ B`, derive `Γ ⊢ M : B` and clear the original. |

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

| Tactic | Description |
| --- | --- |
| `rewrite_relation_equivalence_left` | For each `H : R₁ <~> R₂`, `setoid_rewrite H` in the goal and in every *other* hypothesis, then hide `H` behind `fold (id T)` so the `repeat` does not re-select it; `unfold id in *` at the end. |
| `rewrite_relation_equivalence_right` | Same, rewriting right-to-left. |
| `clear_relation_equivalence` | Discard `H : R₁ <~> R₂` when it is trivial (`R₁` and `R₂` unify) or when either side is a local variable — clearing the variable too, which effectively substitutes it away. |
| `apply_relation_equivalence` | The composite you actually call: clear, rewrite right, clear, rewrite left, clear. |
| `use_relation_equivalence` | Closes `R₁ x y` from `H : R₁ <~> R₂` (or the mirror) by `apply H`. Needed because `apply_relation_equivalence` only ever *rewrites*, and `setoid_rewrite` leaves the conclusion untouched when both sides of the `<~>` are applications — as the head relations `head_rel _ _ D` of a context PER are, for two different witnesses. |

### 4.2 Irrelevance saturation

| Tactic | Description |
| --- | --- |
| `per_univ_elem_right_irrel_assert1` / `…_assert` | For two derivations sharing *both* domain arguments, assert `R₁ <~> R₂`; skip if `R₁` and `R₂` unify or the equivalence is already known (in either direction). |
| `do_per_univ_elem_irrel_assert1` | Three cases — shared left argument (`_right_irrel`), shared right argument (`_left_irrel`), left of one equal to right of the other (`_cross_irrel`) — each guarded against re-derivation. |
| `do_per_univ_elem_irrel_assert` | `repeat` of the above. |
| `handle_per_univ_elem_irrel` | **The composite.** `functional_eval_rewrite_clear`, saturate irrelevance, `apply_relation_equivalence`, `clear_dups`. In effect: "make all the relation names in my context the same one." |
| `do_per_ctx_env_irrel_assert1` / `…_assert` | Same three cases for `per_ctx_env` (environment relations). |
| `handle_per_ctx_env_irrel` | Composite, as above, for contexts. |

### 4.3 Construction and inversion

| Tactic | Location | Description |
| --- | --- | --- |
| `basic_per_univ_elem_econstructor` | `PER/CoreTactics.v` | `simp per_univ_elem; econstructor; rewrite_per_univ_below; try rewrite <- per_univ_elem_equation_1 in *` — unfold one step, apply a constructor, restate the universes below the level by `per_univ_below_spec`, fold the recursive occurrences back. |
| `basic_invert_per_univ_elem H` | `PER/CoreTactics.v` | The dual: `simp` in `H`, `unmark_vars`, `dependent destruction`, `rewrite_per_univ_below`, fold back. `unmark_vars` keeps `dependent destruction` free of uniqueness of identity proofs (see `LibTactics.v`). |
| `per_univ_elem_econstructor` | `PER/Lemmas.v` | Try the smart `Π` constructor `per_univ_elem_pi'` first (`repeat intro; hnf; eapply …`), else fall back to the basic one. |
| `invert_per_univ_elem H` | `PER/Lemmas.v` | Try `per_univ_elem_pi_clean_inversion` — which yields the `out_rel` and the elem-relation equivalence directly, instead of the raw constructor equations — else `basic_invert_per_univ_elem`. |
| `per_ctx_env_econstructor` | `PER/Lemmas.v` | Same pattern for contexts: try `per_ctx_env_cons'`, else `econstructor`. |
| `invert_per_ctx_env H` | `PER/Lemmas.v` | Try `per_ctx_env_cons_clean_inversion`, else plain `inversion H; subst`. |

### 4.4 Destructing "for all related arguments" hypotheses

Semantic function types produce hypotheses of shape
`forall c c', in_rel c c' -> rel_mod_eval …`. You almost never want to
instantiate those by hand.

| Tactic | Location | Description |
| --- | --- | --- |
| `destruct_rel_by_assumption in_rel H` | `PER/CoreTactics.v` | For every hypothesis `Dom c ≈ c' ∈ in_rel` in the context, specialize `H` to it, destruct the result, and `destruct_all`. Marks at level 1 so each argument pair is used once. |
| `destruct_rel_mod_eval` | `PER/CoreTactics.v` | Apply the above to every `rel_mod_eval`-valued hypothesis, and `dependent destruction` any bare `rel_mod_eval`. |
| `destruct_rel_mod_app` | `PER/CoreTactics.v` | Same for `rel_mod_app`. |
| `destruct_rel_typ` | `PER/CoreTactics.v` | Same for `rel_typ`. |

### 4.5 Relation chains (`Core/Semantic/PER/Chain.v`)

Most of the completeness invariants are naturally stated as a *set* of values all
consecutively related, the four-value pattern
`{⟦t[σ]⟧ρ, ⟦t⟧(⟦σ⟧ρ), ⟦t'⟧(⟦σ'⟧ρ'), ⟦t'[σ']⟧ρ'} ⊆ 𝑅_T` chief among them.
`rel_chain R l` is that, over a `list`. Because `R` is a PER, the order and any
repetition are immaterial — `rel_chain_pairwise` and `rel_chain_merge` are what
make that formal, and these three tactics are the whole intended API of `Chain.v`.

| Tactic | Description |
| --- | --- |
| `pairwise` | Closes `R x y` from any `rel_chain` hypothesis about `R`, whichever two of its members `x` and `y` are. `first` over the remaining goals rather than a positional `[ \| \| ]`, because the `PER` obligation may or may not survive to become one. The relation is matched in the **goal** first and only failing that left to the `eapply` to unify (`pairwise_from`, line 356): a goal an `eapply` produced before it could fix the universe level or the element PER has a metavariable where `R` should be, which the syntactic match cannot see. |
| `solve_rel_chain` | Closes a `rel_chain` goal all of whose members occur in **one** hypothesis, by `pairwise` or else `rel_chain_incl`. |
| `merge_rel_chain H1 H2 c` | Closes a `rel_chain` goal whose members are spread over **two** hypotheses: merge them along the shared value `c`, then select. Everything is positional because nothing can be guessed — `rel_chain_merge` leaves *both* chain premises with a metavariable list, so a search tactic would put the same hypothesis in both and only fail later at the inclusion, and `c` is not determined by the goal at all. |

Two tactics in `Core/Semantic/PER/Lemmas.v` mechanize *weak functionality* — the
paper's `S ⊆_R ↘ R'`, which says a chain in `per_univ i` determines one output
PER on inhabitants, the same for every pair of the chain. `per_univ i` is what a
semantic *type* judgment hands over, with each link carrying its own existential
element PER; these move to the single PER weak functionality promises:

| Tactic | Location | Description |
| --- | --- | --- |
| `functionalize_per_univ_chain H R` | `Core/Semantic/PER/Lemmas/Universe.v` | Names the element PER of a chain in `per_univ i` and refines the chain to it in place, via `per_univ_chain_functional` (the *existence* half). Takes no anchor and loses nothing: every pair remains available, at `R`, through `pairwise`. |
| `pairwise_univ` | `Core/Semantic/PER/Lemmas/UniverseSubtyping.v` | `pairwise` at a `per_univ i` goal, whose existential the refined chain no longer carries. |
| `retype_rel_chain Htyp Hanchor H` | `Core/Semantic/PER/Lemmas/UniverseSubtyping.v` | Moves `H` between the element PER the type chain `Htyp` reported and the one `Hanchor` names, via `per_univ_chain_rel_irrel` (the *uniqueness* half). The two need share only one value, and only `H` says which direction is wanted, so both are tried. `H` may be a chain — `rel_chain_Proper` is what rewrites it — or a bare pair. Replaces the recurring three-step `rel_chain_4_related` / `per_univ_elem_*_irrel` / `rewrite` idiom. |

Three more build on the `Chain.v` tactics for the case the semantic rules
actually need — a chain of *environments*:

| Tactic | Location | Description |
| --- | --- | --- |
| `destruct_per_univ_chain H` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v` | Splits a four-value chain in `per_univ i` into its three links, going through `per_univ_chain_functional` first so the three come out at *one* element PER rather than three independent existential ones. |
| `solve_per_head` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v` | Discharges the head component of `per_env_extend_intro'`: introduce the two extended environments and the `per_univ_elem` relating the two type values, identify its outputs by `functional_eval_rewrite_clear`, let `handle_per_univ_elem_irrel` identify its PER with the one the term chain lives in, then read the pair off that chain with `pairwise`. |
| `solve_per_env_extend_chain` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v` | The whole last step of an extended-context rule: split every link of the goal chain with `per_env_extend_intro'`, take the tails off the chain the underlying substitution arrived with (`pairwise`) and bridge the heads (`solve_per_head`). Length-agnostic, because the four-value pattern wants four environments while the rules with a premise in an extended context want every extension of the four tails by either head. |

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

| Tactic | Description |
| --- | --- |
| `eexists_rel_exp` | `eexists; eexists; [eassumption \|]; eexists` — the skeleton for `Γ ⊨ M ≈ M' : A`. |
| `eexists_rel_exp_with i` | Same, but commits to universe level `i` instead of leaving an evar. |
| `eexists_rel_sub` | Skeleton for the substitution judgment (two `eassumption` premises). |
| `eexists_rel_wk` | The same tactic, for `rel_wk_under_ctx`: it has the same outer shape as `rel_sub_under_ctx` — two environment PERs, each with its context witness read off the goal. |
| `eexists_subtyp` / `eexists_subtyp_with i` | Skeletons for semantic subtyping. |
| `invert_rel_typ_body` | **The main workhorse of the completeness proofs.** `simplify_evals`, then `directed invert_per_univ_elem` on every `per_univ_elem` hypothesis, `subst`, `clear_dups`, `clear_refl_eqs`, `handle_per_univ_elem_irrel`, `clear_dups`, and fold `per_univ_elem_equation_1` back. |

Case-specific skeletons, each `apply`ing the corresponding "of" lemma before
opening the existentials:

| Tactic | Location |
| --- | --- |
| `eexists_rel_exp_of_typ` | `Core/Completeness/LogicalRelation/Universes.v` |

Plus:

| Tactic | Location | Description |
| --- | --- | --- |

---

## 6. Soundness layer: glue tactics

Soundness uses a glued (Kripke) logical relation: `glu_univ_elem i P El a`
pairs a *type* predicate `P` with an *element* predicate `El`, and
`glu_ctx_env Sb Γ` gives the substitution predicate for a context. `P`, `El`,
`Sb` are all outputs, so this layer needs the same identify-and-substitute
machinery as the PER layer, with `<∙>` (predicate equivalence) in place of
`<~>`.

### 6.1 Predicate equivalence (`Core/Soundness/LogicalRelation/CoreLemmas.v`)

| Tactic | Description |
| --- | --- |
| `rewrite_predicate_equivalence_left` / `…_right` | Mirror of the `relation_equivalence` versions, for `H : R₁ <∙> R₂`. |
| `clear_predicate_equivalence` | Mirror of `clear_relation_equivalence`. |
| `apply_predicate_equivalence` | Composite: clear, rewrite right, clear, rewrite left, clear. |

### 6.2 Functionality of the glue relations

| Tactic | Description |
| --- | --- |
| `apply_functional_glu_univ_elem1` / `…_elem` | Two `glu_univ_elem` derivations for the same `a` at the same level ⇒ assert `(P₁ <∙> P₂) /\ (El₁ <∙> El₂)`, guarded against re-derivation. |
| `handle_functional_glu_univ_elem` | **Composite.** `functional_eval_rewrite_clear`, re-`fold` the `glu_typ_pred`/`glu_exp_pred` abbreviations (needed for the patterns to match after `simp`), saturate functionality, `apply_predicate_equivalence`, `clear_dups`. |
| `apply_functional_glu_ctx_env1` / `…_env` | Same for `glu_ctx_env`: two derivations for the same `Γ` give `Sb₁ <∙> Sb₂`. |
| `handle_functional_glu_ctx_env` | Composite, as above. |

### 6.3 Construction and inversion

| Tactic | Location | Description |
| --- | --- | --- |
| `basic_glu_univ_elem_econstructor` | `CoreTactics.v` | `simp glu_univ_elem; econstructor; rewrite_glu_univ_below;` fold back. |
| `basic_invert_glu_univ_elem H` | `CoreTactics.v` | The dual, with `unmark_vars` before `dependent destruction`. |
| `glu_univ_elem_econstructor` | `CoreLemmas.v` | Try `glu_univ_elem_core_univ'` first, else the basic constructor. |
| `invert_glu_univ_elem H` | `CoreLemmas.v` | Three-way fallback: `glu_univ_elem_pi_clean_inversion2`, then `…1`, then `basic_invert_glu_univ_elem`. The clean inversions hand back `IP`/`IEl`/`OP`/`OEl` and the two predicate equivalences directly. |
| `invert_glu_rel1` | `CoreTactics.v` | `progressive_invert` any `pi_glu_typ_pred` / `pi_glu_exp_pred` / `neut_glu_typ_pred` / `neut_glu_exp_pred` hypothesis. |
| `simpl_glu_rel` | `CoreLemmas.v` | **The standard opening move for a glue lemma.** `apply_equiv_left`, `repeat invert_glu_rel1`, `apply_equiv_left`, `destruct_all`, `gen_presups`. |
| `invert_glu_ctx_env H` | `Lemmas.v` | Try `glu_ctx_env_cons_clean_inversion`, else `dependent destruction`. |

### 6.4 Saturation

| Tactic | Location | Description |
| --- | --- | --- |
| `saturate_glu_info1` / `saturate_glu_info` | `CoreLemmas.v` | Extract the syntactic consequences of glue membership: from `P Γ A` get `Γ ⊢ A : Type@i`, from `El …` get the typing of the term (`glu_univ_elem_trm_escape`). |
| `saturate_kripke_escape` | `Weakening/Lemmas.v` | For every Kripke weakening `Γ ⊢ᵏ φ : Δ` add `kripke_escape`, i.e. `Γ ⊢ˢ ι φ : Δ`. Because `wf_sub_dom`/`wf_sub_cod` are not hints, this must be **followed by `saturate_sub`** to get the two contexts. |
| `saturate_kripke` | `Weakening/Lemmas.v` | The same for `kripke_dom`/`kripke_cod` directly. Those two are deliberately not hints either — `eauto` would cycle them against the context introduction rules. |

### 6.5 Judgment-level destruction and inversion (`Core/Soundness/LogicalRelation/Lemmas.v`)

| Tactic | Description |
| --- | --- |
| `destruct_glu_rel_by_assumption sub_glu_rel H` | The `glu` analogue of `destruct_rel_by_assumption`: for every `Δ ⊢ˢ σ ® ρ ∈ Sb` in the context, instantiate `H` and destruct. |
| `destruct_glu_rel_exp_with_sub` | Apply it to every `glu_rel_exp_with_sub`-valued hypothesis; also destruct bare ones. |
| `destruct_glu_rel_typ_with_sub` | Same for `glu_rel_typ_with_sub`. |
| `invert_glu_rel_exp H` | Fallback chain over `glu_rel_exp_clean_inversion2`, `…1`, then `inversion`. The "clean" versions require a `glu_ctx_env` (and for `2` also a typing) premise, which they discharge by `eassumption`, and give back a single universe level instead of an existential. |

### 6.6 A deliberate redefinition

`invert_glu_rel_exp` is **redefined** (with `::=`, Ltac1's redefinition
syntax) once as the development proceeds and a stronger clean-inversion lemma
becomes available:

- `Core/Soundness/LogicalRelation/Universes.v` prepends `glu_rel_exp_clean_inversion2'`,
  which only needs `Γ ⊩ Type@i : Type@(S i)` — automatically available —
  rather than an explicit typing premise.

So the meaning of `invert_glu_rel_exp` at a given point in the file tree
depends on whether this file has been loaded. The redefinition only
*adds* an earlier alternative to the `+` chain, so it strictly strengthens it.

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
`#[tactic="impl_obligation_tac"]`. They all follow the same recipe: invert the order
predicate to expose the recursive sub-orders, then `econstructor; mauto`.

| Tactic | Location | Description |
| --- | --- | --- |
| `impl_obligation_tac1` | `Extraction/Evaluation/Evaluation.v`; `Reference/Evaluation.v` | Inverts one order predicate of evaluation (in Extraction `fast_eval_exp_order`, `fast_eval_app_order`, …) by `progressive_invert`. |
| `impl_obligation_tac1` | `Extraction/Evaluation/Readback.v`; `Reference/Readback.v` | The same for the order predicates of readback (in Extraction `fast_read_nf_order`, `fast_read_ne_order`, `fast_read_typ_order`, …). |
| `subtyping_tac` | `Extraction/Checker/Subtyping.v` | Obligations of the *decision* procedure `subtyping_nf_impl`: for a positive goal `⊢anf A ⊆ B`, `subst; mauto 4; try congruence; econstructor`; for a negative goal, introduce, `dependent destruction`, and close by `lia`/`congruence`. |
| `subtyping_impl_tac1` / `subtyping_impl_tac` | `Extraction/Checker/Subtyping.v` | Inverts `subtyping_order` and `nbe_ty_order`; then `econstructor; mauto`. |
| `impl_obligation_tac1` / `impl_obligation_tac` | `Extraction/Checker/TypeCheckBase.v` | For the variable lookup: introduce negations, invert `⊢ Γ ▹ A` and the impossible lookups (`⋅ ∋ #x : A`, `Γ ▹ A ∋ #(S x) : A`, a module slot at `#0`), then `intuition (mauto 4)`. |
| `clear_defs` | `Extraction/Checker/TypeCheck.v`; `Reference/TypeCheck.v` | Housekeeping: `Equations` leaves the mutual recursive-call hypotheses and `let H := fixproto in …` bindings in every obligation context, where they confuse `mauto`. This clears them by matching their (spelled-out) types. |

Completeness of the extracted functions is proved by a third pattern: assert
the order predicate, run the function, and use functionality to identify the
result.

| Tactic | Location | Description |
| --- | --- | --- |
| `functional_eval_complete` | `Reference/Evaluation.v` | For a goal `exists H H', f x H = exist _ m H'`: `assert` the order predicate by `mauto 3`, `eexists` it, `destruct` the call, `functional_eval_rewrite_clear`, `eexists; reflexivity`. |
| `functional_read_complete` | `Reference/Readback.v` | Same, with `functional_read_rewrite_clear`. |

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
- **`invert_glu_rel_exp` is not one tactic.** See *A deliberate
  redefinition* — its meaning depends
  on whether `Soundness/LogicalRelation/Universes.v` is in scope.
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
| `apply_equiv_left`, `apply_equiv_left1` | `LibTactics.v` |
| `apply_equiv_right`, `apply_equiv_right1` | `LibTactics.v` |
| `apply_functional_glu_ctx_env`, `…1` | `Core/Soundness/LogicalRelation/Lemmas.v` |
| `apply_functional_glu_univ_elem`, `…1` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `apply_predicate_equivalence` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `apply_relation_equivalence` | `Core/Semantic/PER/Lemmas/Basic.v` |
| `apply_subtyping` | `Algorithmic/Subtyping/Lemmas.v` |
| `basic_glu_univ_elem_econstructor` | `Core/Soundness/LogicalRelation/CoreTactics.v` |
| `basic_invert_glu_univ_elem` | `Core/Soundness/LogicalRelation/CoreTactics.v` |
| `basic_invert_per_univ_elem` | `Core/Semantic/PER/CoreTactics.v` |
| `basic_per_univ_elem_econstructor` | `Core/Semantic/PER/CoreTactics.v` |
| `bulky_rewrite`, `…1`, `…_in`, `…_in1` | `LibTactics.v` |
| `clean replace … with … by …` | `LibTactics.v` (impl. `clean_replace_by`) |
| `clear_defs` | `Extraction/Checker/TypeCheck.v`; `Reference/TypeCheck.v` |
| `clear_dups` | `LibTactics.v` |
| `clear_PER` | `LibTactics.v` |
| `clear_predicate_equivalence` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `clear_relation_equivalence` | `Core/Semantic/PER/Lemmas/Basic.v` |
| `cutexec` | `LibTactics.v` |
| `decision_complete` | `LibTactics.v` |
| `deepexec` | `LibTactics.v` |
| `destruct_all`, `destruct_logic` | `LibTactics.v` |
| `destruct_by_head`, `directed_destruct_by_head` | `LibTactics.v` |
| `destruct_glu_rel_by_assumption` | `Core/Soundness/LogicalRelation/Lemmas.v` |
| `destruct_glu_rel_exp_with_sub` | `Core/Soundness/LogicalRelation/Lemmas.v` |
| `destruct_glu_rel_typ_with_sub` | `Core/Soundness/LogicalRelation/Lemmas.v` |
| `destruct_per_univ_chain` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v` |
| `destruct_rel_by_assumption` | `Core/Semantic/PER/CoreTactics.v` |
| `destruct_rel_mod_app`, `…_eval`, `destruct_rel_typ` | `Core/Semantic/PER/CoreTactics.v` |
| `directed` | `LibTactics.v` (notation 116) |
| `do_per_ctx_env_irrel_assert`, `…1` | `Core/Semantic/PER/Lemmas/Contexts.v` |
| `do_per_univ_elem_irrel_assert`, `…1` | `Core/Semantic/PER/Lemmas/Universe.v` |
| `eexists_rel_exp`, `…_with` | `Core/Completeness/LogicalRelation/Tactics.v` |
| `eexists_rel_exp_of_typ` | `Core/Completeness/LogicalRelation/Universes.v` |
| `eexists_rel_sub` | `Core/Completeness/LogicalRelation/Tactics.v` |
| `eexists_rel_wk` | `Core/Completeness/LogicalRelation/Tactics.v` |
| `eexists_subtyp`, `…_with` | `Core/Completeness/LogicalRelation/Tactics.v` |
| `exvar` | `LibTactics.v` |
| `fail_at_if_dup`, `fail_if_dup` | `LibTactics.v` |
| `find_dup_hyp` | `LibTactics.v` |
| `find_head` | `LibTactics.v` |
| `functional_alg_type_infer_rewrite_clear`, `…1` | `Algorithmic/Typing/Lemmas.v` |
| `functional_eval_complete` | `Reference/Evaluation.v` |
| `functionalize_per_univ_chain` | `Core/Semantic/PER/Lemmas/Universe.v` |
| `functional_eval_rewrite_clear`, `…1` | `Core/Semantic/Evaluation/Lemmas.v` |
| `functional_initial_env_rewrite_clear`, `…1` | `Core/Semantic/NbE.v` |
| `functional_nbe_rewrite_clear`, `…1` | `Core/Semantic/NbE.v` |
| `functional_read_complete` | `Reference/Readback.v` |
| `functional_read_rewrite_clear`, `…1` | `Core/Semantic/Readback/Lemmas.v` |
| `gen` | `LibTactics.v–20` |
| `gen_core_presup`, `gen_core_presups` | `Core/Syntactic/System/Tactics.v` |
| `gen_lookup_presup` | `Core/Syntactic/System/Tactics.v` |
| `gen_presup`, `gen_presup1`, `gen_presups` | `Core/Syntactic/Presup.v` |
| `glu_univ_elem_econstructor` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `handle_functional_glu_ctx_env` | `Core/Soundness/LogicalRelation/Lemmas.v` |
| `handle_functional_glu_univ_elem` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `handle_per_ctx_env_irrel` | `Core/Semantic/PER/Lemmas/Contexts.v` |
| `handle_per_univ_elem_irrel` | `Core/Semantic/PER/Lemmas/Universe.v` |
| `impl_obligation_tac`, `…1` | `Extraction/Checker/MemberType.v`; `Extraction/Checker/TypeCheckBase.v`; `…1` also `Extraction/Evaluation/Evaluation.v`, `Extraction/Evaluation/Readback.v`, `Reference/Evaluation.v`, `Reference/Readback.v` |
| `impl_opt_constructor` | `Core/Syntactic/SystemOpt.v` |
| `inversion_by_head`, `directed_inversion_by_head` | `LibTactics.v` |
| `inversion_clear_by_head`, `directed_inversion_clear_by_head` | `LibTactics.v` |
| `invert_glu_ctx_env` | `Core/Soundness/LogicalRelation/Lemmas.v` |
| `invert_glu_rel1` | `Core/Soundness/LogicalRelation/CoreTactics.v` |
| `invert_glu_rel_exp` | `Core/Soundness/LogicalRelation/Lemmas.v`; redefined `Core/Soundness/LogicalRelation/Universes.v` |
| `invert_glu_univ_elem` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `invert_per_ctx_env`, `invert_per_univ_elem` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v`; `Core/Semantic/PER/Lemmas/UniverseSubtyping.v` |
| `invert_rel_typ_body` | `Core/Completeness/LogicalRelation/Tactics.v` |
| `invert_wf_ctx`, `…1` | `Core/Syntactic/System/Tactics.v` |
| `lift_sub`, `lift_sub_step` | `Core/Syntactic/System/Structural.v` |
| `lift_sub_eq`, `lift_sub_eq_step` | `Core/Syntactic/System/Lemmas.v` |
| `lift_wk`, `lift_wk_step` | `Core/Syntactic/System/Structural.v` |
| `mark`, `unmark`, `mark_all`, `unmark_all` | `LibTactics.v` |
| `mark_with`, `mark_all_with`, `unmark_all_with` | `LibTactics.v` |
| `match_by_head`, `…1` | `LibTactics.v` |
| `mauto` (10 overloads) | `LibTactics.v–224` |
| `mautosolve`, `mautosolve_impl` | `LibTactics.v–230, 227` |
| `merge_rel_chain` | `Core/Semantic/PER/Chain.v` |
| `not_let_bind` | `LibTactics.v` |
| `on_all_hyp:`, `on_all_hyp_rev:` | `LibTactics.v` |
| `on_all_marked_hyp`, `…_rev` (+ notations) | `LibTactics.v` |
| `pairwise` | `Core/Semantic/PER/Chain.v` |
| `pairwise_from` | `Core/Semantic/PER/Chain.v` |
| `pairwise_univ` | `Core/Semantic/PER/Lemmas/UniverseSubtyping.v` |
| `per_ctx_env_econstructor` | `Core/Semantic/PER/Lemmas/Contexts.v` |
| `per_univ_elem_econstructor` | `Core/Semantic/PER/Lemmas/UniverseSubtyping.v` |
| `per_univ_elem_right_irrel_assert`, `…1` | `Core/Semantic/PER/Lemmas/Universe.v` |
| `pointwise`, `pointwise_solve` | `Core/Syntactic/Substitution.v` |
| `progressive_inversion`, `progressive_invert`, `…_once` | `LibTactics.v` |
| `push_sub`, `…_step`, `…_in`, `…_goal` | `Core/Syntactic/System/Structural.v` |
| `push_wk`, `…_step`, `…_in`, `…_goal` | `Core/Syntactic/System/Structural.v` |
| `reduce_index` | `Core/Syntactic/Substitution.v` |
| `retype_rel_chain` | `Core/Semantic/PER/Lemmas/UniverseSubtyping.v` |
| `rewrite_predicate_equivalence_left`, `…_right` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `rewrite_relation_equivalence_left`, `…_right` | `Core/Semantic/PER/Lemmas/Basic.v` |
| `saturate_ctx_sub` | `Core/Syntactic/CtxSub.v` |
| `saturate_glu_info`, `…1` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `saturate_kripke` | `Core/Soundness/Weakening/Lemmas.v` |
| `saturate_kripke_escape` | `Core/Soundness/Weakening/Lemmas.v` |
| `saturate_refl`, `saturate_refl_for` | `LibTactics.v` |
| `saturate_sub`, `saturate_wk` | `Core/Syntactic/System/Structural.v` |
| `saturate_sub_eq`, `saturate_sub_eq_IH` | `Core/Syntactic/System/Lemmas.v` |
| `saturate_sub_typ` | `Core/Syntactic/System/Lemmas.v` |
| `simpl_glu_rel` | `Core/Soundness/LogicalRelation/CoreLemmas.v` |
| `simpl_sub` | `Core/Syntactic/Substitution.v` |
| `simplify_evals` | `Core/Semantic/Evaluation/Tactics.v` |
| `simplify_subs` | `Core/Semantic/Evaluation/Tactics.v` |
| `solve_chain_PER` | `Core/Semantic/PER/Chain.v` |
| `solve_in`, `solve_incl` | `Core/Semantic/PER/Chain.v` |
| `solve_per_env_extend_chain` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v` |
| `solve_per_head` | `Core/Semantic/PER/Lemmas/CanonicalContexts.v` |
| `solve_refl` | `LibTactics.v` |
| `solve_rel_chain` | `Core/Semantic/PER/Chain.v` |
| `strong_apply` | `LibTactics.v` |
| `subtyping_impl_tac`, `…1` | `Extraction/Checker/Subtyping.v` |
| `subtyping_tac` | `Extraction/Checker/Subtyping.v` |
| `Tauto.intuition_solver` (redefinition) | `LibTactics.v` |
| `unfold_ops` | `Core/Syntactic/Substitution.v` |
| `unify_args` | `LibTactics.v` |
| `unify_by_head_of` | `LibTactics.v` |
| `use_relation_equivalence` | `Core/Semantic/PER/Lemmas/Basic.v` |
