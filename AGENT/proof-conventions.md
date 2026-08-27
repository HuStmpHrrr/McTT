# Proof conventions

Prime directive: **use an existing tactic; if it almost works, improve it; write
a new one last.** See [`README.md`](README.md). Full tactic reference:
[`../doc/tactics.md`](../doc/tactics.md).

## 1. Which tactic do I want?

Before writing anything, check whether the step you are about to do by hand is
already a tactic.

| You need to… | Use |
| --- | --- |
| Close the goal | `mautosolve` / `mautosolve 4`, or `mauto n` |
| Get side conditions of a judgment (`⊢ Γ`, `Γ ⊢ A : Type@i`, …) | `gen_presups` |
| Reconcile two derivations of the same deterministic judgment | `functional_eval_rewrite_clear`, `functional_read_rewrite_clear`, `functional_nbe_rewrite_clear`, `functional_alg_type_infer_rewrite_clear` |
| Clean up a pile of `eval_*` hypotheses | `simplify_evals` |
| Collapse two names for the same PER element relation | `handle_per_univ_elem_irrel` (contexts: `handle_per_ctx_env_irrel`) |
| Collapse two names for the same glue predicate | `handle_functional_glu_univ_elem` (contexts: `handle_functional_glu_ctx_env`) |
| Open a glue hypothesis | `simpl_glu_rel` |
| Invert an `Equations`-defined relation | `invert_per_univ_elem`, `invert_glu_univ_elem`, `invert_glu_rel_exp`, `invert_glu_rel_sub` — never raw `inversion` |
| Instantiate a `forall c c', in_rel c c' -> …` hypothesis | `destruct_rel_mod_eval` / `destruct_rel_mod_app` / `destruct_rel_typ` / `destruct_glu_rel_*_with_sub` |
| Open the existentials of a completeness judgment | `eexists_rel_exp`, `eexists_rel_sub`, `eexists_subtyp` (+ the per-case `eexists_rel_exp_of_*`) |
| Get reflexivity instances out of a PER hypothesis | `saturate_refl`, `saturate_refl_for <head>` |
| Get the syntactic consequences of glue membership | `saturate_glu_info`, `saturate_weakening_escape` |
| Do the same thing to every hypothesis | `on_all_hyp: fun H => …`, or `match_by_head <head> ltac:(fun H => …)` |
| Invert without risking a case split | `progressive_invert`, or wrap in `directed` |
| Discharge an extraction obligation | the `impl_obl_tac` of that file |

If your step is not in this table, it is still worth grepping
`doc/tactics.md` — the index there is complete.

## 2. How to improve a tactic

In order of preference — the cheapest fix is usually the right one.

1. **Add a hint, not a tactic.** Most "`mauto` can't do this" problems are a
   missing `#[export] Hint Resolve <lemma> : mctt`. No tactic changes, and
   every other proof benefits. If a rewrite is what's wanted, use
   `#[export] Hint Rewrite -> <eq lemma> using <side-condition tac> : mctt`
   (precedent: `wf_exp_eq_pi_sub` with `pi_univ_level_tac`,
   `Core/Syntactic/System/Tactics.v:17`).
2. **Add a case to the dispatcher.** The saturation and obligation tactics are
   `match goal` dispatch tables. A new judgment form gets a new branch in
   `gen_core_presup`; a new order predicate gets a new branch in the relevant
   `impl_obl_tac1`. Copy the shape of the neighbouring branches, including
   their guards.
3. **Extend a fallback chain.** `invert_*` and `*_econstructor` tactics are
   `tac_a + tac_b + tac_basic` chains, cheapest and most informative first.
   A new clean-inversion lemma goes at the front.
4. **Redefine with `::=` only when you must.** If the stronger alternative only
   exists later in the dependency order, `::=` is the sanctioned escape hatch
   (precedent: `invert_glu_rel_exp` in `Core/Soundness/UniverseCases.v:56` and
   `Core/Soundness/NatCases.v:61`). Only ever *prepend* alternatives, never
   remove one — and note it, because it makes a tactic's meaning depend on
   what has been loaded.
5. **Supersede properly.** If a new lemma should replace an old hint rather
   than compete with it, `Remove Hints` the old one (precedent:
   `Core/Syntactic/SystemOpt.v`, where the optimized rules with fewer premises
   displace the raw constructors).
6. **New tactic, last resort.** Put it in the layer's `Tactics.v` /
   `CoreTactics.v`; general-purpose Ltac with no McTT vocabulary goes in
   `theories/LibTactics.v`.

## 3. Invariants you must not break

These are the ways an edit to a tactic goes wrong silently.

- **Saturation loops need a terminator.** Every `repeat`-driven saturation
  tactic either ends in `fail_if_dup` or guards its `match` against facts it
  already derived. Drop the guard and you get a non-terminating `repeat` (or,
  worse, one that terminates only because of an unrelated failure). Remember
  `fail n` decrements once per enclosing `match goal` — that is why the levels
  are 1, 2, 3 in different places, and why `fail_at_if_dup` takes the level as
  a parameter.
- **Pick a fresh mark level for a new hypothesis loop.** Taken: `0` for
  `on_all_hyp:` / `mark_all_with 0`, `1` for `destruct_rel_by_assumption` and
  `destruct_glu_rel_by_assumption`, `100` for `progressive_inversion`. Reusing
  a level makes two loops eat each other's marks.
- **Keep `directed` on inversions** unless you actually want the case split.
  It is a `numgoals` guard, and it is the only thing stopping
  `dependent destruction` from fanning a proof out into unrelated branches.
- **`clean replace` is supposed to fail on a no-op.** That is what makes it
  safe inside `repeat`. Do not "fix" it.
- **Keep the loud error messages.** The `functional_*` tactics use
  `fail 3 "… cannot be solved by mauto"` so that a missing functionality hint
  produces a legible complaint instead of a silent stall. Preserve that when
  you add a case.
- **Re-`fold` the abbreviations after `simp`.** `simp` unfolds
  `glu_typ_pred`/`glu_exp_pred` and friends, after which pattern matches stop
  firing; `handle_functional_glu_univ_elem` folds them back for exactly this
  reason. And after `simp per_univ_elem` / `simp glu_univ_elem`, fold the
  recursive occurrences back with `rewrite <- …_equation_1`.
- **`clear_defs` hard-codes signatures.** `Extraction/TypeCheck.v:83` clears
  the mutual recursive-call hypotheses and `fixproto` bindings by matching
  their spelled-out types. Change `type_check`/`type_infer`'s signature and it
  silently stops matching, and the obligations start failing confusingly.

## 4. Cost discipline

- **Always pass a depth.** `mauto 2` / `mauto 3` / `mauto 4` and
  `mautosolve 3` / `mautosolve 4` exist because the `mctt` database is large;
  bare `mauto` at depth 5 is the single biggest compile-time knob in the
  development. Use the smallest depth that works.
- Prefer `mauto n using lem` over adding a narrowly useful lemma to the
  database.
- `Proof with mautosolve.` plus `...` as the end tactic is the house style
  (`foo; bar...` means `foo; bar; mautosolve`). Note that under Rocq 9.2 the
  `...` end-tactic is deprecated (`deprecated-end-tac`, 237 occurrences) and is
  an outright **error** in a plain `Proof.` block with no `with` clause. If you
  add a proof, either give it a `Proof with` clause or write the end tactic
  out.

## 5. Known debt: the completeness layer lost its automation

The port left `Core/Completeness` proving by hand what it used to prove by
tactic: `destruct_rel_by_assumption` went from 94 uses to 0, `on_all_hyp` from
113 to 0, `mauto` from 138 to 14, while `destruct` went 26 → 286 and
`functional_eval_*` 7 → 112. The tactics are not obsolete — they match
`forall ρ ρ', {{ Dom ρ ≈ ρ' ∈ R }} -> _`, and `rel_exp_under_ctx` now has eight
binders in front of that. `LogicalRelation/Tactics.v` grew by one alias line in
the whole port.

This is the layer's main outstanding work, and it is worth roughly 1 000 lines.
In order of expected return:

1. Generalize `destruct_rel_by_assumption` / `on_all_hyp` past the eight leading
   binders, defaulting to `rel_sub_id` / `eval_sub_id` for the instance at `Id`.
2. Give the eighteen constructions in `Completeness/SubstitutionCases.v`
   `Hint Extern` entries keyed on the goal's substitution shape — none of them
   is currently reachable by automation at all.
3. Extend `functional_eval_rewrite_clear`
   (`Semantic/Evaluation/Lemmas.v:86`) to the four-value hypotheses; it is used
   12 times against 112 hand applications of `functional_eval_exp`.

Measurements and the full argument: `../doc/alignment.md` §6.

## 6. When a proof breaks

Diagnose in this order — it is almost always earlier in the list.

1. A hint is missing from `mctt`, or a depth is now too small.
2. A saturation tactic no longer fires because the hypothesis shape changed
   (usually a notation or a `simp`/`fold` mismatch — see *Invariants you must
   not break*).
3. An inversion tactic's clean-inversion premise can no longer be discharged
   by `eassumption`, so it silently falls through to the slow/raw alternative.
4. Only then is the proof itself wrong.

Fix it at the level you found it. A one-line patch to a shared tactic that
fixes twenty proofs is the good outcome; twenty inline patches are the bad one.
