> The code of this experiment was removed; it is in commit 842d4d8 under `experiments/value_msub/`.

# Approach Z: moving values along a module substitution

Proofs in `Exp.v` (compiles with `rocq c -R . Mctt`, no admits; only
`functional_extensionality_dep` via `per_univ_elem`).

- Push, evaluation and readback: `dpush` action on values; `eval_push` (:101),
  `read_push` (:174), `dpush_dpush` (:199), first-order PERs (:226-248). Cheap.
- Push, PER: `per_univ_elem_push_dense` (:269) holds only under `Dense` (every
  GC2-related argument is an image), which is false (`dense_fails`, :346): the Π
  case ranges over arguments headed by, or closures mentioning, the new frame.
  Renaming invariance covers only neutrals. Fix: a PER Kripke over global-context
  extensions (restating `per_univ_elem`, ~6.5k lines of rework).
- Close: no value-level action makes sense (parameters become values, envs grow,
  readback does not commute: `close_readback_not_msub`, :394). Use term-level
  transport for close.
