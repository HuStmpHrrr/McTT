# core-let: algorithmic checker and extraction (status note)

Branch `wip/core-let-algo`. Design: `AGENT/core-let.md`, section 8.

## Status: complete, everything builds

- `real-all`, `post-all`, `dune build` and `dune test` are all green.
- It merges `wip/core-let` (`09bd7bb`) and `wip/core-let-frontend` (`b9a7299`).
- The assumptions in `/tmp/mctt-assump/Assumptions.v` match
  `/tmp/mctt-assump/baseline-56e979d.txt` exactly, and `elaborate_core_iff` is
  closed.

## What changed

- `Algorithmic/Typing/{Definitions,Lemmas}.v`: `ati_let` and `user_exp_let`,
  with their cases in the existing lemmas.
- `Extraction/Evaluation.v`, `Extraction/NbE.v`: the let clause of
  `eval_exp_impl`, and the definition clause of `initial_env_impl`.
- `Extraction/TypeCheck.v`: `lookup` over any entry, `ti_let`, and the let
  clause of `type_infer`. `Equations` presents its four obligations last,
  after the `a_glob` ones, so they sit just before `Extraction Inline`.
- `Extraction/GlobalCheck.v`: the definition clause of `check_ctx`.

## Pitfall

`rocq_compile_file` takes the dune route and fails. Use
`make -f CoqMakefile.mk <file>.vo` from `theories/`.
