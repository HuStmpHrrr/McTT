# core-let: algorithmic checker and extraction (resume note)

Branch `ext/core-let-algo`. Design: `AGENT/core-let.md`, section "Algorithmic
checker and extraction".

## Done (`d7fa490`, builds)
- `Algorithmic/Typing/Definitions.v`: `ati_let`, which infers `A` as a type,
  checks `M : A`, infers `B` in `Γ ▸ A ≔ M`, then takes `nbe_ty_f` of
  `C[Id,,M]`. Also `user_exp_let`. The variable rule needs no change.
- `Extraction/Evaluation.v`: `eeo_let` and the let clause of `eval_exp_impl`,
  which extends the environment.
- `Extraction/NbE.v`: `ie_cons_def` and the `ce_def` clause of
  `initial_env_impl`.
- The completeness lemmas of the implementations are unchanged.
  `initial_env_impl_complete` is closed.

## Drafted, unchecked (WIP commit after `d7fa490`)
- `Algorithmic/Typing/Lemmas.v`: let cases of `functional_alg_type_infer`,
  `alg_type_sound` (via `wf_let` and `soundness_ty'`),
  `alg_type_infer_normal`, and `alg_type_check_complete`.
- `Extraction/TypeCheck.v`:
  - `lookup` matches `cons e G` and returns `(ce_typ e)[↑]ʷ`. This part is
    checked.
  - `ti_let` in `type_infer_order`, and the let clause of `type_infer`, with
    4 obligations.
- `Extraction/GlobalCheck.v`: a `Γ ▸ A ≔ M` clause in `check_ctx` via
  `check_exp`.

## Next
1. Rebase or merge onto `ext/core-let` once Completeness and Soundness build
   there.
2. Build the drafts. Expect the `Next Obligation` blocks to need realigning,
   and auto-generated hypothesis names (e.g. `H1`) to need fixing.
3. `real-all`, then compare the main theorems' assumptions with
   `/tmp/mctt-assump/baseline-56e979d.txt`.
4. Probably unchanged: `Algorithmic/Subtyping/Lemmas.v`,
   `Extraction/Subtyping.v`, `Command.v`, `Entrypoint.v`.

## Tooling
Use the `rocq-core-let-algo` MCP server, which is scoped to this worktree.
`rocq_compile_file` takes the dune route and fails, so use `make -f
CoqMakefile.mk <file>.vo` from `theories/`.
