# Workflow notes

Setup (opam switch, pins, `coq-menhirlib`, `coq-lsp`) is in
[`../README.md`](../README.md) and is authoritative. This file only records what
the README does not.

## Build and verify

The switch is `rocq-9.2.0` (OCaml 5.4.1). Either `eval $(opam env --switch=rocq-9.2.0)`
first, or prefix commands with `opam exec --switch=rocq-9.2.0 --`.

```sh
make                              # build everything (Rocq + OCaml driver)
dune runtest                      # the test suite — NOT mentioned in README.md
dune exec mctt examples/nary.mctt # end-to-end smoke test; must print `6 : Nat`
```

Treat a change as verified only when all three pass, **and run `make` before
`dune`**. Neither half catches the other's breakage:

- `make` alone misses extraction and driver breakage, which surfaces in
  `dune runtest` and the smoke test.
- `dune` alone misses it too, and more insidiously. `driver/extracted/` is
  generated (by the `post-all` hook in `CoqMakefile.mk.local-late`, which runs
  `Separate Extraction main.` on `Entrypoint.v`) and gitignored, so `dune build`
  happily compiles against a **stale** extraction from an earlier constructor
  set. Only `make` regenerates it. This is how removing a constructor from `exp`
  can leave `dune build`, `dune runtest` and the smoke test all green while
  `make` fails on a hand-written match in `driver/` — the port hit exactly that
  with `Coq_a_sub` in `driver/PrettyPrinter.ml`.

So: after any change to `theories/Core/Syntactic/Syntax.v`, or to anything
`Entrypoint.v` extracts, `make` from the repo root is the only real check.

Rocq builds are slow, so `make` incrementally during development and do
`make clean && make` once before declaring victory. Redirect to a log and grep
it rather than reading it inline — a clean build is ~3000 lines.

Other targets: `make pretty-timed`, `make coqdoc`, `make depgraphdoc`,
`make clean`. The root `Makefile` just runs `make -C theories` then
`dune build`; `theories/Makefile` is checked in and delegates to the generated
`theories/CoqMakefile.mk` (gitignored — `CoqMakefile.mk.local` and
`.local-late` are the hand-written hooks, and are checked in).

## Verifying a partial build

If `_CoqProject` is ever trimmed to a prefix of the development again (the port
did this while it was in progress), `make -C theories` fails for a reason that is
not Rocq's: the `post-all` hook extracts `Entrypoint.v`, which a trimmed project
does not list. Verify such a stage by naming the topmost `.vo`, which skips
`post-all`:

```sh
make -C theories Core/Syntactic/Substitution.vo
```

Two accompanying traps:

- `theories/Makefile`'s `update_CoqProject` regenerates `_CoqProject` from
  `find`, undoing the trimming. Do not run it while files are being added and
  removed.
- `.vo` files of *unlisted* files are not cleaned by `make clean` (Rocq's
  `cleanall` only knows the listed ones), and a stale one gives
  `makes inconsistent assumptions over library ...`. Wipe them by hand:
  ```sh
  find theories \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' \
                -o -name '*.glob' -o -name '.*.aux' \) -delete
  ```

## Axioms

The **syntactic** layer is closed under the global context, and should stay that
way; check with `Print Assumptions <lemma>.` It is why pointwise equality, not
functional extensionality, is used for the function-valued `wk` and `sub`.

From the PER model up this is no longer true and is not meant to be:
`Print Assumptions completeness` reports `functional_extensionality_dep` (from
the `pose proof (@relation_equivalence_pointwise env)` in `per_ctx_env_sym`) and
`eq_rect_eq` (from `Equations`). Both predate the port — the footprint is exactly
that of the explicit-substitution development. Treat a *new* axiom as a
regression; treat these two as the baseline.

## Known non-problems

Do not "fix" these; they are expected.

- **268 warnings on a clean build** (`make clean && make`, verified). 129
  notation `level-tolerance`, 98 `deprecated-end-tac` (the `...` end-tactic —
  see *Cost discipline* in `proof-conventions.md`), 23 "notations at level 0
  should be closed",
  6 `per_univ_elem_core is nested using rel_mod_eval`, 5 `From Coq` (in the
  generated `Parser.v`), and a handful of others. All benign under Rocq 9.2.
- **`make depgraphdoc` fails locally** with a `dot` assertion
  (`mincross.c:1314: flat_reorder`) — that is graphviz 2.30.1 on this host, not
  a Rocq problem. CI builds graphviz 12.1.1 from source, so CI is unaffected.
- **`theories/**/Parser.v` is generated** by menhir and gitignored. Never edit
  it; edit the `.vy` grammar.

## rocq MCP server

Registered local-scope for this repo (LLM4Rocq/rocq-mcp), giving interactive
`pet`-backed proof stepping.

- `ROCQ_WORKSPACE` must be **`<repo>/theories`**, not the repo root, and `file`
  arguments are relative to `theories/` (e.g. `Core/Syntactic/Substitution.v`).
  rocq-mcp resolves a relative path against the project root it finds by
  walking up for `_CoqProject`/`dune-project`; with the repo root as workspace
  it lands on `theories/` and produces `theories/theories/Foo.v` →
  "File not found".
- `rocq_step_multi` takes `from_state` (not `state_id`) and runs each tactic in
  its list *independently from that same state* — it explores candidates, it
  does not apply them in sequence. Useful for checking whether an existing
  tactic already closes a goal before writing a new one.
