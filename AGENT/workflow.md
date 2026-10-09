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
dune exec mctt examples/Nary.mctt # end-to-end smoke test; must print `6 : Nat`
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

## Library pages

`dune exec mctt-doc -- lib OUT` writes one HTML page per unit of `lib/` to
`OUT` (CI: `html/lib/`); `mctt-doc --check lib` only reports, and
`mctt-doc --links lib X::Y name` prints where each occurrence of `name`
links to. It runs the checker on every unit, each as its own program
(about 21 s for `lib/`), and exits 1 if a name does not line up with its
token, a use does not resolve, or a unit's evals and its log differ in
number. Below each `eval`, a folded `<details>` box, indented to the eval's
column in characters (`Doc.col`, so Unicode tokens count as one), holds that eval's
output: the checker's log entry for it, printed by `PrettyPrinter`
(`eval_outputs`), so the text is exactly what `mctt` prints; a click on the
open output folds it again. An eval's extent is the span from its `eval`
token that the parser reads back as the same command (`Doc.eval_spans`). Names are resolved by the extracted `Elaborator.lookup`/`elab_cmd`
and the core's `def_site` (`Extraction/Privacy.v`), never by rules of its
own (`driver/Doc.ml`). Extraction exports `def_site` explicitly
(`CoqMakefile.mk.local-late`).

`make homepage` builds the whole deployed site in `html/`: it builds
anything not yet built, then copies in the coqdoc pages, the dependency
graph, the library pages and the README as `index.html` (needs `pandoc` and
Graphviz; `PANDOC=…` overrides the former). CI runs only this target.

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

The same holds from the PER model up: `completeness`, `soundness`,
`consistency`, the canonical forms and `prog_impl_*` are closed under the
global context, and `main_*` assume only `Parser.loc : Type`. Treat any axiom
as a regression. The two usual sources, both removed:

- `functional_extensionality_dep` comes with an `Equations … by wf` definition
  (its unfolding equation). `per_univ_elem`/`glu_univ_elem` are structural
  instead, through `per_univ_below`/`glu_univ_below`.
- `eq_rect_eq` comes with `dependent destruction` when it generalizes an
  argument heterogeneously and simplifies the `JMeq` by `simplification_heq`.
  A marked variable (`__mark__`, e.g. inside `on_all_hyp:`) has a type that is
  not syntactically its own, which is enough; `unmark_vars` first.

## Known non-problems

Do not "fix" these; they are expected.

- **Exactly 6 warnings on a clean build** (`make clean && make`, verified), all
  in the generated `Frontend/Parser.v` and all emitted by menhir's Coq backend,
  not by us: 4 `deprecated-from-Coq` on its own `From Coq Require …` preamble,
  and 2 `deprecated-exact-proof` on the `Proof eq_refl true<:...` of its
  `safe`/`complete` validators. Nothing else warns; treat a new warning as a
  regression. When tallying warnings with a script, note that a warning name can
  contain uppercase (`deprecated-from-Coq`) — a `[a-z0-9.,-]+` character class
  silently drops those records.
- **`make depgraphdoc` fails locally** with a `dot` assertion
  (`mincross.c:1314: flat_reorder`) — that is graphviz 2.30.1 on this host, not
  a Rocq problem. CI builds graphviz 12.1.1 from source, so CI is unaffected.
- **`theories/**/Parser.v` is generated** by menhir and gitignored. Never edit
  it; edit the `.vy` grammar.

## Timing the checker

Run times of `lib/` programs can move by several percent when unrelated OCaml
code changes. Before reading a regression into a difference, count calls with
OCaml-level counters around the functions involved (`nbe_ty_env_impl`,
`exp_sub` and the like) and measure CPU time (`getrusage`), not wall-clock
time; a change in call counts is a real cost, a change in time alone may not
be.

Almost all checking time goes to normalizations at the initial environment
of the context. The checker therefore carries that environment along
(`tenv` in `Extraction/TypeCheckBase.v`, `nbe_ty_env_impl` in
`Extraction/NbE.v`), and never rebuilds it per normalization.  The
refinements of the checker and of evaluation are in
[`refinement.md`](refinement.md).

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
