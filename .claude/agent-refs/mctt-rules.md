# Rules for every McTT agent

Read this first. The brief from the main session overrides it only where the
brief says so explicitly.

## Workspace

- **You work in one git worktree only,** given in your brief:
  `/local/home/zhonhu/workspace/McTT/.claude/worktrees/pool-NN`. Each worktree
  has its own rocq MCP server, `rocq-pool-NN`; use the one whose number
  matches. Never touch another worktree, the main checkout
  (`/local/home/zhonhu/workspace/McTT`) or any branch except your own.
- **Branches.** Your branch is `wip/<topic>`. `ext/` branches belong to the
  user: never commit to, reset or rebase an `ext/` branch, and never push.
- **History** is linear: rebase, never merge. Commit only states that build
  and pass. Mid-way WIP commits must be labelled, and squashed before you
  report.
- **Planning, exploration and scratch notes never go into a commit.** Put them
  under `/local/home/zhonhu/workspace/McTT/.claude/plans/`. Documentation of
  the code itself (`AGENT/` notes about definitions, `doc/`, docstrings) is
  fine.
- **Stash.** The git stash is shared across worktrees: never use a bare
  `git stash` / `git stash pop`.
- **Never spawn, resume or message other agents.** Only the main session
  dispatches work. If your brief puts work in scope that another role
  normally owns (e.g. front-end edits for a core agent), do it yourself,
  following that role's rules in `.claude/agents/<role>.md`. If you think
  the work needs another agent, stop and say so in your report.

## Rocq

- **Use the rocq MCP server for all Rocq work:** checking files, stepping
  through proofs, `Search`/`Check`/`Print`/`Compute`, and Print Assumptions.
  - Don't run `rocq c`, `coqc`, `coqtop` or per-file `make` by hand.
  - The only exception is the full build:
    `make -f CoqMakefile.mk real-all` then `make -f CoqMakefile.mk post-all`,
    in `theories/`.
- **Print Assumptions,** after a full build: use `rocq_query` in *preamble*
  mode, e.g. `preamble="From Mctt Require Import Entrypoint."`,
  `command="Print Assumptions Mctt.Entrypoint.main_sound."`.
  - File mode (`rocq_assumptions`, or `file=`) re-runs the file
    interactively. It can then report `abstract` subproofs as axioms, and its
    output gets truncated by "Fetching opaque proofs" messages.
  - The theorem list is
    `/local/home/zhonhu/workspace/McTT/.claude/agent-refs/mctt-assump/Assumptions.v`,
    plus whatever new top-level theorems you add.
- **Baseline:** no axioms anywhere, except `Parser.loc : Type` for
  `main_sound` / `main_complete`. Menhir generates it; leave it.
- **Driver build:** `dune build --root .` and `dune test --root .` at the
  worktree root. Plain `dune` picks up the parent project.

## Invariants of the development

- **Presupposition:** never weaken a presupposition statement; prove a helper
  instead.
- **Mutual block:** all wf judgments stay in one mutual `Inductive … with …`
  block.
- **No fuel,** anywhere (Bove–Capretta / Equations / well-founded orders
  instead).
- **NbE performs no term transformations.** Evaluation and readback never
  weaken, substitute, shift, instantiate or otherwise rewrite terms, nor any
  new operation of that kind, and never construct terms. They may look
  things up, extend environments and build names.
- **Notations in statements:** write judgments with their notations
  (`Θ ⍮ Ξ ⍮ Γ ⊢ M : A`), never raw `wf_exp …`. Raw forms are only for
  partial applications, scheme motives and tactic patterns.
- **Core over elaborator:** put feature logic in the core (typing, the command
  judgment, semantics). Never add work to the elaborator; move work out of it
  where you can.
- **Privacy** is checked once per command, by the command judgment, outside
  typing. Typing and δ ignore privacy.
- **Shared tactics:** prefer improving them (`mauto`, the inversion and
  presupposition tactics) over ad-hoc proof scripts.
- **Read** `AGENT/README.md`, `AGENT/notations.md` and
  `AGENT/core-modules-decisions.md` before changing `theories/`.

## Definition of done (unless your brief says otherwise)

1. A clean `real-all` + `post-all` build with 0 warnings.
2. `dune build --root .` and `dune test --root .` pass, and every changed
   expect line is reviewed and justified in your report.
3. Every `lib/*.mctt` program and every Prelude unit exits 0, run from
   `lib/`. `examples/` behaves as before (the `examples/multi` negative cases
   fail on purpose).
4. No admits. Print Assumptions matches the baseline.
5. A final report: commits, new definitions with their Rocq types, a worked
   example, line-count deltas, Print Assumptions, files touched outside your
   scope, and anything unresolved.

## Writing for the user

- **Define before use.** Every symbol is defined, or obvious from context,
  before it is used.
- **Concrete over abstract:** concrete Rocq types and worked examples, not
  summaries.
- **Feature misbehaviour:** report a minimal reproducer; never work around it
  silently.
