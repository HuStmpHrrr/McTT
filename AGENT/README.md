# Notes for agents working on McTT

Read this before touching `theories/`.

## The working agreement

**Favour using and improving the existing tactics over writing new ad-hoc proof
scripts.** This codebase is deliberately tactic-driven: the metatheory is proved
by saturating the context with derived facts and letting `mauto` close the goal.
A proof that inlines a bespoke script where a tactic exists is a regression even
if it compiles — it will not survive the next refactor, and it hides the fact
that the tactic was one case short of handling it.

Concretely, in order of preference:

1. Use the existing tactic.
2. Make the existing tactic work — add the missing hint, the missing `match`
   case, the missing alternative in a fallback chain.
3. Only then write something new, and put it in the layer's `Tactics.v` /
   `CoreTactics.v` rather than inline in a proof.

The details, including a decision table for "which tactic do I want" and the
invariants you must preserve when editing one, are in
[`proof-conventions.md`](proof-conventions.md).

## Map

| Where | What |
| --- | --- |
| [`substitution-port.md`](substitution-port.md) | The port to meta-level substitutions (complete): design, order of the development, deviations from the paper, the four-value pattern, and the accumulated gotchas. **Start here before touching anything under `theories/Core/`.** |
| [`proof-conventions.md`](proof-conventions.md) | How to pick, extend, and safely edit tactics. |
| [`notations.md`](notations.md) | The level scheme of the `exp`/`nf`/`domain`/`judg` custom entries. Read before adding or moving a notation. |
| [`workflow.md`](workflow.md) | Build, test, and verification commands; environment gotchas. |
| [`../doc/tactics.md`](../doc/tactics.md) | Reference for all 224 `Ltac`/`Tactic Notation` definitions, grouped by layer, with `file:line` for each. |
| [`../doc/alignment.md`](../doc/alignment.md) | Where the mechanization diverges from `paper.pdf` and `main.pdf`, and answers to the papers' open questions. The one place that cites them by number. |
| [`../README.md`](../README.md) | Toolchain setup (Rocq 9.2.0, opam pins, `coq-menhirlib`, `coq-lsp`). Authoritative — do not duplicate it here. |

Keep these files short. If something belongs in the user-facing `README.md` or
in `doc/`, put it there and link to it.
