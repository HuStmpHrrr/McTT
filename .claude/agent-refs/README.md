# McTT project agents

These are project-scoped custom agents, defined in `.claude/agents/`. This
directory and the main checkout's `.claude/` are untracked: they are never
committed.

| Agent | Role | Writes | Typical brief |
|---|---|---|---|
| `mctt-core-dev` | core syntax, judgments, semantics, metatheory, checker | `theories/Core`, `theories/Algorithmic`, `theories/Extraction` | a language feature or refactor of the core |
| `mctt-frontend-dev` | grammar, elaborator, its spec and proof, driver | `theories/Frontend`, `Cst`, `driver/` | a surface feature, error messages, elaborator simplification |
| `mctt-lib-author` | McTT library and example programs | `lib/`, `examples/`, their expect blocks | library growth or a restyle with new features |
| `mctt-integrator` | combine branches into one linear branch | an integration branch | the track commits, their order, and the notes |
| `mctt-verifier` | independent full check | nothing | a commit to verify, and its base |
| `mctt-researcher` | design studies with examples and costs | `.claude/plans/<topic>/` only | a research question |
| `mctt-cleanup` | mechanical passes that keep meaning: notations, docs, renames | many files, no semantic change | a uniform change |

**Shared rules:** `mctt-rules.md`, which every agent reads first.

**References:**
- `lib_rules.md`: library conventions;
- `doc_rules.md`: doc-comment rules;
- `mctt-assump/Assumptions.v`: the Print Assumptions theorem list.

**Worktrees and rocq MCP servers:** `.claude/worktrees/pool-01` … `pool-10`,
each with its server `rocq-pool-01` … `rocq-pool-10`. A brief must name one
free pool, and its branch (`wip/<topic>`). Check with `git worktree list` and
`git -C <pool> status` that the pool is free and clean.

**Briefs and plans:** `.claude/plans/` (untracked).

**Dispatch rule:** changes that touch the same core code go to one agent on
one branch, in sequence. Run agents in parallel only for independent work:
research, library programs, verification.
