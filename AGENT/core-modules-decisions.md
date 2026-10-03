# Core modules: decisions, paths taken, and the design as of 2026-10-02

This note records every decision made about local and global module bindings
in the core, the alternatives that were rejected and why, and the current
concrete design. It is written so that the effort can be restarted from it.
The frozen design document `AGENT/core-modules.md` (branch `wip/core-modules`)
is still the reference for syntax and typing. Its semantics (§3–§4) is
**superseded** by §5 below.

## 1. Goal and standing priorities

- **Goal:** global and local module bindings in the *core*:
  ```
  module X (a : A) (b : B) := Y::Z aaa bbb                 (global alias)
  let module X (a : A) (b : B) := Y::Z aaa bbb in body     (local alias)
  let module X (a : A) where def … end … end in body       (local body)
  ```
  They must have real typing and wf judgments, so that the elaborator and its
  spec become thin.
- **Priority, from the user:** lower the elaborator's burden. More core work is
  acceptable. Any design that adds elaborator work is rejected.
- **Invariants that must hold throughout:**
  - NbE stays proved sound and complete;
  - evaluation and readback build no syntax;
  - no axioms (the baseline is none, plus `Parser.loc` for `main_*`; see
    `AGENT/workflow.md`, "Axioms");
  - all wf judgments stay in one mutual block;
  - presupposition statements are never weakened;
  - zero build warnings at merge.
- **How questions are asked:** every question to the user comes with a concrete
  program and the outcome under each option, never as text only.

## 2. Exploration of the overall approach (four design studies)

| Variant | Branch | Idea | Verdict |
|---|---|---|---|
| models | `wip/mod-models` | a local module occupies a de Bruijn index and evaluates to a module value | **chosen** (in the term context) |
| alias-as-δ | `wip/mod-alias` | aliases only; members unfold δ-style | rejected: `let module` would be inlined by the elaborator at each use, which is elaborator work |
| module context | `wip/mod-modctx` | a separate module context Ψ | rejected: 1.5–2.5k more lines than the term context for the same result; its frame-as-entry idea was considered (see §3.2) |
| flattening | `wip/mod-flatten` | local members become `ce_def` entries | rejected: k-indices is infeasible, because the elaborator doesn't know imported units' members |

## 3. Decisions on syntax and typing (in order)

### 3.1 Sorts
- **No signatures (`msig`), anywhere.** A member's type is computed when
  needed by the relation `member_type` / `unit_member_type`. A body member's
  type is the `A` of its `ge_def`. An alias member's type is the target
  member's type instantiated with the arguments. The reason: signatures were a
  cache, and if the syntax carried them the elaborator would have to write
  them.
- **Module expressions are their own sort**; `exp` is never reused:
  ```coq
  modexp ::= me_path path | me_var nat | me_mem modexp string | me_app modexp exp | me_lit gunit
  ```
  `me_lit` is produced only by the module-ζ rule.
- **Substitution entries** are `sentry ::= se_var nat | se_exp exp | se_mod modexp`.
  - The name mirrors `centry`; the earlier name `simg` was unclear.
  - `se_var` is needed because, without it, composition
    `M[σ][τ] = M[σ ⨟ τ]` fails across sorts.

### 3.2 Scope
- **Open frames stay as they are.** References to members of open modules
  carry explicit frame arguments, and `preapp` stays in the elaborator. Turning
  frames into context entries was rejected by the user ("today's handling is
  acceptable").
- **Local bodies** may contain:
  - definitions;
  - nested modules (Q1 = b);
  - `private`;
  - imports, as check-only entries (A = b).

  `abstract` and `eval` are rejected in local bodies by the core (B = a).
- **Alias arity** must be exact or partial; surplus arguments are an error
  (Q2 = c).
- **Every import is a core command,** including imports of submodules of the
  current unit. The core checks the target, privacy and the `use` names
  (Q3 = b).
- **Alias arguments are checked eagerly** against the target unit's parameters
  (Q4 = b), via `wf_mod_args`.
- **One grammar for local and global module bodies.** The same nonterminal and
  `Cst` constructor serve both (`mdecl ::= params_opt mdef`,
  `mdef ::= WHERE cmds END | ":=" obj`) (Q5 = b).
- **`let module X := 3` is rejected** (Q6 = a). It is now syntactically
  impossible, since `3` is not a `modexp`.

### 3.3 Later fixes found during implementation
- **Nested module after a definition.**
  - The problem: the member type of a nested module's member contains a `let`
    for an earlier sibling definition, as in `M.N.c Nat Nat` in §6, so
    `member_type_app` got stuck.
  - Decision (b): member typing unfolds `let` (and `let module`) before
    applying the next argument, via `member_type_let` and
    `member_type_let_mod`.
- **The outermost open frame.**
  - The problem: `⊢g` accepted a stack whose outermost frame is a submodule,
    e.g. `[Main.M]` with `Main` not open. That breaks "if a path resolves, its
    prefixes resolve".
  - Decision (b): `frame_fresh` requires `p_mems mp = nil` for the outermost
    frame, so `wf_gc_resolve_prefix_closed : ⊢g → gc_resolve_prefix_closed`
    needs no extra hypothesis.
- **Equivalent substitutions give different units.**
  - The problem: under `σ ≈ σ'`, a slot holds `U[σ]` and `U[σ']`, which are
    syntactically different. For example, `def f : Nat := 1 + 1` against
    `def f : Nat := 2`.
  - Decision: **module equivalence is pointwise.** Add the judgments
    `Γ ⊢ U ≈ U'` and `Γ ⊢ H ≈ H'`, entry by entry in the same order, since
    substitution never reorders entries. Add congruence rules for
    `let module`, `a_mem`, `me_app`, and for slots in contexts.

## 4. The PER saga: why the design's semantics was replaced

1. **The design's clause relates expansions.** Its slot clause related each
   member's *expansion* (`member_expansion U ch`, a term built by syntax). But
   the environment holds module values, and the initial environment stores the
   module value. So `per_ctx_then_per_env_initial_env` was unprovable.
   - Counterexample: `U_bad := gu_mk [ce_mod U0] (md_alias q)`, with
     `q.f : Nat := zero`.
   - Its expansion of `f` evaluates to `zero`, but its module value waits for
     one parameter, so the slot is "related" while its initial environment is
     not.
2. **Five explorers tested fixes.**
   - (a) "closures related" premise: the expansion premise turned out to be
     redundant.
   - Restricting to well-behaved units: no purely syntactic condition on the
     unit suffices.
   - (c) a member-wise PER over closures: works; completeness needs only
     "model ⇒ expansion", which is proved.
   - Changing the module value's shape: selection agrees with the expansion
     for *every* unit (`unit_arity`, `eval_tele`, stepwise selection).
   - Syntactic same-unit: same unit in *contexts* works, but "relate values
     by same unit plus environment" is **proved unstable under substitution**
     (`wip/per-syntactic`, `experiments/per_slot_syntactic/Exp.v`).
3. **The user's diagnosis:** module values were mixed into `domain`, which
   forced an intertwined semantics. Modules must evaluate to a *different*
   type. That is the current design, §5.

## 5. The current semantic design (being built on `wip/cm-semantic-split`)

```coq
Inductive dmod : Set :=
| dm_global : path -> list domain -> dmod                 (* global module, arguments so far *)
| dm_local  : env -> gunit -> list domain -> dmod         (* local unit over an environment, arguments so far *)
| dm_member : dmod -> list string -> dmod.                (* submodule chain of a module still lacking
                                                             arguments: a module closure, like a λ *)
Inductive dentry : Set := de_term : domain -> dentry | de_mod : dmod -> dentry.
Abbreviation env := list dentry.

(* domain gets exactly one module-related constructor: *)
| d_member : dmod -> list string -> domain                (* member chain of a module still lacking
                                                             arguments: the semantic λ of X.f *)
```
- **Two evaluation relations:** `⟦ M ⟧ρ ↘ d : domain` and `⟦ H ⟧ᵐρ ↘ m : dmod`.
- **Selection is δ.** On a saturated module, `a_mem H x` immediately gives
  `x`'s bound value: it evaluates the body up to `x`, or selects from the
  alias's target. On an unsaturated one it gives `d_member` (term side) or
  `dm_member` (module side). Applying either adds an argument.
- **Module arguments are terms,** so a module cannot be passed as an argument.
- **Readback and normal forms** never contain modules.
- **The initial environment** puts `de_mod (dm_local ρ U [])` in a `ce_mod U`
  slot.
- **The module PER `per_dmod`** is closure-style, the way `Π` relates
  λ-closures. Values are compared through what their parts evaluate to, never
  by comparing syntax or environments directly.
  - **`dm_global`:** same path, arguments related at the parameter types.
  - **`dm_local`:**
    - parameters walked outermost first, each type related;
    - supplied arguments related, missing ones quantified over related pairs;
    - then the bodies related entry by entry, with the same names and kinds in
      the same order;
    - aliases related through their targets' values.
  - **`dm_member`:** componentwise.
- **The slot clause** relates `Γ ▹ₘ U` with `Γ' ▹ₘ U'` for possibly
  *different*, pointwise-equivalent units: unit equivalence is in the syntax,
  so the PER must model it too, not only equal units. Its premise is that the
  two units' module values over related tails are related in `per_dmod`. Its
  environment relation ties each head to its own unit's module value, on both
  sides.
- **Left to completeness (M4):**
  - "related module values have related members";
  - the bridge "model ⇒ expansion", which validates `a_mem H x ≡ expansion`.

## 6. Worked examples that drove the decisions

```
let module X (n : Nat) where def f : Nat := n end in X.f 3 end              -->  3
let module X (n : Nat) where module V where def f : Nat := n end end in
  let module P := X.V in P.f 3 end end                                       -->  3   (dm_member)
(fun (n : Nat) -> let module X where def f : Nat := n end in X.f end) 3     (β substitutes into the unit:
                                                                              pointwise equivalence)
let module M (A : Type@0) where def x : Nat := zero end
  module N (B : Type@0) where def c (y : B) : B := y end end in
  M.N.c Nat Nat 3 end                                                        -->  3   (member_type_let)
```

## 7. Branch map (nothing pushed)

| Branch | Tip | Contents | Status |
|---|---|---|---|
| `wip/core-modules` | `e36fc33` | frozen design doc + prototype | reference; semantics superseded |
| `wip/cm-syntax` | `95d79b2` | M1: syntax, schemes, substitution, `member_type` | done |
| `wip/cm-system` | `7608547`+ | M2a/M2: judgments, syntactic metatheory | in progress (`sub_eq_preserves_exp`, pointwise equivalence, `member_type_let`, `frame_fresh`) |
| `wip/cm-semantic-split` | in progress | M3 on separate module values (§5) | **current semantics** |
| `wip/cm-frontend` | `2ebc436` | M7: front end, elaborator shrank from 2918 to 1958 lines | done (expect outputs are predictions) |
| `wip/cm-algo` | `e4da00a` | M6 definitional half, `MemberSearch.v` (Equations, currently fuelled) | being redone without fuel; needs the new semantic interface |
| `wip/cm-algo-draft` | `acd7029` | rest of M6 against stubbed M5 statements | WIP, stubs in `Extraction/M5Stubs.v` |
| `wip/cm-semantic`, `-model-premise` | `82ebeff`, `28c6cd1` | old mixed-domain semantics | **superseded**, reference only |
| `wip/per-*` (5) | see `git log` | PER explorations | reference only |
| `wip/mod-*` (4) | see `git log` | design studies | reference only |

## 8. Open obligations

- **No fuel, by the user's decision.** The member and parameter search
  recurses structurally on (global-context prefix, local-context prefix,
  syntax):
  - an alias's target is resolved in the global-context prefix before the
    alias;
  - a slot's unit is checked in the local context below the slot.

  The key lemma is that prefix resolution agrees with full resolution, via
  `gc_sub`. This replaces L8 and the interim `search_complete` hypothesis.
  The completeness theorems keep their baseline statements.
- **M4:**
  - related module values have related members;
  - the model ⇒ expansion bridge;
  - commutation of module values under `q σ`.
- **M2:** `sub_eq_preserves_exp`, with the pointwise equivalence.
- **Integration:**
  - the `Derive NoConfusion` for the syntax moves from
    `Extraction/Evaluation.v` to `Syntax.v`;
  - driver tests for the core's module errors;
  - `AGENT/elab-spec.md` needs rewriting for the new spec.

## 9. Lessons for a restart

1. **Fix the value sorts before writing any PER.** Decide what modules evaluate
   to (a separate `dmod`) and what environments hold (`dentry`) first. The
   expansion-based PER failed because modules and terms shared `domain`.
2. **Decide the notion of module equivalence up front.** Use pointwise, entry
   by entry. Substitution forces it into both the syntax (`sub_eq`) and the
   PER. Syntactic same-unit holds only for contexts.
3. **Under-applied selection needs its own values** on both sides (`d_member`,
   `dm_member`). Treat them as closures, like λ.
4. **Write the counterexample programs (§6) as tests early.** Each of them
   overturned a design point.
5. **Keep expansions (`member_expansion`) out of the semantics.** They belong
   to typing and to the completeness bridge only.
