# Core modules: decisions, paths taken, and the design as of 2026-10-03

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
  modexp ::= me_unit path | me_var nat | me_mem modexp string | me_app modexp exp | me_lit gunit
  ```
  (`me_path` of a qualified name until 2026-10; see §10.1.)
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
  - imports, as check-only entries (A = b).

  `private` was allowed until 2026-10; it is now an elaborator error (§10.3).

  `abstract` and `eval` are rejected in local bodies (B = a); since 2026-10
  `eval` is rejected by the elaborator (§10.3).
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

## 10. The refactor of 2026-10 (`wip/lm-refactor`)

### 10.1 Paths name only units
- `path` is a unit's name, `list string` (it replaces `fpath`).  The syntax
  names only units: `me_unit : path -> modexp`.
- `a_glob` is gone.  A global is a chain of selections from its unit,
  `a_mem (me_mem … (me_unit fp) …) x`; `qname_term`/`qname_mod` build it and
  `mod_qname` reads a chain back.
- A qualified name is the record `qname` (`q_unit : path`, `q_chain`), the key
  of resolution and the name a global value carries (`dm_global`, `d_glob`,
  `ne_glob`).  It is not syntax.
- A chain into an open frame is not a module expression of a closed module, so
  it has its own typing rules (`wf_mem_glob`, `wf_me_glob`), keyed on
  `mod_qname`.
- Evaluation and readback build no syntax: `⟦ me_unit fp ⟧ᵐ ↘ dm_global …`,
  selection from a global is a lookup (`eval_sel_global`), and an opaque
  definition or an axiom is a neutral `d_glob` at its type
  (`eval_sel_global_neut`).

### 10.2 Privacy is a check of the command judgment
- **One check, in `run_cmd`, outside typing** (`Core/Syntactic/System/Privacy.v`).
  Typing and δ read no privacy flag; `member_type` returns private members.
  Typing must stay monotone under `gc_sub` (closing and filing a module), and
  stored bodies and types may name private members, so privacy cannot be a
  typing premise.
- `acc_ok Θ Ξ refs`: every member reference rooted at a unit, written in the
  command, is to a public member or to one declared in an open frame or an
  ancestor of one.  `mdecl` finds the declaring module, following aliases
  through `gc_module`/`mr_alias`.
- Scanned: `def` (type and body), `eval` (term and type), module parameters,
  alias parameters, target and arguments, imports (target and `use` names),
  unit parameters, and the imports of local bodies inside any of these.
- The extracted checker decides it (`Extraction/Privacy.v`, `refs_check`);
  `prog_impl_*`/`main_*` keep their statements.
- The driver says `Error: Lib::Priv.s is private`, naming the member by the
  module that declares it, after aliases (`q_unit`, then the chain).  This
  choice was left to us: it is what the check computes, and it is the same
  whichever alias the reference went through.
- **Private modules** (`private module X …`, also for aliases).  The flag is
  data on the entry, `ge_mod : bool -> gunit -> gentry`, and on the commands
  `cc_mod`/`cc_alias`; typing ignores it, `body_shape` compares it, and the
  command check enforces it: `gc_entry` reads the entry a path names, and
  `mdecl` declares a submodule as it does a definition (`mdl_entry`, with
  `ge_private`).  `me_mem H y` is a reference `(H, y)` like `a_mem H x`.
  `private module A.B` makes only `B` private.  A chain *past* an alias is
  declared in the alias's target (`mdl_alias`, `r <> nil`); the alias itself
  is an entry like any other.
- Only unit-rooted references were checked at first, so `private` in a local
  body was an elaborator error; since §10.7 the check also resolves
  references through local modules, and local bodies may be `private`.

### 10.3 Local bodies
- Imports stay allowed in local bodies; since §10.7 they are the pre-form
  `gm_import`, expanded into entries before typing.
- `bc_eval` is gone: `eval` in a local body is an elaborator error,
  `eval is not allowed in a local module`.
- A local import of a unit must name an imported unit (`loaded`):
  `Error: the unit is not imported`.
- `private def` and `private module` are allowed in a local body (they were
  elaborator errors before §10.7): `let module L where private def s : Nat
  := 1 end def t : Nat := succ s end end in L.t end` gives `2`, and `… in
  L.s end` gives `Error: s is private`.  The message names the member from
  the local module, which has no name in the core.
- A local `use (n; n)` naming a member twice is rejected by the core
  (`xe_fresh`, `n is already declared`) since §10.7.

### 10.4 Module arities are telescopes
- `member_type … ch R` with `R : mres := mr_term typ | mr_mod ctx`.  A module's
  arity is the telescope of parameters it still takes, innermost first,
  extended (`mres_gen`, `T ++ Δ`) by the bodies and parameters around it.
- `tele_view T` is the outermost assumption and the rest, the definitions and
  modules outside it substituted away; `tele_inst T N` instantiates it.  It is
  computed on the reversed telescope, as `pi_view` is on a type.
- `wf_me_app` checks the argument against `B` where `tele_view T = Some (B,
  T1)`; an empty telescope rejects further arguments, and partial application
  stays (`F ℕ` has arity `⋅ ▹ Π ℕ ℕ` for `F (A : Type@0) (f : A -> A)`).
  `amod_app` checks against `B` directly, with no normalization.
- The semantics reads member types through `mres_ty` (`ctx_pi T ⊤` for a
  module), and `tele_view_pi` relates the two views; so the PER model,
  completeness and soundness are unchanged in substance.  `arity_pi` derives
  the `Π` of an arity from `sem_mt`, which replaced the rule's former
  `A ≈ Π B C` premise.
- `mkind` survives as `mres_kind`, the sort of a member; the termination order
  `mt_order` and the extracted `member_type_impl` no longer take a kind
  (member types are unique: `member_type_functional`).

### 10.5 Notations
`⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms`, `$*| f & ns | Θ ⍮ Ξ ↘ r`, `$ᵐ| h & n | Θ ⍮ Ξ ↘ h'`,
`h ·ₜ x Θ ⍮ Ξ ↘ d`, `h ·ₘ y Θ ⍮ Ξ ↘ h'`, `h ·ₜ* ch Θ ⍮ Ξ ↘ d`,
`h ·ₘ* ch Θ ⍮ Ξ ↘ h'`, `⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ'`, beside `⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h`.
The selected name and the chain are at level 0.

### 10.6 Optional `let` annotations
`b_def : option exp -> exp -> bnd`; `ℓ A ≔ M in B` is `b_def (Some A)`,
`ℓ ≔ M in B` is `b_def None`.  Context entries stay `ce_def A M`, and
telescopes (`ctx_pi`) still generalize definitions with their type.
- **One rule per judgment, not a second family.**  `wf_let`,
  `wf_exp_eq_let_cong` (on both sides) and `wf_exp_eq_let_zeta` premise
  `let_ann oA A := oA = None \/ oA = Some A`, with `A` still a premise of the
  rule.  This is the brief's separate unannotated rule
  (`Γ ⊢ M : A -> Γ ▸ A ≔ M ⊢ B : C -> Γ ⊢ ℓ ≔ M in B : C[Id,,M]`, with
  equality, congruence and ζ) packaged as a disjunct: the meta-theory gets one
  case per rule instead of two, and `destruct_let_ann` splits it where the
  annotation matters.  Applying a rule: `solve_let_ann` for the `let_ann`
  premise, solved first (`cycle`) since conclusions do not mention `A`.
- Evaluation ignores the annotation (one rule for both forms).
- The algorithmic checker infers the definiens's type (`ati_let_infer`).  Its
  completeness is by an outer induction on the number of unannotated `let`s
  (`exp_lets`, `alg_type_complete_lets`): the body's derivation is moved to
  `Γ ▸ A' ≔ M`, `A'` the inferred type, by refinement
  (`wf_sub_id_extend_def`), which is no subderivation but has fewer
  unannotated `let`s.
- Frontend: `Cst.d_def : string -> option obj -> obj -> decl`; the parser
  accepts `x := a` in a `let`; the elaborator passes the option through
  (`sel_let_infer`).  `def` keeps its required type.

### 10.7 Imports generate definitions
- `import E items` is the command `cc_import E items` (`iitem := option
  string * string * bool`: member or the module itself, declared name,
  private).  `import_gen mt Γ E items` (`Core/Syntactic/Imports.v`) checks
  `E` is a module and each item a member, rejects a member both used and
  exported (`xe_both`) and a name declared twice (`xe_fresh`), and gives a
  definition `d : A := E.n` (`A` its member type) or an alias per item.
  `rc_import` declares them with the premises of `rc_def`/`rc_alias`, so their freshness
  is the ordinary one.  Loading is its own command, `cc_load`.
- `mt : mt_oracle` stands for the member types; `mt_spec Θ Ξ mt` ties it to
  `member_type`, and any two such oracles agree (`mt_spec_ext`), so
  expansion is unique (`cmd_xp_ok_functional`).  The checker uses `mt_of`
  (`Extraction/MemberType.v`), total by `mt_order_total`.
- A local import is the pre-form `gm_import Φ E items`, one binder per item
  (`body_ctx` gives placeholder `ce_ass ℕ` entries).  `rcs_cons` and
  `ru_intro` expand every command/parameter telescope first (`cmd_xp`,
  `tele_xp`), turning each `gm_import` into `gm_ext` entries.  No typing rule
  mentions `gm_import`: `body_shape` is `False` on it, so typed units never
  contain one, and `wf_unit_eq_body` lost its import premises.
- Privacy of local bodies: references carry a module table (`ptab`) read off
  the syntax in a scope; `pt_body ch es` checks the newest entry is public,
  `pt_glob H` the global check.  `pt_body` carries the chain `ch` of
  submodules from the local module, for `re_private_local`.
- Privacy checks what is written: `rcs_cons` checks
  `acc_ok Θ Ξ (cmd_refs c)` on the command before expansion, `ru_intro` the
  written parameters; no `run_cmd` rule checks privacy.  `rc_import` declares
  its generated entries by `gens_run` (outside the mutual block, the
  premises of `rc_def`/`rc_alias` without privacy), so a generated type is
  never checked.  An import's refs are its target and each member it names;
  in a local body, `btab` gives each item the table of what it names.
- Typing is untouched: no rule mentions an import.  A generated definition
  `d := E.n` is checked by `gr_def`'s premise `Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ a_mem E n : A`
  through the ordinary member rules, a generated local entry by
  `wf_unit_eq_body` like a written one.
- A unit's leading imports are commands of its own frame, after its
  parameters, so a parameter type cannot name what they declare:
  `import Prelude::Arith::Equality use (Eq) module M (p : Eq 1 1) where … end`
  gives `unbound name Eq` (it was accepted while `use` bound elaborator
  aliases); the qualified name `Prelude::Arith::Equality.Eq` still works.

### 10.8 Import loads, open declares; definition keywords
- `import X::Y` only loads (`cc_load`; a repeated one is `rc_load_filed`, a
  no-op).  It names a unit: `import M` for a module in scope is a syntax
  error.  Declaring is `open E [as W] (use (…) | export (…))*`: the core
  command `cc_import` is renamed `cc_open` (`rc_open`, `gm_open` for the
  local pre-form), otherwise unchanged (`import_gen`, `gens_run`).
- The parser splits the compound forms (`Cst.open_cmds`,
  `Cst.import_cmds`): `open E as W items` is `open E as W` then `open W
  items`, so generated definitions refer to the alias (`W.n`, and a missing
  member is reported as `T.W.n is not a member`); the long form `import X::Y
  ip args as W items` is `import X::Y` then `open X::Y ip args as W items`.
- `import` in a local body is an elaborator error, `import is not allowed in
  a local module; use open`.
- The surface items are core `iitem`s, now defined before `Cst`.
- Leading imports and opens are read twice by the elaborator (§10.7's
  restriction is lifted): before the header, the names they declare denote
  the members they name, so `import Prelude::Arith::Equality open
  Prelude::Arith::Equality use (Eq) module M (p : Eq 1 1) where … end` is
  accepted, the parameter type being `a_mem ⟨Equality⟩ Eq $ 1 $ 1`; in the
  frame they are the generated members, as before.  Their arguments may no
  longer name the unit's parameters (`unbound name n`).
- Definition keywords `theorem`/`lemma` (`abstract def`), `fact`/`remark`
  (`abstract private def`), `let`/`given` (`private def`), with `def`'s
  syntax; a modifier the keyword implies is rejected by the parser through
  `Cst.c_error` (`theorem is already abstract`, `fact takes no modifiers`,
  `let is already private`).  `fact` is now a keyword, so
  `Prelude::Arith::Factorial.fact` is renamed `factorial`.
