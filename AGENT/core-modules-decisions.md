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

## 11. S+K (`wip/sk`, 2026-10-05)

One module representation (self-style units) and abstract definitions as
global constants.  The design source is the S+K proposal; what follows is
what was built, and the decisions taken on the way.

### 11.1 Definitions
- `exp` gains `a_const : qname -> exp`.  `gentry := ge_def pv A (oM : option
  exp) | ge_mod pv U` (no transparency flag; `None` is an axiom, filed only as
  a constant).  `gm_open Φ H oz its` is the local open (`iitem := string *
  string * bool`, member, declared name, private; `oz` the alias).
- `gdecl := gd_unit fp U | gd_const q A oM b`, `gctx := list gdecl`, newest
  first; `gc_unit`/`gc_const` read the first match.  No `gstack`, no levels,
  and `Ξ` is gone from every judgment: `Θ ⍮ Γ ⊢ M : A`.
- Self style: each entry of `gu_body Δ Φ` is checked in `self_ent Φ' :: Δ ++ Γ`
  (`self_ent Φ' := ce_mod (gu_body nil Φ')`, `Φ'` the entries before it), a
  sibling `y` is `a_mem (me_var k) y`.  Member types are
  `ctx_pi (self_ent Φ' :: Δ) A`: they hold the prefix literally.
- Evaluation: `me_unit fp ↘ dm_of nil U`; a constant with a body and `b =
  true` unfolds, any other is the neutral `d_glob q`; selection evaluates the
  member under a closure of its prefix (lazy, no `eval_benv`).

### 11.2 Commands
- Frames `fr_mk chain params body`; a command is checked in `fctx Γimp F =
  self_ent (fr_body f) :: fr_params f ++ … ++ Γimp`.
- `abstract def` (`rc_abs`) files `gd_const q (ctx_pi Γ A) (Some (ctx_fn Γ M))
  false` and the entry `x := apps (a_const q) (ctx_args Γ)`; `axiom`
  (`rc_ax`) the same without a body.  Neither is allowed in a local body
  (elaborator errors).
- Leading imports and opens run before the parameters (`run_leads`).  A
  leading open adds one slot to `Γimp`, `lead_slot E := ce_mod (gu_mk nil
  (md_alias E))`; the names it declares are read from that slot, as members
  from a self slot (the elaborator's `en_mem d c`).  Its items are checked by
  `open_gen_ok` against the slot, and must be private (`lead_items_ok`;
  `Cst.lead_cmds` rejects `export` first, with the same message).  The unit
  is filed as `(gu_body P' Φ)[imp_sub Γimp]`.
  *Why slots and not one definition per item:* `initial_env` evaluates every
  definition of the context at every NbE call, so per-item definitions made
  `Prelude::Arith::Gcd::Properties` run in 32 s (slots: 0.34 s).
- Loading (S2): `rl_run` runs the unit from `nil` and merges what it filed
  with `gc_merge Θ ΘL := filter (not in Θ) ΘL ++ Θ`.  Shared declarations
  agree (`coh`, `fresh`, `loaded_functional`, by `run_functional`), so the
  merge is well formed (`gc_merge_wf`, `run_wf`).  A loaded unit sees only
  what its own imports load: `Frontend/ElabExamples.v` `seeB_rejected`.
- The executable runs each unit once and keeps what it filed in a cache;
  a hit is used under the current chain by `run_chain_irrel`, after checking
  that no unit of the chain is in it (`chain_free`), which `run_chain_fresh`
  shows always holds when the judgment holds.  `run_impl_complete`,
  `prog_impl_sound`/`_complete` are exact (no equivalence up to order).

### 11.3 Axioms and consistency
- `gc_no_axioms Θ` stays the hypothesis of consistency and canonicity;
  unsealing (`gc_unseal`) flips only the flag, so an axiom stays stuck.
- `run_no_axioms`, `prog_sem_no_axioms` and the per-program corollaries
  (`consistency_False_prog`, `canonical_form_of_nat_prog`) assume the
  commands and every loadable unit are axiom-free (`cmds_no_axioms`,
  `unit_no_axioms`).

### 11.4 Elaborator
- `ent := en_var x | en_self | en_mem x c | en_unit fp`; `en_mem x c` denotes
  `a_mem (me_var k) c`, `k` the nearest self slot outside it.  No
  pre-application, no qualified names, one path for global and local bodies.
- A frame reserves its parameters' names (and, for the unit, the leading
  names): a member may not take them (`x is already declared`).
- A unit may be named (`Cst.glob`) or opened only once imported; the core
  rejects it as well when it is not loaded.

### 11.5 Performance notes
- `imp_sub` computes the substitution of the tail once (a `let`): the two
  recursive calls made it exponential in the leading context.
- The checker types a generated item `d := H.x` at a type it recomputes as
  `H.x`'s member type without checking the type (`check_exp_fast`, by
  `member_wf`); checking it would check the literal prefix it holds.
- Member types hold their prefixes literally, and `pi_view`/`tele_open`
  copy them into every sibling an alias or submodule instantiates, so they
  grow multiplicatively with nesting: `AdditiveComm.powOp` (`lib/Groups.mctt`)
  had a 15,742,436-node member type with a 283-node normal form, and
  `Groups.mctt` took 12 s.  The checker no longer builds the member type of
  `a_mem H x` when `H` has no argument (`member_nf_dec`,
  `Extraction/TypeCheck.v`):
  - whether `x` is a definition is decided on kinds only (`member_kind`,
    `member_kind_impl`, `Extraction/MemberType.v`), which reads a slot in
    the context after it instead of weakening it; it agrees with
    `member_type` (`member_kind_complete`; `member_kind_sound` for a
    well-formed `H`, where an application always instantiates, by
    `app_arity_pi`);
  - the normal form is read back from the value: `H` is evaluated in the
    initial environment, `h ⦂ₜ x ↘ a` (`sel_ty`) evaluates `x`'s declared
    type under its self slot, and `a` is read back.  `sel_ty_nbe_wf`
    (`Core/Semantic/MemberNf.v`) shows this is the normal form of the member
    type, through the PER model (`wf_modexp_sem_mt`, `mtyped_sel_ty`);
  - a module value still lacking an argument has no `sel_ty`; then the
    member type is built and normalized as before.
  `ati_mem`, `member_type` and every theorem statement are unchanged.  The
  `me_var` case of `modexp_check` tests the slot with `ctx_find_slot`, without
  weakening its unit.  `Groups.mctt` now takes 2.5 s (2.9 s in the design
  before S+K), `AdditiveComm.powOp` 0.14 s (6.3 s), lib and Prelude 20.0 s
  (32.4 s; 22.9 s before S+K).
- The scope of a command's privacy check, `fctx_tabs`, rebuilt the self
  table of every open frame from the whole body before each command
  (quadratic in a module's length).  `cmds_step` now keeps it: a command only
  adds entries to the innermost frame (`run_cmd_grows`, `fr_grows`), and
  `next_tabs`/`btab_from` put the new entries' tables on top of the kept
  ones, as `btab` itself does; a module's frame is pushed with `tabs_push`.
  The invariant `S = fctx_tabs fp Γimp F` is an argument of `cmds_step` and
  `run_cmd_impl`.  `Prelude/Arith/Gcd/Properties.mctt` 0.30 s → 0.19 s
  (0.20 s before S+K).
- Measuring: the evaluation-heavy files (`Arithmetic`, `Powers`, `Vectors`,
  `Groups`) vary by up to 25% with the code layout of the executable alone
  (where `ocamlopt` happens to place `Evaluation`); compare such files
  across builds only with a padded control.

### 11.6 Imports inside module bodies (`wip/flat-opens`, 2026-10-05)

With imports moved into the module bodies, a body `open`/`import … use (x)`
filed `x : A := E.x` with `A` the literal member type of `E.x`, which holds
the bodies before `x`, including `E`'s own imported items, whose types held
their sources' bodies in turn: exponential in import depth (a chain of 10
units: 72, 550, 5326, 53086, 530686 nodes, for a normal form of 1 node).
`lib` and Prelude took 563 s (21 s before the move).
- **Generated definitions are filed at normal forms (N).**  `gens_run`'s
  `gr_def` (`Core/Syntactic/System/Command.v`) premises the member type `A`
  of `H.n`, its normal form `nbe_ty Θ Γ A B`, and the typing
  `Θ ⍮ Γ ⊢ a_mem H n : B`, and files `ge_def pv B (Some (a_mem H n))`.
  `System/Command.v` imports `Core.Semantic.NbE` (no cycle: NbE does not
  depend on commands).  `gens_run_functional` uses `member_type_functional`
  and `functional_nbe_ty`; `gens_run_wf` is unchanged (the typing premise).
- **Generation decides on kinds only (O).**  `igen` is type-free,
  `ig_def d pv H n`; `open_gen` takes a kind oracle (`mk_oracle`,
  `mk_spec Θ mk := mk Γ H ch = Some k <-> member_kind Θ Γ H ch k`;
  `member_kind` moved to `Core/Syntactic/Members.v`), and `open_gen_ok`
  quantifies over such oracles.  The checker's oracle is `mk_of`
  (`member_kind_impl`).  The checks shared by both kinds of open are
  `open_with`.
- **Local opens are unchanged in meaning:** they are expanded before typing
  (`open_local`, `item_entry`), each definition at its literal member type,
  read by the `mt` oracle on the skeleton.  Normal forms there were
  rejected (option L): `cmd_xp` runs on `skel_ctx`, where NbE has no
  meaning (`.claude/plans/flat-opens/scratch/SkelNbe.v`).
- **Checker (F, K, W).**  `unit_check` infers a definition's body first
  and, when it is a member at its own literal member type
  (`known_def_dec`), concludes without checking the type or subtyping
  (`known_def_ok`, by `member_typed_any` and algorithmic completeness);
  otherwise it checks the type and the subtyping, as `type_check` does.
  `modexp_check (me_mem H y)` decides on kinds (`member_mod_kind_dec`).
  `member_type_impl` weakens a slot's member type by one `wk_shiftn`
  (`rwk_n_shiftn`), not one shift at a time.  `gens_impl` computes the
  normal form with `member_nf_dec` and types the member by
  `member_typed_any` and `soundness_ty'`.
- **Arguments against the next parameter's normal form (A).**
  `modexp_check (me_app H N)` no longer builds `H`'s arity (which holds
  the bodies before `H` literally): `next_param_dec` evaluates `H` in the
  initial environment, takes the type value of its next argument
  (`nextdom`, `Core/Completeness/MemberTyping.v`, computed by
  `nextdom_impl`, `Extraction/MemberType.v`) and reads it back to `C`;
  `N` is checked against `C`.  `nextdom_nbe_wf`
  (`Core/Semantic/MemberNf.v`) shows that `C` is the normal form of the
  arity's outermost parameter `B` (`tele_view T = Some (B, T1)`), and that
  a value with a next argument has an arity with a parameter
  (`tele_view_none_top`, `mtyped_nextdom_pi`); `nextdom_of_arity` the
  converse.  `next_param_check` relates the checks against `B` and `C`, so
  `amod_app` is unchanged.  The existing `nextdom`/`nextparam` were
  reused; nothing new was needed in the PER model.
- Statements of `prog_impl_sound`/`_complete`, `main_*`, consistency and
  canonicity are unchanged; the accepted programs and their outputs are
  those of `ext/local-modules`.  `lib` and Prelude: 19.5 s after N/O/F/K/W,
  563 s before (21.2 s on `ext/local-modules`); A takes `Algebra` from
  0.22 s to 0.15 s and `Prelude/Algebra/Instances` from 0.15 s to 0.08 s.
  The evaluation-heavy files move by up to 17% with the code layout of
  the executable alone (§11.5); a padded control build gives the commit-1
  times.
