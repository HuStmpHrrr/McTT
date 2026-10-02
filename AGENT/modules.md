# Modules, Global and Local Bindings

> **Option B branch:** the core global layer described below (relative paths,
> `a_param`, `↑ₘ`/`close`, `Discharge`/`Transport`) is replaced on this branch;
> see [`optionB.md`](optionB.md).

The design as built.  The request it implements is
[`modules-spec.md`](modules-spec.md); everything below that contradicts it is
listed under [Deviations](#deviations-from-the-specification).

## The one idea

**Modules and `def`s live entirely in the front end.**  `nbe` and
`type_check_closed` are untouched, because a compilation unit elaborates to
*closed* `exp`s.  `a_glob` and `GlobalCtx.v` are the seam left for separate
compilation: the syntactic judgments now carry a global context `Ψ` and have
rules for `a_glob`, but the semantics and the algorithm still do not; see
[deviation 11](#deviations-from-the-specification).

Every definition — global, local, module member — becomes one entry of a
**definition telescope**, and a telescope is emitted as the nest

```
(λ A₁ ((λ A₂ … body …) $ M₂)) $ M₁
```

Entry `i` was elaborated at depth `i`, so the whole nest is closed at `0`.
A name therefore resolves to a de Bruijn index into that nest, and *nothing
about a definition is visible to the core* but its type and its body.  Modules
add no term formers, no universe, no judgment: a module is a *scope*, i.e. a
compile-time tree of names, and a parameterized module is one whose members are
functions.

`abstract` is the only modifier that changes the emitted term's shape, and only
by changing what the name resolves to inside the nest:

| | resolves to | inside the nest |
| --- | --- | --- |
| `def` | the body (`v_inline`) | inlined, at its own depth |
| `abstract def` | the binder (`v_bound`) | the variable, so the body cannot be unfolded |

`private` has *no* effect on the emitted term; it only hides the name from
`import` (`ent_public`).

## Where the code is

| File | What |
| --- | --- |
| `theories/Frontend/Resolve.v` | Scopes: `entry`/`val`/`scope`, lookup, insertion, `ent_public`, `sc_take`, `ent_fix`, `v_bound`/`v_inline`/`v_bind`, `sc_use`, import depths. |
| `theories/Frontend/Elaborator.v` | `elab_res`/`elab` for objects; `ustate`, `elab_def`/`elab_eval`/`elab_import`/`elab_cmd`/`elab_cmds`, `elaborate_prog`; the closedness development. |
| `theories/Frontend/Parser.vy`, `driver/Lexer.mll` | Surface syntax; `parserMessages.messages` holds the 81 error sentences. |
| `theories/Core/Syntactic/Syntax.v` | `Cst.cmd`, `Cst.mods`, `Cst.ispec`, `Cst.prog`, `Cst.decl` (the `let` forms); `Cst.glob`; `qual`/`path`/`path_valid` and `a_glob`. |
| `theories/Core/Syntactic/GlobalCtx.v` | The two-level global context: `gmod`/`gentry` for the `.` level, `gdeps` (the dependency levels) for the `::` level, `gunit`, the `gstack` of open modules, `gctx`, canonicity, resolution. |
| `theories/Core/Syntactic/System/Definitions.v` | One mutual block of all eleven `wf_*` judgments: the four term ones with `Ψ` threaded through, plus `⊢g Ψ`, `Ψ ⍮ Δ ⊢e E`, `Ψ ⍮ Δ ⊢m Φ`, `Ψ ⍮ Δ ⊢u U`, `wf_gdep`/`wf_gdeps`, `wf_gstack`. Also `exp_closed`, the `a_glob` rules, and the `Scheme`s cut from the block. |
| `theories/Entrypoint.v`, `driver/` | One `run_eval` per `eval`; `PrettyPrinter`; exit codes. |
| `examples/*.mctt`, `driver/Test.ml` | 14 examples, 27 expect-tests. |

## Dependency levels

`gctx` is `{ gc_deps : gdeps ; gc_stack : gstack }`.  The `gstack` is the unit
being elaborated (`qu_rel` paths); `gdeps` is everything already compiled
(`qu_abs` paths), and it is *not* one flat table but a list of levels, lowest
first, so that **a unit's level is its index**:

```
gdep  := list (list string * gunit)     (* one level, keyed by absolute path *)
gdeps := list gdep                      (* levels, lowest first *)
```

A unit's level is `1 + max` of the levels of the units it imports, `0` when it
imports nothing.  That equation is **not encoded**: the levels are a structure,
and a unit that sits at the level its imports force can only mention units
strictly earlier in the list, so cycle freedom is granted by where a unit is
filed rather than by a proposition about it.  `⊢g Ψ` therefore says nothing about
levels, and *filing* a unit at the right level is the command layer's job.

`gds_lookup` is a **function** returning `option gunit` — it searches the levels
in order and hands back the unit and nothing else, because that is all a use site
of `a_glob` reads.  So resolution is deterministic whatever the data looks like,
and no level arithmetic appears in `GlobalCtx.v` at all.

The consequence to keep in mind: `⊢g Ψ` alone does not rule out a δ-loop
(`wf_exp_eq_glob_unfold` unfolding a global forever).  Two units filed at levels
that name each other are still well formed, as is a unit whose member refers to
itself, in either form — absolutely, or the `gstack` form `def x : ℕ := succ x` —
because `wf_gmod_ext` checks each entry against the whole `Ψ`.  The `gstack` form
is unreachable from the surface (`elab_def` elaborates the body before inserting
the name).  Closing the rest inside the theory would need an ordering premise on
`wf_gmod_ext` (check an entry against a `Ψ` whose own unit is truncated to the
prefix already checked), which is deliberately not there.

## Surface syntax

The two levels of naming are spelled differently, and the difference is
significant: `X::Y::Z` names a **unit** — a parameterized module in full, and
units do not nest — while
`X.W` selects a member of whatever precedes it, be that an internal module, a
unit, or a local module binding.  `X::Y::Z::W` and `X::Y::Z.W` are different
names.  `a_glob` carries both halves as a `path`, so `X::Y::Z.W.bar` is
`a_glob (p_abs ["X";"Y";"Z"] ["W";"bar"])`.

A `path` is a `qual` and a nonempty list of member names.  The two `qual`s are
the two ways a module can be named: `qu_abs fp` is a unit, named absolutely;
`qu_rel n` is the `n`th enclosing module, counting outward from `0`, which is how
a reference into the unit *being elaborated* is written — an open module is not
yet an entry of anything, so it has no absolute name.  `path_valid` records the
two conditions that make resolution deterministic: an absolute `qual` is
nonempty, so it never also means "this unit", and the members are nonempty, so a
path never denotes a module rather than a term.  Both are consequences of
resolution rather than premises of it (`gc_lookup_valid`).

```
import …                      (* zero or more; only imports may precede *)
module Unit::Path where
  <commands>
end
```

The top declaration names the unit, so its path is a `::` one; a nested
`module A.B where` introduces an internal path.  A command is a nested
`module … where … end`, a `def`, an `import`, or an `eval`.  There is no trailing
main expression: what to normalize is said by `eval`.

```
module Arith::Ops where

module Impl (A : Type@0) where

private abstract def foo (x : A) : A := … end

end

import Impl as M                   (* an internal module of this unit *)
import Other::Unit use (bar; baz)  (* a whole unit *)
import Other::Unit.Mod as N        (* an internal module of another unit *)

eval M.foo Nat bar        (* type inferred  *)
eval M.foo Nat bar : Nat  (* type checked   *)

end
```

Inside a term, `let x : A := a; y : B := b in … end` binds local definitions,
each one a core `let` (`ℓ A ≔ a in …`, see [`core-let.md`](core-let.md)), and
`let module M := X.Y.Z x y in … end` binds a local module.  The two kinds of
binding may be mixed in one `let`, separated by `;`.

`eval M` infers `M`'s type, `eval M : A` checks `M` against `A`.  An `eval` sees
only the definitions declared before it.  The driver exits `3` if any `eval`
fails to type-check, `4` on elaboration failure, `5` on a parse error, `6` on
parser timeout.

## Elaborating a unit

`ustate` threads the whole unit:

| Field | Meaning |
| --- | --- |
| `u_outer` | what the enclosing modules declared |
| `u_frame` | what the module being elaborated has declared so far |
| `u_depth` | binders emitted so far; `u_view = sc_app u_frame u_outer` is well formed at it |
| `u_tele` | the definition telescope of the whole unit |
| `u_evals` | one `(option typ * exp)` obligation per `eval` |
| `u_idepth` | the import depth of the module being elaborated |

`u_enter` starts a module body (the view becomes inherited, the import depth
restarts at `0`), `u_close` ends one (`sc_insert p …` merges the members into the
enclosing frame, so `module X.A` and `module X.B` coexist).  Depth, telescope and
obligations are shared by the whole unit — a nested module does not get its own
nest.

`eval M : A` is elaborated as `tele_nest t (ascribe A M)` with
`ascribe A M := (λ A #0) $ M`, i.e. the ascription is checked *inside* the nest,
where `abstract` definitions are still variables.  The type *reported* is
`A[tele_close t]`, in which they have been substituted away; the check is
opaque, the printed type is not.

Import depths are `max(n, m+1)` as specified, but within one unit they are only
recorded, never checked: a single unit cannot have an import cycle.

## What is proved

Elaboration success used to be characterized by a set of free names
(`cst_variables`, `well_scoped`).  That does not survive modules — whether
`X.Y.Z` elaborates depends on whether `X` is a module and how many parameters it
has, which no set of names records.  What replaces it is the half the pipeline
actually needs, closedness:

| Theorem | Statement |
| --- | --- |
| `elab_res_wf` | `elab_res` at depth `d` returns a term closed at `d`, or a module whose scope and pending arguments are well formed at `d` (mutual induction over `Cst.obj`/`Cst.decl`) |
| `elab_closed` | `sc_wf d s → elab s d o = Some M → closed_at M d` |
| `elab_cmds_wf` | `elab_cmds` preserves `u_wf` and never lowers `u_depth` |
| `elaborate_prog_wf` | every obligation of a successfully elaborated unit is closed: `elaborate_prog prg = Some es → List.Forall eval_wf es` |

`u_wf` says both scopes are well formed at `u_depth`, the telescope is
`tele_wf 0` and has length `u_depth`, and every collected obligation is closed.
The supporting lemmas are `tele_wf_app`, `closed_at_tele_nest`,
`sb_bounded_tele_close`/`closed_at_tele_close`, `ent_wf_bind`, and the scope
lemmas in the `Well-formed Scopes` section.

Nothing else is proved about modules, and nothing needs to be: the type checker
receives closed `exp`s and its existing soundness and completeness apply
unchanged.

## Deviations from the specification

1. **Global and local judgments are derived, not primitive.** The spec asks for
   term judgments carrying a global context and a `global` case.  Since a unit
   elaborates to closed terms, no judgment changes; the tree-shaped contexts
   exist, but as *scopes* in the elaborator, not as contexts in the theory.
2. **`import … use (foo; bar)` aliases, it does not re-define.** The spec
   expands it to `def foo := X.Y.Z.foo`; that would emit new binders and
   duplicate the bodies. `sc_take` binds the names to the same entries instead,
   which is observationally the same and cheaper.
3. **One compilation unit.** A `::` path is grammatical everywhere — in an
   `import`, in a term, and as the unit's own name — but nothing with a nonempty
   file path resolves: `elab_res` sends `Cst.glob _` to `None`, and
   `elab_import` fails unless the file path is empty. A scope holds one unit's
   names, so there is nothing else it could do. The syntax is there so that
   separate compilation can be added without a grammar change, and so that
   `GlobalCtx.v`'s trie has something to be the target of.
4. **Module arguments are parenthesised**: `(X::Y.Z a b).foo`, never
   `X::Y.Z a b.foo`. Resolving the latter needs the arity before parsing.
5. **No implicit sectioning.** A parameter of a parameterized module abstracts
   *every* member's type and body, so a member is used as `(X A).foo` or
   `X.foo A`; members are not generalized only over the parameters they mention.
   The elaborator does this eagerly (`tele_pi`/`tele_fn`). `GlobalCtx.v` does
   not: a member is stored *open*, in its enclosing modules' telescope, and
   resolution accumulates that telescope so the `a_glob` rules generalize at the
   use site with `ctx_pi`/`ctx_fn`. Both conventions describe the same member;
   storing it open is what lets one `gentry` be read at any ambient context.
6. **A transparent definition is inlined at each use.** Sharing would need the
   nest to bind it, which is what `abstract` does; `def` duplicates work in the
   emitted term.
7. **`well_scoped` is gone**, replaced by closedness (see above).
8. **The reported type of an ascribed `eval` unfolds `abstract` definitions**
   even though the check does not.
9. **A top-level `module` declaration is mandatory**, and definitions may not
   precede it.
10. **`eval` is new**: the spec has no command for normalizing a term, and a
    unit no longer ends in a bare expression.
11. **`a_glob` and `a_param` run through the whole development.** `Syntax.v`
    gained `a_glob : path -> exp` and `a_param : lpath -> exp`, and
    `GlobalCtx.v` the global context they refer into; every judgment threads
    that context (`Θ ⍮ Ξ ⍮ Γ ⊢ M : A`, …). The syntactic layer has `wf_glob`,
    `wf_param`, their congruences and the δ-rule `wf_exp_eq_glob_unfold`, which
    unfolds a non-`abstract` definition's body. `Core/Semantic` evaluates a
    transparent global to its body and anything else to a neutral (`d_glob`,
    `d_param`), and the algorithmic layer infers the normal form of the type
    resolution hands back (`ati_glob`, `ati_param`), so a term containing a
    global type-checks.

    Three things to know about the global context in the rules. Note it is an
    *index* of the mutual block, not a parameter, so `induction 1` on a term
    judgment abstracts it — the proofs `remember` it first (see `subtyp_spec`).

    * The `a_glob` rules premise only `⊢ Θ⍮Ξ⍮Γ` and resolution, at type
      `ctx_pi Δ A`. Resolution generalizes a member over its member-chain
      parameters *and* the full telescope of its frame (`gcl_rel`/`gcl_abs`),
      so what it hands back is closed in a well-formed context
      (`wf_gc_lookup_closed`, `System/Scoping.v`); weakening and substitution
      leave it alone (`push_closed`).
    * `⊢g Θ ⍮ Ξ` has the single premise `wf_gstack Θ Ξ`. Units are checked at
      `⋅` with their parameters as the whole telescope; members are checked in
      the frame the module pushes, local context `⋅`. A frame's parameters
      are `$[n, k]` (`a_param`, rule `wf_param`), not local variables.
    * A member of an open frame resolves as stored, shifted `↑ₘ n`
      (`gcl_rel`); reading out of a closed module (`gml_in`, `gcl_abs`)
      applies `close mp c` (module substitution `msub`, `ModSubst.v`), which
      turns the parameters into λ-variables and the members into
      `app_vars` applications.

    **Every `wf_*` judgment is one mutual block** (eleven judgments), with
    `wf_mut_ind_all` over all of them.

    **Presupposition** is the mutual theorem `presup_global`
    (`System/GlobalPresup.v`): term judgments give `rwf Θ Ξ` (every resolved
    global's `ctx_pi Δ A` is a type at `⋅`, its body typed there), modules and
    units give `ins_typed` (each member, generalized, typed in the frame it
    was *inserted* into: `gm_ins`/`gm_prefix`, `GlobalCtx.v`). A definition
    records only `M : A`; that `A` is a type comes from presupposition of that
    derivation inside `⊢g`. Every frame-to-frame step is an instance of one
    transport along a module substitution (`msub_preserves_wf`,
    `System/Transport.v`): push a frame (`↑ₘ 1`), grow a frame or add a level
    (identity, `rebase_preserves_wf`), close a frame (`close_preserves_wf`,
    `System/Discharge.v`). Closing a nested module or a unit being filed
    (`closable_pop`, `closable_file`) is by induction on insertion order: each
    member needs only the members before it closed. `presup_exp_typ`,
    `presup_exp_eq`, `presup_subtyp`, `presup_sub_eq` are the full statements
    (well-formed context, both sides typed, the type a type).

## Module theory

The spec asks for a formulation of module theory and whether one is already
mechanized.  Findings:

* **No mechanized module system for a dependent type theory appears to exist.**
  The closest is Danielsson and Geng, *A Formalisation of a Dependently Typed
  Language with Modules* (TyDe '25, [10.1145/3759538.3759653]), which mechanizes
  a language with modules but not the full module calculus below.
* **The universe claim in the spec needs restating.** "Module is higher-order,
  so it does not need to live in any universe level" is not what the literature
  says. Harper, Mitchell and Moggi, *Higher-order modules and the phase
  distinction* (POPL '90, [10.1145/96709.96744]) get this by *stratification*:
  the module language is a separate, phase-distinguished layer over the core, so
  module types need no universe *in the core*. Hippogriff
  ([arXiv:2608.19728]) shows that a dependent core with first-class modules
  needs three levels, not zero. The design here takes the stratified route, and
  further collapses the module layer into elaboration, which is why no universe
  question arises.
* **F-ing modules** (Rossberg, Russo, Dreyer, JFP 2014,
  [10.1017/S0956796814000264]) is the reference elaboration semantics for
  ML-style modules into a core calculus; the approach here is its degenerate
  case, since our modules are neither first-class nor sealed.
* **Néron, Tolmach, Visser and Wachsmuth**, *A Theory of Name Resolution*
  (ESOP 2015, [10.1007/978-3-662-46669-8_9]), is the reference for scope graphs;
  `sc_lookup_path`/`sc_insert` are the tree special case, and its `import`
  edges are what `sc_take` and `ent_public` implement.
* **MetaCoq's `Kernames.v`** is the closest engineering precedent for the
  qualified names themselves (dotted paths as data, with a merge-on-insert
  module tree).

Anything more — sealing, functors as values, separate compilation with
interfaces — is future work, and none of it is forced by the present design.

## Gotchas

* `elab_cmd` recurses into a module body through an inner `fix`. Neither mutual
  recursion (guard condition would compare `Cst.cmd` with `list Cst.cmd`) nor a
  recursion on the list (it does not see through `list`) is accepted.
  `elab_cmds_go` and `elab_cmd_mod` discharge the duplication, and
  `elab_cmds_wf` induces on `cmds_size` rather than on the syntax.
* `q` is a notation (`q σ`), so it cannot be used as an intro pattern name.
* Order the premises of a scope lemma so the discriminating hypothesis comes
  first, then `eapply L; [| | eassumption]` instantiates the rest; letting
  `eassumption` pick first instantiates the wrong scope.
* An `Equations` branch that is unreachable needs a real term, not `:=!` and not
  a `_` hole: both leave the covering unbuilt or the obligation unsolved, and the
  only symptom is `_functional was not found` at the following `Extraction
  Inline`. Prove a `… -> False` lemma and apply `False_rect` (see
  `eval_exp_order_glob`).
* A grammar change means `make -C theories update_parserMessages`, filling in
  each `<YOUR SYNTAX ERROR MESSAGE HERE>`, then `check_parserMessages`; the build
  fails on a missing sentence.

## The driver pipeline (supersedes the elaboration description above)

* `Frontend/Elaborator.v`: `elaborate_core : Cst.prog -> eres cunit` is lexical
  and reads no filed unit. A path into an imported unit stays unresolved
  (`mr_opaque`) and is checked by typing. Privacy of imported members is not
  checked (REVISIT).
* `Core/Syntactic/System/Command.v`: the static semantics of core commands
  (`run_cmd`/`run_cmds`/`run_unit`, `prog_sem`). `import` loads through
  `load_path`, runs the unit from nothing, and merges it in; the chain rules
  cycles out. The main theorem is `run_wf`.
* `Extraction/Command.v`: the interpreter `prog_impl`, which accumulates one
  gdeps and checks each unit against its restriction to the unit's closure.
  It recurses on `Acc load_step`, which is erased, and is sound and complete
  for `prog_sem` (`prog_impl_sound`, `prog_impl_complete`).
* `Entrypoint.v`: `main load_path read`, with `main_sound`/`main_complete`.
  The driver passes `load_path` (unit `X::Y` is `<search-root>/X/Y.mctt`,
  flag `--search-root`, default `.`) and `read` (OCaml lexer + extracted
  parser). Multi-file tests are under `examples/multi`.
