# Modules, Global and Local Bindings

The design as built.  The request it implements is
[`modules-spec.md`](modules-spec.md); everything below that contradicts it is
listed under [Deviations](#deviations-from-the-specification).

## The one idea

**Modules, `def`s and `let`s live entirely in the front end.**  `nbe` and
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
| `theories/Core/Syntactic/GlobalCtx.v` | The two-level global context: `gmod`/`gentry` for the `.` level, the `gtree` trie for the `::` level, `gunit`, the `gstack` of open modules, `gctx`, canonicity, resolution, `gmerge`. |
| `theories/Core/Syntactic/System/Definitions.v` | `Ψ` threaded through the four judgments; `exp_closed`; the `a_glob` rules; the global well-formedness layer `⊢g Ψ`, `Ψ ⊢e E`, `Ψ ⊢m Φ`, `Ψ ⊢u U`, `Ψ ⊢t T`. |
| `theories/Entrypoint.v`, `driver/` | One `run_eval` per `eval`; `PrettyPrinter`; exit codes. |
| `examples/*.mctt`, `driver/Test.ml` | 14 examples, 27 expect-tests. |

## Surface syntax

The two levels of naming are spelled differently, and the difference is
significant: `X::Y::Z` names a **unit** — a file, and units do not nest — while
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

Inside a term, `let x (y : Some) : Thing := … in … end` binds a local
definition (the same telescope machinery, one binder deeper) and
`let module M := X.Y.Z x y in … end` binds a local module.

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
5. **No implicit sectioning.** A parameter of a parameterized module is
   prepended to *every* member's type and body (`tele_pi`/`tele_fn`), so a
   member is used as `(X A).foo` or `X.foo A`. Members are not generalized only
   over the parameters they mention.
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
11. **Only the syntactic layer knows about `a_glob`.** `Syntax.v` gained
    `a_glob : path -> exp` and `GlobalCtx.v` the global
    context it refers into; `Core/Syntactic` now threads that context through
    every judgment (`Ψ ⍮ Γ ⊢ M : A`, …) and has three rules for `a_glob` —
    `wf_glob`, `wf_exp_eq_glob` and the δ-rule `wf_exp_eq_glob_unfold`, which
    unfolds a non-`abstract` definition's body. `Core/Semantic` downwards does
    not: `eval_exp_order` has no case (the branch of `eval_exp_impl` is
    discharged by `eval_exp_order_glob`), and `type_infer` answers `inright` for
    it, so a term containing a global fails to type-check. Elaboration never
    produces one, so nothing regresses.

    Two consequences of keeping `Ψ` a *parameter* of the judgments rather than
    an index, since no rule changes it:

    * The `a_glob` rules carry an `exp_closed` premise on the recorded type (and
      on the body, for the δ-rule) instead of a `⊢g Ψ` premise. Closedness is
      exactly what weakening and substitution need — `A⟨φ⟩ = A`, `A[σ] = A` —
      and is discharged by the `push_closed` tactic in `System/Lemmas.v`. A
      `⊢g Ψ` premise would have had to be threaded through every statement in
      the layer.
    * `⊢g Ψ` is a `Record`, not an inductive: its two halves are
      `Ψ ⊢t gc_imports Ψ` and `List.Forall (wf_gunit Ψ) (gc_defs Ψ)`, each
      checked with *all* of `Ψ` in scope, plus the two canonicity conditions.
      Weakening along `⊑` is
      therefore a lemma (`gsub_preserves_wf`, `gsub_preserves_global`,
      `gsub_preserves_gtree` in `System/Lemmas.v`) rather than a rule, and the
      well-formedness of an import does not depend on where it sits in the trie.
      `Ψ ⊢m Φ`/`Ψ ⊢e E` (modules and entries), `Ψ ⊢u U` (a unit: its parameters
      form a context, its body a module) and `Ψ ⊢t T` (the trie) are the
      judgments that make it up. `gc_lookup_wf` is the converse direction: in a
      well-formed context, whatever `a_glob p` resolves to is a well-formed
      entry.

    The two layers are *stratified*, not mutually inductive: `Ψ` is a parameter
    of the four term judgments, the global layer is declared after them and
    refers back to them, and no term rule mentions any global judgment — the
    `a_glob` rules premise `gc_lookup`, which is an inductive on data.

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
