# A declarative specification of the elaborator

Branch `ext/params-as-locals-elab-spec` (on `ext/params-as-locals`, option B).

| File | What |
| --- | --- |
| `theories/Frontend/ElabSpec.v` (495 lines) | The spec `elab_spec : Cst.prog -> cunit -> Prop`. Imports only `Syntax`, `Command`; no elaborator data structure. |
| `theories/Frontend/ElabCorrect.v` (1315) | `elaborate_core_iff`, soundness, completeness, functionality, failure characterization. |
| `theories/Frontend/ElabExamples.v` (233) | Hand-written `Cst.prog`s: pre-application, `examples/module_param`, `import_use`, `multi/Main`, privacy, redeclaration, shadowing, missing arguments, dotted modules, unimported units. |

## Theorems (all `Closed under the global context`)

```coq
Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Corollary elaborate_core_sound / elaborate_core_complete    (* the two halves *)
Corollary elab_spec_functional : elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Corollary elaborate_core_fails : (exists e, elaborate_core prg = eerr e) <-> forall u, ~ elab_spec prg u.
```

## The spec in one paragraph

State: leading-import scope `O`, open frames `Fs` (innermost first), each `sframe`
= member chain, named parameters with types, **the core commands emitted so
far**, import scope (aliases, reachable units). Members are read off the emitted
commands (`cs_member`: last `cc_def`/`cc_mod` declaring `x`), so there is no
symbol table. Objects: `sel fp O Fs L o r` with `r` a term, a module reference
(`sref`: unit, chain, signature = commands of its `cc_mod` or `None` if opaque,
arity, args so far) or a definition of a reference awaiting its module
arguments (`s_def`); `as_term` says when that is a term. Name lookup: locals
(`lbound`/`ldenote`), then frames (`fbind`: per frame alias > member > parameter,
a frame binding the name at all hides outer frames), then leading aliases.
**Pre-application** is `preapp off (F :: Fs) args`: the parameters of the
member's frame and every frame outside it, outermost first, parameter `i` of `n`
in a frame whose telescope starts `off` binders in being `#(off + n-1-i)`; a
parameter reference `fb_param` denotes exactly the variable `preapp` passes for
it. Selection through a reference (`select`) reaches only public definitions,
supplies no parameters, and extends opaque paths. Commands: `scmd fp O Fs F c F'`
changes only the innermost frame.

## Proof structure

Representation functions spec → elaborator (`to_mref`, `to_os`, `to_of`,
`to_ls`; the member table is `emod_of cmds`), and one `iff` per layer by
induction on syntax (the spec is syntax-directed): `fr_lookup_iff`,
`mr_member_iff`, `elab_res_iff` (mutual `obj`/`decl` scheme, generalized over
the spine `args` via `fin`), `elab_params_iff`, `import_iff`, `elab_cmd_iff`
(nested `cmd_ind'`, inner induction on the dotted path), `elab_cmds_outer_iff`.
Functionality is free from the `iff`.

## Elaborator refactoring (results unchanged; 34 expect tests unchanged)

* `mr_def` factored out of `mr_member`; an alias `tg_mem mr x` (made by `use`)
  now calls `mr_def` instead of re-looking `x` up in `mr`'s table. The
  re-lookup always found the same public definition checked at import time,
  so the result is identical; it removes a dependency on the table that the
  spec cannot reconstruct from `s_def`.
* `elab_import` split into `import_target`, `use_bind`, `import_binds`
  (pure naming, same computation).

## Quirks the spec records faithfully (review these)

* Import-alias freshness checks only aliases, so `def x … ; import M as x` is
  accepted and the alias then shadows the member `x` (alias before member);
  a later `def x` is rejected.
* A definition or module may reuse a parameter name of its own frame (members
  win over parameters); duplicate parameter names: the last one wins.
* `M.f a` supplies `M`'s argument after the projection (`s_def` + `as_term`);
  surplus arguments become term applications; arity is checked only for
  definitions of non-opaque references.
* Imports inside a module die with it (aliases and unit reachability).
* Privacy of members of imported units is not checked (REVISIT, kept).
