# A declarative specification of the elaborator

Branch `ext/params-as-locals` (option B).

| File | What |
| --- | --- |
| `theories/Frontend/ElabSpec.v` (742 lines) | The spec `elab_spec : Cst.prog -> cunit -> Prop`, and its invariant `sf_wf` with `scmd_wf`/`scmds_wf`/`simports_wf`. Imports only `Syntax`, `Command`; no elaborator data structure. |
| `theories/Frontend/ElabCorrect.v` (1515) | `elaborate_core_iff`, soundness, completeness, functionality, failure characterization. |
| `theories/Frontend/ElabExamples.v` (354) | Hand-written `Cst.prog`s: the running example, pre-application, `examples/module_param`, `import_use`, `multi/Main`, privacy, redeclaration, shadowing, members used without their module arguments, dotted modules, unimported units, and every program the one-binding rule rejects, with its error message. |

## Theorems (all `Closed under the global context`)

```coq
Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Corollary elaborate_core_sound / elaborate_core_complete    (* the two halves *)
Corollary elab_spec_functional : elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Corollary elaborate_core_fails : (exists e, elaborate_core prg = eerr e) <-> forall u, ~ elab_spec prg u.
```

## The naming rule

**One binding per name per frame.** Within a frame a name is bound at most
once — as an import alias, a member (`def`, `module`, first segment of
`module A.B`), or a parameter. Binding a name the frame already binds is an
error (`"x is already declared"`, `"duplicate parameter x"`); binding one an
enclosing frame binds is shadowing. Leading imports are fresh against the
earlier leading aliases only (no frame exists yet). Spec: `sf_fresh F x := ~ In
x (sf_names F)` (aliases ++ members ++ parameters), `alias_fresh`, `NoDup (map
fst ps)` in `sc_mod`/`es_intro`; the invariant is `sf_wf F := NoDup (sf_names
F)`, `ss_wf O`. Because of it `fr_binds` (alias / member / parameter of one
frame) has no priority between its rules, and `ss_binds` is plain `In`.

## Running example

The comments in `ElabSpec.v` explain the definitions with this program.
`ElabExamples.running_spec` checks the output below.

```
module Main where
  module M (A : Type@0) where
    def id (x : A) : A := x end
    module N (B : Type@0) where
      def k (x : A) (y : B) : A := id x end
    end
  end
  def j : forall (x : Nat) -> Nat := M.id Nat end
end
```

It elaborates to the following core unit.  `Main.M.id` stands for
`a_glob (p_abs ["Main"] ["M"; "id"])`, and the transparency and privacy flags
of `cc_def` are omitted.

```
cc_mod "M" (⋅ ▹ Type@0)
  [ cc_def "id" (Π #0 #1) (λ #0 #0);
    cc_mod "N" (⋅ ▹ Type@0)
      [ cc_def "k" (Π #1 (Π #1 #3)) (λ #1 (λ #1 (Main.M.id $ #3 $ #1))) ] ];
cc_def "j" (Π ℕ ℕ) (Main.M.id $ ℕ)
```

**The body of `k`.** While it is elaborated, three frames are open (`sframe`),
innermost first:

| Frame | `sf_path` | `sf_params` | `sf_cmds` so far |
| --- | --- | --- | --- |
| `N` | `["M"; "N"]` | `B` | none |
| `M` | `["M"]` | `A` | the `cc_def` of `id` |
| `Main` | `[]` | none | none, because `cc_mod "M"` is emitted only when `M` ends |

The local bindings are `[lb_var "y"; lb_var "x"]`, so `x` is `#1`.  The name
`id` is not local, so `fbind` looks it up in the frames, starting with
`off = 2` for the two local binders.  `N` does not bind `id`, so the search
moves to `M` and adds the one parameter of `N`, giving `off = 3`.  `M` binds
`id` as a member definition (`fr_def`).  A member is stored generalized over
the parameters of its own frame and of every enclosing frame, so it must be
applied to them.  `preapp 3 [M; Main] [#3]` holds because `Main` has no
parameters and the one parameter `A` of `M` is `#3`.  So `id` denotes
`Main.M.id $ #3`, and `id x` is `Main.M.id $ #3 $ #1`.

**The body of `j`.** Here `M` has been closed and only `Main` is open.  `M` is
found as a member module of `Main` (`fr_mod`).  It denotes a module reference
(`sref`) with unit `["Main"]`, chain `["M"]`, the commands of `M`, and no
arguments.  `M.id` selects the public definition `id` (`select`), which
gives `s_def R "id"`.  Applying it to `Nat` adds `ℕ` to the arguments of the
reference (`sapp`).  The result is the term `Main.M.id $ ℕ` (`as_term`).
`M.id` alone is also a term, `Main.M.id`, because a member is a closed
constant: here its type is `Π (A : Type@0). Π A A`.

## The spec in one paragraph

State: leading-import scope `O`, open frames `Fs` (innermost first), each `sframe`
= member chain, named parameters with types, **the core commands emitted so
far**, import scope (aliases, reachable units). Members are read off the emitted
commands (`cs_member`), so there is no symbol table. Objects: `sel fp O Fs L o
r` with `r` a term, a module reference (`sref`: unit, chain, signature =
commands of its `cc_mod` or `None` if opaque, args so far) or a
definition of a reference awaiting its module arguments (`s_def`); `as_term`
says when that is a term. Name lookup: locals (`lbound`/`ldenote`), then frames
(`fbind`: the innermost frame binding the name decides, via `fr_binds`), then
leading aliases. **Pre-application** is `preapp off (F :: Fs) args`: the
parameters of the member's frame and every frame outside it, outermost first,
parameter `i` of `n` in a frame whose telescope starts `off` binders in being
`#(off + n-1-i)`; a parameter reference `fr_param` denotes exactly the variable
`preapp` passes for it. Selection through a reference (`select`) reaches only
public definitions, supplies no parameters, and extends opaque paths.
Commands: `scmd fp O Fs F c F'` changes only the innermost frame.

## Proof structure

Representation functions spec → elaborator (`to_mref`, `to_os`, `to_of`,
`to_ls`; the member table is `emod_of cmds`), and one `iff` per layer by
induction on syntax (the spec is syntax-directed), each for well-formed states
(`ss_wf O`, `Forall sf_wf Fs`): `fr_lookup_iff`, `mr_member_iff`,
`elab_res_iff` (mutual `obj`/`decl` scheme, generalized over the spine `args`
via `fin`), `elab_params_iff`, `import_iff` (the elaborator's `taken` predicate
`decides` the spec's `sf_taken`), `elab_cmd_iff` (nested `cmd_ind'`, inner
induction on the dotted path; well-formedness carried by `scmd_wf`),
`elab_cmds_outer_iff`. Functionality is free from the `iff`. The well-formedness
hypotheses are only used to read the spec's priority-free `fr_binds` as the
elaborator's ordered lookup (`wf_member_free`, `wf_param`, `ss_binds_lookup`).

## Elaborator changes

Semantics-preserving (results unchanged):
* `mr_def` factored out of `mr_member`; an alias `tg_mem mr x` (made by `use`)
  calls `mr_def` instead of re-looking `x` up in `mr`'s table (the re-lookup
  always found the same public definition checked at import time).
* `elab_import` split into `import_target`, `use_bind`, `import_binds`.

Rule changes (the one-binding rule; the 34 expect tests are unchanged):
* `of_fresh` (members) also rejects a parameter name of the frame (`of_taken`).
* `import_binds`/`use_bind` take `taken`: an alias is rejected if a member or
  parameter of the frame has its name.
* `check_params`: duplicate parameter names in a unit's or module's telescope
  are an error, `"duplicate parameter x"`.

## Remaining behaviours worth knowing

* `M.f a` supplies `M`'s argument after the projection (`s_def` + `as_term`).
  The elaborator does not count module arguments: `M.f` with fewer than `M`'s
  parameters is a partial application of a closed constant, and typing checks
  the rest.
* Imports inside a module die with it (aliases and unit reachability).
* Privacy of members of imported units is not checked (REVISIT, kept).
* A unit's parameter may reuse a leading alias's name (different scopes; the
  parameter shadows it).
