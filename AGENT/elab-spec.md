# A declarative specification of the elaborator

| File | What |
| --- | --- |
| `theories/Frontend/ElabSpec.v` | The spec `elab_spec : Cst.prog -> cunit -> Prop`: objects (`sel` terms, `selm` module expressions, `sparams`, `sunit`, `sdef`, `sbody`, `libinds`), imports (`itarget`, `ibinds`, `simport`), commands (`scmd`, `scmds`, `simports`), and the invariant `sf_wf` with `scmd_wf`/`scmds_wf`/`simports_wf`. |
| `theories/Frontend/Elaborator.v` | `elaborate_core`, on the spec's own data structures (`sframe`, `sscope`, `lbind`, `sden`). |
| `theories/Frontend/ElabCorrect.v` | `elaborate_core_iff`, soundness, completeness, functionality, failure characterization. |
| `theories/Frontend/ElabExamples.v` | Hand-written `Cst.prog`s with their core units: the running example, pre-application, every module form (`module … where`, `module x (ps) := E`, `module A.B`, `let module` with a body or an alias, imports in a local body) and every rejection of the one-binding rule, with its message. |

## Theorems (all closed under the global context)

```coq
Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Corollary elaborate_core_sound / elaborate_core_complete    (* the two halves *)
Corollary elab_spec_functional : elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Corollary elaborate_core_fails : (exists e, elaborate_core prg = eerr e) <-> forall u, ~ elab_spec prg u.
```

## What the elaborator does, and does not, do

It resolves names and nothing else; it never looks inside a module.

* A name is a local binder (`lb_var`, a core variable: λ, Π, `let`, `let
  module`, a module parameter, an entry of a local body), a local alias
  (`lb_alias`, made by an import in a local body), or is looked up in the open
  frames (`fbind`): an import alias, a member of an open frame (its absolute
  path applied to the parameters of the open frames, `preapp`), or a
  parameter of an open frame.  Then the aliases of the leading imports.
* The position decides what an object is: the head of a projection, the head
  of an application there, an alias body and an import target are module
  expressions (`selm`); everything else is a term (`sel`).  A projection is
  the core's member selection (`a_mem`, `me_mem`).  So member existence,
  privacy, module arity and whether `M.x` is a term are all left to typing.
* An import emits `cc_import (ifile fq) E (ispec_names spec)` at the top level
  and `bc_import E ns` in a local body; the core checks it.  `as y` binds `y`
  to the module `E`, `use (n)` binds `n` to the member `E.n`.
* A local module, `let module x (ps) md in B end`, elaborates to
  `ℓₘ (gu_mk Δ D) in B`, and `x` is the slot `#0` in `B`.

## The naming rule

**One binding per name per frame.** Within a frame a name is bound at most
once: as an import alias, a member (`def`, `module`, a module alias, the
first segment of `module A.B`), or a parameter.  Binding a name the frame
already binds is an error (`"x is already declared"`, `"duplicate parameter
x"`); binding one an enclosing frame binds is shadowing.  Leading imports are
fresh against the earlier leading aliases only.  The invariant is `sf_wf F :=
NoDup (sf_names F)` and `ss_wf O`; because of it `fr_binds` has no priority
between its rules.  Local bodies follow the ordinary scoping of binders: an
entry shadows.

## Running example

`ElabExamples.running_spec` checks the elaboration below.  `Main.M.id` stands
for `a_glob (p_abs ["Main"] ["M"; "id"])`, `⟨Main.M⟩` for `me_path (p_abs
["Main"] ["M"])`, and the flags of `cc_def` are omitted.

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

```
cc_mod "M" (⋅ ▹ Type@0)
  [ cc_def "id" (Π #0 #1) (λ #0 #0);
    cc_mod "N" (⋅ ▹ Type@0)
      [ cc_def "k" (Π #1 (Π #1 #3)) (λ #1 (λ #1 (Main.M.id $ #3 $ #1))) ] ];
cc_def "j" (Π ℕ ℕ) (a_mem ⟨Main.M⟩ "id" $ ℕ)
```

In the body of `k` three frames are open, `N`, `M`, `Main`.  `id` is not
local, so `fbind` starts at `off = 2`; `N` does not bind it, so the search
moves to `M` with `off = 3`; `M` binds `id` as a member (`fr_mem`), applied to
`M`'s parameter `#3` (`preapp 3 [M; Main] [#3]`).  In `j`, `M` is closed, so
`M` in module position is `⟨Main.M⟩`, and `M.id Nat` selects `id` of it and
applies the result to `ℕ`.

## Proof structure

The elaborator works on the spec's data structures, so there are no
representation functions.  One `iff` per layer, by induction on the syntax,
for well-formed states (`ss_wf O`, `Forall sf_wf Fs`):

* `fr_lookup_iff` (frames), `lookup_char` (locals, then frames);
* `objects_iff`, by `Cst.cst_mut_ind`: `elab`/`elab_mod` against `sel`/`selm`,
  `let` declarations, `elab_mdef` against `sdef`, and one step of the local
  body loop against `sbody`; the loops nested in `elab_mdef` are restated as
  `elab_body` and `elab_path_unit` (equal by `reflexivity`);
* `import_iff`, `path_iff` (dotted module commands, by induction on the
  path), `commands_iff` (by `Cst.cst_mut_ind` again), `imports_iff` (leading
  imports), and `elaborate_core_iff`.
