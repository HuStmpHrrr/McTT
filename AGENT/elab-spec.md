# A declarative specification of the elaborator

| File | What |
| --- | --- |
| `theories/Frontend/ElabSpec.v` | The spec `elab_spec : Cst.prog -> cunit -> Prop`: the scope (`ent`, `bound`), objects (`sel`, `selm`, `sparams`, `sunit`, `sdef`, `sbody`), imports (`itarget`, `ibinds`, `simport`), commands (`scmd`, `scmds`, `simports`). |
| `theories/Frontend/Elaborator.v` | `elaborate_core`, on the spec's own scope of entries. |
| `theories/Frontend/ElabCorrect.v` | `elaborate_core_iff`, soundness, completeness, functionality, failure characterization. |
| `theories/Frontend/ElabExamples.v` | Hand-written `Cst.prog`s with their core units: the running example, pre-application, every module form (`module … where`, `module x (ps) := E`, `module A.B`, `let module` with a body or an alias, the rejection of imports and evals in a local body) and every rejection of the one-binding rule, with its message. |

## Theorems (all closed under the global context)

```coq
Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Corollary elaborate_core_sound / elaborate_core_complete    (* the two halves *)
Corollary elab_spec_functional : elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Corollary elaborate_core_fails : (exists e, elaborate_core prg = eerr e) <-> forall u, ~ elab_spec prg u.
```

## What the elaborator does, and does not, do

It resolves names and nothing else; it never looks inside a module.  The
design and its history are in [`elab-simplify.md`](elab-simplify.md).

* Everything in scope is one list of entries `ent`, innermost first: core
  binders (`en_var`: λ, Π, `let`, `let module`, parameters, local-body
  entries), members of open frames (`en_mem`, by absolute path), import
  aliases (`en_as`, `en_use`) and imported units (`en_unit`).  A name denotes
  its innermost entry (`bound`), with `k` binders inside the entry and `n`
  outside.  A member is pre-applied to `vars_desc k n`: the binders outside
  it are exactly the parameters it is generalized over.
* The position decides what an object is: the head of a projection, the head
  of an application there, an alias body and an import target are module
  expressions (`selm`); everything else is a term (`sel`).
* An import emits `cc_import (ifile fq) E (ispec_names spec)`; the core checks
  it.  Local bodies have no imports and no `eval`s.
* A module body is elaborated where it stands (`elab_cmd` recurses into it),
  so there is no frame stack.  `module A.B` is desugared by the parser
  (`Cst.c_mod_dotted`).

## The naming rule

**One binding per name per frame**: `fresh x F`, where `F` is what the current
frame has bound (parameters, members, aliases).  Binding a name an enclosing
frame binds is shadowing.  Leading imports form a frame of their own.  Local
bodies follow the ordinary scoping of binders.  Since lookup is first-match,
the rule is a premise only, not an invariant.

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

In the body of `k` the scope is `y, x, B, id ↦ Main.M.id, A`.  `id` has three
binders inside and one outside, so it is `Main.M.id $ vars_desc 3 1 =
Main.M.id $ #3`.  In `j`, `M` is closed, so `M` in module position is
`⟨Main.M⟩`.

## Proof structure

One `iff` per function: `lookup_iff`, `objects_iff` (by `Cst.cst_mut_ind`),
`import_iff`, `commands_iff` (by `Cst.cst_mut_ind`, motive `md = md_where body
-> Pcmds body`), `imports_iff`, `elaborate_core_iff`.
