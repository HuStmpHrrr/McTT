# A declarative specification of the elaborator

| File | What |
| --- | --- |
| `theories/Frontend/ElabSpec.v` | The spec `elab_spec : Cst.prog -> cunit -> Prop`: the scope (`ent`, `bound`), objects (`sel`, `selm`, `sparams`, `sunit`, `sdef`, `sbody`), imports (`ispec_items`, `item_ents`, `item_mems`, `itarget`, `simport`), commands (`scmd`, `scmds`, `simports`, `lunits`). |
| `theories/Frontend/Elaborator.v` | `elaborate_core`, on the spec's own scope of entries. |
| `theories/Frontend/ElabCorrect.v` | `elaborate_core_iff`, soundness, completeness, functionality, failure characterization. |
| `theories/Frontend/ElabExamples.v` | Hand-written `Cst.prog`s with their core units: the running example, pre-application, every module form (`module … where`, `module x (ps) := E`, `module A.B`, `let module` with a body or an alias, imports in a local body and the rejection of an unloaded unit there, private entries of a local body, the rejection of evals in a local body), imports with arguments, `use … as`, `export`, leading imports in the unit's frame, and every rejection of the one-binding rule, with its message. |

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
  entries), members of open frames (`en_mem`, by qualified name) and
  imported units (`en_unit`).  An import's declarations are ordinary
  entries: `en_mem` in a frame, `en_var` in a local body.  A name denotes
  its innermost entry (`bound`), with `k` binders inside the entry and `n`
  outside.  A member is pre-applied to `vars_desc k n`: the binders outside
  it are exactly the parameters it is generalized over.
* The position decides what an object is: the head of a projection, the head
  of an application there, an alias body and an import target are module
  expressions (`selm`); everything else is a term (`sel`).  A projection is
  the core's member selection (`a_mem`, `me_mem`).  So member existence,
  module arity and whether `M.x` is a term are left to typing, and privacy
  to the core's command judgment (`run_cmd`, `acc_ok`); the elaborator checks
  none of them.
* `import P a1 … ak spec` has the items `ispec_items spec : list iitem`:
  `as W` is `[(None, W, true)]`, `use (c as d)` is `(Some c, d, true)`,
  `export (e)` is `(Some e, e, false)` (uses first, then exports).  Its
  target is the module object `itarget fq ip args` (the unit `fq` at member
  path `ip`, or the module `ip` in scope, applied to `args`), read by
  `selm` like an alias body, so a unit it names must be nameable
  (`the unit is not imported`).
* In a frame, an import emits `cc_load fq` (for another unit) and
  `cc_import E items`; the core checks the target and the items and runs
  the definitions and aliases they generate.  Each item's name is bound as
  a member of the frame (`en_mem d (q_abs fp (ch ++ [d]))`) and must be
  fresh in the frame *before* the import (`d is already declared`); a name
  the import itself declares twice, or a member both used and exported, is
  the core's to reject (`n is already declared`, `c is used and exported`).
* In a local body, an import emits the pre-form `gm_import Φ E items`,
  which the core expands into ordinary entries, and binds one core binder
  per item (`item_ents`).  It loads no unit.  Local bodies have no `eval`s
  (`eval is not allowed in a local module`); their entries may be
  `private`, which the core's privacy check enforces.
* `let x : A := M in B end` elaborates to `ℓ A ≔ M in B`, and `let x := M
  in B end` to `ℓ ≔ M in B`: the elaborator emits no type, the core infers it.
* A module body is elaborated where it stands (`elab_cmd` recurses into it),
  so there is no frame stack.  `module A.B` is desugared by the parser
  (`Cst.c_mod_dotted`).

## The naming rule

**One binding per name per frame**: `fresh x F`, where `F` is what the current
frame has bound (parameters, members, import declarations).  Binding a name an
enclosing frame binds is shadowing.  Leading imports are commands of the
unit's frame, after its parameters: their arguments may name the parameters,
their names are members of the unit (fresh against the parameters and each
other, and the unit's own members against them); only their units
(`lunits`) are in scope of the parameters.  Local bodies follow the ordinary
scoping of binders; the core checks their names distinct.  Since lookup is first-match,
the rule is a premise only, not an invariant.

## Running example

`ElabExamples.running_spec` checks the elaboration below.  A global is a chain
of selections from its unit: `Main.M.id` stands for `qname_term (q_abs
["Main"] ["M"; "id"])`, that is `a_mem (me_mem (me_unit ["Main"]) "M") "id"`,
`⟨Main.M⟩` for `qname_mod (q_abs ["Main"] ["M"])`, that is `me_mem (me_unit
["Main"]) "M"`, and the flags of `cc_def` are omitted.

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

One `iff` per function: `lookup_iff`, `ihead_iff` (the head of an import
target), `args_iff`/`target_iff` (import targets, computed without building
the object, so that the elaborator's local bodies stay structural),
`objects_iff` (by `Cst.cst_mut_ind`), `import_iff`, `commands_iff` (by `Cst.cst_mut_ind`, motive `md = md_where body
-> Pcmds body`), `imports_iff`, `elaborate_core_iff`.
