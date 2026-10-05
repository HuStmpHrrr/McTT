# A declarative specification of the elaborator

| File | What |
| --- | --- |
| `theories/Frontend/ElabSpec.v` | The spec `elab_spec : Cst.prog -> cunit -> Prop`: the scope (`ent`, `bound`), objects (`sel`, `selm`, `sparams`, `sunit`, `sdef`, `sbody`), opens (`item_ents`, `item_mems`, `open_ents`, `itarget`), commands (`scmd`, `scmds`), the leading scope (`slead`). |
| `theories/Frontend/Elaborator.v` | `elaborate_core`, on the spec's own scope of entries. |
| `theories/Frontend/ElabCorrect.v` | `elaborate_core_iff`, soundness, completeness, functionality, failure characterization. |
| `theories/Frontend/ElabExamples.v` | Hand-written `Cst.prog`s with their core units: the running example, pre-application, every module form (`module … where`, `module x (ps) := E`, `module A.B`, `let module` with a body or an alias, opens in a local body and the rejection of an unloaded unit there, the rejection of imports and evals in a local body, private entries of a local body), the definition keywords and each modifier rejection, opens with arguments, `use … as`, `export` and lists in any order, a repeated import, leading imports and opens (the parameter-type scope, and the frame), and every rejection of the one-binding rule, with its message. |

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
  imported units (`en_unit`), and, for the unit's parameter types only, the
  names of its leading opens (`en_open`).  An open's declarations are
  ordinary entries: `en_mem` in a frame, `en_var` in a local body.  A name denotes
  its innermost entry (`bound`), with `k` binders inside the entry and `n`
  outside.  A member is pre-applied to `vars_desc k n`: the binders outside
  it are exactly the parameters it is generalized over.
* The position decides what an object is: the head of a projection, the head
  of an application there, an alias body and an open target are module
  expressions (`selm`); everything else is a term (`sel`).  A projection is
  the core's member selection (`a_mem`, `me_mem`).  So member existence,
  module arity and whether `M.x` is a term are left to typing, and privacy
  to the core's command judgment (`run_cmd`, `acc_ok`); the elaborator checks
  none of them.
* The surface items are the core's `iitem`s (`option string * string *
  bool`), written by the parser: `as W` is `(None, W, true)`, `use (c as
  d)` is `(Some c, d, true)`, `export (e)` is `(Some e, e, false)`, in the
  order written.  The parser also splits the compound forms
  (`Cst.open_cmds`, `Cst.import_cmds`): `open E as W items` is `open E as W`
  then `open W items`, so the items refer to the alias; the long form
  `import X::Y ip args as W items` is `import X::Y` then `open X::Y ip args
  as W items`; a bare `import X::Y` only loads.
* `import X::Y` (`Cst.c_import fq`) emits `cc_load fq` and puts the unit in
  scope (`en_unit fq`); it declares nothing, and a repeated one is the core's
  no-op.  `open fq.ip args items` (`Cst.c_open`) has the target `itarget fq
  ip args`, read by `selm` like an alias body, so a unit it names must be
  imported (`the unit is not imported`); it loads nothing.
* In a frame, an open emits `cc_open E items`; the core checks the target
  and the items and runs the definitions and aliases they generate.  Each
  item's name is bound as a member of the frame (`en_mem d (q_abs fp (ch ++
  [d]))`) and must be fresh in the frame *before* the open (`d is already
  declared`); a name the open itself declares twice, or a member both used
  and exported, is the core's to reject (`n is already declared`, `c is used
  and exported`).
* In a local body, an open emits the pre-form `gm_open Φ E items`, which
  the core expands into ordinary entries, and binds one core binder per item
  (`item_ents`).  Local bodies have no `import`s (`import is not allowed in a
  local module; use open`) and no `eval`s (`eval is not allowed in a local
  module`); their entries may be `private`, which the core's privacy check
  enforces.
* The definition keywords are `def` with the modifiers they imply
  (`Cst.dkw_mods`): `theorem`/`lemma` = `abstract def`, `fact`/`remark` =
  `abstract private def`, `let`/`given` = `private def`.  The parser builds
  the `c_def` with the resulting modifiers, or, for a modifier the keyword
  already implies, `Cst.c_error msg` (`theorem is already abstract`, `fact
  takes no modifiers`, `let is already private`), which no rule relates and
  the elaborator reports.  At command level `let` is a keyword; a term `let
  … in … end` is one only in term position.
* `let x : A := M in B end` elaborates to `ℓ A ≔ M in B`, and `let x := M
  in B end` to `ℓ ≔ M in B`: the elaborator emits no type, the core infers it.
* A module body is elaborated where it stands (`elab_cmd` recurses into it),
  so there is no frame stack.  `module A.B` is desugared by the parser
  (`Cst.c_mod_dotted`).

## The naming rule

**One binding per name per frame**: `fresh x F`, where `F` is what the current
frame has bound (parameters, members, open declarations).  Binding a name an
enclosing frame binds is shadowing.  Local bodies follow the ordinary scoping
of binders; the core checks their names distinct.  Since lookup is
first-match, the rule is a premise only, not an invariant.

## Leading imports and opens

They are read twice (`slead`, then `scmds`):

```coq
Inductive slead : list ent -> list Cst.cmd -> list ent -> list ccmd -> Prop :=
| sl_nil : forall L, slead L nil L nil
| sl_import : forall L fq cs L' lds,
    slead (en_unit fq :: L) cs L' lds ->
    slead L (Cst.c_import fq :: cs) L' (cc_load fq :: lds)
| sl_open : forall L fq ip args its o E cs L' lds,
    itarget fq ip args = Some o -> selm L o E ->
    slead (open_ents E its ++ L) cs L' lds ->
    slead L (Cst.c_open fq ip args its :: cs) L' lds.

| es_intro : forall leads fp ps cs L lds tys ccs,
    slead nil leads L lds -> NoDup (map fst ps) -> sparams L ps tys ->
    scmds fp nil L (pents ps) (leads ++ cs) ccs ->
    elab_spec (leads, (fp, ps, cs)) (lds, ptele tys, ccs).
```

* **Before the header** (`slead`), in no binder: their units are in scope,
  and each name an open declares is an entry `en_open d E oc` (`open_ents`),
  denoting the member `oc` of the module `E` (`a_mem E c` / `me_mem E c`),
  or `E` itself for an `as` alias.  This is the scope `L` of the unit's
  parameter types; their loads `lds` run before the unit.  `E` is closed,
  so the entry is never weakened.  This is the one place where the
  elaborator does more than resolve a name to a binder or a member.
* **In the frame**, after the parameters, they are ordinary commands of the
  unit's own frame: the import loads again (a no-op), the open declares
  members of the unit (`cc_open`), applied to its parameters, fresh against
  them and against each other.  The body's scope outside the frame is `L`,
  whose `en_open` entries are always shadowed by those members.
* So a leading open's arguments may not name the parameters (`unbound name
  n`): they precede the header.
* A leading open (or long-form import) may `use` and `as`, but not
  `export`: the parser's `Cst.lead_cmds` replaces such a command by
  `c_error "export is not allowed before the module header"`, which
  `elab_lead` reports (no `slead` rule relates it).

```
import Prelude::Arith::Equality
open Prelude::Arith::Equality use (Eq)
module ScratchP (p : Eq 1 1) where def q : Eq 1 1 := p end end
```
elaborates to the loads `[cc_load Equality]`, the parameters `⋅ ▹ (a_mem
⟨Equality⟩ Eq $ 1 $ 1)`, and the body `cc_load Equality ; cc_open ⟨Equality⟩
[(Some Eq, Eq, true)] ; cc_def q … (ScratchP.Eq $ #0 $ 1 $ 1) #0`
(`ElabExamples.leading_scope`).

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

One `iff` per function: `lookup_iff`, `ihead_iff` (the head of an open
target), `args_iff`/`target_iff` (open targets, computed without building
the object, so that the elaborator's local bodies stay structural),
`objects_iff` (by `Cst.cst_mut_ind`), `commands_iff` (by `Cst.cst_mut_ind`, motive `md = md_where body
-> Pcmds body`), `lead_iff`, `elaborate_core_iff`.
