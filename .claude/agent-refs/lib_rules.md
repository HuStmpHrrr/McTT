# Writing McTT library code (lib/)

**Driver.** Build it in your worktree with `dune build --root .` (after `make -f CoqMakefile.mk real-all post-all` in `theories/` if the extracted OCaml is stale), then run `_build/default/driver/mctt.exe <file>` from `lib/`, or pass `--search-root lib`. You only write `.mctt` files.

**Units.**
- `Prelude/` holds the reusable library, organized hierarchically:
  `Prelude::Logic`; `Prelude::Function::{Iter, Combinators}`; and
  `Prelude::Arith::{Equality, Plus, Mult, Sub, MinMax, Order, Monotone, Lattice, Parity,
  Decide, Induction, Ackermann, Pow, Sum, Factorial, Div, Divides}`; `Prelude::Data::Vec`
  and its laws (being renamed to `Prelude::Data::Vec::Properties`).
  New units go in the right subfolder; create one (e.g. `Prelude/Data/`) if
  none fits.
- The unit `Prelude::A::B` lives in `lib/Prelude/A/B.mctt` and starts with
  `module Prelude::A::B where … end`.
- `Nat` is a keyword, so it can't be a path segment.
- Only programs, the clients, live directly in `lib/`.
- Naming convention: definitions go in `X.mctt` (`Prelude::A::X`). When laws
  are separate from definitions, they go in `X/Properties.mctt`
  (`Prelude::A::X::Properties`). A file `X.mctt` and a directory `X/` can sit
  side by side.
- When a type argument (e.g. `A`) is the same for every operation, make it a unit parameter, as in `Prelude::Data::Vec (A : Type@0)`; operations needing other types take only those.
- Known cost: checking `Eq n n` doubles in time with each +1 in n, so keep
  closed proof instances at numbers of about 20 or below. Plain computations
  are cheap.
- Leading imports go before it: `import Prelude::Arith::Equality use (Eq; refl)`, or
  `import Prelude::Function::Iter as Iter`.
- Units with parameters: `module Prelude::Function::Iter (A : Type@0) (f : …) where`.
- File names are CamelCase and match the module names.

**Lexical rules.**
- Identifiers are letters only, so use camelCase (`plusAssoc`, `hab`). No `_`
  and no digits.
- Comments are `(* … *)`.

**Syntax.**
- `def name (x : A) (y : B) : T := body end`
- `fun (x : A) (y : B) -> M`
- `forall (x : A) (y : B) -> T`
- `rec n return y . T | zero => M | succ p, ih => N end`
- `let x : A := a; y : B := b in body end`
- `let module M := Unit args; …`
- `exfalso t return x . P`
- `True`, `true`, `False`; `Type@0`, `Type@1`, …
- `eval M` and `eval M : T`.
- Module arguments come after the projection: `Iter.iter Nat f n a`.
- Look at the existing `lib/Prelude/*.mctt` and `lib/NatTheory.mctt` for
  working examples.

**Propositions.**
- A proposition is a type in `Type@0`.
- Equality of numbers is `Prelude::Arith::Equality.Eq n m`, which computes to `True` or
  `False`. Use `refl`, `sym` and `trans` from there.
- A proof is a term, usually by induction with `rec`.
- An impossible case is closed with `Prelude::Logic.absurd T h`. `Equality` also has `cong` and `transport`, where
  `h : False`.
- Conversion is by normalization, so `Eq (succ a) (succ b)` is literally
  `Eq a b`, `Eq 0 (succ n)` is `False`, and so on. Choose recursion arguments
  so the goal computes.

**Showcase.**
- Every unit should be reusable: general statements, parameterized units
  where natural, and no client-specific code.
- Each track also writes a client `lib/<Topic>.mctt` (module `<Topic>`). It
  imports the library and `eval`s closed instances. A closed instance of a
  theorem normalizes to `true : True`.

**Tests.** Add one expect test per client to `driver/Test.ml`, in this form:
```
let%expect_test "lib/<Topic>.mctt" =
  let _ = main_of_lib "<Topic>.mctt" in
  [%expect {| …exact driver output… |}]
```
Paste the exact driver output. Append the test at the end of the file;
another track also appends, and the conflicts are resolved at merge.

**Comments.**
- Concise, complete sentences, external-facing: say what a definition or
  theorem is.
- One short header comment per unit, and a comment on non-obvious lemmas.

**Commits.** Commit on your branch, and do not push.

**Speed.**
- Don't optimize slow programs.
- If an evaluation is slow (over ~10s), shrink or drop that example, and explain
  in your report why it is slow.
- Numerals are unary.
