# Writing McTT library code (lib/)

**Driver.** Build it in your worktree with `dune build --root .` (after `make -f CoqMakefile.mk real-all post-all` in `theories/` if the extracted OCaml is stale), then run `_build/default/driver/mctt.exe <file>` from `lib/`, or pass `--search-root lib`. You only write `.mctt` files.

**Units.**
- `Prelude/` holds the reusable library, organized hierarchically:
  `Prelude›Logic`; `Prelude›Function›{Iter, Combinators}`;
  `Prelude›Arith›{Equality, Plus, Mult, Sub, MinMax, Order, Monotone, Lattice, Parity,
  Decide, Induction, Ackermann, Pow, Sum, Factorial, Div, Divides, …}`;
  `Prelude›Data›{Vec, Stream, Church}` and their `›Properties`; `Prelude›Algebra›…`;
  `Prelude›Universe›{Levels, Formers}`.
  New units go in the right subfolder; create one (e.g. `Prelude/Data/`) if
  none fits.
- The unit `Prelude›A›B` lives in `lib/Prelude/A/B.mctt` and starts with
  `module Prelude›A›B where … end`.
- `Nat` (`ℕ`) is a keyword, so it can't be a path segment.
- Only programs, the clients, live directly in `lib/`.
- Naming convention: definitions go in `X.mctt` (`Prelude›A›X`). When laws
  are separate from definitions, they go in `X/Properties.mctt`
  (`Prelude›A›X›Properties`). A file `X.mctt` and a directory `X/` can sit
  side by side.
- When a type argument (e.g. `A`) is the same for every operation, make it a unit parameter, as in `Prelude›Data›Vec (u : Level) (A : Type@{u})`; operations needing other types take only those.
- Abstract universe levels where a definition is naturally level-generic: a level
  parameter `(u : Level)` on the unit or module, types at `Type@{u}`. A common pattern is a
  level-generic submodule plus a level-0 export, e.g. `module Negation (u : Level) … end`
  then `open Negation 0l export (Not; absurd)`. Levels: literals `0l`, `1l`, …,
  `succl t`, `maxl t u`; `Type@n` = `Type@{nl}`. See `AGENT/universes.md`.
- Known cost: checking `Eq n n` doubles in time with each +1 in n, so keep
  closed proof instances at numbers of about 20 or below. Plain computations
  are cheap.
- Leading imports go before it: `import Prelude›Arith›Equality use (Eq; refl)`, or
  `import Prelude›Function›Iter as Iter` (inside the module body unless a parameter type
  needs it).
- Units with parameters: `module Prelude›Function›Iter (u : Level) (A : Type@{u}) (f : …) where`.
- File names are CamelCase and match the module names.

**Lexical rules.**
- Identifiers are letters only, so use camelCase (`plusAssoc`, `hab`). No `_`
  and no digits.
- Comments are `(* … *)`.

**Syntax.** Write the Unicode forms (the printer prints them; ASCII is still accepted):
`→` (`->`), `⇒` (`=>`), `λ` (`fun`), `∀` or `Π` (`forall`), `≔` (`:=`), `›` (`::`),
`ℕ` (`Nat`), `⊤` (`True`), `⊥` (`False`), `⋆` (`true`), `ω` (`omega`).
- `def name (x : A) (y : B) : T ≔ body end`
- `λ (x : A) (y : B) → M`
- `∀ (x : A) (y : B) → T`
- `rec n return y . T | zero ⇒ M | succ p, ih ⇒ N end`
- `let x : A ≔ a; y : B ≔ b in body end`
- `let module M ≔ Unit args; …`
- `exfalso t return x . P`
- `⊤`, `⋆`, `⊥`; `Type@0`, `Type@1`, …, `Type@{u}`, `Type@ω`; `Level`, `0l`, `succl`, `maxl`
- `eval M` and `eval M : T`.
- Module arguments come after the projection: `Iter.iter 0l ℕ f n a`.
- Look at the existing `lib/Prelude/*.mctt` and `lib/NatTheory.mctt` for
  working examples.

**Propositions.**
- A proposition is a type in `Type@0` (or `Type@{u}` for level-generic connectives).
- Equality of numbers is `Prelude›Arith›Equality.Eq n m`, which computes to `⊤` or
  `⊥`. Use `refl`, `sym` and `trans` from there.
- A proof is a term, usually by induction with `rec`.
- An impossible case is closed with `Prelude›Logic.absurd T h`. `Equality` also has `cong` and `transport`, where
  `h : ⊥`.
- Conversion is by normalization, so `Eq (succ a) (succ b)` is literally
  `Eq a b`, `Eq 0 (succ n)` is `⊥`, and so on. Choose recursion arguments
  so the goal computes.

**Showcase.**
- Every unit should be reusable: general statements, parameterized units
  where natural, and no client-specific code.
- Each track also writes a client `lib/<Topic>.mctt` (module `<Topic>`). It
  imports the library and `eval`s closed instances. A closed instance of a
  theorem normalizes to `⋆ : ⊤`.

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
