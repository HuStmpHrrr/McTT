# Custom-entry notation levels

The `exp`, `nf`, `domain` and `judg` custom entries carry the paper's surface
syntax. Rocq 9.2 warns about several things they used to do; the fixes are all at
the notation *definitions*, so no use site needs parentheses. Keep it that way.

`Print Custom Grammar exp` (or `nf`/`domain`/`judg`) is the only reliable
diagnostic. It prints every level with its associativity and every rule with its
`SELF`/`NEXT`/`LEVEL "n"` slots.

## The rules that matter

- **Level 0 is for closed notations only** — those whose first *and* last token
  is a terminal (`ℕ`, `zero`, `Id`, `( x )`, `rec … end`). Everything else moved
  up: prefix-with-`constr`-argument forms (`^x`, `Type@n`, `#n`, `!n`, `⇑M`) are
  at level 1, constructor forms with a recursive last argument (`λ`, `Π`,
  `succ`, `⇑`, `⇓`, `𝕌@n`) at level 2. Postfix notations belong at level 1
  (`ρ ↯`), and `e[s]` / `e⟨φ⟩` are declared *first* so that level 1 is created
  left associative.
- **A level is created the moment it is referenced**, including from an argument
  slot of another notation (`a custom domain at level 30`) or from another entry
  (`Γ custom exp at level 50`). Custom-entry levels default to **right**
  associative, and a later `left associativity` at an already-created level is
  either silently ignored or an outright error. So an argument slot naming a
  level that an infix notation wants left associative destroys that
  associativity — which is what produced 77 `level-tolerance` warnings on
  `Γ , ℕ , A` until the `Γ custom exp at level 50` in `System/Definitions.v`'s
  `# x : A ∈ Γ` was dropped. **Never reference `exp` level 50 or `domain` level
  20 from an argument slot.**
- **`NEXT` is the next *declared* level**, so levels are sparse and a fresh one
  in a gap costs nothing. `succ m` in the `domain` entry sits at 19 purely so
  that it is what `ρ ↦ m` (level 20) admits on the right, letting
  `ρ ↦ succ m` parse unparenthesised.
