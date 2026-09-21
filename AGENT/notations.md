# Notations: one grammar, no delimiters

Every notation in the development lives in ordinary `constr`, in `mctt_scope`.
There are no custom entries and hence nothing to quote:
`Ψ ⍮ Γ ⊢ M[σ] : A -> Ψ ⍮ Γ ⊢ zero : ℕ` is what you write and what Rocq prints.

The price of a single grammar is that a spelling denotes one sort only, so the
sorts that mirror `exp` constructor for constructor carry a superscript:
`ᵈ` for values (`ℕᵈ`, `λᵈ`, `Πᵈ`, `succᵈ`, `#ᵈ`, `$ᵈ`, `recᵈ`) and `ⁿ` for
normal and neutral forms (`ℕⁿ`, `λⁿ`, `Πⁿ`, `succⁿ`, `#ⁿ`, `$ⁿ`, `recⁿ`, `⇑ⁿ`).
This is what makes an un-ported fragment a hard error rather than a misparse:
`exp`, `sub`, `wk`, `ctx`, `domain`, `nf` and `ne` are distinct types.

`Print Notation "…"` and `Print Grammar constr` are the diagnostics.

## Levels

| level | forms |
| --- | --- |
| 0 | closed forms: `ℕ`, `zero`, `Id`, `Wk`, `⋅`, `⋄`, `∅`, `↑`, `rec … end`, `recⁿ … end`, `recᵈ … end` |
| 1, left | postfix and prefix-with-`constr`-argument: `M[σ]`, `M⟨φ⟩`, `ρ↯`, `Type@n`, `#n`, `𝕌@n`, `#ᵈ n`, `#ⁿ n`, `Typeⁿ@n` |
| 2 | constructors with a recursive last argument: `succ`, `λ`, `Π`, `⇑`, `⇓`, `⇑!`, and the `ᵈ`/`ⁿ` counterparts |
| 10, left | application: `M $ N`, `m $ᵈ n`, `M $ⁿ N` |
| 20, left | `ρ ↦ m` |
| 30 | `q σ`, `ι φ` |
| 40, left | `φ ⊙ ψ` |
| 45, right | `σ ⨟ τ` |
| 50, left | `σ ,, M`, `Γ ▹ A`, `Φ ⊳ x ↦ E`, `T ▸ x ↦ u ⊲ T'` |
| 70 | every judgment, with its arguments at 69 |

The syntactic judgments carry a global context, spelled with `⍮`:
`⊢ Ψ ⍮ Γ`, `Ψ ⍮ Γ ⊢ M : A`, `Ψ ⍮ Γ ⊢ M ≈ M' : A`, `Ψ ⍮ Γ ⊢ A ⊆ A'`,
`Ψ ⍮ Γ ⊢w φ : Δ`, `Ψ ⍮ Γ ⊢s σ : Δ`, `Ψ ⍮ Γ ⊢s σ ≈ σ' : Δ`, and
`⊢ Ψ ⍮ Δ ⊆ Γ` for context refinement.  `⍮` is a terminal of each of those
notations, not an operator, so it has no level of its own.  The global context's
own well-formedness uses a letter suffix in the same style as `⊢w`/`⊢s`:
`⊢g Ψ` (a `gctx`), `Ψ ⊢e E` (an entry), `Ψ ⊢m Φ` (a module), `Ψ ⊢u U` (a unit),
`Ψ ⊢t T` (the import trie).  `Γ ∋ #x : A` takes no `Ψ`.

Resolution has one notation per level, distinguished by a superscript because the
three have the same shape: `Φ ∋ ip ⇒ E` in a module, `T ∋ᵘ fp ⇒ U` in the import
trie, and `Ψ ∋ᵍ p ⇒ E` for a whole `path`.  A bare `∋` would collide with the
other two, which is why only the innermost one is unadorned.

`M[σ]` and `M⟨φ⟩` are declared first so that level 1 is created *left*
associative; `ρ↯` likewise in `Domain_Notations`. Level 40 is already left
associative in `constr`, which is why `⨟` sits at 45.

Judgment arguments are at **69** because a slot between two terminals otherwise
defaults to level 200 and swallows Rocq's cast `x : T` (level 100) — `Γ ⊢ M : A`
would read `M` as `M : A`.

## Traps

- **Application needs an explicit operator.** A `constr` notation must contain
  at least one symbol, and pure juxtaposition is Rocq's own application, so
  `a_app` is `M $ N`.
- **`,` is unavailable.** A parsing `,` in `constr` would steal Rocq's pair
  notation, so context extension is `Γ ▹ A`.
- **Right-open forms absorb what follows.** `λ A M`, `Π A B`, `λⁿ`, `Πⁿ` end in
  a slot at level 60, so they must be parenthesised anywhere but in tail
  position: `exp_wk (Π A B) ↑`, not `exp_wk Π A B ↑`. This is the one class of
  silent misparse — both readings are well-typed `exp`.
- **A superscript is an identifier character.** `#ᵈ x` needs the space: `#ᵈx`
  lexes as `#` applied to the identifier `ᵈx`. For the same reason every
  decorated glyph is a single quoted terminal (`"'⇑ⁿ' M"`), never a symbol
  followed by a superscript.
- **`M[σ]` steals `f [a; b]`.** A `[` following a term is read as a
  substitution, so list literals in argument position need parentheses:
  `rel_chain R ([a1; a2])`.
- **camlp5 cannot factor two rules that share a leading token but sit at
  different notation levels.** Four spellings exist only to keep such pairs
  apart: the evaluation judgment is `⟦rec m return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r`
  (`rec … end` is an `exp` at level 0, `⟦rec` is one token); `eval_wk` is
  `⟪φ⟫ ρ` (the `⟦ … ⟧` bracket belongs to evaluation); context lookup is
  `Γ ∋ #x : A` (`#` belongs to `a_var`); and `d_var` is `#ᵈ n` (`!` is a
  terminal of Corelib's `exists ! x, p`).
- **A key slot at level 0 needs its argument parenthesised.** `T ▸ x ↦ u ⊲ T'`
  declares both `x` and `u` at 0, so `∅ ▸ x ↦ Some U ⊲ ∅` raises the
  `level-tolerance` warning; write `(Some U)`.
- **`gm_ext` is `⊳`, not `▹`.** `Φ ▹ x ↦ E` at level 50 is an incompatible
  prefix of `Γ ▹ A`, and camlp5 drops one of them.

## Judgments that are prefixes of other judgments

`⊢ Ψ ⍮ Γ` / `⊢ Ψ ⍮ Δ ⊆ Γ`, `⊨ Γ` / `⊨ Γ ≈ Γ'`, and
`Ψ ⍮ Γ ⊢ M : A` / `Γ ⊢ M : A ® m ∈ R`.
camlp5 has no room for a rule that is a proper prefix of another once the two
agree on the shared slot: the shorter one is absorbed, and `⊢ Γ` stops parsing.
Two things fix it, and both are needed:

- **leave the slot where the two diverge unannotated** — the shorter judgment's
  border slot then defaults to the next level and the longer one's inner slot to
  200, which is enough for camlp5 to keep them as alternatives — this is why
  `⊢ Ψ ⍮ Γ` annotates only `Ψ` and `⊢ Ψ ⍮ Δ ⊆ Γ` only `Ψ` and `Γ`, leaving `Δ`
  free;
- **declare the shorter judgment first**, which is why
  `Reserved Notation "⊨ Γ"` is hoisted above `Notation "⊨ Γ ≈ Γ'"`.

A `notation-incompatible-prefix` warning means one of the two is about to stop
working; there should be none in a clean build.
