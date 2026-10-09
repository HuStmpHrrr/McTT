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
| 0 | closed forms: `ℕ`, `zero`, `Id`, `Wk`, `⋅`, `⋄`, `↑`, `Type⟨t⟩`, `rec … end`, `recⁿ … end`, `recᵈ … end` |
| 1, left | postfix and prefix-with-`constr`-argument: `M[σ]`, `M[φ]ʷ`, `ρ↯`, `Type@n`, `Typeω@n`, `#n`, `𝕌@l`, `𝕌ω@n`, `#ᵈ n`, `#ⁿ n`, `Typeⁿ@n`, `Typeωⁿ@n`, `𝕃@n`, `𝕃ᵒ o` |
| 2 | constructors with a recursive last argument: `succ`, `λ`, `Π`, `⇑`, `⇓`, `⇑!`, `succl`, `maxl`, `univⁿ`, and the `ᵈ`/`ⁿ` counterparts |
| 10, left | application: `M $ N`, `m $ᵈ n`, `M $ⁿ N` |
| 20, left | `ρ ↦ m` |
| 30 | `q σ`, `ι φ` |
| 40, left | `φ ⊙ ψ` |
| 45, right | `σ ⨟ τ` |
| 50, left | `σ ,, M`, `Γ ▹ A`, `Φ ⊳ x ↦ E` |
| 70 | every judgment, with its arguments at 69 |

The syntactic judgments carry a global context, spelled with `⍮`:
`⊢ Ψ ⍮ Γ`, `Ψ ⍮ Γ ⊢ M : A`, `Ψ ⍮ Γ ⊢ M ≈ M' : A`, `Ψ ⍮ Γ ⊢ A ⊆ A'`,
`Ψ ⍮ Γ ⊢w φ : Δ`, `Ψ ⍮ Γ ⊢s σ : Δ`, `Ψ ⍮ Γ ⊢s σ ≈ σ' : Δ`, and
`⊢ Ψ ⍮ Δ ⊆ Γ` for context refinement.  `⍮` is a terminal of each of those
notations, not an operator, so it has no level of its own.  The global context's
own well-formedness uses a letter suffix in the same style as `⊢w`/`⊢s`:
`⊢g Ψ` (the stack, notation of `wf_gstack`), plus three that also carry the
ambient telescope the thing is checked in, again with `⍮`: `Ψ ⍮ Δ ⊢e E` (an
entry), `Ψ ⍮ Δ ⊢m Φ` (a module), `Ψ ⍮ Δ ⊢u U` (a unit; a definition over
`⊢m`, not a judgment).  The filed units alone are well formed when
`⊢g Θ ⍮ nil` (no frame open).  `Γ ∋ #x : A` takes no `Ψ`.

Resolution has two notations, distinguished by a superscript because they have
the same shape: `Φ ∋ ip ⇒ Δ ⍮ E` in a module, and `Ψ ∋ᵍ p ⇒ Δ ⍮ E` for a whole
`path`.  A bare `∋` would collide with the other, which is why only the innermost
one is unadorned.  Lookup in the filed units (`gds_lookup`) is a
*function*, so it needs no notation.
The `Δ` is the telescope crossed on the way in, accumulated innermost-first, so
that a use site can generalize what it found with `ctx_pi`/`ctx_fn`.

`M[σ]` and `M[φ]ʷ` share the prefix `M [ _` at the same levels, so Rocq factors
them and only the closing token (`]` vs `]ʷ`) decides; `M[p]ᵖ`, reserved for
path opening, must follow the same pattern (`p at level 60`).  Level 1 is
predefined *left* associative in `constr`, so the order of the level-1
notations does not matter; level 40 is left associative too, which is why `⨟`
sits at 45.

`Syntax.v` keeps each topic's notations in a module after its definitions:
`Exp_Notations` (terms), `GlobalCtx_Notations` (module bodies, `⋄` and `⊳`),
`Ctx_Notations`, `Nf_Notations`, `Sub_Notations`, `Wk_Notations`.
`Syntax_Notations` exports `Exp_`, `Ctx_`, `Nf_` and `Sub_Notations`; the other
two are imported separately, as before.

Judgment arguments are at **69** because a slot between two terminals otherwise
defaults to level 200 and swallows Rocq's cast `x : T` (level 100) — `Γ ⊢ M : A`
would read `M` as `M : A`.

Evaluation carries the global context the same way, `⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m`,
and so do the module relations: `⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h` (module expressions),
`$ᵐ| h & n | Θ ⍮ Ξ ↘ h'` (a module value applied), `h ·ₜ x Θ ⍮ Ξ ↘ d` and
`h ·ₘ y Θ ⍮ Ξ ↘ h'` (selection of a term member, a submodule), `h ·ₜ* ch …` and
`h ·ₘ* ch …` (along a chain), `⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms` (several terms),
`$*| f & ns | Θ ⍮ Ξ ↘ r` (several arguments) and `⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ'` (the
environment after a body).  The selected name and the chain are at level 0:
`h ·ₜ* (pre ++ x :: nil) Θ ⍮ Ξ ↘ f`.

## Universes and levels

The two tiers of universes are spelled so that the Rocq notation and the
surface syntax agree: a bare `Type` is **small**, and `ω` marks the **large**
tier.

| sort | small | large |
| --- | --- | --- |
| `exp` | `Type⟨t⟩` (`a_univ t`), `Type@n` (literal level) | `Typeω@n` (`a_typ n`, the universe ω²+n) |
| `domain` | `𝕌@l` (`d_suniv l`, a level *value*) | `𝕌ω@n` (`d_univ n`) |
| `nf` | `univⁿ c xs` (`nf_univ c xs`), `Typeⁿ@n` (= `univⁿ n la_nil`) | `Typeωⁿ@n` (`nf_typ n`) |

`Type⟨t⟩` takes a level *term* in angle brackets: braces are impossible
(`Type@{` is Rocq's own universe annotation) and `{ }` in `constr` would
collide with `sig`.  A small normal form carries a constant and a sorted list
of level atoms with offsets, which is why `univⁿ` takes two arguments.

The types of levels are indexed by a sort: `Level@n` in `exp` (`a_level n`),
`Levelᵈ@n` in `domain`, `Levelⁿ@n` in `nf`, and `Level`, `Levelᵈ`, `Levelⁿ`
are the sort-0 ones.  `Level@m ⊆ Level@n` for `m <= n`
(`wf_subtyp_level`), and every `Level@n` is in `Type@0`.  Their terms are `𝕃ᵒ o` (a literal: an ordinal
`o = (a, b)`, that is `ω·a + b`, below ω²; `Core/Syntactic/Ordinals.v`),
`succl M` and `maxl M N`, with `dlvl_lit`, `dlvl_suc`, `dlvl_max` on values
and `nf_lvl_of L` on normal forms.  `𝕃@n` is the finite literal
`𝕃ᵒ (0, n)` and `Type@n` is `Type⟨𝕃@n⟩`: both notations match only a
finite literal, so a lemma about any literal is stated with `𝕃ᵒ`.

`Level@n` holds the levels below ω·(n+1): a literal `𝕃ᵒ o` is in it when
`fst o <= n` (`wf_llit`), and `maxl M 𝕃ᵒ(S n, 0) ≈ 𝕃ᵒ(S n, 0) : Level@(S n)`
for `M : Level@n` (`wf_exp_eq_maxl_absorb`).  An atom of a level normal form
carries its sort, `la_cons k s a r` (offset, sort, neutral); in values the
sort is read from the annotation of the neutral, `dsort (Levelᵈ@s) = s`.
The canonical form drops an atom whose sort is below the constant's tier
(`la_keep`), and `lvl_canon_iff` holds over the assignments that put an atom
of sort `s` below ω·(s+1) (`lvl_adm`).

The surface syntax matches.  A level literal is `nl` (finite, `𝕃ᵒ (0, n)`),
`nL` (`𝕃ᵒ (1, n)`, the same literal as `ω + n`), or `ω`, `ω + b`, `ω * a`,
`ω * a + b` (`𝕃ᵒ (a, b)`; `·` is the Unicode spelling of `*`, `omega` the
ASCII one of `ω`).  `Level@n`, also `Level@{n}`, is `a_level n`, and
`Level` is `Level@0`; the printer writes `Level` and `Level@n`.  The
small universes are `Type@n` (short for `Type@{nl}`), `Type@nl` and
`Type@{t}`, and `Type@ω` (`Type@omega`) and `Type@nL`, short for `Type@{ω}`
and `Type@{ω+n}`.  The large tier `Typeω@i` (`Cst.typ i`), the universe
ω²+i, is written `Type@{ω^2}` and `Type@{ω^2+i}` (`omega^2` in ASCII),
braced; `ω^2` is one token (`OMEGA2`), and not a level: anywhere else the
driver reports "ω^2 is not a level".  The printer picks the shortest
spelling: `Type@n`, `Type@ω`, `Type@nL`, else `Type@{t}`, and `Type@{ω^2}`,
`Type@{ω^2+i}`; a literal prints as `nl` or as `ω·a+b` with `·a` dropped at
`a = 1` and `+b` at `b = 0` (so `1L` prints as `ω+1`, as before `nL` was a
literal).  (`ω` and `·` are among the Unicode spellings listed in
`modules.md`, *Surface syntax*.)

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
- **A slot declared at level 0 needs its argument parenthesised**, or the
  `level-tolerance` warning fires: in `Φ ⊳ x ↦ E`, `x` is at 0.
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
