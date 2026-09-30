# Soundness via extension invariance: negative

`Exp.v` has 392 lines and no `Admitted`. Its only axiom is funext.

## Findings
- The gluing model is not monotone under growing the global context.
- The break is at Π: its gluing clause is contravariant over glued arguments.
  `glu_type_mono_iff_per_mono` (l.264) shows that monotone gluing is equivalent
  to monotone `per_univ`, which is stuck.
- The Kripke clauses can be carried over only with an extra `read_shift` lemma
  (readback commutes with ⇑ⁿ), which the development doesn't have.
- `glu_nat_not_mono` (l.248) is a counterexample when `⊢ Γ` is missing at the
  source.
- Proved positives:
  - `gext_*`: syntax, eval and readback carry over.
  - `ne_clause_mono`, `glu_nat_mono`: monotone, given `read_shift`.
  - `glu_rel_exp_closed_weaken` (l.300): `⊩ Γ → ⋅ ⊩ c : T → Γ ⊩ c : T`. This
    is the glob/param case at a fixed context.
- Soundness's fundamental theorem covers typing only, so there is no δ case.
- A box over extensions covers grow and level but not push or close.
- Identity-only relative transport is cyclic for push: the intermediate
  context contains younger members.

## Recommendation
Kripke over module substitutions, as in completeness. Factor the age induction
of `GlobalCases.v` over an abstract semantic interface. Gluing-specific cost is
about 350–450 lines.
