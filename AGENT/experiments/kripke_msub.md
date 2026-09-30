> The code of this experiment was removed; it is in commit 842d4d8 under `experiments/kripke_msub/`.

# Experiment X: Kripke validity over module substitutions

`Exp.v` (777 lines) builds against the current `.vo`s with no `Admitted`.
`Print Assumptions` lists only funext and `Eq_rect_eq`.
Build it from `theories/` with `rocq c -R . Mctt ../experiments/kripke_msub/Exp.v`.

## Definitions (Exp.v:17–91)
- `syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E` takes the hypotheses of `msub_preserves_wf`.
  Each hypothesis may also assume `⊢ Θ1 ⍮ Ξ1 ⍮ Γ`.
- `sem_msub` is `syn_msub` plus `⊨` of the base context, and `⊨` of each
  parameter, global and unfolding at the target context.
- `kexp_eq Θ1 Ξ1 Γ A M M'` means that for every `sem_msub` into `Θ2 Ξ2`,
  `⊨ tctx Γ` and `tctx Γ ⊨ tm M ≈ tm M' : tm A` hold at `gc_mk Θ2 Ξ2`.
  `kctx` and `ksubtyp` are defined the same way.
  The conclusion includes `⊨ Γ` because `wf_ctx_extend` has no `⊢ Γ` premise.

## Results
| | Lemma | Line |
|---|---|---|
| Fundamental theorem, all rules | `kripke_fundamental` | 95 |
| Transport keeping the source context | `msub_preserves_wf'` | 149 |
| Composition | `syn_msub_then`, `sem_msub_then` | 237, 267 |
| Identity; old-form theorem at a sound context | `sem_msub_id`, `fundamental_at` | 345, 366 |
| Push | `sem_msub_push` | 385 |
| δ and neutrals via the empty environment | `rel_exp_delta_nil`, … | 460–590 |
| Transport with no semantic argument | `kexp_transport_syn` | 600 |
| Grow a frame / add a level | `sem_msub_rebase` | 631 |
| Soundness of one flat frame | `flat_frame_fundamental` | 713–775 |

- The fundamental theorem's ordinary cases reuse the existing case lemmas at
  the target context, after rewriting with `exp_msub_sub*`. The glob, param,
  δ and `⋅` cases each take one line.
- `⊨g` is `⊢g` plus two conditions:
  - every global satisfies `⋅ ⊨ ctx_pi Δ A : Type@i` and `⋅ ⊨ ctx_fn Δ M : …`;
  - every parameter satisfies `⋅ ⊨ T[..] : Type@i`.
  δ evaluates in `nil`; `sb_zero` connects `nil` to any `ρ`.
- Composition needs only the syntactic half of the first step. Validity
  therefore moves along close, push, grow and file with no semantic argument.

## Remaining work for ⊨g of every well-formed global context
- **Circularity.** Proving `⊨g` of the final context needs its identity
  substitution, which needs `⊨g` of that same context.
- **Breaking it.** Induct in insertion order. For each member `g`, map it
  syntactically into `Y_g` (older globals only), then rebase semantically.
  This is done for one flat frame.
- **Nested modules.** `Y_g` is `closable_pop`'s target.
- **Filed units.** `Y_g` must be the truncated level, not `closable_file`'s
  target.
- **Outer frames.** Need a general renaming lemma.
- **Telescopes.** Parameters must come before their frame's members.
- **Estimate.** About 500–650 more lines, with no new PER reasoning.
