> The code of this experiment was removed; it is in commit 842d4d8 under `experiments/extension_invariance/`.

# Approach Y: invariance under resolution-preserving extensions (grow, level)

Files: `Ext.v`, `PERExt.v`, `MonoAttempt.v`, `Kripke.v` (`build.sh`).

- `gc_ext` (resolution and parameters preserved) covers grow (`gc_ext_grow`,
  Ext.v:46) and filing a level (`gc_ext_file_level`, :82).
- Evaluation and readback are monotone (`eval_mono` :117, `read_mono` :136).
- PER model: first-order PERs only grow (PERExt.v); converse inclusions are false
  (`m_bad`: a neutral recursor whose successor branch mentions a new global,
  PERExt.v:65-180). Π-monotonicity of `per_univ_elem` is stuck (contravariant
  argument), conjectured true, unproved.
- The completeness judgment is not monotone as defined.  Minimal fix: box each
  judgment over extensions, `box J G := forall G', gc_ext G G' -> J G'`
  (Kripke.v): monotone by construction, existing case lemmas lift generically
  (`box_lift_tac`, several real lemmas lifted), `sem_globals` records boxed
  validity of entries; grow step's obligation is exactly the new member's boxed
  validity at its insertion frame.  Push/close need renaming extensions.
