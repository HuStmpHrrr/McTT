# core-let: resume notes (semantic side)

Branch `ext/core-let`, worktree `.claude/worktrees/agent-a9f164221c7d1caa7`.
Read `AGENT/core-let.md` (design) first.  The front end is on
`ext/core-let-frontend`, and the algorithmic checker and extraction are on
`ext/core-let-algo`.  Other agents own those branches, so don't edit
Frontend/, Algorithmic/, Extraction/, Entrypoint.v, driver/ or examples/ here.

## State: all of `Core/` builds

- `a85c0cf`, `2d541b3`, `4d81e48`: semantic definitions, PER model, realizability.
- `ed189f4`: completeness.
- `a381352`: soundness.
- The following commit makes `Core/Semantic/Consequences.v` build (rigidity helper for `consistency_ne_helper`).
- `Print Assumptions` of completeness(_gctx), soundness(_gctx, _gctx'), consistency(_gctx) and canonical_form_of_{typ,nat}_gctx is exactly `functional_extensionality_dep` and `eq_rect_eq`, as at the baseline `56e979d`.

## Approved statement changes

- `Completeness/Consequences/Types.v` defines `ctx_ass` and `rigid_typ`.
- `is_typ_constr_and_exp_eq_{var,typ,nat}_*` take `rigid_typ Γ A`.  The var theorem and `eval_var_at_initial_env` also take `ctx_ass Γ x`.
- `initial_env_spec` concerns assumption slots.

These are generalized and strictly stronger: `rel_wk_shift`, `rel_wk_shift_tail`, `rel_wk_under_ctx_shift`, `rel_sub_shift`, `rel_sub_under_ctx_shift`, `rel_exp_under_ctx_shift` and `completeness_fundamental_typ_shift`.  Each now takes any entry `e :: Γ`.

## Where things are

- **PER** (`PER/Lemmas.v`, after `per_env_extend_intro'`).
  - `def_tie` and `per_env_extend_def` are the canonical relation of `Δ ▸ S ≔ M`.
  - `per_ctx_env_extend_def` builds it.
  - `def_tie_resp` says the tie propagates along `per_env_extend` and along `M ≈ M'`.
- **Completeness.**
  - LR Lemmas: `rel_sub_under_ctx_restrict` and `rel_exp_under_ctx_restrict` change the context PER; `rel_exp_under_ctx_of_simple` gives equality from validity plus pointwise relatedness; `rel_exp_under_ctx_simple_at`.
  - ContextCases: `per_ctx_env_of_def`, `rel_ctx_extend_def'`, `per_ctx_env_def_forget`, `per_ctx_env_def_conv`.
  - VariableCases: `valid_exp_var_here`, `rel_exp_var_delta`.
  - LetCases: `rel_sub_under_ctx_into_def`, `_extend_sub_def`, `_q_def`, `per_univ_of_instance_def`, `rel_exp_let_gen`, and its corollaries `rel_exp_let_zeta`, `rel_exp_let_cong` and `valid_exp_let`.
- **Soundness.**
  - Definitions: `cons_def_glu_sub_pred` and `glu_ctx_env_cons_def`.
  - Lemmas: the def cases, plus `glu_ctx_env_cons_def_clean_inversion`, which is an alternative of `invert_glu_ctx_env`.
  - Weakening: `kripke_shift_def`.
  - ContextCases: `glu_rel_ctx_extend_def`.
  - LetCases: `glu_rel_exp_let`.

## Pitfalls

- pet caches every library it has loaded.  After you rebuild an upstream `.vo`, an interactive session in a file that imports it either does not see the new lemmas or fails to load.  For such files, iterate with `make -f CoqMakefile.mk X.vo`.  To inspect a goal, use a scratch copy with `Show.` compiled by `rocq c -R . Mctt`.
- `rocq_compile_file` times out on `PER/Lemmas.v` (about 155 s).  Use make.
- `mauto n` does not fail when it leaves goals.  So `[ mauto 2 |]` or `try (...; mauto 3)` can leave stray goals.
- `etransitivity; [|symmetry]; eassumption` commits to the first `eassumption`.  Use `solve_per`.
