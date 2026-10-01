# Option C: absolute addressing, closing once in the judgments

Branch `optionC-absolute` (from `ext/gctx` at `ec59f26`).  Status: done, no
`Admitted`/`admit`/`Axiom`; `make` (Rocq, extraction) and `dune build/runtest`
pass, and `completeness_gctx`, `soundness_gctx'` assume only
`functional_extensionality_dep` and `eq_rect_eq`.

## The design

* **Frames by level.**  `qu_rel L` and `$[L, k]` name the frame at de Bruijn
  *level* `L` (`0` = outermost, `gs_frame Ξ L := nth_error (rev Ξ) L`), and a
  parameter by its position from the *outer* end of the telescope.  Pushing a
  frame renames nothing, so `↑ₘ`, `path_open`, `sb_params n`-with-shift are gone.
* **Parameter types are stored.**  A frame is `gu_mk params ptys mod`;
  `ptys = ctx_ptys L params` (the `k`-th binding read with the bindings before it
  as `$[L, _]`) is a premise of `wf_gunit_intro` / built by `wf_gmod_ext`
  (`gs_push Ξ P Φ`).  `gs_param` is `nth_error` of it; `wf_param` is
  `gs_param Ξ lp = Some T -> Γ ⊢ a_param lp : T`.
* **Entries are stored as used.**  `gm_lookup`/`gc_lookup`/`gc_resolve` return
  the entry; `wf_glob : Γ ⊢ a_glob p : A`, `δ : a_glob p ≈ M : A`.
* **Closing once, in the judgments.**  `ms_close L mp c d` (params of level `L`
  to λ-vars, `p_rel L ip` to `app_vars (p_app mp ip)`, everything else fixed).
  `gm_close L mp Δ Φ` maps every def entry to `ctx_pi Δ A[cl]`/`ctx_fn Δ M[cl]`.
  `wf_gentry` takes the member's name: `wf_gentry_mod` stores
  `ge_mod Δ' (gm_close |Ξ| (p_rel (pred |Ξ|) [x]) Δ' Φ)`, and `wf_gdep_cons`
  files `gu_close fp U`.  The stored `ge_mod` telescope is informational.

## What changed in the metatheory

* Syntactic: `Scoping` (cs by level; closed entries mention only outer levels),
  `Transport` (generic msub transport; identity transport `rebase_preserves_wf`
  along `gc_ext`, push is an instance), `Discharge` (`close_preserves_wf`,
  `closable_pop`, `closable_file` on `gm_close`), `GlobalPresup` (same shape;
  `rwf` is about stored entries; `entry_typed` of a module records the open
  module it closes).
* Semantic: **the Kripke box is over extensions, not module substitutions.**
  `ext_fundamental`/`kglu_fundamental`: a derivation in `Θ1 ⍮ Ξ1` is valid in
  every well-formed `Θ2 ⍮ Ξ2` with `gc_ext Θ1 Ξ1 Θ2 Ξ2` validating what `Θ1 ⍮ Ξ1`
  resolves.  The cases are the fixed-context lemmas verbatim (no msub
  rewriting).  `GlobalInduction` (age induction) works over `gc_ext`; no `Emb`,
  `ms_comp`, `ms_off`; telescope truncation is a prefix of `ptys`.
* Downstream: elaborator emits levels (aliases need no shifting any more);
  command semantics closes on `cc_mod` and files `gu_close`; `GlobalCheck` keeps
  only `check_ctx`/`check_typ`/`check_exp`/`check_gm_fresh` (a stored closed
  module does not determine the open one its `⊢e` went through, so the old
  `check_gmod`/`check_gunit`/`check_gstack` on stored data are not decidable as
  stated; nothing used them).

## Gotchas

* `length Ξ - 1` does not reduce on a variable stack; use `Nat.pred`.
* `gs_push nil P ⋄` needs `(@nil gunit)`.
* `repeat split` unfolds `unit_scoped`; use `refine (conj _ ...)`.
* The rocq MCP is pinned to the main checkout's `theories/`; in a worktree,
  probe with `rocq c -R . Mctt` on a truncated copy (`/tmp/optC/probe.sh`).
