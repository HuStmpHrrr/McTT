# Option B: module parameters are λ-variables

Branch: `worktree-agent-a9a9388dfbcd1d0d9` (based on `ext/gctx` at `ec59f26`).

## Goal

Evaluation, readback and NbE apply no syntactic operation to a term (no
substitution, weakening, module substitution, `ctx_fn`/`ctx_pi` building, path
opening).  Before this branch `gc_resolve` handed back entries transformed by
`↑ₘ n` / `close mp c`, and `eval_exp_param` computed `T[↑ₘ (S n)]ᵐ[sb_params n]`.

## Design (as built)

* **No module parameters in the syntax.** `a_param`, `ne_param`, `d_param`,
  `lpath`, `sb_params`, `msub` and all of `ModSubst.v` are gone.  The
  parameters of the open frames are ordinary λ-variables: a member is checked
  in the local context `gs_tele Ξ` (the frames' parameter telescopes, innermost
  first), and an `eval` obligation is checked in `Γ ++ gs_tele Ξ`.
* **Members are stored closed.** `wf_gentry_def` checks `T ⊢ M : A` with
  `T = gs_tele Ξ` and *stores* `ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))`:
  generalization happens once, in the typing rule (syntax), never at
  evaluation.  A member is used as `a_glob p` applied to the parameters it
  abstracts — inside its own module to the parameter variables, outside to
  explicit arguments (the elaborator's job).  Its value is the closure the
  stored λ evaluates to; applying it to the parameter variables reads exactly
  the environment suffix that holds them.
* **Absolute paths only.** `path = {| p_unit : list string ; p_mems : list
  string |}`; `qu_rel`, `path_open`, `Opening.v` are gone.  A frame on the
  stack records its own module path (`gstack := list (path * gunit)`), so a
  member of an open module has the same absolute name it will have once the
  module is closed or the unit filed.  Hence resolution is a *pure lookup*:
  `gc_resolve` finds the innermost frame whose module path prefixes `p`, else
  the filed unit `p_unit p`, and returns the stored entry unchanged.
* Consequently resolution is monotone along every way a global context grows
  (push a frame, grow a frame, close a nested module into its parent, file a
  unit, add a level): `Emb Ψ1 Ψ2 := ⊢g Ψ2 ∧ ∀ p e, resolve Ψ1 p = Some e →
  resolve Ψ2 p = Some e`, and a judgment at `Ψ1` holds at `Ψ2`
  (`emb_preserves_wf`).  This replaces `msub_preserves_wf`, `Transport.v`,
  `Discharge.v`.

## Why not the literal "environment suffix"

Reading a suffix of the environment at evaluation needs the offset of the
member's context in the use site's context.  Evaluation does not know it, and
cannot read it off the environment: environments are compared pointwise
(`env_eq`, `⟦σ⟧s` is pointwise), so their length is not an invariant.  Putting
the offset into the term (`a_glob p k`) breaks substitution: for a non-variable
image `σ k` there is no offset to move to, and `M[σ][τ] = M[σ ⨟ τ]` fails.
Applying the closed member to the parameter variables is the same computation
with the offset carried by ordinary variables, which substitution handles.

## Status / notes

(updated as work proceeds)
