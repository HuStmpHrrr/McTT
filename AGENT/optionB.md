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

## Judgments (`System/Definitions.v`)

* `wf_param`, `wf_exp_eq_param` gone.  `wf_glob`, `wf_exp_eq_glob`,
  `wf_exp_eq_glob_unfold` premise `gc_resolve Θ Ξ p = Some (ge_def b pv A B)`
  (the function, so no canonicity is needed anywhere) and type `a_glob p` at `A`
  (δ: `a_glob p ≈ M : A`).
* `Θ ⍮ Ξ ⍮ mp ⊢e E`, `Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ`, `Θ ⍮ Ξ ⍮ mp ⊢u U`: `mp` is the
  module path of the thing checked.  `wf_gmod_nil` premises
  `⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ`; `wf_gmod_ext` pushes `(mp, gu_mk Δ Φ)` and checks
  `E` at `path_in mp x`; `wf_gentry_def`/`_axiom` check in `gs_tele Ξ` and store
  `ctx_pi`/`ctx_fn` of it.
* `wf_gdep_cons` checks a unit at `Θ ⍮ nil ⍮ p_abs fp nil`; `wf_gstack_cons`
  adds `frame_fresh Θ Ξ mp` (bottom frame: unit not filed; inner frame:
  `path_in` of the enclosing frame with a fresh name).  Still one mutual block.

## Metatheory

* `Scoping.v` (no frame counts): every judgment scoped, every resolvable entry
  closed (`wf_gc_resolve_closed`); weakening/substitution leave globals alone.
* `GlobalCtx.v`: `gc_sub` lemmas for push / grow / close-nested / file /
  add-level — pure lookup facts.
* `GlobalPresup.v`: `Emb`, `emb_preserves_wf`, and `global_induction_all`, one
  mutual induction over all eleven judgments, parametric in the notion `V` of a
  valid entry: everything resolvable at `Θ ⍮ Ξ` is `V`-valid at every context
  `Θ ⍮ Ξ` embeds into (`Good`).  `presup_global` is its instance at syntactic
  typing; `presup_exp_typ` etc. keep their full statements.
* `Completeness/ModuleCases.v`: `sem_emb` (embedding + globals valid at the
  target), `kripke_fundamental` (every rule, case lemmas at the target),
  `gctx_sem := global_induction sem_entry`.  `Soundness/ModuleCases.v`: the
  same for gluing (`glu_emb`, `kglu_fundamental`, `gctx_glu`).
* `completeness_gctx`, `soundness_gctx'`: statements unchanged.  Assumptions:
  `functional_extensionality_dep`, `eq_rect_eq` only.

## Build state

`make -f CoqMakefile.mk real-all` builds everything in `_CoqProject`: all of
`Core/` (incl. Consequences, Transparency), `Algorithmic/`, and
`Extraction/{PseudoMonadic,Evaluation,Readback,NbE,Subtyping,TypeCheck}`.
Removed from `_CoqProject` (not ported): `Core/Syntactic/Command.v`,
`Core/Syntactic/System/Command.v`, `Extraction/{GlobalCheck,Command}.v`,
`Frontend/*`, `Entrypoint.v` (so no extraction / driver).  `user_exp` moved
from `Frontend/Elaborator.v` to `Algorithmic/Typing/Definitions.v`.

## What downstream needs

* `System/Command.v`: `gs_push` takes the module path; `gs_add` stores
  `ctx_pi (gs_tele Ξ) A` / `ctx_fn (gs_tele Ξ) M`; closing a module inserts
  `ge_mod Δ Φ` into the parent (no `close`); `run_wf` needs `frame_fresh` for
  pushes.  The merge/level/restriction part is untouched by the design.
* `Extraction/GlobalCheck.v`: decide the new `⊢e/⊢m/⊢u` (check in `gs_tele`,
  compare the stored closed forms) and `frame_fresh`.
* `Frontend/Elaborator.v`: emit absolute paths `p_abs unit chain` (it knows the
  unit name and the open-module chain), apply a member to the parameter
  variables of its enclosing modules (they are λ-variables `#k` now), and emit
  eval obligations in context `gs_tele`.  `PrettyPrinter.ml`: no `a_param`.
