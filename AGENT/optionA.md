# Option A: module substitution delayed into evaluation (working notes)

Branch: `optionA-delayed-msub` (worktree agent-a03ff549a1c2314d5).

## Design

* A *module environment* `menv` says where evaluation is:
  `me_base j` = "the open stack frames j, j+1, …" (no closed frame on top), and
  `me_frame a args κ` = a closed frame (address `a`, a top-level `path` whose
  members are the module chain, and the values `args` of its parameters as an
  env, innermost parameter first) on top of `κ`.  `me_top = me_base 0`.
* Closures capture the menv: `Πᵈ a κ ρ B`, `λᵈ κ ρ M`, `recᵈ … under κ ρ …`.
* `eval_exp Θ Ξ κ M ρ r`.  `$[m,k]` at `κ`: if frame `m` of `κ` is closed, its
  `k`-th argument; if it is the open stack frame `j`, the neutral
  `⇑ a (d_param (j,k))`, `a` its raw parameter type evaluated at `me_base (S j)`
  in the env of the parameter neutrals after it (`eval_ptele`).
* `a_glob (p_rel m ip)` at `κ`: *enter* `me_drop m κ` and resolve `ip` raw
  (`eval_ent`); `a_glob (p_abs fp ip)`: a pending frame for the unit
  (`eval_pend (me_base 0) (p_abs fp nil) |params| nil ip`).  A nested module
  with parameters is a pending frame; a pending frame with too few arguments is
  the value `d_gfn κ a c args ip`, and `eval_app` of it adds one argument.  A
  complete frame is pushed (`me_frame`) and resolution continues inside.
  A transparent entry is its raw body evaluated at the entered menv and `nil`;
  an opaque one the neutral `d_glob (addr.y)` applied to the arguments of the
  closed frames on its chain (`eval_gne`/`eval_fargs`, types = raw parameter
  types at their frames) at type `⟦A⟧ κ nil`.
* No `exp_msub`/`exp_sub`/`exp_wk`/`ctx_fn`/`sb_params`/`close` is applied in
  evaluation, readback, or NbE; only path arithmetic (`me_drop`, `path_in`).

## Proof strategy

The typing judgments are untouched.  The one syntactic-layer change is in
`GlobalInduction`: the `Emb` record gained `em_frame` (the frame map with an
offset), needed to get *all later* parameters of a frame valid — the open-frame
parameter rule evaluates the whole suffix of the telescope.  The models are
ported mechanically (closures carry `κ`; top-level evaluation is at `me_top`).
The only places where evaluation of a global/parameter matters are the bridge
lemmas (`glob_sem_of_raw`, `param_sem_of_raw`, `glob_glu_of_raw`,
`param_glu_of_raw`).  They are reproved through a *simulation* `vsim`
(`Core/Semantic/Simulation.v`): evaluating `M[θ]` at `(κ1,ρ1)` and `M` at
`(κ2,ρ2)`, where `θ` replaces leaves by binder-free terms whose values agree
with the right's leaves, gives related values; `vsim`-related values are
interchangeable in the PER model and the gluing model and read back equally.

## Status

* Done.  `make -f CoqMakefile.mk real-all` builds everything (Core, Algorithmic,
  Consequences, Extraction, Entrypoint, Frontend); nothing commented out of `_CoqProject`.
* `completeness_gctx`, `soundness_gctx'` unchanged statements; Print Assumptions:
  only `functional_extensionality_dep`, `eq_rect_eq`.  No Admitted.
* Extraction: orders for the 8 relations; lookup-dependent premises are stated
  in forall-form (for every result of the lookup) so the Equations impls recurse on a
  subterm; `eval_pend_impl` gets its sub-order by a dependent match on the order
  returning a function of the `Nat.ltb` equation (inversion lemmas are not guard-transparent).
* New files: Simulation.v 744, Bridge.v 409, PERSim.v 141, BridgeGlob.v 1543, GluSim.v 140.
