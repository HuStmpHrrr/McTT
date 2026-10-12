# Inductive types (stage A: parameterised, no indices, no OTT)

Branch `wip/ott`. What exists, where, and where it departs from the design
report (`.claude/plans/inductives-ott/report.md`, "Families" and "Plan",
stage A).

## The language

```
inductive List (A : Type@0) : Type@0 where
| nil
| cons (x : A) (xs : List A)
end

def length (A : Type@0) (l : List A) : ℕ :=
  elim l return z . ℕ
  | nil ⇒ 0
  | cons x xs, r ⇒ succ r
  end
end
```

* The parameters in parentheses are **uniform**; the type after `:` binds
  the **non-uniform** ones in front of the sort,
  `inductive Climb : ∀ (n : ℕ) → Type@0 where | stop | step (r : Climb (succ n)) end`.
* An argument whose type is the declared name applied to all its
  parameters, the uniform ones as declared, is **recursive**
  (`ca_rec (pt_self 0 Ps)`); one in which the name does not occur is
  non-recursive (`ca_arg A`); any other is rejected.  No argument may depend
  on a recursive one.  Recursion is first order: the name is in scope nowhere
  else, so positivity holds by construction (no separate positivity check).
* `elim M return ys z . A | c xs, hs ⇒ B … end`: the motive binds the
  non-uniform parameters and the scrutinee; a branch binds the non-uniform
  parameters, the constructor's arguments, then (after the optional comma,
  cosmetic) one hypothesis per recursive argument.  The core checks the
  counts, the order of the branches and the constructor names.
* Declarations are members of units and of global modules (also under
  module parameters, which become outermost uniform parameters); not of
  local bodies (`"an inductive type is not allowed in a local module"`).
* ℕ is unchanged.

## Shapes of recursive arguments

`ca_rec : ptyp_g E -> carg_g E` with
`ptyp_g E := pt_self k Ps | pt_aux k Ps | pt_pi A t` (`Syntax.v`): the
data is shaped for mutual blocks (`k`), nesting (`pt_aux`) and
function-shaped arguments (`pt_pi`).  Stage A accepts only `pt_self 0 Ps`
(`wf_gentry_indty`, decided by `decl_shapes_dec`).  The metatheory reads any
shape by its parameters alone, `ptyp_ps`, declared a coercion to `list`, so
the semantics of the other shapes is not built: a later stage replaces the
uses of `ptyp_ps` by a case on the shape.

## Classification in the command (A0.4)

The elaborator binds the declared name and nothing more: `cc_ind x pv R`
carries the declaration as written (`raw_decl`), whose constructors'
argument types see every earlier argument as a binder, then the
declaration's own parameters, then `Self : Π Δ. S`, bound outside them (but
inside the parameters of the enclosing frames, which stay implicit).  A
recursive occurrence is written Rocq-style with all the declaration's own
parameters, `cons (x : A) (xs : List A)`.
`rc_ind` classifies each argument (`cls_args nu np`,
`Core/Syntactic/System/IndClassify.v`):

* `cls_free`: `T = A[cls_wk np gs1]` — neither `Self` nor an earlier
  recursive argument occurs; filed `ca_arg A`;
* `cls_self`: `T = #(k + np) (uvars ++ Ps[cls_wk np gs1])`, the leading
  `nu` arguments exactly the uniform variables; filed `ca_rec (pt_self 0 Ps)`;
* anything else has no rule.
  `cls_wk np gs1 = wk_pat (cargs_pat gs1 ++ repeat false np ++ [true])`.

The classification is syntactic (`img_dec`: candidate by the left inverse
`unwk_pat`, then `exp_eq_dec`); stage A″ replaces `cls_arg` by a judgment
on normal forms.  `cls_con_ty` (syntactic) and `rc_ind_con_types` (after a
run, also `≈` at `⋅`) state that the filed constructor type is the
user's, with `Self := a_ind p` at the frames' parameters (`user_con_ty`,
`self_inst`).

## Core

| What | Where |
| --- | --- |
| `a_ind p`, `a_con p c`, `a_elim nm A Bs M`; `ind_decl`, `carg`, `ge_ind pv D` | `Core/Syntactic/Syntax.v` |
| telescopes, `ind_ty`, `con_ty`, `cargs_ctx`, `elim_mctx`, `elim_bctx`, `elim_bty`, `elim_ihs` | `Core/Syntactic/Inductives.v` |
| `wf_ind`, `wf_con`, `wf_elim`, congruences, `wf_exp_eq_elim_iota`, `wf_gentry_indty` (in the mutual block) | `Core/Syntactic/System/Definitions.v` |
| declarations are well typed (`decl_typed`), presupposition | `System/GlobalPresup.v`, `System/IndTyping.v`, `Syntactic/IndCong.v`, `Syntactic/IndConv.v` |
| values `d_ind`, `d_con`, neutral eliminator; evaluation, readback | `Core/Semantic/Domain.v`, `Evaluation*`, `Readback*` |
| PER: `ind_rel`, `ind_adm`; canonical relations `ind_nr`, `ind_ar` | `Core/Semantic/PER/Definitions.v`, `IndPER.v`, `IndCanon.v`, `IndElim.v`, `PER/Tele.v` |
| completeness | `Core/Completeness/IndSem.v`, `IndCases.v`, `ElimCases.v`, `TeleSem.v` |
| gluing (`glu_univ_elem_core_indty`, `ind_typ_at`, `glu_ind`, `ind_glu_exp_pred`) and soundness | `Core/Soundness/LogicalRelation/*`, `Soundness/IndCases.v`, `IndElimCases.v` |
| commands: `cc_ind`, `rc_ind`, `ind_name = "#"`, `rd_uparams`, `ind_frame`, `ind_qname`, `gs_ind`, `ind_gens` | `Core/Syntactic/Command.v`, `System/Command.v` |
| the type as a term (`ind_head`, `mem_xp`), the declaration-site oracle (`md_spec`, `xoracle`) | `Core/Syntactic/Imports.v`; `md_of`, `xo_of` in `Extraction/Privacy.v` |

## The type is a module

A declaration `cc_ind x pv R` makes the module `x` (`ge_body pv Δu Φ`),
over the uniform parameters `Δu = rd_uparams R`, as `rc_mod` makes one: it
pushes the frame `ind_frame Ξ x R` with `rc_mod`'s premises (`tele_ass Δu`,
`⊢ Δu ++ gs_tele Ξ`, `x` fresh), files the structural declaration there
under the unwritable name `#` (`ge_ind pv (gs_ind Ξ D)`, the frames'
parameters, the module's own included, its outermost uniform parameters;
its name is `ind_qname Ξ x = …x.#`), runs the generated constructors
`c := a_con p c $ (Δu ++ frame) vars` (`ind_gens`, run by `gens_run` with
the premises of `rc_def`), and closes the frame as the member `x`.

* Constructors are members of the module: `List.cons A x xs`, and
  `(List A).cons x xs` by module application; `open List use (nil; cons)`
  declares them (`examples/Inductives.mctt`).  Their names need only be
  distinct within the type.
* As a term, the module is the type former.  Expansion (`cmd_xp`, core)
  replaces a term `a_mem H x` whose `H.x.#` is a declaration
  (`ind_head`) by `apps (a_ind p) args`, `args` the arguments of `H`; `p`
  is found by the declaration-site oracle (`md_spec`: `mdecl`, which follows
  aliases), so `module M := List` and `open A use (List)` give the type
  too.  Typing has no new rule.
* The expansion oracles are bundled (`xoracle`: member types `xo_mt`,
  declaration sites `xo_md`); `cmd_xp_ok`/`tele_xp_ok` quantify over a
  bundle meeting both specifications; the checker uses `xo_of`.
* Not covered: a local module slot (`me_var`) is never an inductive type,
  so a local alias of one is not the type as a term.

## Algorithmic layer and checker

* `ati_ind`, `ati_con`, `ati_elim` (`Algorithmic/Typing/Definitions.v`); the
  eliminator's scrutinee infers `nf_indty p Rs`, and the motive and branches
  are checked at the parameters' normal forms `Rs`, related to the
  derivation's by `wf_elim_params_conv` (`Core/Syntactic/IndConv.v`).
* Completeness is by induction on the derivation with an outer induction on
  `exp_lets`; an eliminator counts `+1` there, since its motive and branches
  are re-derived at `Rs` and are no longer subderivations.
* Both checkers share `Extraction/IndCheck.v`; the eliminator's recursive
  calls are passed in as closures, so the mutual fixpoints and their
  obligation numbering are unchanged.
* A declaration is decided premise by premise in `Extraction/IndDecl.v`
  (`ind_entry_dec`); `exp_mvc` by a boolean mirror (`mvcb_spec`).

## Deviations from the report

1. **No separate positivity check**: first-order recursive arguments only,
   by construction of `carg`.
2. **Non-uniform parameters are typed at the inductive's sort** (option 1
   chosen by the coordinator), the uniform ones are free.
3. `wf_con` has two extra premises (the context of the arguments and the
   closed type of the constructor), read off by the models.
4. **Admissible uniform parameters** (`ind_adm`, option K): a stuck
   eliminator's readback makes fresh variables from the uniform parameters of
   the scrutinee's type, so the neutral clause of `ind_rel` asks them to be
   admissible beside the canonical ones.
5. **Gluing redesigns.** The components of the type (non-uniform parameter
   types and argument types) are glued inside the type predicate
   (`ind_glu_comps`), the sort is required `⊆` the gluing's universe, the
   recursive facts of `glu_ind_con` are closed under related parameter
   values (PER-closed) and under weakening and equal instances of the
   parameters (Kripke wrappers), the earlier link between the type
   predicate and the element predicate is removed, and
   `ind_glu_exp_pred` asks `glu_ind` at every equal instance of the
   parameters (eq-closed).
6. The eliminator's case along an embedding (`k_elim`, in
   `Completeness/ModuleCases.v` and `Soundness/ModuleCases.v`) takes the
   `⊢ˣ` premises of `wf_elim` too.
7. `ati_elim` has the premise `length (nfs_to_exps Rs) = ind_np D`; the
   checker decides it.
8. The checker's message for an ill-formed declaration names the type only
   (`"ill-formed inductive declaration x"`), not the failing premise; the
   classification has its own messages (non-positive occurrence, function
   into the type, dependency on a recursive argument, uniform parameters
   not as declared, wrong arity).
