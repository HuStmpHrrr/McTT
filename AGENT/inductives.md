# Inductive types (stage A/A′: parameterised, function-shaped arguments, no indices, no OTT)

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
  List.elim l return z . ℕ
  | nil ⇒ 0
  | cons x xs, r ⇒ succ r
  end
end

eval length ℕ (List.cons ℕ 1 (List.nil ℕ))
```

### Left and right of `:`

Where a parameter is written decides how it behaves, in the declaration
and in the eliminator.  **The rule:** a parameter written left of `:` is
uniform, the same in every recursive argument and fixed for the
eliminator; one bound right of `:`, by the type in front of its sort, is
non-uniform and may take a new value in each recursive argument.

**Left of `:` — uniform parameters.**  `List (A : Type@0)` has one.  A
uniform parameter is the same everywhere in the type:

* in a constructor, a recursive argument passes it back unchanged:
  `cons (x : A) (xs : List A)`.  `(xs : List ℕ)` or `(xs : List)` is
  rejected: "List is not applied to its uniform parameters as declared in
  the argument xs of cons";
* the eliminator reads it off the scrutinee's type `List A`: the motive
  `return z . T` does not bind it, and a branch `| cons x xs, r ⇒ …` does
  not receive it;
* the uniform parameters are the parameters of the module `List`:
  `List.cons A x xs` is `(List A).cons x xs`.

**Right of `:` — non-uniform parameters** (with constructor results, a
later stage, these become indices).  `Climb : ∀ (n : ℕ) → Type@0` has one.
The type binds it in front of its sort, and it may vary:

```
inductive Climb : ∀ (n : ℕ) → Type@0 where
| stop
| step (r : Climb (succ n))
end

def steps (n : ℕ) (c : Climb n) : ℕ :=
  Climb.elim c return m z . ℕ
  | stop m ⇒ 0
  | step m r, h ⇒ succ h
  end
end
```

* a recursive argument may give it a new value: `r : Climb (succ n)`;
* the motive binds it, then the scrutinee: `return m z . ℕ`;
* a branch binds the constructor's value of it first (`m`), then the
  constructor's arguments (`r`), then, after the optional comma, one
  hypothesis per recursive argument (`h`), which is the motive at that
  argument's own values: `h` is about `r : Climb (succ m)`, at `succ m`.

A recursive occurrence is the type applied to all its own parameters,
uniform then non-uniform.  The parameters of an enclosing module are never
written: they are the type's outermost uniform parameters, as for every
member.

### Rules

* An argument whose type is the declared name applied to all its
  parameters, the uniform ones as declared, is **recursive**
  (`ca_rec (pt_self 0 Ps)`); so is a function into it, `∀ (b : B) … → X Ps`,
  each domain free of the name (`ca_rec (pt_pi B … (pt_self 0 Ps))`, stage
  A′); one in which the name does not occur is non-recursive (`ca_arg A`);
  any other is rejected.  No argument may depend on a recursive one.  The
  name occurs only strictly positively by construction of the shapes (no
  separate positivity check).
* `X.elim M return ys z . A | c xs, hs ⇒ B … end`: the core checks the
  counts, the order of the branches and the constructor names; the branch
  labels are the declaration's constructor names, unqualified.
* Declarations are members of units and of global modules (also under
  module parameters, which become outermost uniform parameters); not of
  local bodies (`"an inductive type is not allowed in a local module"`).
* ℕ is unchanged (`rec`); an inductive type can be bound as the natural
  numbers, which the numerals then denote (below).

## Shapes of recursive arguments

`ca_rec : ptyp_g E -> carg_g E` with
`ptyp_g E := pt_self k Ps | pt_aux k Ps | pt_pi A t` (`Syntax.v`): the
data is shaped for mutual blocks (`k`), nesting (`pt_aux`) and
function-shaped arguments (`pt_pi`).  Stage A′ accepts the shapes
`ptyp_simple t = true`: `pt_pi B1 (… (pt_pi Bk (pt_self 0 Ps)))`, `k ≥ 0`
(`wf_gentry_indty`; the domains `ptyp_doms t` are typed, each over those
before it, at the sort).  `pt_aux` and `pt_self (S k)` are reserved.

### Function shapes (stage A′)

```
inductive Ord : Type@0 where
| base
| next (o : Ord)
| lim (f : ∀ (n : ℕ) → Ord)
end

def approx (o : Ord) (k : ℕ) : ℕ :=
  Ord.elim o return z . ℕ
  | base ⇒ 0
  | next p, r ⇒ succ r
  | lim f, h ⇒ h k
  end
end
```

* The type of a recursive argument of shape `t` is `ptyp_ty p D pat t`: a
  `Π` over the domains, into the type at the parameters.  Its hypothesis
  has type `ptyp_ihty A β σ x t`: `Π (b : B). (ihty of the rest at x b)`,
  ending in the motive at the leaf's parameters and `x b…`
  (`Inductives.v`).  The hypothesis term is `ptyp_ih`: `λ b. X.elim (x b)`.
* ι: `X.elim (c … f …) ≈ B[…, f, …, λ b. X.elim (f b), …]` (`wf_iota`).
* Semantics: `eval_ih` (the eliminator at `v`, or the value
  `d_ihfn ρ nm A Bs t v` at a `Π` shape), applied by `eval_app_ihfn`
  (apply `v`, then `eval_ih` of the rest); `eval_shty` / `eval_ihty` give
  the type of an argument / of its hypothesis, a `Πᵈ b (nil ↦ fam) fam_cod`
  whose codomain closure applies the family `d_shfam` / `d_ihfam`
  (`eval_app_shfam`, `eval_app_ihfam`).  Readback needs nothing new: a
  hypothesis is read back by η at its `Π` type.
* `read_brs_cons` has the premise `cargs_plen (ind_nn D) gs` (every shape
  ends at `ind_nn D` parameters): the freshness invariant of
  `Core/Semantic/Avoid.v` places the motive's bad position by it.
* `wf_con` has a third derivable premise: the context of the arguments
  before a recursive argument, then `k` of its domains, extended by the
  rest of its type, is well formed (`shape_rest_wf'` derives it;
  `wf_con_of_lookup` is the rule without it, a `mctt` hint).  The Kripke
  fundamental theorem needs the rest's types valid at the target
  (`k_con`), and no inversion on a `Π` gives them.
* The classification: `cls_sh nu np gs1 d T t` (a shape under `d`
  domains), `cls_rec` files it.  `cls_wkd d np gs1 = wk_pat (repeat false d
  ++ cargs_pat gs1 ++ repeat false np ++ [true])`.  The normal-form path
  makes `(f : Arr Ord)`, `Arr X := ∀ (n : ℕ) → X`, recursive.
* Rejections (`cls_reason`, `Extraction/IndDecl.v`, messages in
  `Extraction/Command.v`): the name in a domain ("… occurs in the domain of
  a function in the argument f of mk, which is not strictly positive"),
  under a head that does not compute, not at the uniform parameters as
  declared, elsewhere.

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
* `cls_rec` with `cls_sh … 0 T t`: `T = Π B1[cls_wkd 0]. … #(d + k + np)
  (uvars ++ Ps[cls_wkd d])`, the leading `nu` arguments exactly the uniform
  variables; filed `ca_rec t`;
* anything else has no rule.
  `cls_wk np gs1 = wk_pat (cargs_pat gs1 ++ repeat false np ++ [true])`.

The classification is syntactic (`img_dec`: candidate by the left inverse
`unwk_pat`, then `exp_eq_dec`).

### On normal forms (stage A″, design P-cmd)

An argument the syntactic classification rejects is classified as its
normal form (`cls_arg_in`, `System/Command.v`):

```
cls_in_nf : (forall g', ~ cls_arg nu np gs1 T g') ->
            Θ ⍮ Ξ ⍮ rarg_ctx Ξ R args1 ⊢ T : Typeω@i ->
            nbe_ty Θ Ξ (rarg_ctx Ξ R args1) T W ->
            cls_arg nu np gs1 (nf_to_exp W) g -> cls_arg_in Θ Ξ R args1 gs1 T g
```

`rarg_ctx Ξ R args1 = rtele args1 ++ tele_wk (rd_params R) ↑ ++ Self :: gs_tele Ξ`,
`Self : rd_self_ty R = Π (own params). S`.  The syntactic path comes first,
so the classification is a function (`cls_arg_in_functional`); `rc_ind` has
the premise `cls_cons_in Θ Ξ R cs`.  The nbe premise is in the command
judgment, outside the mutual block; NbE builds no syntax.

* `Id N`, `M.F N` (a transparent member), `let Y := N in Y` are recursive;
  `(λ X. ℕ) (N → ℕ)` is `ca_arg ℕ`.
* `Neg Bad` (`Neg X := X → ⊥`) and `(Bad → Type@0) → Type@0`: "Bad occurs
  in a non-positive position in the argument f of mk".
* `F Bad` with `F` abstract, an axiom or a module parameter: "Bad occurs in
  the argument f of mk under a head that does not compute (an opaque
  definition, an axiom or a parameter)" (`cls_reason` 4).
* The checker (`cls_arg_in_dec`, `Extraction/IndDecl.v`) checks the context
  and that the argument is a type, normalizes it, and classifies the normal
  form; a rejection gives the reason on the normal form.  The judgment's
  global state is equivalent to the checker's, so the normal forms agree
  (`nbe_ty_ext`, `Core/Semantic/GlobalExt.v`).

`rc_ind_con_types` (`Core/IndCommand.v`) states that after a run each filed
constructor type is `≈` at `⋅` to the user's (`user_con_ty`, `Self := a_ind p`
at the frames' parameters): an argument classified as written is filed as
its weakening (`cls_con_ty`); one classified as its normal form is equal to
it by `soundness_ty'`, and the equality moves through the substitution of
`Self` (`base_sub`, `self_typed`) and the `Π`s before it (`conv_tail`).

The filed (normal-form) types are what the constructors' members carry and
what is printed (question G5): the user's term would need the constructor
step to be proved never to fail at the user's type, beyond
`rc_ind_con_types`.

## Core

| What | Where |
| --- | --- |
| `a_ind p`, `a_con p c`, `a_elim p nm A Bs M`; `ind_decl`, `carg`, `ge_ind pv D` | `Core/Syntactic/Syntax.v` |
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

## The eliminator names its type (item 4a)

`a_elim p nm A Bs M` records the declaration's name `p` (`…X.#`); the
neutral `ne_elim p …` too (the domain's `d_elim` already had it).
`wf_elim`, its congruence and `ι` use the same `p` as the scrutinee's
type `apps (a_ind p) Ps`; evaluation ignores it (the scrutinee's value
carries it); readback takes it from `d_elim`.

* Surface `X.elim M return … end`: the elaborator elaborates `X` as a module
  and records, lexically, `elim_head`: the chain from the unit, arguments
  dropped, then `#`.  A head that is not a chain from a unit (a local
  slot) is rejected there: `"only an inductive type declared in a module
  has an eliminator"`.
* Expansion resolves the name as written through aliases (`elim_xp`, the
  declaration-site oracle): `module M := N` gives `M.elim = N.elim`.  A name
  that reaches no entry fails with `xe_ind`: `"Test.M is not an inductive
  type"`.  The name is a privacy reference (`qname_refs`), as `X.c` is.
* The checker compares the recorded name with the scrutinee's inferred type
  (`elim_infer`, `qname_eq_dec`).  Room for stage M: the member index can
  be added beside `p`.

## The recursor (item 4b)

The declaration also generates the member `rec` of its module
(`ind_gens`, last), in the module's frame `Γ0`:

```
rec : Π (u : Level). Π (P : Π Δn. Π (z : X us ns). Type⟨u⟩).
      Π (b_c : Π (elim_bctx … P …). elim_bty … P …) … .
      Π Δn. Π (z : X us ns). P ns z
rec := λ u P b_c … . λ Δn z. a_elim p (S nn) P' [(c, n_c, b_c $ its n_c vars)] z
```

(`rec_ty`, `rec_fn`, `rec_tele`, `rec_btys`, `rec_motive`, `rec_brs`,
`System/Command.v`): each branch argument has exactly the type the
eliminator gives the branch at the motive `P`.  It is checked by `gens_run`
like the constructors, when the declaration runs, and it always checks:
`ind_gens_run` (`System/IndRec.v`) shows that the generated commands run
for every well-formed filed declaration, and `rc_ind_runs` that such a
declaration command runs.  The surface reads `X.rec`
(`rec` is a keyword: `atomic_obj . REC` in the parser; `Doc.ml` pairs the
token).  Not done: `open X use (rec)` (the items are names, not the
keyword).

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

## The natural numbers as a builtin (`builtin natural ≔ X`)

```
inductive Num : Type@0 where
| Z
| S (n : Num)
end

builtin natural ≔ Num

eval Num.elim 2 return x . Num | Z ⇒ 1 | S p, r ⇒ Num.S r end   (* 3 : Num *)
```

* A numeral is a core literal, `a_nlit n` (`Syntax.v`), not a term of the
  typing judgment: expansion (`exp_xp`, `Imports.v`) replaces it by the
  chain `nat_chain p z s n` of the bound type's constructors, or by the
  builtin `ℕ`'s while no binding is visible (until `ℕ` is removed), and
  fails with `xe_nat` where the visible bindings disagree.  The elaborator
  maps a numeral to the literal and does nothing else.
* What a numeral stands for is the oracle field `xo_nb`, specified as
  `nat_binding Θ Ξ` (`Core/Syntactic/Builtin.v`): the bindings of the filed
  units (`gds_natbinds`) and of the unit being run, the bottom frame
  (`gs_natbinds`), classified as none, one with its constructors, or many.
  It depends on the filed units only up to `gds_equiv`
  (`gds_equiv_nat_binding`, `Extraction/IndDecl.v`).
* The command `cc_builtin k p` (`p` resolved as an eliminator's name is)
  runs by `rc_builtin`: `k` is `natural`, the stack is the frame of a
  unit without parameters, no binding is visible, `p`'s declaration has
  `nat_shape` (no parameter, a constructor without arguments and one with
  the single argument `ca_rec (pt_self 0 nil)`, in either order), and the
  binding is filed as the transparent definition `#natural : ind_ty D ≔
  a_ind p` of the unit, with the premises of `rc_def`.  So a binding is
  visible exactly where its unit is imported, directly or not.
* The printer folds a chain of the bound constructors ending in the
  nullary one into a numeral; it reads the binding off the eval's state
  (`nat_binding ev_deps ev_stack`).  The type prints by its name.
* Errors: "the natural numbers are bound already", "X is not shaped as
  the natural numbers: …", "builtin is allowed only at the top of a unit
  without parameters", "there is no builtin k", "builtin is not allowed in
  a local module" (elaborator), "the numeral n has no meaning here: the
  visible bindings of the natural numbers disagree".

## Deviations from the report

1. **No separate positivity check**: the shapes of `carg` (the type at its
   parameters, or a function into such a shape over domains free of the
   type) admit only strictly positive occurrences, by construction.
2. **Non-uniform parameters are typed at the inductive's sort** (option 1
   chosen by the coordinator), the uniform ones are free.
3. `wf_con` has three extra premises, all derivable from the declaration
   and read off by the models: the context of the arguments, the closed
   type of the constructor, and, for each recursive argument and each
   prefix of its shape's domains, the rest of its type over them
   (`shape_rest_wf'`; `wf_con_of_lookup` states the rule without them).
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
   (`"ill-formed inductive declaration x"`), not the failing premise, except
   for a non-uniform parameter outside the sort ("the type of the
   non-uniform parameter 1 of L, Type@1, is not in the sort of L,
   Type@0"); the
   classification has its own messages (non-positive occurrence, the type
   in a domain, the type nested inside another inductive type, dependency on a recursive argument, uniform parameters
   not as declared, wrong arity).
