# Inductive types (stage A/A′: parameterised, function-shaped arguments, no indices, no OTT)

What exists, where, and where it departs from stage A of the design report
for inductive types (a planning document, not kept in the repository; the
departures are listed under [Deviations](#deviations-from-the-report)).

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
  elim c return m z . ℕ
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
* `elim M return ys z . A | c xs, hs ⇒ B … end`: the core checks the
  counts, the order of the branches and the constructor names; the branch
  labels are the declaration's constructor names, unqualified.
* Declarations are members of units and of global modules (also under
  module parameters, which become outermost uniform parameters); not of
  local bodies (`"an inductive type is not allowed in a local module"`).
* There is no built-in ℕ: an inductive type is bound as the natural
  numbers, which the numerals and `ℕ` then denote (below).

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
  elim o return z . ℕ
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
  (`Inductives.v`).  The hypothesis term is `ptyp_ih`: `λ b. elim (x b) …`.
* ι: `elim (c … f …) ≈ B[…, f, …, λ b. elim (f b), …]` (`wf_iota`).
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
  (`rel_exp_under_ctx_con_of_emb`, `glu_rel_exp_con_of_emb`), and no
  inversion on a `Π` gives them.
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
`Core/Syntactic/System/Inductives/Classify.v`):

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
| `a_ind p`, `a_con p c`, `a_elim nm A Bs M`; `ind_decl`, `carg`, `ge_ind pv D Φ`, `ge_ind_alias pv Δ p Ns` | `Core/Syntactic/Syntax.v` |
| telescopes, `ind_ty`, `con_ty`, `cargs_ctx`, `elim_mctx`, `elim_bctx`, `elim_bty`, `elim_ihs` | `Core/Syntactic/Inductives/Inductives.v` |
| `wf_ind`, `wf_con`, `wf_elim`, congruences, `wf_exp_eq_elim_iota`, `wf_gentry_indty` (in the mutual block) | `Core/Syntactic/System/Definitions.v` |
| declarations are well typed (`decl_typed`), presupposition | `System/Global/Presup.v`, `System/Inductives/Typing.v`, `Syntactic/Inductives/IndCong.v`, `Syntactic/Inductives/IndConv.v` |
| values `d_ind`, `d_con`, neutral eliminator; evaluation, readback | `Core/Semantic/Domain.v`, `Evaluation*`, `Readback*` |
| PER: `ind_rel` (two-sided, each element at its own parameters, indexed by both sides' non-uniform parameters), `con_args_rel`, `rec_arg_rel`, `rec_arg_app_rel`, `adm_uparams`; canonical relations `canon_nparams_rel`, `canon_args_rel`, `canon_doms_rel`; telescopes `tele_rel`, `tele_prefix_rel`, `shape_doms_rel` | `Core/Semantic/PER/Definitions.v`, `Inductives/IndPER.v`, `Inductives/IndCanon.v`, `Inductives/IndElim.v`, `PER/Tele.v` |
| completeness | `Core/Completeness/Inductives/{Decl,Con,Elim,Iota}.v`, `IndCases.v`, `ElimCases.v`, `IotaCases.v`, `LogicalRelation/Telescope.v` |
| gluing (`glu_univ_elem_core_indty`, `ind_typ_at`, `ind_glu_elem`, `ind_glu_exp_pred`) and soundness | `Core/Soundness/LogicalRelation/*`, `Soundness/Inductives/{Con,Elim}.v`, `IndCases.v`, `ElimCases.v`, `IotaCases.v` |
| commands: `cc_ind`, `rc_ind`, `rd_uparams`, `ind_qname`, `gs_ind`, `ind_gens`, `gen_body` | `Core/Syntactic/Command.v`, `System/Command.v` |
| the members' derivation (`ind_gens_typed`) | `System/Inductives/Rec.v` |

## The entry: `ge_ind pv D Φ`

An inductive type is ONE entry of its frame, `ge_ind pv D Φ`
(`Syntax.v`): the declaration `D` and the body `Φ` of its module, whose
members are exactly the constructors and `rec`.  There is no separate
declaration entry, no `#` name, no frame of its own.  Its module is
derived, `ind_unit D Φ = gu_mk (ind_uparams D) (md_body Φ)`: its parameters
are the uniform ones (the frames' parameters outermost), and its members are
stored closed over them, as every definition is.

* `gm_submodule` reads `ge_ind` as a body module, `mr_body (ind_uparams D)
  (Some D)`; `ind_lookup Θ Ξ p` is the `Some D` of the module at `p`.
  `gm_resolve`/`gm_entry`/`gm_subbody` go into `Φ` like into a body.
* **The judgment is incremental**, as `wf_gmod_ext` is
  (`System/Definitions.v`):

  ```
  wf_gentry_ind_nil : … D ok … -> Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind pv D ⋄
  wf_gentry_ind_ext :
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ ⍮ qname_in mq y ⊢ᵉ ge_ind pv D Φ ->
    Θ ⍮ (mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv D Φ)) :: Ξ ⍮ ind_uparams D ⊢ M : A ->
    gm_fresh x Φ ->
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ ⍮ qname_in mq y
      ⊢ᵉ ge_ind pv D (Φ ⊳ x ↦ ge_def b pv' (ctx_pi (ind_uparams D) A) (Some (ctx_fn (ind_uparams D) M)))
  ```

  Each member is checked with the entry so far visible in its frame.  That
  `Φ = gen_body p D` is no premise of the judgment; `rc_ind` files
  `gen_body` with this judgment as premise.  `gc_sub` (`Members.v`) lets a
  body module grow "same `D`, longer body" (`gm_grows`); `gc_subx` is the
  growth that keeps every body.
* `rc_ind` (`System/Command.v`):
  `cls_cons_in Θ Ξ R cs -> gs_fresh x Ξ ->
   Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv p D' (gen_body p D') ->
   Θ ⍮ Ξ ⊢[ch] cc_ind x pv R ⇝ Θ ⍮ gs_add x (ge_ind pv p D' (gen_body p D')) Ξ`,
  `p = ind_qname Ξ x`, the entry's own canonical path, and
  `D' = gs_ind Ξ (rd_filed R cs)`.  `ind_gens_typed` (`Rec.v`) derives
  that premise from `ge_ind pv p D' ⋄` and `rec` not naming a constructor; the
  checker (`Extraction/Command.v`, `ind_ok`) decides only those two.

## Names (option B)

A member is typed by one rule, `wf_mem`, over what its module expression
denotes (`mdenote`, `Core/Syntactic/Members.v`): a `ge_ind` entry denotes
`ds_ind Θ' p Ns`, whose type (`ds_ty`) is the type former's at the
arguments, and whose δ-reduct (`ds_red`) is the type former `p Ns`
(`wf_exp_eq_mem_delta`).  Selecting from it reads the module part
(`ds_mod`): the inductive type's module, at its canonical path.  A module
alias of it (`module M := N`) denotes the module, not the type former, so
it is a module only:

```
inductive N : Type@0 where | z end
module M := N
eval M.z : N      (* N.z : N *)
eval M.z : M      (* Error: Test.M is a module, not a term *)
```

The checker names that case (`mod_blame`, `re_mod_term`).

## Inductive aliases

`[private] inductive L (Δ) := E` (`cc_ind_alias`, `rc_ind_alias`): `E`, a
well-formed module expression in `Δ ++ gs_tele Ξ`, denotes an inductive
type `ds_ind Θ' p Ns`, over the parameters `Θ'` it still takes (any
number: an alias of an alias is accepted as what it names).  The entry is
`ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) p Ns`: `p` the canonical path,
`Ns` (at most `ind_nu D` of them) over the alias's telescope.  The checker
(`indalias_step`) checks `Δ`, the module `E` applies, `E`, then reads its
description.

* As a term, `L` denotes `ds_ind` again: of type `ctx_pi Δ (ind_ty_at D
  Ns)`, δ-reducing to `λΔ. p Ns` (`wf_mem`, `wf_exp_eq_mem_delta`).
* As a module, `L.cons` is `(p Ns).cons`, and `L.rec` the type's
  recursor.
* `open … use (X)` declares an inductive alias where `X` is an inductive
  type or an inductive alias (`item_gen`, `ig_ind_alias`).

```
inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end
inductive LN := List Nat
inductive L (B : Type@0) := List B
eval L Nat                 (* List ℕ : Type@0 *)
eval LN.cons 1 LN.nil      (* List.cons ℕ 1 (List.nil ℕ) : LN *)
```

## The eliminator

`a_elim nm A Bs M` names no type: `wf_elim`, its congruence and ι take the
inductive type `p` and its parameters `Ps` from the scrutinee's type,
`M : apps (a_ind p) Ps`.  Evaluation reads `p` off the value (`d_con`,
`d_ind`); a stuck eliminator `d_elim … p …` keeps it for the readback, and
the neutral `ne_elim nm A Bs M` does not.  `X.elim` is no member: `elim` is
a keyword.  The printer marks a branch's induction hypotheses after a
comma where the branches name the constructors of known declarations that
agree on them (`elim_decls`, `mark_ihs`).
The doc tool (`driver/Doc.ml`) cannot link a branch's constructor name
to its declaration, since nothing in the syntax names the type: such names
are marked `bare` and left unlinked (accepted for now).

## The recursor (item 4b)

The declaration also generates the member `rec` of its module
(`ind_gens`, last), over the uniform parameters `Γ0`:

```
rec : Π (u : Level). Π (P : Π Δn. Π (z : X us ns). Type⟨u⟩).
      Π (b_c : Π (elim_bctx … P …). elim_bty … P …) … .
      Π Δn. Π (z : X us ns). P ns z
rec := λ u P b_c … . λ Δn z. a_elim (S nn) P' [(c, n_c, b_c $ its n_c vars)] z
```

(`rec_ty`, `rec_fn`, `rec_tele`, `rec_btys`, `rec_motive`, `rec_brs`,
`System/Command.v`): each branch argument has exactly the type the
eliminator gives the branch at the motive `P`.  It is a member of the
entry like the constructors (`wf_gentry_ind_ext`), and it always checks:
`ind_gens_typed` (`System/Inductives/Rec.v`) derives the whole entry from the
declaration's, and `rc_ind_runs` shows that such a declaration command
runs.  The surface reads `X.rec`; `rec` is an ordinary name, so `open X
use (rec)` declares it too.

## Algorithmic layer and checker

* `ati_ind`, `ati_con`, `ati_elim` (`Algorithmic/Typing/Definitions.v`); the
  eliminator's scrutinee infers `nf_indty p Rs`, and the motive and branches
  are checked at the parameters' normal forms `Rs`, related to the
  derivation's by `wf_elim_params_conv` (`Core/Syntactic/Inductives/IndConv.v`).
* Completeness is by induction on the derivation with an outer induction on
  `exp_lets`; an eliminator counts `+1` there, since its motive and branches
  are re-derived at `Rs` and are no longer subderivations; its head counts
  too (`modexp_lets`), whose arguments are re-checked as the type former's
  (`exp_lets_head_apps`).
* Both checkers share `Extraction/IndCheck.v`; the eliminator's recursive
  calls are passed in as closures, so the mutual fixpoints and their
  obligation numbering are unchanged.
* A declaration is decided premise by premise in `Extraction/IndDecl.v`
  (`ind_entry_dec`, the entry `ge_ind pv D ⋄`); `exp_mvc` by a boolean
  mirror (`mvcb_spec`).

## The natural numbers as a builtin (`builtin natural ≔ X`)

There is no built-in ℕ in the core: no type former, constructors,
eliminator, values or normal forms of their own.  The natural numbers are an
inductive type that a command binds; `lib/Prelude/Builtin/Nat.mctt` is the
standard one:

```
module Prelude›Builtin›Nat where
inductive Nat : Type@0 where | zero | succ (n : Nat) end
builtin natural ≔ Nat
open Nat export (zero; succ)
end
```

A bound type may name its constructors otherwise; an eliminator uses the
declared names:

```
inductive Num : Type@0 where | Z | S (n : Num) end
builtin natural ≔ Num
open Num use (Z; S)
eval elim 3 return x . Num | Z ⇒ Z | S k, r ⇒ S (S r) end   (* 6 : ℕ *)
```

* **The configuration.**  `builtins` (`Core/Syntactic/Builtin.v`) is
  `{ bt_nat : option qname }`, apart from the filed units and the stack;
  no typing judgment reads it.  Records merge field by field (`bt_merge`):
  a field bound on one side keeps its binding, one bound on both sides must
  agree, else the merge fails.  `bt_merge` has the empty record as unit and
  is commutative, associative up to failure (`bt_merge_assoc`, in the
  option monad), idempotent, and keeps well-formedness (`bt_merge_wf`).
* **Scope.**  A unit sees the bindings it makes and those of the units it
  imports, transitively, never those of the unit importing it.
  `run_cmd`/`run_cmds` (`Core/Syntactic/System/Command.v`) thread the
  record `B` of the unit being run and a map `Rb : bmap` from each filed
  unit to the record it ended with: `Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] c ⇝ Θ' ⍮ Ξ' ⍮
  B' ⍮ Rb'`.  The map is apart from `Θ` and the stack.  `run_unit ch u B Rb
  Θ U` runs from `bt_empty` and `nil` and returns the unit's record `B` and
  the map `Rb` of what it filed.  `rc_load` merges the loaded unit's record
  in and files it in the map (`bm_merge Rb ((fp, BU) :: RbU)`);
  `rc_load_filed` merges the record the map keeps (`bm_lookup Rb fp`).
  `prog_sem prg B Θ U` hides the map.
* **`rc_builtin`.**  `cc_builtin k H` with `k = natural`: `H` names, by
  `ind_target`, an inductive type `p` or an inductive alias of one with no
  parameter and no argument; `p`'s declaration has `nat_shape` (no
  parameter; one constructor without arguments and one with the single
  argument `ca_rec (pt_self 0 nil)`, in either order) and `ind_sort D =
  nat_sort` (`Type@0`); then `bt_bind_nat B p = Some B'`, the merge with
  `{bt_nat := Some p}`: bound if nothing is, kept if `p` is, rejected if
  another type is.  Allowed anywhere a
  command is, also inside a module; the elaborator still rejects it in a
  local module.
* **Literals.**  A numeral `a_nlit n` and the token `ℕ`, `a_ntok`, are
  core expressions with no typing, evaluation or readback rule.
  `rcs_cons` generates them per command from the bindings, before
  expansion (`cmd_lits_ok Θ Ξ B c c1`, `cmd_lits` over `nat_view Θ Ξ B`):
  a numeral becomes `nat_chain p z s n`, `ℕ` becomes `a_ind p`.  Unit
  parameters get theirs in `ru_intro` (`tele_lits_ok`).  Without a
  binding read at the state, a literal fails with `le_num n` / `le_tok`.
  `cmd_lits_agree`: a literal generated without a binding is the same with
  one, which is what `run_functional` needs.
* **Metatheory.**
  - `run_functional`: two runs from the same record and map end in the
    same units, stack, record and map; two runs of a unit agree when their
    chains have the same head.
  - `run_wf`: carries `canon Rb Θ` (every filed unit is what loading its
    file yields, and `Rb` has the record that run ends with, for exactly
    the filed units) and `bt_le B B'` (a record only gains bindings).
  - `run_builtins_wf`, `prog_sem_builtins_wf`: the record stays read at
    its state, `builtins_wf Θ Ξ B` (the bound type is found by
    `ind_lookup`, has `nat_shape`, is in `Type@0`), and so are the records
    of the filed units (`bm_wf Θ Rb`), through added entries, closed module
    frames (`ind_lookup_close`), filing, merging and record merges.
  - `canonical_form_of_bound_nat_prog` (`Core/Semantic/Consequences.v`):
    with `bt_nat B = Some p` at the end of a program, a closed term of
    `a_ind p` normalizes to `nat_chain p z s n`.  Below it,
    `canonical_form_of_ind_nat(_gctx)`, `…_stuck(_gctx)` and
    `…_no_axioms` are about any inductive type of `nat_shape`.
* **Examples** (`driver/Test.ml`): `module Main where import
  Prelude›Builtin›Nat import Lib›Bare end` fails, since `Lib›Bare` uses `2`
  without importing a binding; `Lib›Num` and `Lib›Arith` both reaching
  `Prelude›Builtin›Nat` is one binding; `Lib›Unary` and `Lib›Peano` together
  conflict; a binding made in a body does not reach a unit imported later
  in it, and meets that unit's own binding there.
* **Checker.**  `Extraction/Command.v`: `cstate` / `ustate` carry the
  record (`cs_bt`, `us_bt`); the map of records is part of `kmap`, which
  keeps, for each filed unit, its closure (`kfind`) and its record (`kbt`).
  The judgment's map is related by `rb_ok K ΘR RbR` (canonical, and the
  records `K` keeps); `post_*` quantify over it.  A loaded unit is checked
  from `bt_empty`; a load, fresh or shared, merges the unit's record, and
  reports a conflict as "the natural numbers are bound already, to X".
  `builtin_step` runs `rc_builtin`, the literal pass runs before
  expansion, and `prog_impl` returns the final record.  Errors: `re_lit
  le` for a literal without a binding, and `re_nat Θ Ξ nv e`, wrapping the
  error of a command or a unit parameter with the state and the view, so
  the printer folds numerals in it.
* **Printer** (`driver/PrettyPrinter.ml`): the bound type prints as `ℕ`
  (also through an inductive alias), a chain of its constructors ending in
  the nullary one as a numeral, other constructors by their declared
  names, unqualified.  An eliminator's hypotheses are named by the sort
  convention: `A1` when the motive is a type.
* **Errors**: "the natural numbers are bound already, to X", "X is not
  shaped as the natural numbers: …", "the natural numbers must be declared
  in Type@0, not X", "there is no builtin k", "builtin is not allowed in a
  local module" (elaborator), "unknown numeral n: no natural-number type is
  bound", "unknown type ℕ: no natural-number type is bound".
* **Surface.**  `ℕ` is the only token for the bound type; `Nat`, `zero`,
  `succ` and `rec` are ordinary identifiers (`X.rec` is the recursor
  member).  Tests: `main_of_body` imports `Prelude›Builtin›Nat use (Nat;
  zero; succ)`; `main_of_bare_body` does not.  The driver takes
  `--search-root` repeatedly; tests add `../lib`.

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
4. **Admissible uniform parameters** (`adm_uparams`, option K): a stuck
   eliminator's readback makes fresh variables from the uniform parameters of
   the scrutinee's type, so `ind_rel` asks each element's own uniform
   parameters to satisfy a predicate `adm` (the universe takes
   `adm_uparams` beside the type's).  `ind_rel` is symmetric in form
   (design B): each element is read at its own stored parameters; lemmas
   move elements between indices (`ind_rel_idx`) and rebase shapes and
   arguments to other bases (`rec_arg_rel_rebase`, `con_args_rel_rebase`,
   `rec_result_rel_rebase`).
5. **Gluing redesigns.** The components of the type (non-uniform parameter
   types and argument types) are glued inside the type predicate
   (`ind_glu_comps`), the sort is required `⊆` the gluing's universe, the
   recursive facts of `ind_glu_elem_con` are closed under related parameter
   values (PER-closed) and under weakening and equal instances of the
   parameters (Kripke wrappers), the earlier link between the type
   predicate and the element predicate is removed, and
   `ind_glu_exp_pred` asks `ind_glu_elem` at every equal instance of the
   parameters (eq-closed).
6. The eliminator's case along an embedding
   (`valid_exp_under_ctx_elim_of_emb` in `Completeness/Inductives/Elim.v`,
   `glu_rel_exp_elim_of_emb` in `Soundness/Inductives/Elim.v`) takes the
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
