# Core module bindings: implementation plan (branch `wip/cm-restart`)

Restart from `ext/params-as-locals` at `23d792b`.  Inputs: the decision record
(`restart-decisions.md`, its §5 and §9 binding) and the frozen design
(`core-modules.md`, for syntax and typing only).  This file lists what is built,
in which order, and every place where the plan deviates from those documents.

Baseline sizes (for the final report): `Elaborator.v` 507, `ElabSpec.v` 698,
`Resolve.v` 207, `ElabCorrect.v` 1506 lines.

## 1. Syntax (`Core/Syntactic/Syntax.v`)

One mutual block, nested through `list centry` and `option exp`:

```coq
exp     ::= … (every former but the old a_let) | a_let : bnd -> exp -> exp | a_mem : modexp -> string -> exp
modexp  ::= me_path path | me_var nat | me_mem modexp string | me_app modexp exp | me_lit gunit
bnd     ::= b_def typ exp | b_mod gunit
gunit   ::= gu_mk ctx moddef
moddef  ::= md_body gmod | md_alias modexp
gmod    ::= gm_nil | gm_ext gmod string gentry | gm_check gmod bcheck
bcheck  ::= bc_import modexp (list string) | bc_eval exp (option typ)     (* check-only entries of a local body *)
gentry  ::= ge_def bool bool typ (option exp) | ge_mod gunit
centry  ::= ce_ass typ | ce_def typ exp | ce_mod gunit
sentry  ::= se_var nat | se_exp exp | se_mod modexp        (* sub := nat -> sentry *)
```

* `gentry`/`gmod`/`gunit` move from `GlobalCtx.v` into the block.  `gu_params`,
  `gu_mod` become functions; `gu_body Δ Φ` and `ge_body Δ Φ` are abbreviations
  for the body forms, so the global layer keeps its spelling.
* Notations: `ℓ A ≔ M in B` (= `a_let (b_def A M) B`, unchanged spelling),
  `ℓₘ U in B`, `H.x` for `a_mem`, `Γ ▹ₘ U`, `⌜U⌝`, `ᵐk`, `⟨q⟩`.
* Hand-written schemes: `syn_mut_ind` (all sorts) and `exp_deep_ind`.
* Weakening and substitution: structural mutual fixpoints on every sort.
  `sentry_exp (se_mod _) = a_zero`, `sentry_modexp (se_exp _) = me_path (p_abs nil nil)`;
  the defaults match the semantic projections of a wrong-sort entry, so
  evaluation commutes with substitution on the nose for every entry.
* Syntactic helpers (functions): `member_ref`, `body_ctx`, `gm_prefix_upto`,
  `gm_checks`, `member_expansion`, `modexp_spine`, `pi_view` (looks through
  `ℓ`/`ℓₘ` by substitution), `ctx_find_mod`.

## 2. Global context and resolution (`GlobalCtx.v`)

* `gc_resolve` keeps its type and meaning (definitions only, never through an
  alias), so every existing user is unchanged.
* New `gc_module Θ Ξ p : option modres` with
  `modres ::= mr_body ctx (* full telescope *) | mr_alias gunit (list string) | mr_open`:
  the module at `p`, or the first alias on `p` and the rest of the chain.
* `frame_fresh` requires `p_mems mp = nil` for the outermost frame (decision).
* `gc_sub` lemmas extended to `gc_module`.

## 3. Member types (outside the block, `Core/Syntactic/Members.v`)

`member_type Θ Ξ Γ H ch k A` / `unit_member_type Θ Ξ Γ U ch k A`, with
`k ∈ {mk_term, mk_mod}`: chain `ch` of `H` is a public definition of canonical
type `A` (`mk_term`), or a module whose *arity type* is `A = ctx_pi T ⊤`
(`mk_mod`, `ch` may be empty).  The arity type replaces `module_params` and
`params_after`: argument checking is checking against a Π-type, so exact and
partial application are accepted and surplus arguments are not.

```
mt_path_def   gc_resolve (q ⧺ ch) = ge_def b false A _          ⇒ ⟨q⟩ ∙ ch ⇒term A
mt_path_mod   gc_module (q ⧺ ch) = mr_body T                     ⇒ ⟨q⟩ ∙ ch ⇒mod ctx_pi T ⊤
mt_path_alias gc_module (q ⧺ ch1) = mr_alias U r, ⋅ ⊢ U ∙ r ++ ch2 ⇒k A ⇒ ⟨q⟩ ∙ ch ⇒k A
mt_var        Γ ∋ #j ⇒ₘ U, Γ ⊢ U ∙ ch ⇒ᵘk A                       ⇒ ᵐj ∙ ch ⇒k A
mt_lit        Γ ⊢ U ∙ ch ⇒ᵘk A                                   ⇒ ⌜U⌝ ∙ ch ⇒k A
mt_mem        H ∙ (y :: ch) ⇒k A                                 ⇒ H.y ∙ ch ⇒k A
mt_app        H ∙ ch ⇒k A, pi_view A = Some (B, C)               ⇒ (H N) ∙ ch ⇒k C[Id,,N]
umt_self      gu_mk Δ (md_body Φ) ∙ [] ⇒mod ctx_pi Δ ⊤
umt_def       prefix up to x = Φ' ⊳ x ↦ ge_def b false A (Some M) ⇒ ∙ [x] ⇒term ctx_pi (body_ctx Φ' ++ Δ) A
umt_mod       prefix up to y = Φ' ⊳ y ↦ ge_mod Uy, body_ctx Φ' ++ Δ ++ Γ ⊢ Uy ∙ ch ⇒ᵘk A
                                                                 ⇒ ∙ y :: ch ⇒k ctx_pi (body_ctx Φ' ++ Δ) A
umt_alias     Δ ++ Γ ⊢ E ∙ ch ⇒k A                               ⇒ gu_mk Δ (md_alias E) ∙ ch ⇒k ctx_pi Δ A
```

`pi_view` unfolds `ℓ`/`ℓₘ` before the next argument (decision 3.3).  The δ-reduct
is the function `member_unfold Θ Ξ Γ H x` (one lookup, never through an alias
chain).  Functionality of both relations; commutation with weakening, with
same-unit substitutions and with `gc_sub` growth.

## 4. Judgments (`System/Definitions.v`, one mutual block of 14)

New judgments, each an *equivalence*; well-formedness is the reflexive instance
(`Γ ⊢ U unit := Γ ⊢ U ≈ U`, `Γ ⊢ H mod := Γ ⊢ H ≈ H`):

* `Γ ⊢ Ψ ≈ Ψ' ext` — two extensions of `Γ`, entry by entry (assumption,
  definition, module slot).  Entries are compared in the left extension; the
  right entries are typed in the right one, so presupposition needs no context
  conversion.
* `Γ ⊢ U ≈ U'` — units, pointwise: body units compare `body_ctx Φ ++ Δ` as
  extensions, with the same names, kinds and privacy, `tele_ass Δ`, transparent
  definitions only (B = a), no `bc_eval` (rejected), and the import checks of
  `gm_checks`; alias units compare `Δ` and the bodies `Δ ++ Γ ⊢ E ≈ E'`.
* `Γ ⊢ H ≈ H'` — module expressions: path (must name a module: `mk_mod` arity),
  slot, literal congruence, `me_mem` congruence (`y` a submodule),
  `me_app` congruence (the argument is typed against the arity type
  `A ≈ Π B C`, with the premises of `wf_app`), symmetry, transitivity.  Each
  congruence also has the right side well-formed as a premise.

Rules for terms:

```
wf_ctx_extend_mod   Γ ⊢ U unit                                       ⇒ ⊢ Γ ▹ₘ U
wf_let_mod          Γ ⊢ U unit, Γ ▹ₘ U ⊢ B : C                        ⇒ Γ ⊢ ℓₘ U in B : C[Id,,ₘ⌜U⌝]
wf_mem              H has no arguments, Γ ⊢ H mod, H ∙ [x] ⇒term A, Γ ⊢ A : Type@i,
                    member_unfold H x = Some M, Γ ⊢ M : A             ⇒ Γ ⊢ H.x : A
wf_mem_app          Γ ⊢ H mod, spine H = (R, args, pre), args ≠ [],
                    Γ ⊢ apps (member_ref R (pre ++ [x])) args : A     ⇒ Γ ⊢ H.x : A
wf_exp_eq_let_mod_cong, wf_exp_eq_let_mod_zeta, wf_exp_eq_mem_cong,
wf_exp_eq_mem_delta (premises of wf_mem; H.x ≈ M : A),
wf_exp_eq_mem_app   (premises of wf_mem_app; H.x ≈ apps (…) args : A)
wf_gentry_alias     tele_ass Δ, gs_tele Ξ ⊢ Δ ≈ Δ ext, Δ ++ gs_tele Ξ ⊢ E mod
                                                                     ⇒ ⊢e ge_mod (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))
```

Weakening/substitution records gain a module field.  `wf_sub` asks for the
*same unit*: a slot `x : U` goes to `⌜U[σ]⌝` or to a slot of unit `U[σ]`.
`wf_sub_eq` has no module field.  `sub_eq_preserves_exp` goes through ζ for `ℓₘ`
and through δ for `H.x`, which is why `wf_mem` carries the reduct's typing.
Context refinement `ctx_sub_extend_mod` keeps the same unit.

## 5. Semantics (§5 of the record, as decided)

* `domain` gains `d_member : dmod -> list string -> domain`; `dmod ::=
  dm_global path (list domain) | dm_local env gunit (list domain) | dm_member dmod (list string)`;
  `env := list dentry`, `dentry ::= de_term domain | de_mod dmod`.  `ρ x` stays
  the term projection, `ρ ↦ a` extends by a term, `ρ ↦ᵐ m` by a module.
* Evaluation block: `eval_exp`, `eval_natrec`, `eval_app` (+ `d_member` case),
  `eval_modexp`, `eval_body`, `eval_selm` (submodule chain), `eval_sel` (term
  member), `eval_appm` (module argument), `eval_apps`.  `⟦⟨q⟩⟧ = dm_global q []`
  for a body module and the alias's value otherwise; selection on a saturated
  module gives the bound value (δ); on an unsaturated one `dm_member`/`d_member`.
  Nothing builds syntax.
* `initial_env (Γ ▹ₘ U) (ρ ↦ᵐ dm_local ρ U [])`.
* `per_dmod` (before `per_ctx_env`, untyped): `dm_global` same path and
  arguments related at the telescope's types; `dm_local` walks parameters
  outermost first (supplied related, missing quantified), then bodies entry by
  entry (same names and kinds; definitions: types and values related; modules:
  `per_dmod` of the nested values; aliases: `per_dmod` of the targets);
  `dm_member` componentwise.  PER lemmas.
* `per_ctx_env_cons_mod` relates `Γ ▹ₘ U` and `Γ' ▹ₘ U'` (different units):
  premise `∀ ρ ≈ ρ', per_dmod (dm_local ρ U []) (dm_local ρ' U' [])`; the
  environment relation is tail related plus each head `per_dmod`-tied to its
  own unit's value.

## 6. Completeness

* Predicates: `Γ ⊨ U ≈ U'` and `Γ ⊨ H ≈ H'` are four-value chains in
  `per_dmod`; `sem_unit_ok`/`sem_modexp_ok` carry the validity of the parts
  (extension contexts, alias bodies, arguments); `⊨ Γ ▹ₘ U` stores both.
* Key lemmas: commutation of selection and application (on the nose);
  `ctx_pi` over `body_ctx` evaluates like `eval_body`; applicative agreement of a
  literal's members with their expansions and its closure lemma (bridge);
  "related module values have related members" (from the tie, by the walk and
  determinism, and for arguments by telescope instantiation under valid
  substitutions); validity of `q σ` under a slot and of `Id,,ₘ⌜U⌝`.
* Fundamental theorem over all 14 judgments.

## 7. Soundness

No gluing of module values: `cons_mod_glu_sub_pred` is the syntactic `wf_sub`
plus the `per_dmod` tie and the glued tail.  `wf_mem` is glued through its
reduct (δ), the bridge, and "gluing respects the element PER"; `wf_mem_app`
through its application premise; `ℓₘ` through ζ.

## 8. Checker, extraction, commands

* Algorithmic rules `ati_let_mod`, `ati_mem`, `ati_mem_app`, and checkers for
  units, extensions and module expressions; `member_type`/`member_unfold`
  computed by Equations, structurally on (global-context prefix, local
  context, syntax) through a size measure, no fuel; "prefix resolution agrees
  with full resolution" via `gc_sub`.
* Commands: `cc_alias x Δ E`, `cc_import fp E spec` (every import checked by the
  core: target a module, `use` names public members or submodules).
* `Extraction/` implementations in Equations; `prog_impl_*`, `main_*` keep
  their statements.

## 9. Front end and driver

`Cst.mdef` (`md_where cmds | md_alias obj`) shared by top level and `let`;
`elab`/`elab_mod`; spec rules `sel`/`selm`/`sunit`; `elaborate_core_iff`.  The
elaborator stops resolving members (the core does it).  Driver examples and
expect tests for every module form and every rejection (§6 programs of the
record first).

## 10. Order and milestones

1. Syntax, substitution algebra, global resolution, member types (M1).
2. Judgments, scoping, structural (wk/sub), global presupposition, sub_eq,
   presupposition, inversions, ctx_sub, SystemOpt, commands (M2).
3. Domain, evaluation, readback/NbE, PER and its lemmas (M3).
4. Completeness (M4), soundness (M5).
5. Algorithmic typing, extraction, commands (M6).
6. Front end, driver, docs (M7).

Each milestone is committed when the files up to it compile with no warning.

## 11. Deviations from the documents (so far)

* Well-formedness of units, extensions and module expressions is the reflexive
  instance of their equivalence judgment (fewer judgments, the same content).
* `wf_mem` carries the canonical type's typing and the δ-reduct's typing as
  premises, and members of applied module expressions are typed through the
  application of the root's member (`wf_mem_app`).  This replaces the lemmas
  L2 (`member_type_wf`, `member_unfold_typed`) inside presupposition; the
  checker checks the reduct.
* `module_params`/`params_after`/`wf_mod_args` are replaced by the arity type
  (`mk_mod` member types) and Π-checking of arguments.
* `wf_sub` keeps the frozen design's same-unit module field; pointwise
  equivalence lives in `Γ ⊢ U ≈ U'`, `Γ ⊢ H ≈ H'`, the congruence rules and the
  PER.
* `wf_let_mod` and `wf_exp_eq_let_mod_zeta` premise that the body's type is a
  type, and `wf_mem_app`/`wf_exp_eq_mem_app` that the member's type is one.
  `sub_eq_preserves_exp` cannot use the congruence rules for these forms (unit
  equivalence under equivalent substitutions needs presupposition), so it
  reduces both sides by ζ or δ and meets them at that type.
* `wf_sub_apply_mod` also gives the well-formedness of a literal image, as
  `wf_sub_apply` gives the typing of a term image.
* `wf_sub_eq` relates term images only; equivalent substitutions extended into
  a slot by the literals of their own transported units are equivalent
  (`wf_sub_eq_extend_mod`).
* Commands: `cc_alias x Δ E` and `cc_import (option fpath) E ns` (the unit to
  load, if any; the target; the `use`d names), checked by `import_ok`.
  `rc_mod` and `ru_intro` require assumption-only parameters (`tele_ass`), as
  `wf_gmod_nil` does.
