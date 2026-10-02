# Resume notes: True and False (branch ext/true-false)

These are working notes for the agent, not documentation. Delete this file
before the final commit.

## Design so far

- **Rocq spellings.** `⊤` is `a_True`, `⋆` is `a_true`, `⊥` is `a_False`, and
  `efq M return A` is `a_exfalso A M`, at level 2 with both slots at 60. The
  motive binds the scrutinee.
  - `True`, `true` and `exfalso` cannot be Rocq notations. As keywords they
    would take over Prop `True` and bool `true`, and they break the `exfalso`
    tactic: `[ exfalso; lia ]` fails to parse.
  - The surface syntax (Parser.vy) will still use `True`/`true`/`False`/`exfalso`.
- **Constructors.**
  - Cst: `true_ty`, `true_tm`, `false_ty`, and `exfalso : obj -> string -> obj -> obj`
    (scrutinee, binder, motive). `Cst.True` is avoided because ElabExamples
    does `Import Cst`.
  - nf: `nf_True`, `nf_true`, `nf_False` (`⊤ⁿ`, `⋆ⁿ`, `⊥ⁿ`).
  - ne: `ne_exfalso A M` (`efqⁿ M return A`).
- **Rules** (System/Definitions.v, placed after the ℕ cases):
  - typing: `wf_True` and `wf_False` (`: Type@0`), `wf_true` (`⋆ : ⊤`), and
    `wf_exfalso` (`Γ ▹ ⊥ ⊢ A : Type@i`, `Γ ⊢ M : ⊥` gives `A[Id,,M]`);
  - equality: `wf_exp_eq_True_cong`, `wf_exp_eq_true_cong`, `wf_exp_eq_False_cong`,
    and `wf_exp_eq_exfalso_cong`, which lets the motive vary like natrec_cong;
  - η: `wf_exp_eq_true_eta` (`M : ⊤` gives `M ≈ ⋆ : ⊤`), placed after fn_eta;
  - SystemOpt: `wf_True'`, `wf_False'`, `wf_exp_eq_True_cong'`,
    `wf_exp_eq_False_cong'` (at any level), and `wf_exp_eq_exfalso_cong'`;
  - CoreInversions: `wf_True_inversion`, `wf_true_inversion`,
    `wf_False_inversion`, `wf_exfalso_inversion` (returns `exists i`, the motive
    typing, `M : ⊥`, and `A'[Id,,M] ⊆ A`).
- **Domain.** `d_True`, `d_true`, `d_False` (`⊤ᵈ`, `⋆ᵈ`, `⊥ᵈ`), and
  `d_exfalso ρ A m` (`efqᵈ m under ρ return A`, level 2, so write
  `⇑ a (efqᵈ …)`).
- **Evaluation.** `eval_exp_True`/`true`/`False`. `eval_exp_exfalso` is the
  only rule for `efq`: `⟦M⟧ρ ↘ ⇑ b m` and `⟦A⟧(ρ ↦ ⇑ b m) ↘ a` give
  `⇑ a (efqᵈ m under ρ return A)`. No separate relation is needed.
- **Readback.**
  - `read_nf_true`: `Rnf ⇓ ⊤ᵈ m ↘ ⋆ⁿ` for any `m`. This is the only place η
    is implemented.
  - `read_nf_False_neut`: `Rne m ↘ M` gives `Rnf ⇓ ⊥ᵈ (⇑ a m) ↘ ⇑ⁿ M`.
  - `read_ne_exfalso`: the motive is evaluated at `ρ ↦ ⇑! ⊥ᵈ s` and read with
    Rtyp at `S s`, and the scrutinee with Rne.
  - `read_typ_True` and `read_typ_False`.
- **PER (planned).** `⊤ᵈ` relates every pair of values. `⊥ᵈ` relates neutrals
  related at the bottom PER, like the ℕ neutral case.

## Done

- Commit 9a4645d (the syntax milestone): Syntax, Substitution
  (`exp_wk/sub_True/true/False` and the `sb` rewrite database), System
  Definitions, Scoping, and Structural (`wf_wk_q_False`, `wf_sub_q_False`,
  `wf_sub_False_single`, and a second branch in `lift_wk_nat`/`lift_sub_nat`).
  Also GlobalPresup (an extra `eexists; mauto 3` bullet), System/Lemmas
  (`wf_sub_eq_q_False` and a branch in `lift_sub_eq_nat`), Presup (an `efq`
  right-hand-side bullet), CoreInversions and SystemOpt. Everything up to
  Core/Syntactic builds.
- Commit bca207e (WIP semantics): Domain, Evaluation/Definitions, and
  Evaluation/Lemmas. `functional_eval` gained two things: a
  `d_neut = d_neut` injection branch, and an `assert_fails (constr_eq a b)`
  guard so that an IH is not specialized on its own premise. Readback
  definitions are done too. `make Core/Semantic/Readback.vo` passes.

## Where I was

I had just got `Core/Semantic/Readback.vo` to build. The next file in order is
Readback/Lemmas.v (functional_read), then PER.

## Broken / not started

Everything after Readback.vo is untouched. From an earlier `make -k` run, the
known failures are:

- Frontend/Elaborator.v: non-exhaustive match on `Cst.true_ty`;
- Extraction/Evaluation.v: NoConfusion;
- Algorithmic/Typing/Definitions.v: `user_exp_all`;
- Completeness/ModuleCases.v.

## Next steps, in order

1. Semantic layer: Readback/Lemmas, Evaluation/Tactics (simplify_evals),
   PER/Definitions (add ⊤ᵈ, ⊥ᵈ cases to per_univ_elem and per_bot-based ⊥), and
   PER/Lemmas, CoreTactics, Chain, Realizability, Transparency, Fixed, NbE, and
   Consequences. In Consequences, add `consistency_False` and its `_gctx` form
   for `~ ⋅ ⊢ M : ⊥`. Then commit "semantics".
2. Completeness: LogicalRelation, a new set of cases next to NatCases (maybe in
   NatCases or a new file listed in `_CoqProject`), SubtypingCases, and the
   FundamentalTheorem. Commit.
3. Soundness: the gluing for ⊤/⊥, the cases, and the FundamentalTheorem.
   Commit.
4. Algorithmic Subtyping/Typing, and Extraction Evaluation/Readback/TypeCheck/
   Subtyping. Run `make -f CoqMakefile.mk post-all`. Commit.
5. Front end: Parser.vy tokens TRUE_TY/TRUE/FALSE_TY/EXFALSO and the production
   `exfalso t return x. P`; Cst/Elaborator/ElabSpec/ElabCorrect; then
   `update_parserMessages` and `check_parserMessages`; driver/PrettyPrinter.ml;
   expect tests in driver/Test.ml; then `dune build && dune test`. Commit.
6. Check assumptions with /tmp/mctt-assump/Assumptions.v plus the new
   theorem. Delete this file.

## Pitfalls

- The shared rocq MCP serves another worktree's libraries, so its goals are
  unreliable. Verify with `make -f CoqMakefile.mk X.vo`. For goal inspection,
  compile scratch files in /tmp/tf with `rocq compile -R . Mctt` from
  `theories/`, putting `Show.` before `Abort.`
- Run `eval $(opam env --switch=rocq-9.2.0)` first. CoqMakefile.mk is generated
  with `rocq makefile -f _CoqProject -o CoqMakefile.mk`.
- Python edits: inside a non-raw string, write `/\\` for `/\`. A bare `\`
  followed by a newline silently joins the lines.
- The `register-all` and `notation-for-abbreviation` warnings in Syntax.v and
  Domain.v are pre-existing.
