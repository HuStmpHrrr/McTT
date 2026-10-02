# core-let: resume notes (semantic side)

Branch `ext/core-let`, worktree `.claude/worktrees/agent-a9f164221c7d1caa7`.
Read `AGENT/core-let.md` (design) first.  The front end is on
`ext/core-let-frontend`, and the algorithmic checker and extraction are on
`ext/core-let-algo`.  Other agents own those branches, so don't edit
Frontend/, driver/ or examples/ here.

## Done (all committed, all building)

- `a85c0cf` adds the semantic definitions:
  - `eval_exp_let`;
  - `initial_env_cons_def`, with `initial_env_spec` restated for assumption slots;
  - `rel_elem`, `per_ctx_env_cons_def` (four ties: both bodies on both sides) and `per_ctx_subtyp_def` (a single generic constructor: env inclusion into `e :: Γ'`);
  - `solve_per` in LibTactics, and the `rel_elem` cases of `destruct_rel_typ`.
- `2d541b3` finishes `PER/Lemmas.v`: right_irrel, sym, trans, subtyp_to_env, env_subtyping, refl1, subtyp_trans, and `per_ctx_env_resp_env_eq`.
- `4d81e48` finishes `Semantic/Realizability.v` (`per_ctx_then_per_env_initial_env`).
- `Semantic/Transparency.v` compiles unchanged.
- Baseline assumptions at `56e979d` are in `/tmp/mctt-assump/baseline-56e979d.txt`, built in the scratch worktree `/tmp/mctt-baseline-56e979d`.
  - completeness(_gctx), soundness(_gctx, _gctx'), consistency(_gctx), canonical_form_of_{typ,nat}_gctx, prog_impl_sound and prog_impl_complete depend on `functional_extensionality_dep` and `eq_rect_eq`.
  - main_sound and main_complete depend on those two plus `Parser.loc`.
  - elaborate_core_iff is closed.
  - The `Assumptions.v` script is `/tmp/mctt-assump/Assumptions.v`. Compile it with `rocq c -R . Mctt` from `theories/`.

## Where I stopped

Completeness has not been started. Nothing is uncommitted.

- The first error is `Core/Completeness/VariableCases.v:107`, in `valid_exp_var`. `ctx_lookup` now has 3 constructors (`here`, `here_def`, and `there` over any `e`).
- These compile untouched: Completeness/LogicalRelation/{Definitions, Tactics, Lemmas}, UniverseCases, ContextCases, SubstitutionCases, Soundness/Weakening/*, and Soundness/LogicalRelation/{Definitions, CoreTactics, CoreLemmas}.

## Plan for completeness

It mostly reuses the assumption-entry machinery.

1. **PER layer** (`PER/Lemmas.v`, next to `per_env_extend`):
   - Define `def_tie A M ρ := exists m, ⟦M⟧ρ↯ ↘ m /\ Dom m ≈ ρ 0 ∈ per_head A A ρ↯ ρ↯`.
   - Define `per_env_extend_def A M R ρ ρ' := per_env_extend A A R ρ ρ' /\ def_tie A M ρ /\ def_tie A M ρ'`.
   - Prove `per_ctx_env_extend_def`, the analogue of `per_ctx_env_extend`: it takes the simple forms of A and M and gives `EF Δ ▸ A ≔ M ≈ Δ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend_def A M R`. Build it with `per_ctx_env_cons_def` and `head_rel := per_head A A`. Converting `per_head A A ρ↯ ρ↯` to `per_head A A ρ↯ ρ'↯` is `per_head_resp`.
   - Prove the inclusion lemma: `EF Γ▸A≔M R1` and `EF Γ▹A R2` imply `R1 ⊆ R2`.
2. **The tie is closed under the extended relation.** If ρ1 ≈ ρ2 ∈ per_env_extend A A R and def_tie A M ρ1, given the simple forms of A and M, then def_tie A M ρ2. So to place a whole chain of environments in the def relation it is enough to prove the tie at one environment.
3. **Restriction lemmas** (LogicalRelation/Lemmas.v). Let R1 ⊆ R2 be the relations of Γ1 and Γ2.
   - `rel_sub_under_ctx` is covariant in the codomain relation and contravariant in the domain relation.
   - `Γ2 ⊨ M ≈ M' : A` implies `Γ1 ⊨ M ≈ M' : A`.
   - With these, `here_def` and the shifts over a def entry come from the assumption versions.
4. **Generalize `rel_wk_shift`** (and `rel_wk_under_ctx_shift`, `rel_sub_shift` and `rel_exp_under_ctx_shift`) from `Γ ▹ A` to `e :: Γ`. The design approves this, and it is strictly stronger. Add `sem_ctx_cons_def` (⊨ Γ, EF, Γ ⊨ A : Type@i, Γ ⊨ M : A) to `sem_ctx`, and `rel_ctx_extend_def'`.
5. **VariableCases.**
   - Split out `valid_exp_var_here`, then handle `here_def` by restriction.
   - Prove δ (`rel_exp_var_delta`) by induction on `ctx_lookup_def`. The step is the shift. The base uses item 6 with #0 and M[↑]ʷ, plus `rel_exp_under_ctx_wk_simple` at ↑ and the tie.
6. **`rel_exp_under_ctx_of_simple`.** Validity of N and of N' at T, plus their relatedness at Id on related environments, gives `Γ ⊨ N ≈ N' : T`. The proof merges the N-chain, the Id link and the N'-chain, identifying the PERs at the inner type values.
7. **New `Completeness/LetCases.v`.**
   - `rel_sub_under_ctx_extend_sub_def`: `σ,,M[σ]` into `Δ▸A≔M`. It is `extend_sub` plus the tie at env 2, whose inner value is ⟦M⟧t2.
   - `rel_sub_under_ctx_q_def` and `per_ctx_env_of_def_sub`: `q σ` from `Γ▸A[σ]≔M[σ]`. This is `rel_sub_under_ctx_q` plus domain contravariance plus the tie: ⟦M⟧(⟦σ[↑]⟧t) ≈ ⟦M⟧⟦σ⟧t ≈ ⟦M[σ]⟧t ≈ head.
   - The instance lemma: `Γ ⊨ M ≈ M' : A` and `Γ▸A≔M ⊨ B ≈ B' : C` give `Γ ⊨ B[Id,,M] ≈ B'[Id,,M'] : C[Id,,M]`. Copy the shape of `rel_typ_of_instance` and the term half of `rel_exp_pi_beta`.
   - let_cong: the type chain comes from the instance lemma at C, then `rel_exp_implies_rel_typ`. The links are as follows.
     - The left link is B at `q σ` (refl) at `(ρ↦⟦M[σ]⟧ρ)` twice. It is bridged to `⟦B⟧(ρσ↦⟦M⟧ρσ)` by B at Id, using `rel_sub_under_ctx_q_at` for the tails.
     - The middle link is B≈B' at Id at `(ρσ↦n2, ρ'σ'↦n3')`.
     - The right link is the mirror image, from `Γ▸A'≔M' ⊨ B' : C`. That judgment comes by restriction, because the def relations of (A,M) and (A',M') are equivalent.
   - ζ is item 6 with the let and `B[Id,,M]`. The pointwise link is B's judgment at `Id,,M`, whose chain is exactly ⟦B[Id,,M]⟧ρ, ⟦B⟧(ρ↦⟦M⟧ρ), …. Recall that ⟦ℓ A≔M in B⟧ρ = ⟦B⟧(ρ↦⟦M⟧ρ) by `eval_exp_let`.
8. **ModuleCases (`kripke_fundamental`).** Add the new cases: ctx_extend_def, wf_let, let_cong, zeta and var_delta. Then fix Consequences/{Rules,Types}, where the `rigid_typ` restatements are approved, and Completeness.v.
9. Then soundness (gluing: `cons_def_glu_sub_pred`, design §6), then the commits, then the reports to "main".

## Helpers added

- `move_by_relation_equivalence` and `move_goal_by_relation_equivalence`, in PER/Lemmas.v.
- `solve_def_heads`, in PER/Lemmas.v after the Existing Instances. It closes definition-entry tie goals from the rel_typ and rel_elem premises plus tail facts in context.
- `per_ctx_env_incl_irrel`.
- `solve_per` (LibTactics). It searches for a symmetric and transitive chain of hypotheses, depth 5.

## Pitfalls

- `rocq_compile_file` routes through dune, because the worktree root has a `dune-project`, and fails to find `Mctt`. Use `make -f CoqMakefile.mk X.vo` instead. `rocq_start` and `rocq_check` work, but other agents share pet's library cache, so confirm every result with make.
- `solve_def_heads` is slow when there are many tail hypotheses, because `destruct_rel_typ` instantiates every premise at every one. Assert only the tail facts you need (`per_ctx_env_resp_env_eq` takes 14 s).
- `etransitivity; [|symmetry]; eassumption` commits to the first `eassumption`. Use `solve_per`.
