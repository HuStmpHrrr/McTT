# Porting McTT to meta-level substitutions

The reference is `doc/paper.pdf` ("Normalization by Evaluation with
Substitutions as Operations").

Extracting text from the PDF (no `pdftotext` on this host, but `pypdf` is
installed):

```sh
python3 - <<'EOF' > /tmp/paper.txt
from pypdf import PdfReader
r = PdfReader("doc/paper.pdf")
for i, p in enumerate(r.pages):
    print(f"\n=== PAGE {i+1} ===")
    print(p.extract_text())
EOF
```

## The change

Explicit substitutions are gone: there is no `sub` syntactic category, no
`a_sub : exp -> sub -> exp` constructor, and no mutually defined substitution
judgments. Instead

- `wk := nat -> nat` and `sub := nat -> exp` are meta-level functions,
- `exp_wk M φ` (`M⟨φ⟩`) and `exp_sub M σ` (`M[σ]`) are recursive functions,
- the substitution algebra is a set of **theorems** in
  `Core/Syntactic/Substitution.v`, most of them plain `=` rather than `≈`,
- `wf_wk` / `wf_sub` / `wf_sub_eq` are **records**, not inductive families.

Two tiers matter: `sb_q σ (x+1)` must weaken (`(σ x)⟨↑⟩`), not substitute, or
`exp_sub` is not structurally recursive. Composition is **diagrammatic**:
`wk_compose φ ψ = fun x => ψ (φ x)`, `sb_compose σ τ = fun x => (σ x)[τ]`,
written `σ ⨟ τ` (U+2A1F — *not* `∘`) and `φ ⊙ ψ`.

The syntactic layer is axiom-free; check with `Print Assumptions` after each
stage (`dependent induction` in `CoreInversions.v` is fine — verified). From the
PER model on, `Print Assumptions completeness` reports
`functional_extensionality_dep` and `eq_rect_eq`. Both are inherited, not
introduced: the first comes from the `pose proof (@relation_equivalence_pointwise
env)` in `per_ctx_env_sym`, which predates the port, and the second from
`Equations`. The axiom footprint is exactly HEAD's.

## Order of the development

The order is forced, and it is not the obvious one. Presupposition
(`presup_exp_typ`) would naturally be proved before "equivalent substitutions
preserve judgments" (`sub_eq_preserves_exp`), and can be when N-E-Cong has a
*fixed* motive. McTT's `wf_exp_eq_natrec_cong` lets the motive vary, so
presupposition needs `sub_eq_preserves_exp` first. The way out:
`sub_eq_preserves_exp` is about **typing** derivations only, so it is a plain
`induction 1` on `wf_exp` and needs no presupposition.

`wf_wk` and the weakening algebra → `wk_preserves_wf` → `wf_sub` and the
substitution algebra → `sub_preserves_wf` → context conversion → type transport →
`wf_wk_q'`/`wf_sub_q'` → cumulativity → `ctx_lookup_wf` →
**`presup_exp_typ`** → `wf_sub_eq` (`wf_sub_eq_q`, **`sub_eq_preserves_exp`**,
PER, composition) → `wf_fn_eta_expand` → `wf_conv` last → `System/Tactics.v` →
`Presup.v` (**`presup_exp_eq`**, **`presup_subtyp`**) → `SubEq.v`
(**`sub_eq_preserves_exp_eq`**, **`sub_eq_preserves_subtyp`**, plus
`exp_eq_sub_eq_head`) → `CoreInversions.v` → `SystemOpt.v`.

`wf_conv`/`wf_exp_eq_conv` come last in `Lemmas.v` on purpose: as hints they let
`eauto` change the type of any goal at will, which presupposition needs on almost
every case and which the lemmas above are deliberately kept free of.

## Deviations from the paper, and why

1. `wf_exp_eq_natrec_cong` lets the motive vary (McTT's rule) — this is what
   forces the order above.
2. Sub-Univ is `i < j`, not `i ≤ j` (McTT's rule).
3. `wf_subtyp_pi` checks both codomains in `Γ , A'`, not `Γ , A`.
4. `wf_ctx_eq` and `wf_ctx_sub` are **dropped as judgments**: `{{ Δ ⊢s Id : Γ }}`
   *is* context refinement, and refinement in both directions is context
   equality. `CtxEq.v` is deleted outright; `CtxSub.v` survives, but holding only
   the inductive `ctx_sub` and its bridge to `⊢s Id`, not a system rule.
5. `wf_wk_q`/`wf_sub_q` take an extra premise; `wf_wk_q'`/`wf_sub_q'` drop it
   again and the unprimed versions are `Remove Hints`ed.
6. Three new congruence rules `wf_exp_eq_typ_cong`, `_nat_cong`, `_zero_cong`.
   With explicit substitutions their instances came from the `_sub` equations.
7. `wf_sub_of_wk` (a weakening is a substitution) has no counterpart in a system
   where `⇑` is a substitution in its own right.
8. **`wf_sub_eq_q` needs `Γ ⊢ A[σ] ≈ A[σ'] : Type@i` as a premise.** The
   tempting shortcut is to get it from `sub_preserves_exp_eq` applied to
   reflexivity on `Δ ⊢ A : Type@i`, but that yields only `A[σ] ≈ A[σ]`. The
   equation really comes from `sub_eq_preserves_exp`, which is not yet available
   at that point in the file — hence the premise.
9. **`sub_eq_preserves_exp_eq` and `sub_eq_preserves_subtyp` need no induction at
   all** once presupposition is available. An equivalence `σ ≈ σ'` is both a pair
   of substitutions and a relation between them: transport along `σ` by
   `sub_preserves_exp_eq`, then move the right-hand side from `σ` to `σ'` by
   `sub_eq_preserves_exp` applied to its *typing* derivation, then compose. All
   fifteen rule cases a direct induction would need disappear.
   `sub_eq_preserves_subtyp` uses `wf_subtyp_refl` for the second step, since
   subtyping has no symmetry.
10. Presupposition is split three ways and none of the three is a mutual
    induction:
    `presup_exp_typ` (in `Lemmas.v`), `presup_exp_eq` and `presup_subtyp` (in
    `Presup.v`). `presup_exp_eq`'s `wf_exp_eq_subtyp` case gets `Γ ⊢ A' : Type@i`
    from a premise instead of from `presup_subtyp`; `presup_subtyp`'s
    `wf_subtyp_refl` case calls the finished `presup_exp_eq`. Both are what the
    extra arguments on those two rules are for.
11. `pi_univ_level_tac` and the `wf_exp_eq_pi_sub` rewrite hint are dropped as
    unnecessary.

## Status

**The port is complete.** All 77 files of `_CoqProject` compile, `dune runtest`
passes, and `dune exec mctt examples/nary.mctt` prints `6 : Nat`.

### Syntactic layer

| File | Note |
| --- | --- |
| `Syntax.v` | `exp` with 9 constructors; `wk`/`sub` and their operations |
| `Substitution.v` | the algebra, as equations; `simpl_sub`; rewrite dbs `sb`, `sb_index` |
| `System/Definitions.v` | the four judgments; `wf_wk`/`wf_sub`/`wf_sub_eq` records; `ctx_lookup` weakens with `⟨↑⟩` |
| `System/Lemmas.v` | everything from `wf_wk` to `wf_sub_eq` (see order above) |
| `System/Tactics.v` | `invert_wf_ctx`, `gen_core_presup(s)`, `gen_lookup_presup` |
| `Presup.v` | `presup_exp_eq`, `presup_subtyp`; `gen_presup(s)`, whose `gen_presup1` gained a `wf_sub_eq` case |
| `SubEq.v` | `sub_eq_preserves_exp_eq`, `sub_eq_preserves_subtyp`; `exp_eq_sub_eq_head`/`_single` replace the deleted `exp_eq_sub_cong_*` family |
| `CoreInversions.v` | the 9 term-former inversions |
| `CtxSub.v` | the inductive `ctx_sub`, plus `ctxsub_sub_cod` |
| `Corollaries.v` | the three survivors, plus `ctx_lookup_functional` (was `functional_ctx_lookup`) |
| `SystemOpt.v` | rewriting morphisms + the rules with redundant premises removed |

`CtxEq.v` is **deleted and stays deleted**: `{{ Δ ⊢s Id : Γ }}` *is* context
refinement, and `ctxsub_exp` / `ctxsub_exp_eq` / `ctxsub_subtyp` (all `mctt`
hints) are what transport judgments across it. Where a *symmetric* context
equality is genuinely needed the semantic one is used instead — see below.

### Semantic layer

`eval_sub` is **not** an inductive: `Evaluation/Definitions.v` has three mutual
relations (`eval_exp`, `eval_natrec`, `eval_app`) and

```coq
Definition eval_sub (σ : sub) (ρ ρσ : env) : Prop := forall x, eval_exp (σ x) ρ (ρσ x).
Arguments eval_sub : simpl never.
```

with `eval_sub_intro`/`eval_sub_index` as its intro and elim, `eval_wk φ ρ :=
fun x => ρ (φ x)`, and `eval_exp_var_eq : ρ x = m -> {{ ⟦ # x ⟧ ρ ↘ m }}` for
conversion-only goals. Consequences: readback and the PER model need no
substitution case at all, and `Extraction/Evaluation.v` needs no fourth
termination order (below).

### The four-value pattern

`Core/Semantic/PER/Chain.v` is new and is the heart of the port's completeness
proof. The set notation `{a₁, …, aₙ} ⊆ R` for consecutive relatedness is here
`rel_chain R l` on a **`list`**, not a set — the notation never needed one
(consecutive relatedness needs an *order*, and repetition is harmless), and what
makes order and repetition immaterial is that `R` is a PER. That is exactly the
content of its two lemmas:

- **`rel_chain_pairwise`** — consecutive relatedness in a PER is relatedness of
  every pair, in either direction. Hence `rel_chain_incl`: a chain may be
  reordered, reversed, thinned or padded.
- **`rel_chain_merge`** — two chains sharing a value join into one.

On top of them sit the four-value pattern proper —

```
{⟦t[σ]⟧(ρ), ⟦t⟧(⟦σ⟧(ρ)), ⟦t'⟧(⟦σ'⟧(ρ')), ⟦t'[σ']⟧(ρ')} ⊆ 𝑅_T
```

— with `rel_chain_4` and the three projections named after the obligations they
discharge (`_commut_left`, `_related`, `_commut_right`), the outer pair
`rel_chain_4_outer` that is none of the three, `rel_chain_4_of_2` for the
degenerate case where both commutations hold by *equality* (every judgment about
weakenings, and every instance at `Id`), `rel_chain_4_sym` (semantic symmetry
*is* reversal), and `rel_chain_mono` / `rel_chain_map` (the latter transports a
chain along `eval_wk φ`).

The three tactics are the API: **`pairwise`** closes `R x y` from any chain
containing both, **`solve_rel_chain`** closes a chain goal from one hypothesis,
and **`merge_rel_chain H1 H2 c`** closes one whose members are spread over two —
positionally, because none of the three arguments can be guessed (`rel_chain_merge`
leaves *both* chain premises metavariable, and the shared value `c` is not
determined by the goal).

Gotcha: every lemma taking `PER R` takes it as an instance argument that `apply`
does **not** always resolve, because the instances (`per_env_PER`,
`per_elem_PER`) are found from a hypothesis rather than from the goal. Hence
`solve_chain_PER` and the `first [ solve_in | solve_chain_PER ]` in `pairwise` —
if you write a new chain tactic, discharge the `PER` goal explicitly or it will
be silently shelved and only bite at `Qed`.

### Completeness

- `{{ ⊨ Γ }}` is now the **inductive** `sem_ctx`
  (`Completeness/LogicalRelation/Definitions.v`), with `sem_ctx_per_ctx_env` as
  the bridge to `per_ctx_env`.
- `rel_exp_under_ctx` and `subtyp_under_ctx` are stated with the substitutions
  **universally quantified**; `rel_exp_under_ctx_simple` and
  `subtyp_under_ctx_simple` are what consume that extra generality.
- `subtyp_under_ctx` drops the two `rel_typ` self-relations, so
  `rel_exp_eq_subtyp` needs an extra premise.
- `{{ Γ ⊢s σ : Δ }} → {{ Γ ⊨s σ : Δ }}` is **false**, and semantic substitutions
  **do not compose**. Every proof that wants either must go through the syntactic
  side. The extended-context PER is always the canonical one.
- Syntactic context *equality* is not re-introduced; the semantic one is.
  `Completeness/Consequences/Rules.v` provides `per_ctx_of_exp_eq :
  {{ Γ ⊢ A ≈ A' : Type@i }} -> {{ ⊨ Γ, A ≈ Γ, A' }}` (an `mctt` hint) and
  `ctxeq_nbe_eq` / `ctxeq_nbe_ty_eq` and primed variants, all taking
  `{{ ⊨ Γ ≈ Γ' }}`. **Direction matters**: `ctxeq_nbe_ty_eq'` transports *from*
  its first context *to* its second, so the `nbe_ty` source context comes first.
- `per_head_of` supplies the `per_head` premise of `per_bot_natrec_diag`;
  `per_univ_of_instance` is the destruct pattern that cooperates with
  `saturate_glu_by_per`.

### Soundness and Kripke weakening

**The gluing model's weakening is not the default weakening.** It uses a
Kripke-style notion, `{{ Γ ⊢k φ : Δ }}` = `wk_kripke Γ Δ φ`, in
`Core/Soundness/Weakening/{Definitions,Lemmas}.v` — the weakenings built from `↑`
alone, with no lifting under a binder. `q φ` is therefore *not* a Kripke
weakening, and the trio `kripke_q_escape` / `kripke_preserves_exp_q` /
`kripke_preserves_typ_q` is what covers the extended context instead. Read that
file's header comment before touching it; the three things it records are:

- The two constructors are `kwk_id` and `kwk_shift` (renamed: the old `wk_id` /
  `wk_p` clashed with `Syntax.v`'s `wk_id`), and they recurse on the
  **codomain**, so the domain is a parameter. `kripke_compose` is then an
  induction on the *outer* weakening; recursing on the domain would need a
  strengthening lemma the system does not have.
- Both rules may coarsen their codomain by `{{ ⊢ Δ' ⊆ Δ }}`, which the subtyping
  cases need. The price: `⊢k` does **not** imply `⊢w`, because `wf_wk_lookup`
  demands a lookup at exactly `A⟨φ⟩` and refinement only gives a subtype. So the
  escape lemma cannot land in `⊢w`; `kripke_escape` lands in `wf_sub` via `ι`.
- The `wk_eq` premise on each rule is what makes the judgment `Proper`, so a
  weakening may be presented in any pointwise-equal form; `kripke_shiftn`
  recovers the canonical `⇑^n`.

`glu_ctx_env_sub_monotone` is stated with `⊢k` and `sb_wk`. The Soundness layer
has **no `⊩s` judgment at all**.

The three-layer weakening bridge (syntactic `⊢w`, semantic `rel_wk`, Kripke
`⊢k`) is completed by `rel_wk_under_ctx_shift`.

Other things worth knowing before editing a gluing proof:

- `wf_sub_dom` / `wf_sub_cod` are **deliberately not** `mctt` hints. The
  canonical prelude is `assert {{ Δ ⊢s σ : Γ }} by mauto 3. saturate_sub.`, and
  `saturate_kripke_escape` must likewise be followed by `saturate_sub`.
  `simplify_subs` is what reduces `ℕ[σ]` to `ℕ`.
- `glu_univ_elem_typ_resp_ctxsub` / `..._trm_resp_ctxsub` cannot be `mctt` hints.
- `glu_univ_elem_trm_morphism_iff3` (`CoreLemmas.v`) is the *term*-position
  rewriting morphism; `..._iff1` is the *type*-position one.
- `saturate_glu_by_per` matches on `per_univ_elem ?i _ ?a ?a'`, **not**
  `per_univ` — a `per_univ` fact must be destructed one level deeper.
- `destruct` on `glu_elem_top` / `glu_elem_bot` needs **7** slots;
  `glu_typ_top` needs 3.
- Setoid-rewriting an `sb_eq` inside `cons_glu_sub_pred` fails; route through
  `wf_sub_eq_of_sb_eq`.
- `{{ Γ ⊩ A[Id,,zero] : Type@i }}` is not derivable, so the ℕ-eliminator pins
  its level with `presup_typ_glu_rel_exp` plus a `max`-level normalization.
- `eapply` cannot solve `?A[?σ] ≟ ℕ`, which is why
  `cons_glu_sub_pred_q_nat_helper` spells out `@cons_glu_sub_pred_q_helper`.
- `exp_sub_q_extend_wk` replaces `sub_decompose_q_typ`. The gluing model cannot
  evaluate `B[Id,,N]`, hence `cons_glu_sub_pred_pi_helper` /
  `exp_eq_fn_sub_wk_beta` and the `rel_typ_of_nat_step_gen` generalization
  (apply it with `exact`, not `eapply`).
- `natrec` substitution and weakening are **definitional**, and the
  `destruct_glu_rel_exp_with_sub` chain pre-`cbn`s the goal.
- The soundness fundamental theorem has only two conjuncts, via the new 2-way
  `syntactic_wf_ctx_exp_mut_ind`.

### Algorithmic, Extraction, Frontend

- `Wk∘Wk` is `Wk ⨟ Wk` everywhere; `A[Wk]` is `A⟨↑⟩`.
- `wf_subtyp_univ_weaken` is gone: `Type@i⟨↑⟩` *is* `Type@i`, so `wf_subtyp_ge`
  (`{{ ⊢ Γ }} -> i <= j -> {{ Γ ⊢ Type@i ⊆ Type@j }}`) subsumes it. The old call
  site silently no-op'd, because `repeat match goal` swallows an
  unresolved-reference error.
- `Extraction/Evaluation.v` lost `eval_sub_order` and `eval_sub_impl` entirely —
  `eval_sub` is a `Definition` over `eval_exp`, not a relation to recurse on, and
  `M[σ]` is no longer an expression, so a substituted term reaches
  `eval_exp_impl` already computed. `eval_sub_order_sound` survives as a
  standalone pointwise lemma.
- `type_infer`'s `| _ => inright _` catch-all is gone: it covered `M[σ]`, the one
  expression with no inference rule, and every constructor of `exp` is now
  inferrable.
- Several `Next Obligation`s in `Extraction/TypeCheck.v` had to be made
  deterministic. Two reasons, both worth remembering:
  `eapply sub_preserves_exp` cannot unify `?A[?σ]` with `Type@i`, so it is
  applied by hand (`exact (sub_preserves_exp _ _ _ _ _ HA' Hσ)`); and
  `assert {{ ⊢ G , ℕ }} by mauto` **shelves a `nat`** (the level argument of
  `wf_ctx_extend`) unless `{{ G ⊢ ℕ : Type@0 }}` is already in the context, which
  fails only at `Qed`, as "the proof term is not complete".

The paper lists this MLTT mechanization as future work — only STLC is
mechanized there, in Agda. Everything from the semantic layer on is new proof.

## Gotchas

Convertible is **not** syntactically equal. `rewrite` and `assert … as ->` match
syntactically; `eapply`/`apply`/`exact`/`eassumption` unify up to
fixpoint/delta reduction. So these need no rewrite at all: `#0[σ,,M]`,
`Wk ⨟ (σ,,M)`, `(ρ ↦ v) ↯`, `#(S n)[σ]`, `(Π A B)[σ]`, `(λ A M)[σ]`, `(M N)[σ]`,
`Type@i[σ]`, `ℕ[σ]`, `ℕ⟨↑⟩`, `Type@i⟨↑⟩`, `zero[σ]`, `(succ M)[σ]`, `#0⟨φ⟩`,
`^(ι wk_id)`, and `natrec` under both `[σ]` and `⟨φ⟩`.

- `exp_wk_sub : M[σ]⟨φ⟩ = M[^(sb_wk σ φ)]` **over-matches**: it also matches
  `A[σ,,M]⟨φ⟩`. Order rewrite chains most-specific-first, e.g.
  `rewrite natrec_typ_sub_wk, exp_wk_sub_q2, exp_wk_sub_q, exp_wk_sub.`
- Two similarly-named tactics, easily confused: `simpl_sub` (`Substitution.v`) is
  `autorewrite with sb in *`, `simplify_subs` (`Evaluation/Tactics.v`) is
  `cbn [exp_sub exp_wk] in *`. `rewrite`'s unification delta-unfolds `sb_q`;
  `Arguments sb_q : simpl never` is what stops the `cbn` one from doing so.
- `↑` needs `Import Wk_Notations.` — without it you get
  `Syntax Error: Lexer: Undefined token`.
- `mauto 3` cannot prove `{{ Γ, A ⊢s Wk : Γ }}`; use `eapply wf_sub_shift; mauto 3`.
- `assert … by …` applies to the **first** goal only. `eauto`/`mauto` never
  fail, so a "successful" `by mauto` may have left the wrong goal.
- `eapply glu_univ_elem_*_cumu_max_*` leaves metavariables unconstrained — pin
  them with `[| exact H |]; eassumption`.
- `invert_per_univ_elem H` *clears* `H`.
- `repeat split` can descend into `exists` goals; prefer `repeat apply conj`.
- `eapply f with (i := …)` fails on maximally-inserted implicits; use `@f …`.
- `wf_sub_eq_sym` is not an `mctt` hint. `wf_sub_id_extend_eq` is
  `Remove Hints`ed in favour of the presupposition-free `wf_sub_id_extend_eq'`.
- No whitespace between a statement's `.` and `Proof` is a syntax error.
- zsh: quote `echo "==="` and `--include='*.v'`. Prefix a `python3 - <<'EOF'`
  heredoc with `cd …/theories &&` if the shell's cwd may have drifted.

## Tooling

`make -f CoqMakefile.mk real-all`, **not** `make`. `/tmp/mb.sh` regenerates the
makefile and runs the whole thing with the deprecation warnings silenced; a
single file is

```sh
eval "$(opam env --switch=rocq-9.2.0)" && make -f CoqMakefile.mk Extraction/TypeCheck.vo
```

Do **not** run `make update_CoqProject` while files are being added and removed.

The rocq MCP server's workspace is `theories/`, so its paths are relative to
`theories/`, not the repo root. Recipes that pay off:

- `rocq_start(file, line, character)` to inspect the goal *inside* an `Equations`
  obligation — position on the previous sentence, since the cursor rounds
  forward.
- `rocq_check(from_state, body)` runs a whole sequence and returns
  `proof_tactics` when the proof closes. `rocq_step_multi` does **not** chain.
- Goal selectors (`all: [> tacA | tacB ]`) for probing several goals at once.
- **After editing a `.v` file the first `rocq_start` must pass
  `force_restart: true`**, or you get the stale Flèche cache.
- `Undo` is a forbidden command in `rocq_check`.
- A scratch `theories/Probe.v` is the way to try something needing the project
  load path.

## Shared lemmas added for reuse

Reach for these before writing `max`-juggling inline; each was added because two
or more proofs wanted it (see `proof-conventions.md`).

| Lemma | Statement |
| --- | --- |
| `lift_exp_common` | two types in one context, at a *common* level, existentially |
| `lift_exp_pi_common` | the same for `Γ ⊢ A` and `Γ , A ⊢ B` |
| `wf_pi_max` | `wf_pi` with the two levels taken as they come |
| `wf_subtyp_refl_typ` | `Γ ⊢ A : Type@i → Γ ⊢ A ⊆ A`, in one step |
| `wf_fn_eta_expand` | the right-hand side of η is well-typed at the same type |
| `wf_subtyp_refl'` etc. | in `SystemOpt.v`: every rule minus its presupposable premises |

`wf_subtyp_refl_typ` and `SystemOpt.v`'s `wf_subtyp_refl'` overlap: the latter
subsumes the former via `wf_exp_eq_refl`, but costs a level of `mauto` search
and is only available after presupposition, so both exist.
