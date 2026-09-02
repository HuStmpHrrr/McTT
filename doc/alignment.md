# The mechanization against the paper and the technical report

Where `theories/` diverges from the two write-ups of the meta-level-substitution
development, why, and what the mechanization settles about the questions those
write-ups leave open.

Unlike the rest of the tree, this document *does* cite the write-ups by number
(`Def 6.30`, `§7.1`, `Fig. 4`). That is its subject matter: a comparison that
cannot name what it compares is not checkable. Numbered references were
deliberately removed from the `.v` comments and the other markdown; do not
"clean" them out of here.

Throughout, **paper** is `paper.pdf` (27pp, the ICFP-style submission) and
**report** is `main.pdf` (142pp, the technical report). Line counts are code
lines — comments and blank lines stripped — and "pre-port" means commit
`9967255`, the last explicit-substitution tree.

---

## 1. What lines up

Worth stating first, so the divergences below read as the exceptions they are.

- **Syntax and substitution.** One expression sort, no substitution
  constructor, `wk := nat -> nat`, `sub := nat -> exp`, `q(φ)` and `q(σ)`
  exactly as in report Def 2.3 / §2.3, diagrammatic composition on both tiers
  (`(φ ⊙ ψ)(x) = ψ(φ x)`), and `ι : wk -> sub`. Every law of report §2.2–2.3 is
  a theorem in `Core/Syntactic/Substitution.v`.
- **Domain and evaluation.** Report Def 5.1's domain, environments as
  `nat -> domain`, `eval_wk φ ρ = fun x => ρ (φ x)` (report §5.7 verbatim), and
  `eval_sub σ ρ ρσ := forall x, eval_exp (σ x) ρ (ρσ x)` — the pointwise
  definition of report §5.7, as a `Definition` rather than a fourth clause of
  the evaluation induction. The three equations report §5.7 says *fail*
  (`⟦σ⟨φ⟩⟧`, `⟦M[σ]⟧`, `⟦σ ⨟ τ⟧`) fail here for the reason it gives, and are
  recorded as such in `Semantic/Evaluation/Definitions.v`.
- **The four-value pattern.** Report Def 6.30/6.31 are `rel_sub` and `rel_exp`
  in `Completeness/LogicalRelation/Definitions.v`, with the same four values in
  the same order, and the same reading (commutation / relatedness /
  commutation). Paper Lemma 2.5 (Pairwise) and Lemma 2.6 (Merge) are
  `rel_chain_pairwise` and `rel_chain_merge` in `Semantic/PER/Chain.v`.
- **Semantic subtyping.** Report Def 6.32 is `subtyp_under_ctx`, including its
  asymmetry: two one-sided commutations in `per_univ i` plus `Sub a <: a' at i`
  between the inner two values, not a chain.
- **Semantic context well-formedness.** Report Def 6.33 / paper Def 5.7 is the
  inductive `sem_ctx`, carrying both the context-PER witness and
  `Γ ⊨ A ≈ A : Type@i` in the extension rule — including the third premise the
  paper flags as having no counterpart in the explicit-substitution McTT.
- **Kripke gluing.** Report Def 7.4's `U*_i ↘ P ↘ El`, the concrete predicates
  of §7.3, context gluing (§7.4), realizability (Thm 7.32) and the shape of
  `Γ ⊩ t : T` all carry over.
- **Both fundamental theorems have the arity the documents give them**: four
  parts for completeness (report Thm 6.73), two for soundness (Thm 7.47), with
  no substitution conjunct in either.

---

## 2. Misalignments with the paper

### 2.1 Object-language rules

These are inherited from the pre-port McTT rather than introduced by the port,
and `AGENT/substitution-port.md` lists them as deviations; they are repeated
here because they are misalignments with the *paper*, which is what this
document is about.

| Paper | Mechanization | Note |
| --- | --- | --- |
| `Sub-Univ` at `i ≤ j` (Fig. 4) | `wf_subtyp_univ` at `i < j` | `i = j` comes from `wf_subtyp_refl`. The gap is visible in `completeness_fundamental`, which has to discharge `Sub-Univ` by hand because the semantic lemma is stated at `≤`. |
| `Sub-Pi` checks `Γ,x:S ⊢ T ⊆ T'` | `wf_subtyp_pi` checks `Γ ▹ A' ⊢ B ⊆ B'` | Interderivable given the `A ≈ A'` premise and context conversion; `Γ ▹ A'` is the form the soundness proof consumes. |
| `elimNat` congruence with a fixed motive | `wf_exp_eq_natrec_cong` also takes `Γ ▹ ℕ ⊢ A ≈ A' : Type@i` | Strictly stronger, and it is what `Algorithmic` compares. It is also what forces the file order (see §2.4). |
| `λx.t` unannotated (report Def 2.1) | `a_fn : exp -> exp -> exp`, i.e. `λ A M` | The annotation survives into `nf_fn` and the readback, and into the η rule, whose right-hand side is `λ A (M⟨↑⟩ #0)`. Neither document's grammar has it. |
| `elimNat(x.T) z (x,y.s) t` | `a_natrec A MZ MS M` | Argument order only. |
| — | `wf_subtyp_refl`, `wf_exp_subtyp`, `wf_exp_eq_subtyp` each carry one extra typing premise | Needed to split presupposition three ways without a mutual induction; the in-file comments give the `Type@0⟨↑⟩ : Type@1` regress that motivates it. |
| — | `wf_exp_eq_typ_cong`, `_nat_cong`, `_zero_cong` | With explicit substitutions these instances came free from the `_sub` equations. |

Two further presentational differences, neither of them a real gap: the
mechanization states the `natrec` successor type as `A[Wk⨟Wk,,succ(#1)]` — a
*substitution* composition — where the report writes `T[⇑◦⇑, succ x₁/x₀]` with a
weakening composition; and η uses `M⟨↑⟩` where the paper writes `t[⇑]`. Both
agree because `ι` is faithful (`Substitution.v`), which is a theorem here and an
elision there.

### 2.2 Context equality and context refinement are not judgments

The paper's system has neither, but the pre-port McTT did, and the port removed
them: `Δ ⊢s Id : Γ` *is* refinement, and refinement in both directions is
context equality. `CtxEq.v` is deleted; `CtxSub.v` survives holding only the
inductive `ctx_sub` and its bridge to `⊢s Id`, not a system rule. So the
mechanization is *closer* to the paper here than its own predecessor was.

### 2.3 Evaluation is a relation, so the judgments quantify over witnesses

The paper writes `⟦σ⟧(ρ)` as if evaluation were a metafunction, and report
Def 6.31 binds it implicitly the same way. It is a relation here, and
`functional_eval_sub` pins its result down only up to `env_eq` — which is not
enough to substitute one witness for another, because a closure captures its
environment. So `rel_exp_under_ctx` quantifies **universally** over `ρσ` and
`ρ'σ'` together with caller-supplied `eval_sub` witnesses, and `rel_exp` takes
those two environments as parameters rather than existentials:

```coq
forall ρ ρ' ρσ ρ'σ',
  Dom ρ ≈ ρ' ∈ env_rel' ->
  ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
  exists elem_rel, rel_typ i A σ ρ ρσ A σ' ρ' ρ'σ' elem_rel /\ ...
```

Nothing is lost — the claim that `σ` evaluates at `ρ` is already part of
`Γ' ⊨s σ ≈ σ' : Γ`, which every instantiation supplies anyway — and something
is gained: a premise's values arrive in the *same* environment as the
conclusion's, so two instantiations of one judgment share values instead of
merely being pointwise equal, and `rel_chain_merge` applies. This is the single
largest structural difference between the mechanized semantic judgment and the
one on paper, and it is invisible in a presentation that treats evaluation as a
function.

Relatedly, `rel_sub_under_ctx` takes the bare `rel_wk φ env_rel' env_rel` as its
Kripke premise rather than the packaged `Γ' ⊨w φ : Γ` of report Def 6.30. The
two are equivalent in context (both context PERs are already in scope) and the
bare form avoids re-packing witnesses at every use.

### 2.4 The order of the development

The paper proves substitution equivalence (§4.6 in the report) before
presupposition. The mechanization cannot: `wf_exp_eq_natrec_cong` with a varying
motive makes the direct induction for `sub_eq_preserves_exp_eq` fail. The order
is instead typing → presupposition → the rest, and it pays for itself:
`sub_eq_preserves_exp_eq` and `sub_eq_preserves_subtyp` become **three-line
proofs with no induction at all** (`Core/Syntactic/SubEq.v`), since an
equivalence `σ ≈ σ'` is both a pair of substitutions and a relation between
them. All fifteen rule cases a direct induction works through disappear. That
is a simplification the write-ups do not describe.

### 2.5 There is no semantic substitution judgment in either fundamental theorem

Both documents state the fundamental theorems without a substitution part, and
so does the mechanization — but the mechanization also records *why it cannot
have one*: `wf_sub` constrains `σ` only at the indices `Δ` types, whereas
`eval_sub` is total, so `⋅ ⊢s (fun _ => zero zero) : ⋅` holds vacuously
while its semantic counterpart would need `zero zero` to have a value. Concrete
substitutions are handled by lemmas in `Completeness/SubstitutionCases.v` and
`Soundness/SubstitutionCases`-style helpers instead. The documents present the
omission as a design choice; here it is a necessity.

---

## 3. Misalignments with the technical report

### 3.1 Kripke weakening — the sharpest divergence

Report Def 7.1:

```
KW-Id     ⊢ Γ                              KW-Shift  Γ ⊢k φ : Δ   Γ ⊢ S : Ty_i
       ───────────────                              ─────────────────────────────
        Γ ⊢k id : Γ                                    Γ,x:S ⊢k φ◦⇑ : Δ
```

`Core/Soundness/Weakening/Definitions.v`:

```coq
Inductive wk_kripke : ctx -> ctx -> wk -> Prop :=
| kwk_id   : `( ⊢ Γ ⊆ Δ -> wk_eq φ wk_id -> Γ ⊢k φ : Δ )
| kwk_shift: `( Γ ⊢k ψ : Δ' ▹ A -> ⊢ Δ' ⊆ Δ ->
                wk_eq φ (↑ ⊙ ψ) -> Γ ⊢k φ : Δ ).
```

Three differences, in increasing order of consequence.

1. **The rules recurse on the codomain, not the domain.** The report's
   `KW-Shift` grows `Γ`; here `Γ` is a parameter and the codomain shrinks from
   `Δ' ▹ A` to `Δ`. This is forced by composition: `kripke_compose` is an
   induction on the *outer* weakening, and recursing on the domain instead
   would need a strengthening lemma the system does not have.
2. **A `wk_eq` premise on both rules.** Weakenings are functions, so the slack
   the explicit-substitution presentation got from stating rules up to `≈` has
   to be put back explicitly. It makes `wk_kripke` `Proper`, so a weakening may
   be presented in any pointwise-equal form; `kripke_shiftn` recovers the
   canonical `⇑^n`. The report's "every Kripke weakening is a finite
   composition `⇑◦···◦⇑`" is therefore true here only up to `wk_eq`.
3. **Both rules may coarsen the codomain by `⊢ Δ' ⊆ Δ`.** This is what
   makes the judgment closed under `kripke_ctxsub`, which the subtyping cases
   need. **The price is that report Lemma 7.2 is false as stated**:
   `Γ ⊢k φ : Δ` does *not* imply `Γ ⊢w φ : Δ`, because `wf_wk_lookup` demands a
   variable lookup in `Γ` at the very type `A⟨φ⟩` and refinement only gives a
   subtype of it. The escape lemma is `kripke_escape`, landing in `wf_sub` via
   `ι`:

   ```coq
   Lemma kripke_escape : forall Γ Δ φ, Γ ⊢k φ : Δ -> Γ ⊢s ^(ι φ) : Δ.
   ```

   It transports judgments just as well — `kripke_preserves_exp`,
   `_exp_eq`, `_subtyp`, `_typ`, `_nat`, and the `q`-variants are all derived
   from it — so nothing downstream needs Lemma 7.2. But a reader of the report
   would expect a lemma the mechanization cannot prove.

### 3.2 `wf_wk`, `wf_sub`, `wf_sub_eq` are records

The report presents substitution typing (§3.4) with inference rules. Here there
is no grammar of substitutions to recurse on, so each is a **record with one
field**: `wf_wk_lookup`, `wf_sub_apply`, `wf_sub_eq_apply`. The rules of §3.4
survive as lemmas (`wf_sub_id`, `wf_sub_compose`, `wf_sub_extend`, …), and
`wf_wk_q`/`wf_sub_q` need an extra premise which the primed
`wf_wk_q'`/`wf_sub_q'` then discharge; the unprimed forms are `Remove Hints`ed.
`wf_sub_of_wk` — a weakening is a substitution — has no counterpart in a system
where `⇑` is a substitution in its own right.

### 3.3 `wf_sub_eq_q` needs a premise the report does not give it

`Γ ⊢ A[σ] ≈ A[σ'] : Type@i`. The tempting shortcut —
`sub_preserves_exp_eq` on reflexivity of `Δ ⊢ A : Type@i` — yields only
`A[σ] ≈ A[σ]`. The equation really comes from `sub_eq_preserves_exp`, which is
not available at that point in the file order (§2.4), hence the premise.

### 3.4 Minimality schemes, not induction schemes

The mutual judgment block generates `Minimality` schemes (plus combined 4-way,
3-way and 2-way variants) rather than `Induction` schemes. This is invisible in
the write-ups but is what lets the three presupposition lemmas be separate
non-mutual inductions.

---

## 4. What the mechanization has that neither document describes

- **`Semantic/PER/Chain.v`** (214 code lines). The four-value pattern is
  mechanized as `rel_chain R (l : list A)` — *consecutive* relatedness over a
  list, per the standing instruction to use `list` rather than a set. Around it:
  `rel_chain_pairwise` (paper Lemma 2.5), `rel_chain_merge` (Lemma 2.6),
  `rel_chain_incl`, `rel_chain_4` with its three projections
  (`_commut_left`, `_related`, `_commut_right`), `rel_chain_4_outer`,
  `_4_of_2`, `_4_sym`, `rel_chain_mono`, `rel_chain_map`, a `Proper` instance,
  and the tactics `solve_in`, `solve_incl`, `solve_chain_PER`, `pairwise`,
  `solve_rel_chain`, `merge_rel_chain`. The generalization from four values to
  a list is what makes merge statable once instead of per-case.
- **`completeness_fundamental_typ_shift`** — a bespoke bridge for the soundness
  variable case, discussed in §5.1.
- **The `Algorithmic`, `Extraction` and `Frontend` layers**: algorithmic
  subtyping and type checking, extraction to OCaml, a Menhir parser and
  elaborator. Neither document mentions them; they are 1 746 code lines, and the
  port barely touched them (493 → 490, 1 055 → 1 030, 226 → 226).
- **Two axioms**, both inherited and both from the standard library:
  `functional_extensionality_dep` and `eq_rect_eq`. The substitution algebra
  itself is stated with pointwise equality (`wk_eq`, `sb_eq`) precisely to avoid
  needing the first.

---

## 5. Answers to the open questions

### 5.1 §6.3: does the complexity of soundness drop?

> we observe several extra invocations of completeness, absent in the
> explicit-substitution setting … We have observed two specific cases that force
> this pattern. Thus we are no longer certain whether the proof complexity of
> soundness drops. We leave the concrete verification to the future.

**Verified. Soundness gets shorter; the appeals to completeness get more
numerous; and the paper's two predicted cases account for almost all of the
increase.**

Code lines in `Core/Soundness/`: **4 202 → 3 788 (−9.9 %)**. So yes, soundness
drops — but by less than the STLC experience would suggest, and for a reason the
paper identifies exactly.

Appeals from the soundness layer to the completeness fundamental theorem,
counted as occurrences in proof scripts with comments stripped:

| Lemma appealed to | Pre-port | Now |
| --- | --- | --- |
| `completeness_fundamental_exp` | 6 | 15 |
| `completeness_fundamental_typ_shift` (new) | — | 2 |
| `completeness_fundamental_subtyp` | 2 | 2 |
| `completeness_fundamental_ctx` | 3 | 2 |
| `completeness_fundamental_ctx_eq` | 1 | — |
| **total** | **12** | **21** |

The eleven new appeals, by lemma:

| Soundness lemma | New appeals | Paper's prediction |
| --- | --- | --- |
| `glu_rel_exp_vlookup` | 2 (`_typ_shift`) | the variable rule ✓ |
| `glu_rel_exp_app_helper` | 2 | elimination rules — the paper's worked example ✓ |
| `glu_rel_exp_natrec_intro` | 2 | elimination rules ✓ |
| `per_univ_zero_instance` | 2 | the `ℕ`-eliminator's motive at `zero` ✓ |
| `per_univ_nat_step_instance` | 2 | the `ℕ`-eliminator's motive at `succ #1` ✓ |
| `glu_rel_exp_fn_helper` | 1 | not predicted |

Ten of eleven fall inside the two families the paper names. `glu_rel_exp_pi`,
`glu_rel_exp_fn_helper` and `glu_rel_exp_natrec_neut_helper` already appealed to
completeness *before* the port (2 each), so the pattern is not new to those
rules — only one extra appeal appears there.

The variable case is worth spelling out, because it is the one place where a
bespoke lemma had to be added to the completeness layer to serve soundness.
`cons_glu_sub_pred` supplies the gluing at `⟦A⟧(ρ↯)` while the goal reads
`⟦A⟨↑⟩⟧(ρ)`, and those are not equal. `completeness_fundamental_typ_shift`
produces `Dom a ≈ a' ∈ per_univ i` between them and
`glu_univ_elem_resp_per_univ` moves `P` and `El` across — exactly the
paper's argument, and needed in *both* branches of the lookup induction, not
only the base case the paper considers.

So the honest summary: soundness is ~10 % shorter, but it acquired a structural
dependency on completeness that it did not have before — a 75 % increase in
appeals, concentrated where the paper said it would be. The complexity did not
so much drop as move — §6.2 gives the mechanism behind the 10 %, and §6 as a
whole explains why the saving lands here and the bill lands on completeness.

### 5.2 §8, first question: a more localized invariance?

> the four-value relation is the primary source of growth in proof complexity.
> Can it be replaced by a more localized invariance, for instance an improved
> PER model that is aware of evaluations of substituted terms?

**Not by changing the PER model, and probably not at all — but that is not where
the cost actually is.**

Three pieces of evidence from the mechanization.

**(a) No domain-level fix exists.** The obstruction to
`⟦M[σ]⟧(ρ) = ⟦M⟧(⟦σ⟧ρ)` is not the PER but the closure: `⟦λ A M⟧(ρσ)` is
`λ ρσ M`, while `⟦(λ A M)[σ]⟧(ρ)` is `λ ρ (M[q σ])`. These are different domain
values — different captured environment *and* different captured syntax — and no
relation on `domain` that is a congruence for the existing constructors can
identify them without already being the semantic type-indexed relation. Making
`eval_exp` respect `env_eq` would not help either, and is in fact false. A "PER
model aware of evaluations of substituted terms" would have to *be* the
four-value relation, or something interderivable with it.

**(b) The invariance cannot be proved separately from typing.** A standalone
lemma "for all `M σ ρ ρσ`, if `⟦σ⟧ρ ↘ ρσ` then `⟦M[σ]⟧ρ ≈ ⟦M⟧ρσ ∈ R`" is not
provable by induction on `M`: at the `λ` case, relating the two closures means
relating their applications at arbitrary related arguments, which is exactly the
statement of the semantic judgment at a `Π` type. So the invariance has to be
carried *by* the semantic judgment, which is what the paper does. There is no
localization to extract.

**(c) But the four-value packaging is already close to minimal, and it is not
the expensive part.** Two observations:

- `subtyp_under_ctx` shows the pattern decomposes: with no symmetry available
  it is written as two one-sided commutations plus one relation, and works
  fine. The chain is a *convenience* for the symmetric case, not the content.
  The content is one commutation obligation per side, and equality has two
  sides; four is what two sides cost.
- Where the completeness growth actually went (code lines):

  | File | Pre | Now | Factor |
  | --- | --- | --- | --- |
  | `Completeness/LogicalRelation/Lemmas.v` | 38 | 520 | ×13.7 |
  | `Completeness/SubstitutionCases.v` | 257 | 640 | ×2.5 |
  | `Completeness/LogicalRelation/Definitions.v` | 51 | 113 | ×2.2 |
  | `Completeness/NatCases.v` | 734 | 909 | ×1.24 |
  | `Completeness/FunctionCases.v` | 297 | 344 | ×1.16 |
  | `Completeness/ContextCases.v` | 70 | 55 | ×0.79 |

  The per-rule cases — the part a "more localized invariance" would make
  cheaper — grew by 9 % (1 632 → 1 782 across the six case files, counting the
  deleted `TermStructureCases.v` on the pre side). The growth is in *plumbing*:
  introduction and inversion lemmas for the judgments (`rel_exp_of_*`,
  `rel_exp_of_typ_inversion_wk`, …) and the algebra of semantic
  substitutions. That is a tactic-and-lemma-API problem, not a semantics
  problem. `Chain.v` itself, the entire mechanization of the four-value
  pattern, is 222 lines. §6 takes this apart in detail.

So: the answer to the question as asked is no. The useful reformulation is that
the four-value relation should be attacked at the API level — better
`eexists_rel_exp_of_*`-style constructors and inversions, so that each case of
the fundamental theorem names its four values once — and that is what the 520
lines of `LogicalRelation/Lemmas.v` already are. Further gains are available
there, not in the relation.

### 5.3 §8, second question: several kinds of substitution

> Universe polymorphism, modalities, and global variables are all natural
> targets, and a follow-up study would investigate how the four-value relation
> behaves in these richer semantic settings.

**The mechanization contains the two-kind case already, and the news is good:
each extra kind costs one semantic judgment layer and one Kripke-style
quantification, but the chain stays four values wide.**

The development has *two* substitution tiers, not one, and not by choice:
`sb_q σ` must weaken the results of `σ`, so weakening application has to exist
before substitution application can be defined by structural recursion. That
forced tower is the multi-kind situation in miniature, and its cost is legible:

- **Syntax**: the interaction laws between the tiers (`sb_wk_q`, `sb_wk_wk`,
  `sb_wk_extend`, `exp_sub_wk`, `exp_wk_sub`, …) are a visible fraction of
  `Substitution.v`'s 550 lines. With `k` kinds ordered by which can be pushed
  under which, expect on the order of `k(k+1)/2` such families.
- **Semantics**: a separate judgment layer, `rel_wk` / `rel_wk_under_ctx`
  (report Def 6.26), sits below `rel_sub`, with its own identity/shift/
  composition lemmas.
- **The chain does not widen.** `rel_sub`'s four values are
  `⟦σ⟨φ⟩⟧(ρ)`, `⟦σ⟧(⟦φ⟧ρ)`, `⟦σ'⟧(⟦φ⟧ρ')`, `⟦σ'⟨φ⟩⟧(ρ')` — a substitution
  *and* a weakening are in play, and it is still four values, because the
  Kripke quantification absorbs the weakening tier instead of adding a link to
  the chain. This is the encouraging part: the pattern's width is set by the
  number of sides (two), not by the number of substitution kinds.

One warning the mechanization does supply: the fragile object is not the chain
but the *gluing model's* notion of weakening. `wk_kripke` had to be given a
`⊆`-coarsening and a `wk_eq` premise that the report's Def 7.1 does not have,
and lost the implication into `wf_wk` in the process (§3.1). Expect to
re-derive the Kripke sub-class for each substitution kind from what the gluing
proofs actually need, rather than to reuse a general definition.

### 5.4 §8, third question: mechanize it in Rocq and compare the cost concretely

> we plan to mechanize the MLTT development of this paper in a proof assistant
> such as Rocq, both to certify the proof and to compare its mechanization cost
> concretely against that of the explicit-substitution counterpart.

**Done. Here are the numbers.** Code lines, comments and blanks stripped, over
the 76 tracked `.v` files, `9967255` (explicit substitutions) → HEAD
(meta-level operations):

| Layer | Explicit subst. | Meta-level | Δ |
| --- | --- | --- | --- |
| `Core/Syntactic` | 3 063 | 2 803 | **−8.5 %** |
| `Core/Semantic` | 2 215 | 2 895 | **+30.7 %** |
| `Core/Completeness` | 2 243 | 3 362 | **+49.9 %** |
| `Core/Soundness` | 4 202 | 3 788 | **−9.9 %** |
| `Algorithmic` | 493 | 490 | −0.6 % |
| `Extraction` | 1 055 | 1 030 | −2.4 % |
| `Frontend` | 226 | 226 | 0 |
| other (`Base`, `LibTactics`, …) | 542 | 576 | +6.3 % |
| **total** | **14 039** | **15 170** | **+8.1 %** |

Comparison with the paper's own Agda measurement for **STLC** (§3: explicit
completeness 808 / soundness 658, meta-level 840 / 504):

| | Agda, STLC | Rocq, MLTT |
| --- | --- | --- |
| completeness | +4.0 % | **+49.9 %** |
| soundness | −23.3 % | **−9.9 %** |

The qualitative claim survives: **completeness up, soundness down**. The
magnitudes do not. In MLTT the completeness penalty is an order of magnitude
larger in relative terms than in STLC, and it swamps the soundness saving, so
the total goes *up* by 8 % rather than down. Two reasons, both structural:

1. MLTT's semantic judgment carries a **two-layer** four-value pattern — one
   chain for the type in `per_univ_elem i R`, one for the term in `R` — where
   STLC has one. The paper says as much in its Costs paragraph; the numbers put
   a size on it.
2. The `Core/Semantic` growth (+31 %, of which `PER/Lemmas.v` is
   1 048 → 1 363 and `Evaluation/Definitions.v` is 86 → 207) is entirely new
   infrastructure that STLC does not need at this scale: `Chain.v`, the
   evaluation-of-substitution API, and the PER lemmas that make chains
   composable.

The user-facing gains the paper claims are also visible, and are the reason
`Core/Syntactic` *shrank* by 8.5 % despite gaining a 550-line substitution
algebra: `CtxEq.v` (80) is gone, `CtxSub.v` shrank 116 → 85, `SubEq.v`
replaced a mutual induction with 58 lines, and — the largest single item — the
rule block of `System/Definitions.v` fell 482 → 288 (−40 %), with
`Presup.v` 225 → 113,
`SystemOpt.v` 340 → 262 and `CoreInversions.v` 175 → 117 following it down.
Together those absorb the whole of the new 550-line algebra and more.

**Certification.** All 76 files compile under Rocq 9.2.0 (`make -C theories`),
`dune runtest` passes, `dune exec mctt examples/nary.mctt` prints `6 : Nat`, and
the axiom footprint is the two inherited standard-library axioms named in §4. So
the certification half of the third question is discharged as well.

---

## 6. Why completeness grew and soundness shrank

The two headline figures of §5.4 pull in opposite directions:
`Core/Completeness` **+49.9 %**, `Core/Soundness` **−9.9 %**. Neither document
predicts this split — the paper worries only about soundness (§6.3), and the
report presents the four-value judgments as a change of definition with no
proof-engineering consequence attached. So the split is itself a misalignment,
and it is worth taking apart, because the two numbers have *different* causes
and only one of them is about type theory.

### 6.1 They are not two instances of one phenomenon

| | Lemmas | Code lines | Lines / lemma |
| --- | --- | --- | --- |
| `Core/Completeness`, explicit subst. | 87 | 2 273 | 26.1 |
| `Core/Completeness`, meta-level | 120 | 3 426 | 28.6 |
| `Core/Soundness`, explicit subst. | 143 | 4 260 | 29.8 |
| `Core/Soundness`, meta-level | 145 | 3 845 | 26.5 |

(Counting `Lemma`/`Corollary`/`Theorem` statements, and including the top-level
`Completeness.v`/`Soundness.v`, which §5.4's table books under "other".)

Completeness grew by **acquiring 33 lemmas** of roughly the previous average
size. Soundness kept its lemmas — 143 → 145, and the two sets are nearly
identical by name — and **each one got about 11 % shorter**. Two different
things happened.

### 6.2 Soundness: syntactic derivations became equations

The reason soundness was cheap to port is that **no gluing judgment changed
shape.** The gluing model was already Kripke before the port: every clause of
every predicate already quantified over a weakening. Pre-port
`Soundness/LogicalRelation/Definitions.v`, two clauses of many:

```coq
(* neut_glu_exp_pred *)
(forall Δ σ M', Δ ⊢w σ : Γ -> Rne m in length Δ ↘ M' ->
                Δ ⊢ M[σ] ≈ M' : A[σ]) -> ...
(* pi_glu_typ_pred *)
(forall Δ σ, Δ ⊢w σ : Γ -> Δ ⊢ IT[σ] ® IP) -> ...
```

The port replaced the *syntactic object* `σ` inside those quantifiers with a
function, and split `⊢w` into `⊢w`/`⊢k` (§3.1). It did not add a quantifier or
a value. So there was nothing to re-derive — only obligations to discharge more
cheaply, which is exactly what shows up in the tactic census:

| | explicit subst. | meta-level |
| --- | --- | --- |
| `… ⊢s …` obligations in proof scripts | 168 | 101 |
| `assert` | 585 | 427 |
| `mauto` | 832 | 606 |
| `autorewrite` | 25 | 0 |
| plain `rewrite` | 57 | **132** |

`mauto` and `assert` fall by 27 % in step with the line count, `⊢s` obligations
by 40 %, and plain `rewrite` more than doubles. That is one mechanism seen from
five angles: **a substitution fact that used to be a derivation to search for is
now an equation to rewrite with.** The clearest single instance is the weakening
judgment itself. Pre-port:

```coq
| wk_id : `( Γ ⊢s σ ≈ Id : Δ -> Γ ⊢w σ : Δ )
```

Now:

```coq
| kwk_id : `( ⊢ Γ ⊆ Δ -> wk_eq φ wk_id -> Γ ⊢k φ : Δ )
```

A `wf_sub_eq` derivation became a `pointwise_relation nat eq`. Records instead
of rules (§3.2) does the same thing to `⊢s σ : Δ` itself: there is no rule set
to search, only a field to project.

Two things did get more expensive, and they are the whole reason the drop is
10 % rather than STLC's 23 %:

- **`Soundness/Weakening/` went 108 → 225 lines (+108 %).** The Kripke
  weakening of §3.1 — the codomain recursion, the `⊆` coarsening, `Proper`ness
  under `wk_eq`, `kripke_compose`, `kripke_shiftn`, `kripke_escape` — is new
  work with no pre-port counterpart beyond the 17-line inductive above.
- **The appeals to completeness went 12 → 21** (§5.1).

Everything else about soundness is *unchanged in kind*. Its tactic vocabulary
survived the port intact — `Proof with` 16 → 15, `saturate_*` 34 → 41 (it grew),
`gen_presups` 9 → 9, `*clean_inversion*` 42 → 35 — and the deletion of
`Soundness/SubstitutionCases.v` (135 lines, 7 lemmas: `glu_rel_sub_id`,
`_weaken`, `_compose`, `_extend`, and three presupposition lemmas) is pure
subtraction, since the rules it validated no longer exist.

### 6.3 Completeness: the judgment moved out of range of its own tactics

Here the judgment *did* change shape. Pre-port, in full:

```coq
Definition rel_exp_under_ctx Γ A M M' :=
  exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel) i,
  forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_rel),
  exists (elem_rel : relation domain),
     rel_typ i A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
```

Two values, no substitution, no Kripke quantification — because substitution was
handled by the *syntax*: `M[σ]` was a term, so closure under substitution was
three rule cases and `rel_exp` was `Hint Constructors`-ed. The meta-level
version (§2.3) inserts three more universally quantified blocks — a context
`Γ'` with its PER, a related pair `σ ≈ σ'`, and two environments `ρσ`, `ρ'σ'`
with their `eval_sub` witnesses — and widens `rel_exp` from two values to
four. **Eight
extra binders in front of the payload.** Everything below follows from that one
fact.

**(a) The workhorse tactics stopped matching.** They were not deleted and they
are not obsolete; they simply no longer apply.

| | explicit subst. | meta-level |
| --- | --- | --- |
| `destruct_rel_by_assumption` | 94 | **0** |
| `on_all_hyp` | 113 | **0** |
| `Proof with` (mauto) | 36 | **0** |
| `mauto` | 138 | **14** |
| `invert_rel_typ_body` | 30 | 3 |
| `apply_relation_equivalence` | 34 | 2 |
| — replaced by — | | |
| `destruct` | 26 | **286** |
| `assert` | 104 | **316** |
| `functional_eval_*` | 7 | **112** |
| plain `rewrite` | 2 | 71 |
| `rel_chain_*` | 0 | 99 |

`destruct_rel_by_assumption` still sits unchanged in
`Semantic/PER/CoreTactics.v`. It matches a hypothesis of the form
`forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> _`, and there are now eight binders in
front of that. Nobody generalized it: compare
`Completeness/LogicalRelation/Tactics.v`, which went **33 → 34 lines**, the one
added line being `Ltac eexists_rel_wk := eexists_rel_sub`. So a use of a premise
that used to read `(on_all_hyp: destruct_rel_by_assumption env_relΓ)` now reads

```coq
destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
```

followed by `functional_eval_exp` steps to reconcile the values it returns with
the ones already in hand — which is why that lemma goes from 7 uses to 112.
Roughly 345 automated call sites disappeared and 1 153 lines appeared: about
3.3 lines per lost call site. That accounts for the completeness growth on its
own.

**(b) One general judgment no longer serves its consumers.** With four values
and a Kripke quantification, most callers want a *specialisation*: at `Id`, at
`q σ`, precomposed with a weakening, or with the chain collapsed onto one link.
**29 of the 120 lemmas** now carry such a shape suffix (`_simple`, `_at`, `_q`,
`_wk`, `_shift`). The smallest example is `rel_exp_of_typ_inversion_simple`,
which exists only because `per_ctx_env_cons` asks for `⟦A⟧ρ` while the judgment
delivers `⟦A[σ]⟧ρ`; at `Id` they agree, and getting there is `rewrite
exp_sub_id` plus `rel_chain_4_related`. The 99 `rel_chain_*` uses in the layer
are overwhelmingly that projection step: `rel_chain_4_related` 50,
`rel_chain_4` 44, `rel_chain_4_outer` 26, against `rel_chain_merge` 3.

**(c) `SubstitutionCases.v` changed job.** Pre-port it proved the fifteen cases
of the substitution judgment; about 173 of its 257 lines were the ten
composition and extension laws, each a dozen lines of near-automatic proof.
There is no such judgment now, so the file instead *builds* the substitution
witnesses the binding rules need — `rel_sub_under_ctx_q`, `_extend`,
`_extend_sub`, `rel_exp_under_ctx_q`, `rel_typ_of_instance` — in 640 lines and
18 lemmas. The telling detail: **not one of them is `Hint Resolve`d.** Each
takes a context PER, a universe level and two `eval_sub` witnesses, none of
which automation can guess, so each is applied by hand at each of its uses.

**(d) What the port did remove from completeness**, before any of the above:

- **248 lines of substitution-rule cases** — 173 in `SubstitutionCases.v`
  (`rel_sub_id`, `_weaken`, `_compose_cong`, `_extend_cong`,
  `_id_compose_left`/`_right`, `_compose_assoc`, `_extend_compose`,
  `_p_extend`, `_extend`) and 75 in `TermStructureCases.v`
  (`rel_exp_sub_cong`, `_sub_id`, `_sub_compose`).
- **68 lines that existed only for context equality** — `rel_exp_conv`,
  `presup_rel_exp`, `presup_rel_sub`, `rel_sub_conv`. These have no successors
  at all, for the reason in §2.2.

So the port did remove 316 lines of genuine simplification from this layer.
The net +1 153 decomposes exactly as:

| File group | Pre | Now | Δ |
| --- | --- | --- | --- |
| rule cases (`Context`/`Function`/`Nat`/`Subtyping`/`Universe`/`Variable`) | 1 438 | 1 782 | +344 |
| `TermStructureCases.v` (deleted) | 194 | — | −194 |
| `SubstitutionCases.v` (new purpose) | 257 | 640 | +383 |
| `LogicalRelation/{Definitions,Lemmas,Tactics}` | 123 | 668 | **+545** |
| `Consequences/*` + `FundamentalTheorem.v` | 231 | 272 | +41 |
| `Completeness.v` | 30 | 64 | +34 |
| **total** | **2 273** | **3 426** | **+1 153** |

Four fifths of the growth (+928 of +1 153) is in the two files that hold the
judgment API — `LogicalRelation/Lemmas.v` and `SubstitutionCases.v` — and
neither contains a case of the fundamental theorem.

**(e) The rule cases are nearly flat.** Excluding the two files whose purpose
changed, the term-rule case files went **1 438 → 1 782 (+24 %)**, or
**1 632 → 1 782 (+9 %)** if the deleted `TermStructureCases.v` is counted on the
pre side. `ContextCases.v` and `VariableCases.v` actually *shrank* (70 → 55 and
110 → 95). The four-value pattern is not what costs; the four-value pattern
without tactic support is.

### 6.4 The bill was always there — the port changed who pays it

- An explicit-substitution calculus pays the **PER model's** substitution bill
  in the *syntax*, where it is nearly free: `M[σ]` is a term, closure under
  substitution is a constructor plus a hint database, and the composition laws
  are ordinary rule cases closed by `mauto`.
- It pays the **gluing model's** bill in the *proofs*, where it is expensive:
  every predicate obligation drags a `⊢s` derivation along with it, and every
  weakening premise is a `wf_sub_eq` derivation.
- Meta-level substitution inverts both. Completeness must now *prove* what it
  used to *state* — the four-value pattern is that obligation, carried in the
  judgment — while soundness gets to *rewrite* what it used to *search for*.

The paper's Agda STLC figures have the same two signs (completeness +4.0 %,
soundness −23.3 %), so the direction is confirmed. What the MLTT mechanization
adds is that the completeness penalty is not intrinsic in the proportion
observed here: the semantics of the four-value pattern is 222 lines
(`Chain.v`); the 1 153 extra lines are the price of eight binders that the
layer's tactics were never taught about.

### 6.5 The actionable form of this

Per `AGENT/proof-conventions.md`, the fix is in the existing tactics rather than
in new proof scripts. In rough order of expected return:

1. Generalize `destruct_rel_by_assumption` and `on_all_hyp` to skip the eight
   leading binders, supplying `rel_sub_id`/`eval_sub_id` when the caller wants
   the instance at `Id`. That alone addresses the 94 + 113 lost call sites.
2. Give `SubstitutionCases.v`'s eighteen constructions `Hint Extern` entries
   keyed on the goal's substitution shape, so `q σ` and `σ ,, M` goals close
   without hand instantiation.
3. `functional_eval_rewrite_clear` (`Semantic/Evaluation/Lemmas.v:86`) already
   does the reconciliation step, and is used 12 times against 112 hand
   applications of `functional_eval_exp`. Extending it — or `simplify_evals` —
   to the four-value hypotheses is the cheapest of the three.

None of these is a change to the type theory or to the model. That is the point.
