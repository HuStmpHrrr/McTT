# The small Π at open levels

This note covers how a function type of small types gets a small universe when
the level is a term rather than a literal, as in

```
def Endo (u : Level) (A : Type@{u}) : Type@{u} := forall (a : A) -> A end
def Arr (u : Level) (v : Level) (A : Type@{u}) (B : Type@{v}) : Type@{maxl u v} := forall (a : A) -> B end
```

It describes the declarative rule, the algorithm, and the proof route. It also
explains why the obvious proof route does not work.

## The rule

`wf_pi_small` and `wf_exp_eq_pi_cong_small` (`Core/Syntactic/System/Definitions.v`)
take a level term `L` of `Γ`. The codomain is at the weakening of `L`:

```
Γ ⊢ L : Level -> Γ ⊢ A : Type⟨L⟩ -> Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ -> Γ ⊢ Π A B : Type⟨L⟩
```

- **Why the codomain sits at the weakened level.** A level that mentions the
  bound variable cannot name a universe of `Γ`. So `forall (u : Level) -> Type@{u}`
  stays in `Type@ω`.
- **Why the premise `Γ ⊢ L : Level` is there.** It is admissible by
  presupposition. But weakening and substitution (`Structural.v`) come before
  presupposition, and they need it to move `A` into a large universe and
  extend the context with it.
- **Why the congruence rule is generalized too.** The gluing readback clause
  asks for `Π A B ≈ W : Type⟨L⟩` at open `L`.
- **The literal forms.** `wf_pi_small_lit` and `wf_exp_eq_pi_cong_small_lit`
  are derived, since `𝕃@n[↑]ʷ` is `𝕃@n`.

## The algorithm

`ati_pi` infers the normal form of `unf_pi_tm u v` (`Core/Syntactic/Fresh.v`),
where `u` and `v` are the universes of the parts:

- **Both parts small, codomain level fresh at index 0.** The result is
  `Type⟨maxl LA LB'⟩`, where `LB'` is the codomain level un-weakened by
  `la_unwk 0`.
- **Otherwise.** The result is the large join, `unf_tm (unf_max u v)`, as
  before.

The result is the *normal form* of that term, a side condition
`nbe_ty_f Γ (unf_pi_tm u v) W`, in the style of `ati_suniv`:

- **Why not compute the canonical join directly?** Un-weakening a canonical
  level breaks the order of its atoms. The canonical join would then be a
  normal form only if NbE commuted with un-weakening, and that is not proved.
  With the normalisation, normality is `idempotent_nbe_ty`.
- **What changes in practice.** For two literal levels the output is the same
  as before.

## Proof route: semantic strengthening, by induction on normal forms

**Soundness** of the small case needs the un-weakened level to be a level of
`Γ`. That is `level_nf_strengthen` (`Algorithmic/Strengthening.v`):

```
⊢ Γ ▹ A -> Γ ▹ A ⊢ L[↑]ʷ : Level -> Γ ⊢ L : Level        (L a normal form)
```

The atoms of `L` are arbitrary neutrals, for example `g (fun x -> x)`. So this
needs strengthening of every normal form (`nf_strengthen`), by mutual induction
on `nf`/`ne`/`lvl_atoms`. Each case does three things:

- It inverts the long typing of its head (`CoreInversions`).
- It strengthens the parts by the induction hypotheses.
- It moves every remaining subtyping and equation through the PER model:
  - `exp_eq_strengthen` for equations;
  - `subtyp_strengthen`, the semantic subtyping read back by `per_subtyp_read`, for subtypings;
  - `typ_pi_shape_strengthen` and `typ_univ_shape_strengthen` for the shape of a type.

A global is a closed member, typed in every context (`chain_mem_any_ctx`).

**Why not induct on the derivation.** A long derivation may pass through
terms that mention the dropped variable, and those cannot be strengthened.
Here is an example:

- `Γ ▹ A ⊢ L[↑]ʷ : Level` may be derived by subsumption from
  `L[↑]ʷ : (λ (x : A). Level) #0`.
- The type `(λ (x : A). Level) #0` mentions `#0`, but it is equal to `Level`.
- So no derivation in `Γ` has the same shape.

The induction on normal-form syntax never looks at the detours.

**Completeness** of the small case needs the codomain's universe level to be
fresh. NbE invents no variables: `nbe_wk_fresh` and `nbe_ty_wk_fresh` in
`Core/Semantic/Avoid.v` give `nf_fresh 0` of the normal form of a weakened
term. The proof is an invariant on values, `dav v b`:

- the value mentions no de Bruijn level `v`, and only levels below `b`;
- a closure may carry one bad environment position `K`, provided its body is
  fresh at the shifted `K`.

The invariant is needed because the initial environment of `Γ ▹ A` holds the
excluded variable itself. Evaluation preserves the invariant (`eval_av`), and
readback turns it into freshness (`read_av`).

The completeness argument for the small case (`alg_pi_small_complete`) then
runs in five steps:

1. Below the normal form of `Type⟨L[↑]ʷ⟩`, which is fresh, the codomain's
   level is fresh too (`lvl_le_la_fresh`).
2. Both parts' levels are below `L`.
3. The codomain's level is below `L` in `Γ ▹ A`.
4. That inequality strengthens to `Γ` (`exp_eq_strengthen`).
5. So the join is below `L`.

## The semantic cases

In the model, the level's value has a realiser `n` at each pair of
environments, and the case is the old one at index `us n`:

- completeness: `rel_exp_pi_cong_small_tm`;
- soundness: `glu_rel_exp_pi_small_tm`.

The codomain is at the weakened level. Its value at an extended environment
has the realiser of the level's value at the tail, through the level's
judgment along `Wk` (`suniv_real_shift`).

The inversions at `Type⟨T⟩` are:

- completeness: `rel_exp_of_suniv_tm_inversion(_simple)`;
- soundness: `glu_rel_exp_of_suniv_tm_inversion(')`.

## Rejected routes

- **Readback commutes with weakening, as the proof route.** It is now
  proved, as a second route (next section), but it cannot replace route R:
  it says nothing about a term that is not already typed in `Γ`.
- **Re-checking the un-weakened level algorithmically.** Completeness would
  still need the declarative typing, and it breaks `type_infer_order`.
- **Danielsson et al.'s rule, checking the codomain against the weakened
  universe.** With cumulativity it is incomplete, for example on
  `Π (x : ℕ) Type@0`.

## The second route: NbE commutes with weakening

A second, semantic proof of freshness, next to `Avoid.v`. It is in three
files:

| file | lines | what |
| --- | --- | --- |
| `Core/Syntactic/NfRename.v` | 243 | `nf_wk φ` (the renaming of normal forms); `ne_cmp_wk`; `lvl_canon_wk`; freshness and injectivity of `nf_wk` |
| `Core/Semantic/Rename.v` | 522 | `drn f` (a renaming of levels on values); `eval_rn`, `read_rn`, `read_shift` |
| `Core/NbEWeakening.v` | 137 | `nbe_wk`, `nbe_wk_fresh_sem`, `exp_eq_strengthen_sem` |

**The theorem.** For a term `M` of `Γ`, the normal form of `M[↑]ʷ` in
`Γ ▹ A` is the weakening of the normal form of `M` in `Γ`:

```
nbe_wk : ⊢ Γ ▹ A -> Γ ⊢ M : T -> nbe_f Γ M T W -> nbe_f (Γ ▹ A) M[↑]ʷ T[↑]ʷ (nf_wk ↑ W)
```

`nbe_ty_wk` is the same for types. The proof has three steps:

1. The fundamental theorem of the PER model, along `Γ ▹ A ⊨w ↑ : Γ`,
   relates `⟦M[↑]ʷ⟧ρ1` to `⟦M⟧ρ`. Here `ρ1` is the initial environment of
   `Γ ▹ A`, and `ρ` is its tail, the initial environment of `Γ`.
2. Related values read back equally at every length (`per_top`). So the
   normal form of `M[↑]ʷ` is the readback of `⟦M⟧ρ` at `|Γ| + 1`.
3. **Readback shift** (`read_shift`). Readback of `⟦M⟧ρ` at `|Γ| + 1` is
   `nf_wk ↑` of its readback at `|Γ|`, which is `W`.

**Readback shift.** The two readbacks cannot be compared on the same value.
Under a binder, readback at `s` applies the closure to the fresh level `s`,
and readback at `s + 1` to the fresh level `s + 1`. So `read_rn` is stated
for a renaming `f` of levels:

```
rn_ok f s s' φ -> dbd_nf s m -> Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> Rnf drn_nf f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W
```

- `rn_ok f s s' φ` says that `φ` sends the index of `x` at `s` to the index
  of `f x` at `s'`, for each level `x < s`. From `s` on, `f` is the shift by
  `s' - s`, so the fresh levels of the two readbacks correspond. It is
  preserved by `wk_q`.
- `dbd s m` says that `m` mentions only levels below `s`. It is
  `Avoid.dav v s` at every `v ≥ s`. That invariant already handles closures
  whose environment holds the new variable.
- **Evaluation is equivariant under every `f`** (`eval_rn`). It never looks
  at a level, it only carries them.
- **The canonical form of a level commutes with `φ` when `φ` preserves
  order** (`lvl_canon_wk`). The order on atoms (`ne_cmp`) is lexicographic
  on a coding where a variable is its index. Two codings are compared up to
  their first difference, and both sides are at the same binder depth there.
  So an order-preserving `φ` (and each `wk_q` of it) does not change the
  result (`nf_cmp_wk`).
- `read_shift` is the instance where `f` fixes the levels below `|Γ|` and
  moves the others up by one, and `φ = ↑`. This `f` fixes the initial
  environment of `Γ`, and so every value evaluated in it (`initial_env_rn`).

**Consequences.**

- `nbe_wk_fresh_sem` and `nbe_ty_wk_fresh_sem`: the normal form of a weakened
  term is fresh at `#0`, because `nf_wk ↑ W` is (`nf_wk_fresh`).
- `exp_eq_strengthen_sem`: if `M` and `N` are terms of `Γ` and
  `Γ ▹ A ⊢ M[↑]ʷ ≈ N[↑]ʷ : T[↑]ʷ`, then `Γ ⊢ M ≈ N : T`. Completeness gives
  one normal form of `M[↑]ʷ` and `N[↑]ʷ`. It is `nf_wk ↑` of the normal form
  of `M`, and also of that of `N`. `nf_wk ↑` is injective, so the two
  normal forms are equal, and soundness gives the equation.

**Comparison.**

| | route R (`Avoid.v`, `Strengthening.v`) | the second route |
| --- | --- | --- |
| size | `Avoid.v` 649 for freshness. `Strengthening.v` 1216 for EqStr, SubStr, shapes and `nf_strengthen`. | 902 in all |
| NbE of a weakened term | fresh at `#0` (`nbe_wk_fresh`) | equal to `nf_wk ↑ W` (`nbe_wk`), which is stronger |
| hypotheses of freshness | none: any `M`, typed or not | `⊢ Γ ▹ A` and `Γ ⊢ M : T` |
| EqStr | at any position `k`, under a telescope `Δ` | at `k = 0` only |
| strengthening of typing (`nf_strengthen`, `level_nf_strengthen`) | yes | no |

**Why the second route proves no strengthening of typing.**
`level_nf_strengthen` concludes `Γ ⊢ L : Level` from `Γ ▹ A ⊢ L[↑]ʷ : Level`.
`nbe_wk` needs `Γ ⊢ L : Level` as a hypothesis, so it cannot start. The
algorithm needs exactly that conclusion, so route R stays the one it uses.

**Why EqStr only at `k = 0`.** At a position `k > 0`, the long context is
`tele_wk Δ ↑ ++ Γ ▹ A`. The renaming `f` would have to send the short
initial environment to the image of the long one. But the entries of `Δ`
are evaluated again in the long context, and the two are related only by
the PER model. So the step would need the PER model to be closed under
renaming of levels, and that is a new lemma over the whole model.
