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

- **Readback commutes with weakening.** This needs a level-renaming
  equivariance lemma over all five domain sorts and readback, which is more
  than the invariant.
- **Re-checking the un-weakened level algorithmically.** Completeness would
  still need the declarative typing, and it breaks `type_infer_order`.
- **Danielsson et al.'s rule, checking the codomain against the weakened
  universe.** With cumulativity it is incomplete, for example on
  `Π (x : ℕ) Type@0`.
