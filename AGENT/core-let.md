# Core `let` with local definitions in contexts (design)

Branch `ext/core-let`, based on `ext/params-as-locals` (option B) plus the
elaborator patch v2 (commit `56e979d`).  This file is the Phase 1 design.
Nothing has been implemented yet.

## 0. Summary

* `exp` gets one constructor, `a_let A M B`, written `ℓ A ≔ M in B`.  `B`
  is under one binder.
* A context entry is either an assumption `x : A` or a definition
  `x : A := M`: `ctx := list centry`.
* There are five new rules: `wf_ctx_extend_def`, `wf_let`,
  `wf_exp_eq_let_cong`, `wf_exp_eq_let_zeta` (ζ) and `wf_exp_eq_var_delta`
  (δ).  They are all constructors of the existing mutual block.
* A well-typed substitution or weakening into a context with definitions
  must respect them.  `wf_sub` and `wf_wk` each gain one field.
* Evaluation of a let extends the environment: `⟦ℓ A ≔ M in B⟧ρ =
  ⟦B⟧(ρ ↦ ⟦M⟧ρ)`.  The initial environment of `Γ ▸ A ≔ M` binds the slot to
  the value of `M`.  Values, readback and normal forms are unchanged.  No
  syntax is transformed during evaluation.
* The PER model, the gluing model and `⊨ Γ` each get one constructor for a
  definition entry.  It ties the head of the environment to the value of the
  body.
* Front end: `Cst.d_def` loses its modifiers, so an abstract let cannot be
  represented.  `sel_let_abs` and `lb_let` are removed.  A `let` elaborates
  to a core `let`, and its name is an ordinary local variable (`lb_var`).

## 1. Syntax (`Core/Syntactic/Syntax.v`)

```coq
Inductive exp : Set := ...
(** Local definition: [ℓ A ≔ M in B] binds [#0] in [B] to [M] at type [A]. *)
| a_let : typ -> exp -> exp -> exp.

Inductive centry : Set :=
| ce_ass : typ -> centry          (* x : A        *)
| ce_def : typ -> exp -> centry.  (* x : A := M   *)

Definition ce_typ (e : centry) : typ := match e with ce_ass A | ce_def A _ => A end.

Abbreviation ctx := (list centry).
```

`exp_wk` and `exp_sub` treat `a_let` like `a_fn`:

```coq
| a_let A M B => a_let (exp_wk A φ) (exp_wk M φ) (exp_wk B (wk_q φ))
| a_let A M B => a_let (exp_sub A σ) (exp_sub M σ) (exp_sub B (sb_q σ))
```

The algebra in `Substitution.v` is proved by induction on `exp`, so each
lemma gets one more case and no new lemma is needed.  `nf`/`ne` are
unchanged: a normal form never contains a let.

**Notations** (`Syntax_Notations`).  All the tokens are new (`ℓ`, `≔` and
`▸` are not used anywhere in the development):

| Notation | Meaning | Level |
| --- | --- | --- |
| `ℓ A ≔ M 'in' B` | `a_let A M B` | 2, `A` at 1, `M` and `B` at 60 (right-open, like `λ`) |
| `Γ ▹ A` | `cons (ce_ass A) Γ` | 50, left (as now, over `centry`) |
| `Γ ▸ A ≔ M` | `cons (ce_def A M) Γ` | 50, left |
| `Γ ∋ #x ≔ M : A` | `ctx_lookup_def x A M Γ` | 70 |

`'let'` cannot be the keyword because Rocq's own `let x := … in` already
starts with it.  `▸` is used instead of `▹` because `Γ ▹ A ≔ M` would have
`Γ ▹ A` as a proper prefix, which is the camlp5 prefix trap in
`notations.md`.

**Telescopes.**  `gu_params`, `ge_mod` and `gs_tele` stay of type `ctx`.
`ctx_pi` and `ctx_fn` get a definition clause that generalizes a local
definition as a `let`, as a Rocq section does with `Let`:

```coq
| cons (ce_ass B) Δ' => ctx_pi Δ' (a_pi B A)       | ... => ctx_fn Δ' (a_fn B M)
| cons (ce_def B N) Δ' => ctx_pi Δ' (a_let B N A)  | ... => ctx_fn Δ' (a_let B N M)
```

The elaborator only ever builds parameter telescopes from assumptions, so
this clause is never used in practice.  It is still the cheapest way to keep
the types unchanged.  The alternative is a separate `tele := list typ`, which
would touch all 60-odd uses of `gs_tele`/`gu_params` in the global layer,
`Command.v`, the extraction and the front end.  The cost of the let clause is
one extra case each in `ctx_pi_wf`/`ctx_fn_wf` (by `wf_let` and ζ) and in
`ctx_pi_scoped`/`ctx_fn_scoped`.

## 2. Judgments (`Core/Syntactic/System/Definitions.v`)

### Lookup

```coq
Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here  : `(e :: Γ ∋ #0 : (ce_typ e)[↑]ʷ)
  | there : `(Γ ∋ #n : A -> e :: Γ ∋ #(S n) : A[↑]ʷ)

(** The body of a definition entry, weakened to the use site like its type. *)
Inductive ctx_lookup_def : nat -> typ -> exp -> ctx -> Prop :=
  | here_def  : `(Γ ▸ A ≔ M ∋ #0 ≔ M[↑]ʷ : A[↑]ʷ)
  | there_def : `(Γ ∋ #n ≔ M : A -> e :: Γ ∋ #(S n) ≔ M[↑]ʷ : A[↑]ʷ)
```

`ctx_lookup` gives the type of every entry.  So `wf_vlookup`, `wf_exp_eq_var`
and every existing lookup lemma cover definitions without change.  A single
`here` keeps one case per induction instead of two.  `ctx_lookup_def_lookup :
Γ ∋ #x ≔ M : A -> Γ ∋ #x : A` is a lemma.

`ctx_ass Γ x := exists A, nth_error Γ x = Some (ce_ass A)` says that `x` is
bound by an assumption (used in §7).

### New rules (all in the one mutual block)

```coq
(* wf_ctx *)
| wf_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M )

(* wf_exp *)
| wf_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : C[Id,,M] )

(* wf_exp_eq: congruence *)
| wf_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M] )

(* wf_exp_eq: computation *)
| wf_exp_eq_let_zeta :                                         (* ζ *)
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M] )
| wf_exp_eq_var_delta :                                        (* δ *)
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ M : A )
```

The `Γ ⊢ A : Type@i` premises have the same purpose as those of `wf_fn` and
`wf_app`: they let the presupposition and model proofs avoid recovering a
level.  `SystemOpt.v` adds the optimized forms without them (`wf_let'`,
`wf_ctx_extend_def'`, `wf_exp_eq_let_cong'`, `wf_exp_eq_let_zeta'`), as it
does for the other rules.  Subtyping gets no new rule: `ℓ A ≔ M in T ⊆ T'`
goes through ζ and `wf_subtyp_refl`.

δ has to be stated at any depth.  If it held only at `#0`, weakening could
not be proved: `wk_preserves_wf` sends `#0` of `Γ ▸ A ≔ M` to a definition
at an arbitrary depth of the target context.  This mirrors `wf_vlookup`.

The motivating example type checks.  In `Γ ▸ ℕ ≔ 3`, δ gives `#0 ≈ 3 : ℕ`.
Hence `Vec ℕ #0 ≈ Vec ℕ 3`, and `v[↑]ʷ : Vec ℕ 3` checks against `Vec ℕ #0`.

### Weakening and substitution typing

Each record gets one field.  The other fields are unchanged.

```coq
Record wf_wk Θ Ξ Γ Δ φ := { ... ;
  wf_wk_lookup_def : forall x A M, Δ ∋ #x ≔ M : A -> Γ ∋ #(φ x) ≔ M[φ]ʷ : A[φ]ʷ }.
Record wf_sub Θ Ξ Γ Δ σ := { ... ;
  wf_sub_apply_def : forall x A M, Δ ∋ #x ≔ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ σ x ≈ M[σ] : A[σ] }.
```

A renaming has to send a definition to the same definition, syntactically.
A substitution only has to send it to something judgmentally equal to the
substituted body.  `wf_sub_eq` needs no change, because both of its sides are
`wf_sub`.

### Context refinement (`CtxSub.v`)

```coq
| ctx_sub_extend_def : forall Δ Γ A A' M M' i,           (* definition ⊆ definition *)
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i -> Θ ⍮ Ξ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' -> Θ ⍮ Ξ ⍮ Δ ⊢ M' ≈ M : A ->
    Θ ⍮ Ξ ⊢ Δ ▸ A' ≔ M' ⊆ Γ ▸ A ≔ M
| ctx_sub_forget : forall Δ Γ A A' M' i,                 (* definition ⊆ assumption *)
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i -> Θ ⍮ Ξ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A -> Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⊢ Δ ▸ A' ≔ M' ⊆ Γ ▹ A
```

`ctx_sub_forget` says that knowing a definition refines knowing only the
type.  Because of it, `Γ ▸ A ≔ M ⊢k ↑ : Γ` is already derivable from
`kwk_shift` and `kwk_id`, so `wk_kripke` needs no change.  The length
equation is kept.

### The substitution story

The meta-level substitutions stay `nat -> exp`.  Nothing becomes explicit.
The new closure lemmas (`System/Lemmas.v`) are the following.  All of them
are stated over `e :: Γ` where the existing lemma is entry-agnostic.

| Lemma | Statement |
| --- | --- |
| `wf_wk_shift` (generalized) | `⊢ e :: Γ -> e :: Γ ⊢w ↑ : Γ` |
| `wf_wk_q_def` | `Γ ⊢w φ : Δ -> Δ ⊢ A : Type@i -> Δ ⊢ M : A -> Γ ▸ A[φ]ʷ ≔ M[φ]ʷ ⊢w wk_q φ : Δ ▸ A ≔ M` |
| `wf_sub_shift` (generalized) | `⊢ e :: Γ -> e :: Γ ⊢s Wk : Γ` |
| `wf_sub_extend_def` | `Γ ⊢s σ : Δ -> Δ ⊢ A : Type@i -> Δ ⊢ M : A -> Γ ⊢ N ≈ M[σ] : A[σ] -> Γ ⊢s σ,,N : Δ ▸ A ≔ M` |
| `wf_sub_id_extend_def` | `Γ ⊢ M : A -> Γ ⊢s Id,,M : Γ ▸ A ≔ M` (the instance ζ and `wf_let` use) |
| `wf_sub_q_def` | `Γ ⊢s σ : Δ -> Δ ⊢ A : Type@i -> Δ ⊢ M : A -> Γ ▸ A[σ] ≔ M[σ] ⊢s q σ : Δ ▸ A ≔ M` (`#0 ≈ M[σ][↑]ʷ` is δ at `here_def`) |
| `wf_sub_eq_q_def` | as `wf_sub_eq_q`, plus the premise `Γ ⊢ M[σ] ≈ M[σ'] : A[σ]` (the same reason as deviation 8 of `substitution-port.md`) |
| `wf_sub_compose` | its definition field is `(σ x)[τ] ≈ M[σ][τ]`, which is `sub_preserves_exp_eq` |
| `ctx_lookup_def_wf` | `⊢ Γ -> Γ ∋ #x ≔ M : A -> Γ ⊢ M : A` |

**Order of the development.**  `wk_preserves_wf` and `sub_preserves_wf` are
already one three-way induction over typing, equality and subtyping.  The
δ case consumes exactly the new field.  The `wf_let` case recurses under
`wk_q φ`/`q σ` into a definition context, and needs `wf_wk_q_def`/
`wf_sub_q_def` at the inner context.  Those use only the induction
hypotheses for `A` and `M` and weakening.  The definition field of
`wf_sub_compose` needs `sub_preserves_exp_eq`, so `wf_sub_compose` stays
after `sub_preserves_wf`, which is where it already is.
`sub_eq_preserves_exp` gets the `wf_let` case through `wf_sub_eq_q_def`.
Presupposition of `wf_exp_eq_let_cong` needs
`Γ ▸ A' ≔ M' ⊆ Γ ▸ A ≔ M` (`ctx_sub_extend_def`) to move `B'`.  It also
needs `C[Id,,M'] ≈ C[Id,,M]`, from `sub_eq_preserves_exp` at
`Id,,M' ≈ Id,,M : Γ ▸ A ≔ M`.  Both are available in `Presup.v`.
`CoreInversions.v` gets `wf_let_inversion` (`∃ i C`, the three premises and
`Γ ⊢ C[Id,,M] ⊆ T`).

The global layer gets one case per new rule in each mutual induction
(`Scoping.v`, `Structural.v`, `GlobalPresup.v` (`global_induction_all`),
`emb_preserves_wf`).  The global context is untouched: no new rule reads
`gc_resolve`.

## 3. Semantic domain, evaluation, readback, NbE

**Domain.**  There is no change: `domain`, `env := list domain`, `d_*`.

**Evaluation** (`Evaluation/Definitions.v`) gets one constructor:

```coq
| eval_exp_let :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ m ↘ r ->
     ⟦ ℓ A ≔ M in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
```

The annotation `A` is not evaluated, just as the domain of `λ` is not.  The
environment is extended with a value, and no term is substituted.  This is
the same computation as `(λ A B) $ M` without the closure.

**Readback** has no change, because values contain no let.

**Initial environment** (`NbE.v`):

```coq
| initial_env_cons :                   (* as now, at Γ ▹ A *)
  `( initial_env Θ Ξ Γ ρ -> ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     initial_env Θ Ξ (Γ ▹ A) (ρ ↦ ⇑! a (length Γ)) )
| initial_env_cons_def :
  `( initial_env Θ Ξ Γ ρ -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     initial_env Θ Ξ (Γ ▸ A ≔ M) (ρ ↦ m) )
```

A definition slot holds the value of its body.  This is δ in the semantic
domain.  `length Γ` still counts every entry, so de Bruijn levels and
`Rne … in length Γ` are unchanged.  The level of a definition slot is simply
never given to a neutral, so a normal form never mentions a defined
variable.  `nbe` and `nbe_ty` keep their definitions.

`initial_env_spec` is restated with `nth_error Γ x = Some (ce_ass A)` in
place of `Γ ∋ #x : A`.  The old statement is false at a definition slot,
whose value is not a neutral.  Its one user is `eval_var_at_initial_env`
(§7).

`Transparency.v`: `initial_env_clean` gets the definition case from
`eval_clean`.

## 4. PER model (`PER/Definitions.v`)

A helper for elements, next to `rel_typ`, reuses the `rel_mod_eval` tactics:

```coq
Definition rel_elem M ρ M' ρ' (R : relation domain) :=
  rel_mod_eval (fun R a a' => R a a') M ρ M' ρ' R.     (* ∃ m m', ⟦M⟧ρ↘m, ⟦M'⟧ρ'↘m', R m m' *)
```

Context PER, new constructor:

```coq
| per_ctx_env_cons_def :
  `{ forall tail_rel
        (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
        env_rel
        (equiv_Γ_Γ' : EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_elem M ρ M' ρ' (head_rel equiv_ρ_ρ')) ->
        (env_rel <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel),
               Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop /\
               rel_elem (#0) ρ M' ρ'↯ (head_rel equiv_ρ_drop_ρ'_drop) /\   (* ρ 0 ≈ ⟦M'⟧ρ'↯ *)
               rel_elem M ρ↯ (#0) ρ' (head_rel equiv_ρ_drop_ρ'_drop)) ->  (* ⟦M⟧ρ↯ ≈ ρ' 0 *)
        EF Γ ▸ A ≔ M ≈ Γ' ▸ A' ≔ M' ∈ per_ctx_env ↘ env_rel }
```

* The first conjunct is the clause of an assumption entry.  So a definition
  environment is in particular an assumption environment
  (`per_ctx_env_cons_head`).  That is what lets `rel_wk_shift`, the variable
  case and `per_ctx_subtyp_forget` treat both kinds of entry alike.
* The second and third conjuncts tie each head to the value of the other
  side's body.  They are swapped by symmetry, so `per_ctx_env_sym` stays a
  constructor-by-constructor proof.  Transitivity chains through the middle
  head.
* The `rel_elem M … M'` premise (the bodies are related at related tails) is
  what `per_ctx_then_per_env_initial_env` needs to relate two initial
  environments.  It is also what makes `per_ctx_env_resp_env_eq` go through:
  evaluation does not respect `env_eq`, so a head of a pointwise-equal
  environment is bridged through `M'`.
* The first conjunct is derivable from the other three.  It is kept for the
  uniformity above.

Context subtyping gets the two refinements of `ctx_sub`:
`per_ctx_subtyp_cons_def` (`Sub a <: a'` pointwise, and the bodies related at
the larger type) and `per_ctx_subtyp_forget` (definition ⊆ assumption).
`per_ctx_subtyp_to_env`, `_refl1` and `_trans` keep their statements.

## 5. Completeness (`Completeness/`)

`⊨ Γ` gets the following constructor:

```coq
| sem_ctx_cons_def : forall Γ A M i env_rel,
    ⊨ Γ ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ A ≈ A : Type@i ->
    Γ ⊨ M ≈ M : A ->
    ⊨ Γ ▸ A ≔ M
```

The four-value judgments (`rel_exp_under_ctx`, `rel_sub_under_ctx`,
`rel_wk`) are unchanged.  These are the new lemmas:

| File | Lemma |
| --- | --- |
| `PER/Lemmas.v` | `per_ctx_env_extend_def` (the analogue of `per_ctx_env_extend`, with `per_head`), `per_ctx_env_cons_def_clean_inversion`, the definition cases of `_right_irrel`, `_sym`, `_trans`, `_resp_env_eq`, `per_ctx_respects_length` |
| `ContextCases.v` | `rel_ctx_extend_def : ⊨ Γ ≈ Γ' -> Γ ⊨ A ≈ A' : Type@i -> Γ ⊨ M ≈ M' : A -> ⊨ Γ ▸ A ≔ M ≈ Γ' ▸ A' ≔ M'` and its `⊨` form |
| `LogicalRelation/Lemmas.v` | `rel_wk_shift` and `rel_sub_shift` over `e :: Γ` |
| `VariableCases.v` | `rel_exp_under_ctx_shift` over `e :: Γ`; `valid_exp_var` unchanged; `rel_exp_var_delta : Γ ∋ #x ≔ M : A -> ⊨ Γ -> Γ ⊨ #x ≈ M : A`, by induction on the lookup, whose step is `rel_exp_under_ctx_shift` and whose base reads the head clause, like the `here` case of `valid_exp_var` |
| `SubstitutionCases.v` | `rel_wk_under_ctx_q_def`, `rel_sub_under_ctx_extend_def` (`σ,,N` into `Δ ▸ A ≔ M` given `Γ ⊨ N ≈ M[σ] : A[σ]`), `rel_sub_under_ctx_q_def`, `rel_exp_under_ctx_q_def` |
| `LetCases.v` (new) | `rel_exp_let_cong` (which gives `valid_exp_let`), `rel_exp_let_zeta` |
| `Consequences/Rules.v` | `per_ctx_of_def_eq : Γ ⊢ A ≈ A' : Type@i -> Γ ⊢ M ≈ M' : A -> ⊨ Γ ▸ A ≔ M ≈ Γ ▸ A' ≔ M'` |

The let case follows the pattern of `rel_exp_fn_cong` and `rel_exp_pi_beta`.
The value of `(ℓ A ≔ M in B)[σ]` at `ρ` is `⟦B[q σ]⟧(ρ ↦ ⟦M[σ]⟧ρ)`, and the
value of `ℓ A ≔ M in B` at `ρσ` is `⟦B⟧(ρσ ↦ ⟦M⟧ρσ)`.  They are bridged by
`B`'s judgment at `q σ` into `Γ' ▸ A[σ] ≔ M[σ]` and at `Id`, and by `M`'s
chain.  ζ is `pi_beta` without the closure.  `completeness` and
`completeness_ty` keep their statements.

## 6. Soundness (`Soundness/`)

Gluing of a definition entry:

```coq
Variant cons_def_glu_sub_pred i Γ A M (TSb : glu_sub_pred) : glu_sub_pred :=
| mk_cons_def_glu_sub_pred :
  `{ forall P El R,
        Δ ⊢s σ : Γ ▸ A ≔ M ->                      (* carries σ 0 ≈ M[Wk ⨟ σ] syntactically *)
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        ⟦ M ⟧ ρ↯ ↘ m ->
        Dom (ρ 0) ≈ m ∈ R ->                        (* semantic tie, up to the PER *)
        Δ ⊢s Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢s σ ® ρ ∈ cons_def_glu_sub_pred i Γ A M TSb }.

| glu_ctx_env_cons_def :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Type@i ->
        Γ ⊢ M : A ->
        (forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ TSb -> glu_rel_typ_with_sub i Δ A σ ρ) ->
        (forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ TSb -> glu_rel_exp_with_sub i Δ M A σ ρ) ->
        Sb <∙> cons_def_glu_sub_pred i Γ A M TSb ->
        EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb }
```

The tie is a relation and not `⟦M⟧ρ↯ ↘ ρ 0`, because
`glu_ctx_env_subtyp_sub_if` has to cross `ctx_sub_extend_def`, where only
`M' ≈ M` is known.  It is needed at all because `glu_ctx_env_per_env` lands
in the PER of §4.

The definition cases go in these lemmas: `glu_ctx_env_cons_def_clean_inversion`
(and `invert_glu_ctx_env` gets that alternative first),
`functional_glu_ctx_env`, `glu_ctx_env_per_ctx_env`, `glu_ctx_env_per_env`,
`glu_ctx_env_wf_ctx`, `glu_ctx_env_sub_escape`,
`glu_ctx_env_sub_resp_sub_eq`, `glu_ctx_env_sub_monotone` (`ρ` does not
move, so the tie is unchanged), `glu_ctx_env_subtyp_sub_if` (for
`ctx_sub_extend_def`, completeness of `M' ≈ M` plus the element inclusion
of `Sub`; for `ctx_sub_forget`, drop the tie) and `initial_env_glu_rel_exp`.
In `initial_env_glu_rel_exp` the head is `⟦M⟧ρ↯`, and its gluing is `M`'s
gluing pushed along `↑`, then moved to `#0` by δ and
`glu_univ_elem_trm_resp_exp_eq`.

The new fundamental cases are `glu_rel_ctx_extend_def` and `glu_rel_exp_let`.
For the let case, glue `σ,,M[σ] ® ρ ↦ ⟦M⟧ρ` into `Γ ▸ A ≔ M` (a helper like
`cons_glu_sub_pred_helper`).  Use `B`'s gluing there, then move it from
`B[σ,,M[σ]]` to `(ℓ A ≔ M in B)[σ]` by ζ and the algebra.  Gluing is about
one environment, so `⟦ℓ A ≔ M in B⟧ρ = ⟦B⟧(ρ ↦ ⟦M⟧ρ)` holds on the nose and
no commutation is needed.  The soundness fundamental theorem stays two-way
(`wf_ctx`, `wf_exp`), so ζ, δ and the congruence need no gluing case.
`soundness` and `soundness'` keep their statements.

`ModuleCases.v` (both models): `kripke_fundamental`/`kglu_fundamental` get
one case per new rule, each discharged by the lemma above at the target
context.

## 7. Statements that cannot stay as they are

The following are **false** once δ exists.  In `⋅ ▸ Type@1 ≔ ℕ`, δ gives
`#0 ≈ ℕ : Type@1`, but `ℕ ≠ #0`.  In `⋅ ▸ Type@1 ≔ Type@0`, δ gives
`#0 ≈ Type@0`.

* `Consequences/Types.v`:
  * `is_typ_constr_and_exp_eq_var_implies_eq_var`
  * `is_typ_constr_and_exp_eq_typ_implies_eq_typ`
  * `is_typ_constr_and_exp_eq_nat_implies_eq_nat`
  * `eval_var_at_initial_env`
* `NbE.v`: `initial_env_spec` (§3).

The proposal is to replace the premise `is_typ_constr A` of the three
theorems by `rigid_typ Γ A`, where

```coq
Inductive rigid_typ (Γ : ctx) : typ -> Prop :=
| typ_is_rigid : forall i, rigid_typ Γ Type@i
| nat_is_rigid : rigid_typ Γ ℕ
| pi_is_rigid : forall A B, rigid_typ Γ (Π A B)
| var_is_rigid : forall x, ctx_ass Γ x -> rigid_typ Γ #x.
```

The var theorem and `eval_var_at_initial_env` additionally take
`ctx_ass Γ x`.  Every current caller (`subtyp_spec`, `consistency`,
`consistency_ne_helper`) uses them at `Π`, `Type` or `ℕ`, or at `#0` of
`⋅ ▹ Type@i`.  `Hint Constructors rigid_typ` keeps them automatic.
`is_typ_constr` itself stays, so `canonical_form_of_typ(_gctx)` keeps its
statement.  Every other existing theorem keeps its exact statement.

## 8. Algorithmic typing, extraction, commands

* `Algorithmic/Typing/Definitions.v` gets this rule, which mirrors `ati_app`:

  ```coq
  | ati_let :
    `( Γ ⊢a A ⟹ Typeⁿ@i ->
       Γ ⊢a M ⟸ A ->
       Γ ▸ A ≔ M ⊢a B ⟹ C ->
       nbe_ty_f Γ C[Id,,M] D ->
       Γ ⊢a ℓ A ≔ M in B ⟹ D )
  ```

  `user_exp_let` is added.  Soundness: `wf_let` plus `soundness_ty'`.
  Completeness: `wf_let_inversion`, the induction hypothesis in
  `Γ ▸ A ≔ M`, and `sub_preserves_subtyp` at `Id,,M`.  This is the `ati_app`
  argument.
* `Extraction/Evaluation.v`: `eval_exp_order` gets `eeo_let`, and
  `eval_exp_impl` gets a let clause.  `Extraction/NbE.v`:
  `initial_env_order` and `initial_env_impl` get the definition case.
  `Extraction/Readback.v` has no change.
* `Extraction/TypeCheck.v`: `lookup` matches `e :: G`.  `type_infer_order`
  and `type_infer` get a let clause: infer `A` to a universe, check `M`,
  infer `B` in `G ▸ A ≔ M`, then `nbe_ty_impl` of `C[Id,,M]`.  The clause
  has four obligations, in the style of the app ones.  `clear_defs` must be
  checked, since it matches the recursive signatures literally.
* `Extraction/GlobalCheck.v`: `check_ctx` gets the clause `Γ ▸ A ≔ M` (check
  `A` is a type, then check `M : A`).
* `Command.v` (System and Extraction) and `Entrypoint.v`: no change beyond
  the types.

## 9. Front end

* **CST** (`Syntax.v`, module `Cst`): `d_def : string -> obj -> obj -> decl`.
  The `mods` argument is dropped, so an abstract or private let cannot be
  represented at all.  This is the cleaner of the two options.  The grammar
  never produced anything but `md_pub` there, so no surface program is
  rejected that is accepted today.  Top-level `abstract def` (`c_def`)
  keeps its `mods`.
* **Parser** (`Parser.vy`): `let_defn` builds `Cst.d_def x A M`.  The
  declaration form `let def x … def y … in B end` keeps folding into nested
  `Cst.letb`.  That fold is the multi-let sugar, and each `letb` becomes one
  core let.  The CST keeps one declaration per `letb`, which is the reason
  given in `Syntax.v` (an ordinary mutual pair for `Functional Scheme`).
  **Open point (legacy form)**, see §11.
* **Elaborator** (`Elaborator.v`):

  ```coq
  | Cst.letb (Cst.d_def x oA oM) obody =>
      let* A := res_term (elab_res ls d oA nil) in
      let* M := res_term (elab_res ls d oM nil) in
      let* B := res_term (elab_res ((x, le_term #0 (S d)) :: ls) (S d) obody nil) in
      eok (r_exp (sc_apply (ℓ A ≔ M in B) args))
  ```

  `x` is bound in the body exactly as a `fun` binder is.  `let module` is
  unchanged.
* **Spec** (`ElabSpec.v`): `lb_let` is deleted, because a let binding now
  denotes its core variable, which is what `lb_var` does.  So
  `lbind := lb_var | lb_mod`, `lb_binders (lb_var _) = 1`, and
  `ldenote k (lb_var _) = s_term #k`.  The one let rule is:

  ```coq
  (** [let x : A := M in B] elaborates to the core [ℓ A ≔ M in B].  Inside [B],
      [x] is the let's own variable, which the core binds to [M]. *)
  | sel_let : forall L x oA oM ob A M B,
      selt L oA A -> selt L oM M -> selt (lb_var x :: L) ob B ->
      sel L (Cst.letb (Cst.d_def x oA oM) ob) (s_term (ℓ A ≔ M in B))
  ```

  `sel_let_abs` is deleted.  `shift_by` becomes unused if `lb_let` was its
  only user, in which case it is deleted too.
* **ElabCorrect.v**: the let case of `elab_res_iff` loses its
  `md_abstract` split, and `to_ls` loses the `lb_let` clause.
  `elaborate_core_iff` and its corollaries keep their statements.
* **ElabExamples.v**: new cases `let_nested` (`let def x … in let def y … in
  … end end`), `let_multi` (three declarations in one `let`, later ones
  using earlier ones in both type and body), and `let_shadow` (a let name
  shadowing a frame member).  Each checks the exact core term.  The running
  example in `ElabSpec.v` and `elab-spec.md` is extended with one let in
  `j`: `def j : … := let def f : forall (x : Nat) -> Nat := M.id Nat in f
  end end`.  This shows that a let adds one binder to the offset `fbind`
  starts from.
* **Printer** (`PrettyPrinter.ml`): `Coq_a_let (A, M, B)` prints as
  `Cst.letb (Cst.d_def x A M) B` with a fresh `x`.  Runs of nested lets
  already print as one `let`.  The `md_abstract` printing of `d_def` goes.

## 10. Driver tests (`examples/`, `driver/Test.ml`)

* New `let_delta.mctt`.  It is Nat-only, since `vector.mctt`'s `Vec` is a
  Church encoding.  It defines `Nary : Nat -> Type@0` by recursion, and then:

  ```
  eval let def n : Nat := 3
           def f : Nary n := fun (a : Nat) (b : Nat) (c : Nat) -> a
       in f 1 2 3 end : Nat
  ```

  This needs `n ≡ 3` both to check `f`'s body against `Nary n` and to apply
  `f` three times.  Under the old abstract reading it is rejected.  A second
  eval does the `Vec ℕ n` / `Vec ℕ 3` example with `vector.mctt`'s
  definitions.
* New `let_multi.mctt`: three declarations, each depending on the previous
  one.
* Expected outputs change only where the printed elaborated expression
  changes: an `Evaluate` line now shows `let … in … end` instead of an
  inlined body or a β-redex.  Results and types (`--> 4 : Nat` etc.) are
  unchanged, because NbE ζδ-reduces the let to the value the inlined or
  β-form had.  `let_decl` is affected in any case.  `simple_let`,
  `let_two_vars`, `let_nary` and `let_vector` are affected under option L1
  of §11.

## 11. Open point: the legacy `let ((x : A) := t) … in b`

Today the parser itself turns this into a β-redex, `(fun (x : A) … -> b) t
…`, so in `b` the name `x` is abstract.  That is an abstract let in all but
name.

* **L1 (recommended).**  The parser folds it into nested `Cst.letb (d_def x A
  t)`, as it does for the declaration form, so it becomes real core lets.
  Example: `let ((n : Nat) := 3) ((f : Nary n) := fun (a b c : Nat) -> a) in
  f 1 2 3` is accepted.  The scope changes in one respect: a later definiens
  now sees earlier names.  `let ((n : Nat) := 3) ((m : Nat) := n) in m`
  becomes accepted (today `n` is unbound in `m`'s definiens, or names an
  outer `n`).  No example relies on the old scoping.  `simple_let`,
  `let_two_vars`, `let_nary` and `let_vector` then print with `let`.
* **L2.**  Keep it as β-redex sugar (it is not a `letb` in the CST).  The
  four outputs stay byte-for-byte.  `let ((n : Nat) := 3) ((f : Nary n) :=
  …) in f 1 2 3` stays rejected, because `f`'s type is `Nary n` with `n` a
  λ-variable.

## 12. Files that change

`Syntax.v`, `Substitution.v`, `System/{Definitions,Lemmas,Tactics,Scoping,
Structural,GlobalPresup}.v`, `Presup.v`, `SubEq.v`, `CoreInversions.v`,
`CtxSub.v`, `SystemOpt.v`, `Corollaries.v` (lookup functionality),
`Semantic/{Evaluation/*,NbE,PER/Definitions,PER/Lemmas,Realizability,
Transparency,Consequences}.v`, `Completeness/{LogicalRelation/*,ContextCases,
VariableCases,SubstitutionCases,ModuleCases,FundamentalTheorem,
Consequences/*}.v` + new `LetCases.v`, `Soundness/{LogicalRelation/*,
Weakening/Lemmas,ContextCases,ModuleCases,FundamentalTheorem,Realizability}.v`
+ new `LetCases.v`, `Algorithmic/Typing/{Definitions,Lemmas}.v`,
`Extraction/{Evaluation,NbE,TypeCheck,GlobalCheck}.v`,
`Frontend/{Parser.vy,Elaborator,ElabSpec,ElabCorrect,ElabExamples}.v`,
`driver/{PrettyPrinter.ml,Test.ml}`, `examples/let_{delta,multi}.mctt`,
`_CoqProject`, the notes (`AGENT/{elab-spec,notations,README}.md`, this file).

## 13. Hardest obligations (estimate)

1. **Completeness, substitution infrastructure for definition entries**
   (`rel_sub_under_ctx_q_def`, `_extend_def`, `rel_wk_under_ctx_q_def`,
   `rel_exp_under_ctx_q_def`) and the let, ζ, congruence and δ cases.  Each
   head tie is a four-value chain whose links come from `M`'s judgment at two
   instantiations, as in `rel_exp_under_ctx_shift`.  The largest piece:
   roughly 600–900 lines, modeled on `SubstitutionCases.v`.
2. **PER layer for `per_ctx_env_cons_def`**: the dependent `head_rel`,
   irrelevance, the funext-based symmetry, transitivity and `resp_env_eq`.
   Roughly 300 lines.
3. **Syntactic `wf_sub`/`wf_wk` field.**  Every closure lemma and
   `ctx_sub_escape` gets a definition obligation.  The order inside
   `Lemmas.v` (composition after `sub_preserves_exp_eq`) is delicate.  The
   presupposition of `let_cong` needs context conversion of a definition.
   Roughly 300 lines.
4. **Gluing**: the tie through `glu_ctx_env_subtyp_sub_if`, which calls
   completeness inside soundness, and `initial_env_glu_rel_exp`.  Roughly 250
   lines.
5. **Mechanical breadth**: five rules times the mutual inductions (scoping,
   structural, global presupposition, the two `kripke_fundamental`s,
   `consistency_ne_helper`), `ce_typ` showing up after `dependent
   destruction` on `here`, and the `Equations` obligations of `type_infer`.
   There are many cases, and individually they are easy.

Process for Phase 2: record the `Print Assumptions` baseline of
`completeness_gctx`, `soundness_gctx`, `soundness_gctx'`,
`prog_impl_sound`/`_complete`, `main_sound`/`_complete` and
`elaborate_core_iff` first.  Then do syntax and syntactic layer → semantic
and PER → completeness → soundness → algorithmic and extraction → front end
and driver, with a commit at each green milestone.
