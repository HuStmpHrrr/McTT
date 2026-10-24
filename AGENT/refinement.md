# Refinement: the extracted checker and its reference

`theories/Extraction/` holds the code that is extracted; `theories/Reference/`
holds the direct implementation each refined function was refined from, with
its original proofs.  Every refined function has the same specification
(dependent type) as its reference, so `main_sound`, `main_complete` and
`prog_impl_*` hold for the extracted code with unchanged statements and
proofs; `Reference/Refinement.v` states the input–output equalities at
the default lookup data (`fctx_none`), and `Extraction/Refines.v` at any
`FCtx` (see below).

| Extracted | Reference | Refinement |
| --- | --- | --- |
| `Extraction/TypeCheck.v` | `Reference/TypeCheck.v` | an application spine is checked against the *value* of the head's type (`type_infer_val_in`, `type_infer_app_in`), and the codomain is evaluated without the argument when it does not read it (`app_cod`); a check normalizes only the type it checks against; an eliminator's motive and branches get their initial environments from the context's (`tenv_ext`) |
| `Extraction/Evaluation.v`, `Readback.v` | `Reference/Evaluation.v`, `Readback.v` | the eliminator of an inductive type at a constructor computes the result of a recursive argument only when the branch reads it (`exp_freshb (cargs_nrec gs) B`); an unread entry is `𝕌ω@0`.  Constructors of the shape of `zero` and `succ` are taken apart without lists (`con_view`); a branch's environment is built without copying the arguments (`elim_env`); global names are looked up in the data of the command (`FCtx`) |
| `Extraction/NbE.v` | `Reference/NbE.v` | normalization by the fast evaluator, same specification (`nbe`, `nbe_ty`) |

The termination orders of normalization (`nbe_ty_order`, …) stay those of
the reference evaluator: they are the specification the checker's
obligations prove.

Shared by both checkers: `Extraction/TypeCheckBase.v` (orders, side-condition
decisions, `tenv`, and the obligation tactics, which live outside the
sections so that both checkers can use them).

## The value of a type (`typ_val`)

`typ_val G P v T`: `v` is related by `per_univ i` to `⟦ T ⟧ ρ`, `ρ` the
initial environment `P`, and `G ⊢ T : Typeω@i`.  It reads back to `T`
(`typ_val_rtyp`), and a `Πᵈ a ρ' b` that stands for `Πⁿ A B` gives, at an
argument `N : A`, the value `⟦ b ⟧ ρ' ↦ ⟦ N ⟧ ρ` that stands for the normal form
of `B[Id,,N]` (`typ_val_pi`, `typ_val_app_step`): the result of `ati_app`
without the substitution and the re-normalization.

The orders gained `app_order M N` (`ti_app : app_order M N -> type_infer_order
(M $ N)`, `ao_app : type_check_order M -> type_check_order N -> app_order M N`)
so that the head of an application is a strict subterm at the order of a
check: `type_infer_val_in` recurses through `type_infer_app_in` on an
application and calls `type_infer_in` otherwise, both structurally.

## The skipped recursive result (`Extraction/FastEval.v`, `Simulation.v`)

`FastEval.v` copies the evaluation and readback relations of
`Core/Semantic` with one rule split in two, `feval_ihs_rec` and
`feval_ihs_skip`: the recursive results of a constructor's arguments are
computed for the branch `B` (`⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ`), and
the result of the recursive argument heading `ca_rec t :: gs`, the variable
`cargs_nrec gs` of `B`, is computed only when `B` reads it; otherwise the
entry is `𝕌ω@0`.  A function-shaped result is a closure (`d_ihfn`),
skipped alike.

The readback of a stuck eliminator's branch (`fread_brs`) gives a
recursive result the branch does not read (`exp_freshb (cargs_nrec gs) B`)
the type `𝕌ω@0` instead of evaluating the motive at it (`ffresh_ihs_skip`);
`fread_sim` relates the recursive results only where the branch reads them
(`dsim_list_at`, `env_agree_binders_at`), as for evaluation.

Evaluation selects a member of a global module by one lookup of its entry
(`gc_entry`, `Extraction/Evaluation.v`): a definition (`gc_entry_def`) or the
module of an inductive type, the type former (`gc_entry_ind`,
`ind_lookup_entry`); the relation keeps `gc_resolve` and `ind_lookup`.

The checker of an eliminator (`Extraction/IndCheck.v`) checks and
normalises nothing for an unapplied head: the type former at no parameter
is its own normal form, which the algorithmic rule's premises get by
completeness.

Readback has one rule more: a type former without arguments reads back as
`nf_indty p nil` without looking its declaration up
(`fread_typ_indty_nil`; the general rule asks `as' <> nil`).

The implementations keep a declaration they looked up (`lk_cache`,
`cache_lookup`, `Extraction/Lookup.v`): the eliminator passes the one of
the constructor it takes apart to the recursive results, and readback of a
constructor or of a stuck eliminator to what it reads below, so a lookup of
the same name is a comparison of names.  The relations are unchanged.

Normal forms are compared by `nf_eq_dec` (`Syntax.v`), whose names are
compared by `string_dec` (native string equality once extracted), not
taken apart character by character by `decide equality`.  Notations carry `ᶠ` (`⟦ M ⟧ᶠ`, `Rtypᶠ`, …).
The orders and implementations of `Extraction/Evaluation.v` and
`Readback.v` are those of `Reference/` over the copied relations.

`Simulation.v` relates the two.  `dsim a a'` (reference `a`, fast `a'`) is
equality up to the entries of closures' environments at which the body is
fresh; `env_agree P ρ ρ'` is agreement at the entries `P` selects.

- `feval_sim`: from environments that agree where the term may read
  (`fun x => ~ exp_fresh x M`), the fast evaluation terminates whenever the
  reference one does, at a related value.  A body's environment agrees on
  the entries it adds and, above them, where its input did (`above`).
  The recursive results are related only at the entries the branch reads
  (`dsim_list_at (fun x => ~ exp_fresh x B)`: the head of `a :: l` sits at
  entry `List.length l`), and the branch's environment agrees where the
  branch reads (`env_agree_binders_at`).
- `fread_sim`: readback of related values gives the same normal form.

So the fast normalizers meet `nbe`/`nbe_ty` (`Extraction/NbE.v`): the order
gives the reference derivation, `feval_sim`/`fread_sim` the fast one, and
determinism of fast readback the equality.  The checker's environment
`tenv G` is `fenv`: a fast environment related to the initial environment of
`G` entry by entry.

## What a command looks up once (`Extraction/Lookup.v`)

The implementations take an instance of a class, the data a command
computes once for all the checks it runs:

```coq
Class FCtx (Θ : gdeps) (Ξ : gstack) : Set := mk_fctx
  { fc_seed : lk_cache Θ Ξ
  ; fc_units : path -> option gunit
  ; fc_units_ok : forall fp, fc_units fp = gds_lookup Θ fp }.
```

- `fc_seed`: a declaration the evaluator and readback start from, as if
  they had looked it up already (`lk_cache Θ Ξ` is
  `option {x : qname * ind_decl | ind_lookup Θ Ξ (fst x) = Some (snd x)}`).
- `fc_units`: the filed units by path, equal to `gds_lookup Θ`.

Every lookup of a global name is defined in `Core/Syntactic/Members.v` at a
function `uf : path -> option gunit` (`gc_resolve_u`, `gc_module_u`,
`ind_lookup_u`, `gc_entry_u`, `ind_alias_lookup_u`, `ind_target_u`), and
the core's lookup is that function at `gds_lookup Θ`, e.g.
`gc_resolve Θ Ξ p := gc_resolve_u (gds_lookup Θ) Ξ p`.  At any `uf` that
agrees with `gds_lookup Θ` the lookups agree (`gc_resolve_u_ok` and the
like).  The implementations call them at `fc_units F` (`gc_entry_f`,
`ind_lookup_f`, …, each returning `{ o | gc_entry Θ Ξ p = o }`), so their
specifications name only the core's lookups.

Two instances:

- `fctx_none Θ Ξ`: no seed, `gds_lookup Θ`.  It is the default instance
  (priority 100), so the reference checker and the statements of
  `Reference/Refinement.v` get it without naming it.  The extracted
  command checker uses it only on its error paths (the blame searches).
- `fctx_at Θ Ξ op`: the trie of `Θ` and, as seed, the declaration at `op`
  looked up through it.  A command builds `fctx_cmd B Θ Ξ := fctx_at Θ Ξ
  (bt_nat B)` (`Extraction/Command.v`) for each check it runs: the
  eliminator of the type bound as the natural numbers then looks nothing
  up.

**The trie of the filed units.**  `ptrie` is a trie keyed by the components
of a path:

```coq
Inductive ptrie : Set := pnode : option gunit -> pkids -> ptrie
with pkids : Set :=
| pk_nil : pkids
| pk_cons : string -> ptrie -> pkids -> pkids.
```

`pt_find t fp` compares one component per level with the components
present at that level (strings are compared for equality only, which is
native once extracted), instead of comparing `fp` with every filed path.
`pt_of Θ` adds the entries of `Θ` oldest first, so that the newest entry of
a path decides, as in `gds_lookup`; `pt_of_find : pt_find (pt_of Θ) fp =
gds_lookup Θ fp`.  Members inside a unit are still scanned: the profile of
`lib/Binary.mctt` puts them under 2%.

## Fast paths of the evaluator and readback (`Extraction/Evaluation.v`, `Readback.v`)

The relations are those of `FastEval.v`; only the implementations take the
shortcuts below, and each is proved to give the value or normal form of
the general rule.

**Constructors of the shape of `zero` and `succ`.**  `nat_cargs D gs` is
`Some false` when `D` has no parameters, no uniform ones and `gs = nil`
(the arguments of `zero`), `Some true` when `gs = ca_rec (pt_self k nil) ::
nil` (those of `succ`), and `None` otherwise.  `con_view D c vs :
option (option domain)` is the constructor `c` at the values `vs`: `Some
None` of the shape of `zero`, `Some (Some v)` of the shape of `succ v`.

- The eliminator at a `zero`-shaped constructor evaluates the branch at its
  environment; at `succ v`, at `v` and the recursive result, which it
  computes only when the branch reads it (`exp_freshb 0 B`; otherwise the
  entry is `𝕌ω@0`), passing the declaration on as the cache.
- Readback of such a constructor reads its argument at the type former;
  readback of a stuck eliminator's branch binds the argument and the
  recursive result directly.
- `con_view_zero` / `con_view_succ` give back the facts of the general rule
  (`ind_con D c`, `ind_params D = nil`, `ind_np D = 0`, `ind_nu D = 0`, the
  shape of `vs`).

Every other constructor takes the general rule.

**The environment of a branch.**  The general rule evaluates a branch at
the non-uniform parameters, the arguments and the recursive results
(`env_args p (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs
++ ihs)`).  `elim_env p D vs ihs` is that environment, built as
`env_args (env_args p vs) ihs` when `D` has no parameters, without slicing
and appending the value list (`elim_env_eq`, by `env_args_app`).

**Recursive argument types without indices.**  For an argument at the type
itself without indices (`pt_self k nil`), `feval_shty_fast` gives its type
as the type former at the uniform parameters, and `feval_ihty_fast` the type
of its recursive result as the motive at the argument, without evaluating
an empty list of indices; readback uses both.

## The checker's shortcuts (`Extraction/TypeCheck.v`, `IndCheck.v`)

**The codomain of an application (`app_cod`).**  The type of an
application spine is a value: the codomain closure `Πᵈ a ρ b` at the
argument's value.  `app_cod G P N ρ b` evaluates `b` at `ρ ↦ 𝕌ω@0`,
without evaluating the argument `N`, when `b` does not read its variable
(`exp_freshb 0 b = true`), and at `ρ ↦ n`, `n` the value of `N`, otherwise
(`app_cod_val`).  `typ_val` is up to `dsim`, which relates closures only
where their bodies read (`feval_clo_unread`, `Simulation.v`), so the value
still stands for the normal form (`typ_val_app_cod_step`).  A numeral, a
chain of `n` constructors typed by the spine rule, is typed in time linear
in `n`: `eval succ 3200` takes 15 ms, 141 ms before.

**The environments of an eliminator's motive and branches (`tenv_ext`).**
They are checked in extensions `Ψ ++ G` of the context `G` of the
eliminator.  `tenv_ext G P Ψ : ⊢ Ψ ++ G -> tenv (Ψ ++ G)` extends `G`'s
initial environment `P`, which the checker carries, by one entry per entry
of `Ψ`, rather than computing the environment of `Ψ ++ G` from scratch
(`tenv_of`).  The contexts of `lib/` are small at eliminators, so the
timings do not move beyond noise; the work no longer grows with `G`.

## The equalities at any lookup data (`Extraction/Refines.v`)

`Reference/Refinement.v` states the input–output equalities at
`fctx_none`, which instance resolution picks there.  `Extraction/Refines.v`
states the same equalities, with the same proofs, in a section with
`{GC : GCtx} {F : FCtx gc_deps gc_stack}`, so at any `FCtx`, in particular
the one a command builds (`fctx_at`): `type_check_in_refines_f`,
`type_infer_in_refines_f`, `ext_check_refines_f`, `unit_check_refines_f`,
`modexp_check_refines_f` (the checkers decide the same judgments and infer
the same types), `nbe_ty_env_impl_refines_f`, `nbe_ty_impl_refines_f`,
`nbe_impl_refines_f`, `read_typ_impl_refines_f`, `read_nf_impl_refines_f`
(the same normal forms), `eval_exp_impl_refines_f`,
`initial_env_impl_refines_f` (related values).

## Timings

Wall-clock milliseconds, median of 3 runs of the driver per program; `lib`
is the sum of the medians over every `lib/` program and Prelude unit.  OLD
is ℕ built in (`a2a7f15`, on its own `lib/`); NEW is ℕ an inductive type
bound by `builtin natural`, before any of the refinements above; FINAL is
NEW with all of them, two runs.

| | OLD | NEW | FINAL (run 1 / 2) |
| --- | ---: | ---: | ---: |
| Arithmetic | 21.0 | 27.7 | 24.9 / 26.3 |
| Division | 46.5 | 78.7 | 65.2 / 66.7 |
| Powers | 39.3 | 64.4 | 52.9 / 52.9 |
| Binary | 198.8 | 615.6 | 372.2 / 372.7 |
| Vectors | 101.6 | 220.5 | 156.6 / 159.3 |
| Streams | 97.0 | 203.0 | 150.8 / 151.3 |
| NumberTheory | 86.0 | 178.3 | 122.9 / 122.7 |
| lib | 2298.9 | 3978.5 | 3174.4 / 3198.1 |

The commit message of each refinement carries the table with one column
more.  The `lib` total, refinement by refinement, in the order they were
added: the seed 3978.5 → 3901.6, `con_view` → 3613.4, `elim_env` and the
types without indices → 3531.0, the trie → 3312.8, `app_cod` → 3195.5,
`tenv_ext` within noise.
