# Refinement: the extracted checker and its reference

`theories/Extraction/` holds the code that is extracted; `theories/Reference/`
holds the direct implementation each refined function was refined from, with
its original proofs.  Every refined function has the same specification
(dependent type) as its reference, so `main_sound`, `main_complete` and
`prog_impl_*` hold for the extracted code with unchanged statements and
proofs; `Reference/Refinement.v` states the input–output equalities at
every fast context `F` (see below).

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
of `B[Id,,N]` (`typ_val_pi`, `typ_val_app_step`): the result of `alg_type_infer_app`
without the substitution and the re-normalization.

The orders gained `app_order M N` (`type_infer_order_app : app_order M N -> type_infer_order
(M $ N)`, `app_order_app : type_check_order M -> type_check_order N -> app_order M N`)
so that the head of an application is a strict subterm at the order of a
check: `type_infer_val_in` recurses through `type_infer_app_in` on an
application and calls `type_infer_in` otherwise, both structurally.

## The skipped recursive result (`Extraction/FastEval.v`, `Simulation.v`)

`FastEval.v` copies the evaluation and readback relations of
`Core/Semantic` with one rule split in two, `fast_eval_ihs_rec` and
`fast_eval_ihs_skip`: the recursive results of a constructor's arguments are
computed for the branch `B` (`⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ`), and
the result of the recursive argument heading `ca_rec t :: gs`, the variable
`cargs_nrec gs` of `B`, is computed only when `B` reads it; otherwise the
entry is `𝕌ω@0`.  A function-shaped result is a closure (`d_ihfn`),
skipped alike.

The readback of a stuck eliminator's branch (`fast_read_brs`) gives a
recursive result the branch does not read (`exp_freshb (cargs_nrec gs) B`)
the type `𝕌ω@0` instead of evaluating the motive at it (`fast_fresh_ihs_skip`);
`fast_read_sim` relates the recursive results only where the branch reads them
(`domain_list_simulation_at`, `env_agree_binders_at`), as for evaluation.

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
(`fast_read_typ_indty_nil`; the general rule asks `as' <> nil`).

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

`Simulation.v` relates the two.  `domain_simulation a a'` (reference `a`, fast `a'`) is
equality up to the entries of closures' environments at which the body is
fresh; `env_agree P ρ ρ'` is agreement at the entries `P` selects.

- `fast_eval_sim`: from environments that agree where the term may read
  (`fun x => ~ exp_fresh x M`), the fast evaluation terminates whenever the
  reference one does, at a related value.  A body's environment agrees on
  the entries it adds and, above them, where its input did (`above`).
  The recursive results are related only at the entries the branch reads
  (`domain_list_simulation_at (fun x => ~ exp_fresh x B)`: the head of `a :: l` sits at
  entry `List.length l`), and the branch's environment agrees where the
  branch reads (`env_agree_binders_at`).
- `fast_read_sim`: readback of related values gives the same normal form.

So the fast normalizers meet `nbe`/`nbe_ty` (`Extraction/NbE.v`): the order
gives the reference derivation, `fast_eval_sim`/`fast_read_sim` the fast one, and
determinism of fast readback the equality.  The checker's environment
`tenv G` is `fenv`: a fast environment related to the initial environment of
`G` entry by entry.

## What the extracted code looks up in (`Extraction/FastContext.v`, `Lookup.v`)

The extracted code runs on fast data only.  Neither a Core global context
`Θ ⍮ Ξ` nor any `gdeps` or `gstack` is built or read at run time:

- the filed units are one map from the whole path of a unit to the unit,
  with the filing order (`funits`, `Extraction/FastGlobal.v`);
- next to it, in `funits`, the units the unit being run sees: a second map
  of the same kind (`fus_vis`), whose invariant `vis_rep s D` says it holds
  exactly the filed units at the imported paths `D`.  It grows by one add
  per path that becomes imported (`fus_see`, at a load); while an imported
  unit runs it is set aside and that run starts from an empty one
  (`fus_with_vis`, `unit_pre_f`); it is never rebuilt per command.  What a
  command sees (`fview`: the units and the list `D`) is built in O(1)
  (`cmd_view`), and a unit lookup is one search in `fus_vis` (`fv_find`);
- a unit's body, and the body of every open frame, is a trie: a balanced
  map from a member's name to its entry, with the order index of the names
  (`ftrie`, `fentry`, `funit`; `fframe`, `fstack`).

The searches are written directly over the trees, one comparison per node
(`sfind` for member names, `pfind` for paths), with `_ok` lemmas equating
them with `SRaw.find` / `PM.find`.  Both unit maps are keyed by the reversed
path (`path_key`, through `pk_find` / `pk_add`).  Names and paths are compared
by `String.compare`, which the directive of `Entrypoint.v` extracts to the
native comparison; `String.eqb` and `string_dec` extract to OCaml's generic
`(=)`, so hot equalities (`names_eqb`, `qname_eqb`, `qname_dec`) go through
`String.compare` too.

```coq
Record FCtx : Type := mk_fctx
  { fc_view : fview                 (* the units the unit being run sees *)
  ; fc_frames : fstack              (* the open frames *)
  ; fc_ok : fctx_ok fc_view fc_frames   (* a Prop: they translate a canonical Core context *)
  ; fc_seed_found : lk_cache (view_deps fc_view) (dec_stack fc_frames) }.
```

The Core context a fast context stands for, `fc_gctx F` (`fc_deps F`,
`fc_stack F`), is the decoding of its data (`dec_units`, `dec_stack`,
`view_deps`).  It is in types and proofs only: the decoding sits behind the
sealed module of `Extraction/Decoding.v` (`FcDecoding`, `fc_gctx_eq`
implemented by a proof), in a file of its own so that extraction does not
need it.  Every lookup has a fast twin with the lemma that, on a
translation, it finds the translation of what the Core lookup of the
decoding finds (`fc_entry_ok`, `fc_ind_ok`, `gc_entry_f`, …), and every Core
function of the checker that reads the global context has a twin over `F`
(`Extraction/LookupTwins.v`, `FastState.v`, with `_ok` or `_dec` lemmas).
Core is unchanged.

**The run's state** (`Extraction/Command.v`).  The interpreter keeps the
state fast (`cstate`: the filed units, the closures, the paths imported,
the builtin bindings, the frames; `ustate` for a unit's result); the
invariants and the `post_*` are about its Core reading (`cs_read`,
`us_read`).  A step takes `pre ch s K D fs`: the invariant of the reading,
`units_rep s (dec_units s)`, `vis_rep s D` and `fs = fs_of (dec_stack fs)`.
Its checks run at `fctx_cmd B s D fs Hok`, the fast context of the command,
where `Hok : fctx_ok (cmd_view s D) fs` comes from `pre_fctx_ok`: the
reading is canonical because the invariant makes it well formed
(`canon_of_wf`).  A result carries `fast_res P r`: `P (cs_read r)` with the
same three refinements.  How the refinement is kept:

- the units seen: a step that keeps `D` keeps them (`state_res`,
  `same_res`); a load that hits a filed unit sees it and its closure
  (`see_res`); a fresh load files the unit and sees it and its closure on
  top of the units seen before, which stay valid because the run only adds
  units (`load_units`, `load_vis`, from `ext_sub` of the unit's post);

- a frame opened is empty (`push_frames`, `pre_cons`);
- an entry added is the translation of a canonical Core entry
  (`add_res`, `dec_stack_add`);
- a frame closed is the translation of its own reading (`frame_body_tr`,
  `close_res`, `mod_res`, `record_res`);
- a unit filed is the translation of a canonical unit (`load_res`,
  `dec_units_file`, `units_rep_file`); a unit's run returns its unit fast,
  `usf_unit r = tr_unit (dec_unit (usf_unit r))` (`ures`, `unit_res`).

The main theorems read the fast results in Core: `prog_impl_sound`,
`prog_impl_complete`, `main_sound`, `main_complete` at `dec_units s` and
`dec_unit u`; `prog_impl_rep` and `main_rep` state that `s` and `u` are the
translations of their readings.

**The scan.**  No decoding and no Core global context may reach the
extracted OCaml.  After `make -f CoqMakefile.mk post-all`:

```sh
cd driver/extracted
grep -nw 'dec_units\|dec_stack\|view_deps\|gds_restrict\|dec_mod\|dec_entry\|dec_unit\|dec_frame\|gds_lookup\|gdeps\|gstack\|fc_gctx\|FcDecoding\|coq_GCtx\|gc_deps\|gc_stack' *.ml *.mli
```

must print nothing: not even the types `gdeps`, `gstack` or `GCtx` are
extracted any more.  A hit is a computational use of the Core context: a Core
function with a `Θ` or `Ξ` argument that is not `Prop` (an implicit
`{Θ Ξ}` is extracted, and OCaml evaluates it even when the function ignores
it), or a `{GC : GCtx}` instance.  The fix is a twin over `F`, or the
indices taken from `F` (`{F : FCtx}`, as `blame_error` and
`level_blame_app` do).

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
itself without indices (`pt_self k nil`), `fast_eval_shty_fast` gives its type
as the type former at the uniform parameters, and `fast_eval_ihty_fast` the type
of its recursive result as the motive at the argument, without evaluating
an empty list of indices; readback uses both.

## The checker's shortcuts (`Extraction/TypeCheck.v`, `IndCheck.v`)

**The codomain of an application (`app_cod`).**  The type of an
application spine is a value: the codomain closure `Πᵈ a ρ b` at the
argument's value.  `app_cod G P N ρ b` evaluates `b` at `ρ ↦ 𝕌ω@0`,
without evaluating the argument `N`, when `b` does not read its variable
(`exp_freshb 0 b = true`), and at `ρ ↦ n`, `n` the value of `N`, otherwise
(`app_cod_val`).  `typ_val` is up to `domain_simulation`, which relates closures only
where their bodies read (`fast_eval_clo_unread`, `Simulation.v`), so the value
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

## The equalities at every fast context (`Reference/Refinement.v`)

The extracted code takes a fast context `F : FCtx` (`Extraction/Lookup.v`)
and no Core global context: the Core context `fc_gctx F` it stands for
(`fc_deps F`, `fc_stack F`) is the decoding of the fast data, in types and
proofs only.  So the refinement theorems are stated over `F`:
`type_check_in_refines`, `type_infer_in_refines`, `ext_check_refines`,
`unit_check_refines`, `modexp_check_refines` (the checkers decide the same
judgments and infer the same types; `Reference/TypeCheck.v` runs on `F` too,
as it shares the eliminator, record and normalization code of `Extraction`),
`nbe_ty_env_impl_refines`, `nbe_ty_impl_refines`, `nbe_impl_refines`,
`read_typ_impl_refines`, `read_nf_impl_refines` (the same normal forms),
`eval_exp_impl_refines`, `initial_env_impl_refines` (related values).  The
reference evaluation, readback and normalization stay on Core `Θ ⍮ Ξ`;
the seven theorems about them also have `_at` corollaries, whose
reference side is at any `Θ ⍮ Ξ` and whose extracted side is at its
translation `fctx_of Θ Ξ HcΘ HcΞ`.  Their only premise is canonicity
(`canon_deps Θ`, `canon_stack Ξ`: closed bodies without opens, fresh
names), which every well-formed context has (`canon_of_wf`).  It cannot be
dropped: a non-canonical context has no fast context to run the extracted
code on.  It is weaker than `⊢ᵍ Θ ⍮ Ξ`, which the corollaries therefore do
not take.  The checker theorems need no corollary: their arguments
(`⊢ G`, `G ⊢ A : Typeω@i`) give `⊢ᵍ` already.

The decoding `fc_gctx` sits behind a sealed module (`FcDecoding`, with
`fc_gctx_eq` implemented by a proof), so that no tactic reduces it into
the decoding functions: `firstorder` does so through any transparent
definition whatever its `Opaque` status, and took two minutes per
obligation of `Extraction/TypeCheck.v` before the sealing.

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
