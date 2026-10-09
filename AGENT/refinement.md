# Refinement: the extracted checker and its reference

`theories/Extraction/` holds the code that is extracted; `theories/Reference/`
holds the direct implementation each refined function was refined from, with
its original proofs.  Every refined function has the same specification
(dependent type) as its reference, so `main_sound`, `main_complete` and
`prog_impl_*` hold for the extracted code with unchanged statements and
proofs; `Reference/Refinement.v` states the input–output equalities.

| Extracted | Reference | Refinement |
| --- | --- | --- |
| `Extraction/TypeCheck.v` | `Reference/TypeCheck.v` | an application spine is checked against the *value* of the head's type (`type_infer_val_in`, `type_infer_app_in`); a check normalizes only the type it checks against |
| `Extraction/Evaluation.v`, `Readback.v` | `Reference/Evaluation.v`, `Readback.v` | the eliminator at a successor skips the recursive result when the step case does not read it (`exp_freshb 0 MS`); its entry is `zeroᵈ` |
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
`Core/Semantic` with one rule split in two: `feval_natrec_succ` (the step
case reads `#0`: `exp_freshb 0 MS = false`) and `feval_natrec_skip` (it does
not; the entry is `zeroᵈ`).  Notations carry `ᶠ` (`⟦ M ⟧ᶠ`, `Rtypᶠ`, …).
The orders and implementations of `Extraction/Evaluation.v` and
`Readback.v` are those of `Reference/` over the copied relations.

`Simulation.v` relates the two.  `dsim a a'` (reference `a`, fast `a'`) is
equality up to the entries of closures' environments at which the body is
fresh; `env_agree P ρ ρ'` is agreement at the entries `P` selects.

- `feval_sim`: from environments that agree where the term may read
  (`fun x => ~ exp_fresh x M`), the fast evaluation terminates whenever the
  reference one does, at a related value.  A body's environment agrees on
  the entries it adds and, above them, where its input did (`above`).
- `fread_sim`: readback of related values gives the same normal form.

So the fast normalizers meet `nbe`/`nbe_ty` (`Extraction/NbE.v`): the order
gives the reference derivation, `feval_sim`/`fread_sim` the fast one, and
determinism of fast readback the equality.  The checker's environment
`tenv G` is `fenv`: a fast environment related to the initial environment of
`G` entry by entry.
