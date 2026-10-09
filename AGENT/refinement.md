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

Shared by both: `Extraction/TypeCheckBase.v` (orders, side-condition
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
