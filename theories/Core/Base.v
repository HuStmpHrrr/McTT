#[global] Declare Scope mctt_scope.
#[global] Delimit Scope mctt_scope with mctt.
#[global] Bind Scope mctt_scope with Sortclass.

(** The [mctt] hint database is created here, in the module every other
    module loads first, so that no [Hint ... : mctt] creates it implicitly. *)
Create HintDb mctt discriminated.
