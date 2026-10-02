#[global] Declare Scope mctt_scope.
#[global] Delimit Scope mctt_scope with mctt.
#[global] Bind Scope mctt_scope with Sortclass.

(** [Syntax.cmd], [Command.ccmd] and [Domain.domain] nest through [list]; with
    this scheme registered, their generated induction principles carry the
    induction hypothesis for the list elements (as [list_all]). *)
Scheme All for list.
