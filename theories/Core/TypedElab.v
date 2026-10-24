(** * The Typed Elaboration of Commands

    The second level of elaboration, done by the command judgment before a
    command runs: one typed fill of its literals, eliminators and accesses
    through terms ([Fill]), the group and uniform parameters of an
    eliminator read off its scrutinee's type ([ElimTarget]), and the
    fill's functionality ([Lemmas]). *)

From Mctt.Core.TypedElab Require Export ElimTarget Fill Lemmas.
