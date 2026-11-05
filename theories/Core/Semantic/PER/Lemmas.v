(** * PER Lemmas

    The lemmas on the PERs of the model, in seven parts, each on top of
    the one before:
    - [Basic]: the morphisms of the evaluation relations and the basic
      PERs ([per_bot], [per_top], levels, [per_ne], [per_prop],
      [per_proof]);
    - [Universe]: the universe PER is of one kind, right irrelevant,
      symmetric and transitive; chains of related types;
    - [UniverseSubtyping]: types of levels, the constructors and the
      inversion of the universe PER, cumulativity, [per_subtyp];
    - [ModuleValues]: the module PER [per_dmod] is a PER;
    - [Contexts]: the heads of context PERs, [per_ctx_env] is a PER;
    - [CanonicalContexts]: the canonical context PERs;
    - [Environments]: extending related environments, agreement up to
      retagging, and the readability of kept proofs. *)
From Mctt.Core.Semantic.PER.Lemmas Require Export
  Basic Universe UniverseSubtyping ModuleValues Contexts CanonicalContexts Environments.
