(** * Values Whose Kept Proofs Are Typed

    The gluing model is closed under the PERs, which relate a kept proof
    to any proof ([KeptProofs.v]), so it says nothing of the readback of a
    value's own kept proofs.  This file states that fact as a separate,
    structural predicate on values, [kept_proofs_typed Δ v], read at the
    context [Δ] the value is read back in: every kept proof [⋆ᵈ⟨N, ρ⟩]
    inside [v] is the proof [N] of a proposition [P] typed in a context
    [Γ], over an environment glued in [Δ] for [Γ] ([env_glued]).  The
    gluing is not changed, and its lemmas keep holding.

    A kept proof is read back only once its closure is evaluated, so the
    closures inside a value carry the same fact: each environment is glued
    for a context in which the closure's body is typed, and the entries of
    the environment satisfy the predicate in turn.  Values without
    closures or kept proofs satisfy it by their parts. *)

From Stdlib Require Import List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness.LogicalRelation Require Import Definitions.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [ρ] is glued in [Δ] for the context [Γ]: at some substitution of the
    gluing of [Γ]. *)
Definition env_glued (Δ Γ : ctx) (ρ : env) : Prop :=
  exists Sb σ, EG Γ ∈ glu_ctx_env ↘ Sb /\ Δ ⊢ˢ σ ® ρ ∈ Sb.

Section KeptProofsTyped.
  Variable (Δ : ctx).

  (** [kept_proofs_typed v]: every kept proof inside the value [v], and
      every closure, is typed over an environment glued in [Δ]; mutually
      for neutrals, normal values, module values, environment entries and
      the types entries are stored at. *)
  Inductive kept_proofs_typed : domain -> Prop :=
  (** A [Π]: its domain, and its codomain typed over its environment at a
      type whose value is the domain *)
  | kept_proofs_typed_pi : forall κd κc a ρ B,
      kept_proofs_typed a ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ A (i : nat), env_glued Δ Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i) ->
      kept_proofs_typed (d_pi κd κc a ρ B)
  (** A large universe *)
  | kept_proofs_typed_univ : forall i, kept_proofs_typed (d_univ i)
  (** A small universe, by its level *)
  | kept_proofs_typed_suniv : forall l, kept_proofs_typed l -> kept_proofs_typed (d_suniv l)
  (** A type of levels *)
  | kept_proofs_typed_level : forall n, kept_proofs_typed (d_level n)
  (** The sort of the types of levels *)
  | kept_proofs_typed_level_sort : kept_proofs_typed d_level_sort
  (** A level, by the neutrals of its atoms *)
  | kept_proofs_typed_lvl : forall c xs,
      (forall j s m, List.In (j, s, m) xs -> kept_proofs_typed_ne m) ->
      kept_proofs_typed (d_lvl c xs)
  (** [Prop] *)
  | kept_proofs_typed_prop : kept_proofs_typed d_prop
  (** [⊤] *)
  | kept_proofs_typed_True : kept_proofs_typed d_True
  (** A kept proof: the proof of a proposition typed in a context its
      environment is glued for, whose entries satisfy the predicate *)
  | kept_proofs_typed_proof : forall N ρ,
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ P, env_glued Δ Γ ρ /\ Γ ⊢ N : P /\ Γ ⊢ P : Propₘ) ->
      kept_proofs_typed (d_proof N ρ)
  (** [⊥] *)
  | kept_proofs_typed_False : kept_proofs_typed d_False
  (** A [Σₚ], as a [Π] into [Prop] *)
  | kept_proofs_typed_and : forall a ρ Q,
      kept_proofs_typed a ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ A, env_glued Δ Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ Γ ▹{ak_propositional} A ⊢ Q : Propₘ) ->
      kept_proofs_typed (d_and a ρ Q)
  (** A function: its domain, and its body typed over its environment *)
  | kept_proofs_typed_fn : forall a ρ M,
      kept_proofs_typed a ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ κ A B, env_glued Δ Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ Γ ▹{κ} A ⊢ M : B) ->
      kept_proofs_typed (d_fn a ρ M)
  (** A neutral, by its type and itself *)
  | kept_proofs_typed_neut : forall a m,
      kept_proofs_typed a -> kept_proofs_typed_ne m -> kept_proofs_typed (d_neut a m)
  (** A member of a module lacking arguments, by its module *)
  | kept_proofs_typed_member : forall h ch,
      kept_proofs_typed_mod h -> kept_proofs_typed (d_member h ch)
  (** A type former of a group, by its parameters *)
  | kept_proofs_typed_indty : forall p k as',
      (forall v, List.In v as' -> kept_proofs_typed v) -> kept_proofs_typed (d_ind p k as')
  (** A constructor, by its arguments *)
  | kept_proofs_typed_con : forall p k c vs,
      (forall v, List.In v vs -> kept_proofs_typed v) -> kept_proofs_typed (d_con p k c vs)
  (** A recursive result: its argument and the group's parameters, and the
      blocks typed over its environment *)
  | kept_proofs_typed_ihfn : forall ρ Bks p ups t i f,
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (forall v, List.In v ups -> kept_proofs_typed v) ->
      kept_proofs_typed f ->
      (exists Γ D Us r (j : nat), env_glued Δ Γ ρ /\ blocks_typed gc_deps gc_stack Γ p D Us Bks r j) ->
      kept_proofs_typed (d_ihfn ρ Bks p ups t i f)
  (** The codomain family of an argument's type: the group's parameters,
      and the domain typed over its environment *)
  | kept_proofs_typed_shfam : forall p ups ρ B t,
      (forall v, List.In v ups -> kept_proofs_typed v) ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ T, env_glued Δ Γ ρ /\ Γ ⊢ B : T) ->
      kept_proofs_typed (d_shfam p ups ρ B t)
  (** The codomain family of a recursive result's type: the motives', the
      group's parameters, the argument, and the domain typed over its
      environment *)
  | kept_proofs_typed_ihfam : forall ρm As p ups ρ B t i f,
      (forall x, x < List.length ρm -> kept_proofs_typed_entry (env_entry ρm x)) ->
      (forall v, List.In v ups -> kept_proofs_typed v) ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      kept_proofs_typed f ->
      (exists Γm Γ T, env_glued Δ Γm ρm /\ env_glued Δ Γ ρ /\ Γ ⊢ B : T /\
         forall A, List.In A As -> exists Tm, Γm ⊢ A : Tm) ->
      kept_proofs_typed (d_ihfam ρm As p ups ρ B t i f)
  (** A record type, by its parameters *)
  | kept_proofs_typed_record : forall p ns,
      (forall v, List.In v ns -> kept_proofs_typed v) -> kept_proofs_typed (d_record p ns)
  (** A record value, by its fields *)
  | kept_proofs_typed_tuple : forall fs,
      (forall f v, List.In (f, v) fs -> kept_proofs_typed v) -> kept_proofs_typed (d_tuple fs)
  with kept_proofs_typed_ne : domain_ne -> Prop :=
  (** A variable *)
  | kept_proofs_typed_ne_var : forall x, kept_proofs_typed_ne (d_var x)
  (** An application, by its function and its argument *)
  | kept_proofs_typed_ne_app : forall m n,
      kept_proofs_typed_ne m -> kept_proofs_typed_nf n -> kept_proofs_typed_ne (d_app m n)
  (** Ex falso, by its type and its proof *)
  | kept_proofs_typed_ne_absurd : forall c h,
      kept_proofs_typed c -> kept_proofs_typed h -> kept_proofs_typed_ne (d_absurd c h)
  (** A global *)
  | kept_proofs_typed_ne_glob : forall p, kept_proofs_typed_ne (d_glob p)
  (** A stuck elimination: its scrutinee, the group's parameters and the
      member's, and the blocks typed over its environment *)
  | kept_proofs_typed_ne_elim : forall ρ Bks p ups m as' e,
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (forall v, List.In v ups -> kept_proofs_typed v) ->
      (forall v, List.In v as' -> kept_proofs_typed v) ->
      kept_proofs_typed_ne e ->
      (exists Γ D Us r (j : nat), env_glued Δ Γ ρ /\ blocks_typed gc_deps gc_stack Γ p D Us Bks r j) ->
      kept_proofs_typed_ne (d_elim ρ Bks p ups m as' e)
  (** A projection of a neutral *)
  | kept_proofs_typed_ne_proj : forall f m,
      kept_proofs_typed_ne m -> kept_proofs_typed_ne (d_proj f m)
  with kept_proofs_typed_nf : domain_nf -> Prop :=
  (** A value at a type, by both *)
  | kept_proofs_typed_nf_dom : forall a m,
      kept_proofs_typed a -> kept_proofs_typed m -> kept_proofs_typed_nf (d_dom a m)
  with kept_proofs_typed_mod : dmod -> Prop :=
  (** A global module, by its arguments *)
  | kept_proofs_typed_mod_global : forall p args,
      (forall v, List.In v args -> kept_proofs_typed v) -> kept_proofs_typed_mod (dm_global p args)
  (** The closure of a unit: its environment's entries, and the unit
      typed over the context its environment is glued for *)
  | kept_proofs_typed_mod_local : forall Θc D ρ,
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ, env_glued Δ Γ ρ /\ gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk Θc D ≈ gu_mk Θc D) ->
      kept_proofs_typed_mod (dm_local Θc D ρ)
  (** A submodule of a module lacking arguments, by the module *)
  | kept_proofs_typed_mod_member : forall h ch,
      kept_proofs_typed_mod h -> kept_proofs_typed_mod (dm_member h ch)
  with kept_proofs_typed_entry : dentry -> Prop :=
  (** A term entry, by its value and its stored type *)
  | kept_proofs_typed_entry_term : forall v t,
      kept_proofs_typed v -> kept_proofs_typed_entry_type t -> kept_proofs_typed_entry (de_term v t)
  (** A module entry, by its module *)
  | kept_proofs_typed_entry_mod : forall h U,
      kept_proofs_typed_mod h -> kept_proofs_typed_entry (de_mod h U)
  (** A definition with a module part, by its parts *)
  | kept_proofs_typed_entry_dm : forall v t h U,
      kept_proofs_typed v -> kept_proofs_typed_entry_type t -> kept_proofs_typed_mod h ->
      kept_proofs_typed_entry (de_dm v t h U)
  with kept_proofs_typed_entry_type : entry_type -> Prop :=
  (** A type value *)
  | kept_proofs_typed_entry_type_value : forall a,
      kept_proofs_typed a -> kept_proofs_typed_entry_type (entry_type_value a)
  (** A type in an environment: typed over it *)
  | kept_proofs_typed_entry_type_closure : forall A ρ,
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      (exists Γ T, env_glued Δ Γ ρ /\ Γ ⊢ A : T) ->
      kept_proofs_typed_entry_type (entry_type_closure A ρ)
  (** The type of a recursive argument, by the group's parameters and its
      environment *)
  | kept_proofs_typed_entry_type_shape : forall p ups ρ t,
      (forall v, List.In v ups -> kept_proofs_typed v) ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      kept_proofs_typed_entry_type (entry_type_shape p ups ρ t)
  (** The type of a recursive result, by its parts *)
  | kept_proofs_typed_entry_type_ih : forall ρm As p ups ρ t v i,
      (forall x, x < List.length ρm -> kept_proofs_typed_entry (env_entry ρm x)) ->
      (forall w, List.In w ups -> kept_proofs_typed w) ->
      (forall x, x < List.length ρ -> kept_proofs_typed_entry (env_entry ρ x)) ->
      kept_proofs_typed v ->
      kept_proofs_typed_entry_type (entry_type_induction_hypothesis ρm As p ups ρ t v i)
  (** No type *)
  | kept_proofs_typed_entry_type_none : kept_proofs_typed_entry_type entry_type_none.

End KeptProofsTyped.

(** Every entry of an environment satisfies the predicate. *)
Definition env_kept_proofs_typed (Δ : ctx) (ρ : env) : Prop :=
  forall x, x < List.length ρ -> kept_proofs_typed_entry Δ (env_entry ρ x).

End Fixed_GCtx.
