From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Export Definitions.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Fresh.
Import Domain_Notations Fixed_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢a' M ⟸ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢aˣ' Ψ" (at level 70, Ψ at level 69).
Reserved Notation "Γ '⊢aᵖ' Δ" (at level 70, Δ at level 69).
Reserved Notation "Γ '⊢aᵘ' U" (at level 70, U at level 69).
Reserved Notation "Γ '⊢aᵐ' H" (at level 70, H at level 69).
Reserved Notation "Γ '⊢aᵇ' Φ ⇝ Φx" (at level 70, Φ at level 69, Φx at level 69).

Generalizable All Variables.

(** That a normal form is the type of a type: a universe, whose types are
    relevant, [Prop], whose types are propositions, or [LevelSort], whose
    types are types of levels; [κ] is the kind of the types it sorts
    ([sort_kind]).  The side condition of every algorithmic rule that asks
    for a type of some sort.  The universe [u] is the one the type is
    counted in when a [Π] joins its parts: a proposition and a type of
    levels count as the least small universe, as a domain of another kind
    does not bound the universe of a [Π] ([wf_pi]). *)
Variant is_sort_nf : nf -> abs_kind -> universe_nf -> Prop :=
(** A universe: its types are relevant *)
| is_sort_nf_univ : forall W u, is_univ_nf W u -> is_sort_nf W ak_relevant u
(** [Prop]: its types are propositions *)
| is_sort_nf_prop : is_sort_nf Propⁿ ak_propositional (universe_small (ordinal_of_nat 0, nil))
(** [LevelSort]: its types are types of levels *)
| is_sort_nf_level : is_sort_nf LevelSortⁿ ak_level (universe_small (ordinal_of_nat 0, nil)).

#[export]
Hint Constructors is_sort_nf : mctt.

(** A normal form is the type of a type of one sort and universe. *)
Lemma is_sort_nf_functional : forall W r r' u u', is_sort_nf W r u -> is_sort_nf W r' u' -> r = r' /\ u = u'.
Proof.
  intros * H H'; destruct H as [W u Hu | |]; inversion H'; subst;
    try solve [ inversion Hu ]; try solve [ match goal with Hu' : is_univ_nf _ _ |- _ => inversion Hu' end ];
    [ split; [ reflexivity | eapply is_univ_nf_functional; eassumption ] | split; reflexivity | split; reflexivity ].
Qed.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [nfs_agree Γ Ms Rs Ts]: the terms [Ms] and [Rs] have, position by
    position, normal forms equal up to proofs at the types [Ts].  The
    eliminator's rule compares by it the uniform parameters its member's
    type has at the eliminator's uniform parameters with those of the type
    its scrutinee infers. *)
Inductive nfs_agree (Γ : ctx) : list exp -> list exp -> list typ -> Prop :=
(** No term *)
| nfs_agree_nil : nfs_agree Γ nil nil nil
(** The first terms have the normal forms [W] and [W'], equal up to
    proofs, at the first type, then the rest agree *)
| nfs_agree_cons : forall M R T W W' Ms Rs Ts,
    nbe_f Γ M T W ->
    nbe_f Γ R T W' ->
    nf_eq_upto_proofs W W' ->
    nfs_agree Γ Ms Rs Ts ->
    nfs_agree Γ (M :: Ms) (R :: Rs) (T :: Ts).

(** [alg_ty_conv Γ A B]: the types [A] and [B] have normal forms equal up
    to proofs, as completeness gives equal types. *)
Definition alg_ty_conv (Γ : ctx) (A B : typ) : Prop :=
  exists W W', nbe_ty_f Γ A W /\ nbe_ty_f Γ B W' /\ nf_eq_upto_proofs W W'.

(** [nbe_ty_kind Γ A κ]: the type [A] is of the kind [κ], read off its
    value at the initial environment ([domain_kind]): a type of a universe
    has a relevant value, a proposition a propositional one, a type of
    levels one of levels.  It decides the sort of a type the algorithm has
    inferred, which is a normal form, not a subterm, so it is not inferred
    again. *)
Definition nbe_ty_kind (Γ : ctx) (A : typ) (κ : abs_kind) : Prop :=
  exists ρ a, initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ domain_kind a = κ.

Inductive alg_type_check : ctx -> typ -> exp -> Prop :=
| alg_type_check_ati :
  `( Γ ⊢a M ⟹ A ->
     Γ ⊢a A ⊆ B ->
     Γ ⊢a M ⟸ B )
where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) : type_scope
with alg_type_infer : ctx -> nf -> exp -> Prop :=
(** The universes of both tiers infer the universe above.  A small universe's
    level infers a type of levels, and the universe above is the normal form
    of [Type⟨succl M⟩], as the type of an application is the normal form of
    the instantiated codomain: the side condition is a normalisation, not an
    index computed in the conclusion. *)
| alg_type_infer_typ :
  `( Γ ⊢a Typeω@i ⟹ Typeωⁿ@(S i) )
| alg_type_infer_suniv :
  `( Γ ⊢a M ⟹ Levelⁿ@n ->
     nbe_ty_f Γ Type⟨succl M⟩ W ->
     Γ ⊢a Type⟨M⟩ ⟹ W )
(** A type of levels infers the sort of the types of levels ([wf_level]);
    that sort is of no type. *)
| alg_type_infer_level :
  `( Γ ⊢a Level@n ⟹ LevelSortⁿ )
(** A level literal is of the type of levels of its tier, the least one it
    is in; the two operations infer the types of levels of their arguments,
    and are of the larger. *)
| alg_type_infer_llit :
  `( Γ ⊢a 𝕃ᵒ o ⟹ Levelⁿ@(fst o) )
| alg_type_infer_succl :
  `( Γ ⊢a M ⟹ Levelⁿ@n ->
     Γ ⊢a succl M ⟹ Levelⁿ@n )
| alg_type_infer_maxl :
  `( Γ ⊢a M ⟹ Levelⁿ@m ->
     Γ ⊢a N ⟹ Levelⁿ@n ->
     Γ ⊢a maxl M N ⟹ Levelⁿ@(Nat.max m n) )
(** [Prop] is a small type at the least level. *)
| alg_type_infer_prop :
  `( Γ ⊢a Propₘ ⟹ Typeⁿ@0 )
(** [⊤] is a proposition. *)
| alg_type_infer_True :
  `( Γ ⊢a ⊤ ⟹ Propⁿ )
(** The introduction of [⊤] proves it. *)
| alg_type_infer_tt :
  `( Γ ⊢a a_tt ⟹ ⊤ⁿ )
(** [⊥] is a proposition. *)
| alg_type_infer_False :
  `( Γ ⊢a ⊥ ⟹ Propⁿ )
(** Ex falso: the target is a type of a universe or a proposition, never
    a type of levels ([level_closed_sort]), the proof is checked at [⊥],
    and the term infers the target's normal form. *)
| alg_type_infer_absurd :
  `( Γ ⊢a C ⟹ UC ->
     is_sort_nf UC r u ->
     r <> ak_level ->
     Γ ⊢a M ⟸ ⊥ ->
     nbe_ty_f Γ C W ->
     Γ ⊢a efq M return C ⟹ W )
(** The dependent conjunction of two propositions is a proposition. *)
| alg_type_infer_and :
  `( Γ ⊢a P ⟹ Propⁿ ->
     Γ ▹{ak_propositional} P ⊢a Q ⟹ Propⁿ ->
     Γ ⊢a Σₚ P Q ⟹ Propⁿ )
(** A proof of a conjunction: its annotations are propositions, each
    component is checked at its part, and the proof infers the normal form
    of the conjunction. *)
| alg_type_infer_conj :
  `( Γ ⊢a P ⟹ Propⁿ ->
     Γ ▹{ak_propositional} P ⊢a Q ⟹ Propⁿ ->
     Γ ⊢a M ⟸ P ->
     Γ ⊢a N ⟸ Q[Id,,M] ->
     nbe_ty_f Γ (Σₚ P Q) W ->
     Γ ⊢a a_conj P Q M N ⟹ W )
(** The proofs of the components of a proof of a conjunction. *)
| alg_type_infer_left :
  `( Γ ⊢a M ⟹ Σₚⁿ P Q ->
     Γ ⊢a a_left M ⟹ P )
| alg_type_infer_right :
  `( Γ ⊢a M ⟹ Σₚⁿ P Q ->
     nbe_ty_f Γ (nf_to_exp Q)[Id,,a_left M] W ->
     Γ ⊢a a_right M ⟹ W )
(** The type former of a declared member and a constructor of any member
    infer the normal forms of their closed types. *)
| alg_type_infer_ind_case :
  `( ind_lookup gc_deps gc_stack p = Some D ->
     ind_member D k = Some Mk ->
     k < ind_ndecl D ->
     nbe_ty_f Γ (ind_ty D Mk) W ->
     Γ ⊢a a_ind p k ⟹ W )
| alg_type_infer_con :
  `( ind_lookup gc_deps gc_stack p = Some D ->
     ind_member D k = Some Mk ->
     ind_con Mk c = Some gs ->
     nbe_ty_f Γ (con_ty p D k Mk gs) W ->
     Γ ⊢a a_con p k c ⟹ W )
(** The eliminator of the group at [p] at its member [m], at the uniform
    parameters [Us] it carries.  The scrutinee infers the type of the
    member's type former, the declared member [k] of the group at [pc]
    ([im_ref]: the group itself at a declared member, the container's at a
    view).  The uniform parameters are checked at the group's telescope,
    and the uniform arguments of the member's type at them ([im_pre]) have
    the normal forms of the inferred type's; its other parameters [Ns] are
    the member's non-uniform ones.  The blocks are checked at [Us]: the
    scrutinee types at one universe [Typeω@i], each of the member's type
    there, the motives of the eliminator's sort [r] (types of
    [Typeω@i], or propositions), the branches at their types.  The type is
    the normal form of the motive's instance. *)
| alg_type_infer_elim :
  `( Γ ⊢a M ⟹ nf_indty pc k Rs ->
     ind_lookup gc_deps gc_stack p = Some D ->
     ind_member D m = Some Mm ->
     im_ref p m Mm = (pc, k) ->
     ind_lookup gc_deps gc_stack pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Us = ind_nu D ->
     (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
        Γ ⊢a U ⟸ T) ->
     nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs))
       (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
     Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_binder_count b = S (im_nn Mj)) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ ⊢a eb_scrutinee_type b ⟸ Typeω@i) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) (eb_scrutinee_type b)
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        elim_mctx p D j Mj Us ++ Γ ⊢a eb_motive b ⟸ abs_kind_sort r Typeω@i) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
     (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
        n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
     (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
        elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ ⊢a B ⟸ elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
     motive_kind r ->
     nbe_ty_f Γ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] T ->
     Γ ⊢a a_elim r p Us m Bks M ⟹ T )
(** A [Π] is at the join of the universes of its parts ([universe_nf_pi_tm]): a
    large universe absorbs a small one, and two small ones join on levels,
    the codomain's bounded under the binder ([lvl_bound]): an atom that
    mentions the bound variable is bounded by its sort.  The join is the
    normal form of that universe, a side condition rather than the
    conclusion's index: an index computed from the premises makes the
    judgment's inversion non-terminating.  The side conditions on the parts
    are [is_univ_nf] rather than equations on a deciding function, for the
    reason given there.  The codomain's universe is taken normalised
    ([UB']): the bound trusts the sorts its atoms carry, and those of a
    normal form are the sorts of the atoms' types.  (An inferred type is
    already normal, [alg_type_infer_normal], so [UB'] is [UB]; the premise
    is what lets soundness, which that theorem rests on, see it.) *)
(** One rule for every [Π], as [wf_pi]: the domain is a type of the kind
    [κd] the [Π] carries, the codomain one of the kind [κc], at kinds a
    [Π] may join ([pi_kinds]), and the [Π] is of the sort of the kind
    [κc] at that join ([abs_kind_sort]): a type of functions in the join,
    a universal proposition in [Prop], a type of functions between levels
    in [LevelSort].  A proposition and a type of levels count as the
    least small universe ([is_sort_nf]). *)
| alg_type_infer_pi :
  `( Γ ⊢a A ⟹ UA ->
     is_sort_nf UA κd u ->
     Γ ▹{κd} A ⊢a B ⟹ UB ->
     nbe_ty_f (Γ ▹{κd} A) UB UB' ->
     is_sort_nf UB' κc v ->
     pi_kinds κd κc ->
     nbe_ty_f Γ (abs_kind_sort κc (universe_nf_pi_tm u v)) W ->
     Γ ⊢a a_pi κd κc A B ⟹ W )
(** A λ-abstraction, over a type of the kind [κd] its sort says: a
    function, a proof of a [∀] or a function between levels, as the kind
    [κc] of its body's type is ([nbe_ty_kind]), at kinds a [Π] may join
    ([pi_kinds]).  The body's type is no [LevelSort], which is of no sort
    and so no codomain ([wf_fn]). *)
| alg_type_infer_fn :
  `( Γ ⊢a A ⟹ UA ->
     is_sort_nf UA κd u ->
     Γ ▹{κd} A ⊢a M ⟹ B ->
     nf_to_exp B <> LevelSort ->
     nbe_ty_kind (Γ ▹{κd} A) B κc ->
     pi_kinds κd κc ->
     nbe_ty_f Γ A C ->
     Γ ⊢a λ A M ⟹ nf_pi κd κc C B )
(** An application of a function, of a proof of a [∀] or of a function
    between levels. *)
| alg_type_infer_app :
  `( Γ ⊢a M ⟹ nf_pi κd κc A B ->
     Γ ⊢a N ⟸ A ->
     nbe_ty_f Γ B[Id,,N] C ->
     Γ ⊢a M $ N ⟹ C )
(** A local definition: its annotation infers a sort, and the body is
    checked against it; then the body of the [let].  The body's type is no
    [LevelSort], of no sort, and of a kind the binding may build
    ([level_closed_sort]): a type of levels only under a definition of a
    level ([wf_let]). *)
| alg_type_infer_let :
  `( Γ ⊢a A ⟹ UA ->
     is_sort_nf UA r u ->
     Γ ⊢a M ⟸ A ->
     Γ ▸ A ≔ M ⊢a B ⟹ C ->
     nf_to_exp C <> LevelSort ->
     nbe_ty_kind (Γ ▸ A ≔ M) C κC ->
     (κC = ak_level -> r = ak_level) ->
     nbe_ty_f Γ C[Id,,M] D ->
     Γ ⊢a a_let (b_def A M) B ⟹ D )
(** A local module: the body's type is no [LevelSort] and no type of
    levels ([module_body_sort], [wf_let_mod]). *)
| alg_type_infer_let_mod :
  `( Γ ⊢aᵘ U ->
     Γ ▹ₘ U ⊢a B ⟹ C ->
     nf_to_exp C <> LevelSort ->
     nbe_ty_kind (Γ ▹ₘ U) C κC ->
     κC <> ak_level ->
     nbe_ty_f Γ C[Id ,,ₘ me_lit U] D ->
     Γ ⊢a ℓₘ U in B ⟹ D )
(** A member infers the normal form of the term part of what it denotes.
    Neither that type nor the member's δ-reduct is checked: of a well-formed
    module, the one is a type and the other inhabits it. *)
| alg_type_infer_mem :
  `( Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     nbe_ty_f Γ A B ->
     Γ ⊢a a_mem H x ⟹ B )
| alg_type_infer_vlookup :
  `( Γ ∋ #x : A ->
     nbe_ty_f Γ A B ->
     Γ ⊢a #x ⟹ B )
(** A record's type former infers the normal form of its closed type. *)
| alg_type_infer_record :
  `( record_lookup gc_deps gc_stack p = Some R ->
     nbe_ty_f Γ (record_ty R) W ->
     Γ ⊢a a_record p ⟹ W )
(** A tuple: its annotation is a type whose normal form is the record
    type at normal parameters [Rs], and each field is checked at its type
    at [Rs] and the fields before it; the tuple infers that normal form. *)
| alg_type_infer_tuple :
  `( Γ ⊢a T ⟹ UT ->
     is_univ_nf UT u ->
     nbe_ty_f Γ T (nf_record p Rs) ->
     record_lookup gc_deps gc_stack p = Some R ->
     List.map fst fs = List.map fst (record_fields R) ->
     (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
        Γ ⊢a M ⟸ U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))]) ->
     Γ ⊢a a_tuple T fs ⟹ nf_record p Rs )
(** A projection: the element infers a record type at normal parameters
    [Rs]; the field is the first one so named, and the projection infers
    the normal form of its type at [Rs] and the projections before it. *)
| alg_type_infer_proj :
  `( Γ ⊢a M ⟹ nf_record p Rs ->
     record_lookup gc_deps gc_stack p = Some R ->
     field_index (record_fields R) f = Some k ->
     List.nth_error (record_fields R) k = Some (f, U) ->
     nbe_ty_f Γ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] W ->
     Γ ⊢a a_proj f M ⟹ W )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope
(** The well-formedness of extensions, units and module expressions, entry by
    entry, part by part. *)
with alg_ext : ctx -> ctx -> Prop :=
| alg_ext_nil :
  `( Γ ⊢aˣ ⋅ )
(** An assumption of a type of either sort *)
| alg_ext_ass :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_sort_nf UA κ u ->
     Γ ⊢aˣ Ψ ▹{κ} A )
(** A definition of a type of either sort, its body checked against it *)
| alg_ext_def :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_sort_nf UA r u ->
     Ψ ++ Γ ⊢a M ⟸ A ->
     Γ ⊢aˣ Ψ ▸ A ≔ M )
| alg_ext_mod :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢aᵘ U ->
     Γ ⊢aˣ Ψ ▹ₘ U )
(** A definition with a module part: as a definition and as a module slot. *)
| alg_ext_dm :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Ψ ++ Γ ⊢a M ⟸ A ->
     Ψ ++ Γ ⊢aᵘ U ->
     Γ ⊢aˣ Ψ ▸ₘ A ≔ M ‖ U )
where "Γ '⊢aˣ' Ψ" := (alg_ext Γ Ψ) : type_scope
(** The parameters of a unit: assumptions, each of a type of a universe
    (the premise (R) of the unit rules).  A proposition is no parameter. *)
with alg_params : ctx -> ctx -> Prop :=
(** No parameter *)
| alg_params_nil :
  `( Γ ⊢aᵖ ⋅ )
(** A parameter, of a type that infers a universe *)
| alg_params_ass :
  `( Γ ⊢aᵖ Δ ->
     Δ ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢aᵖ Δ ▹{ak_relevant} A )
(** A parameter of a type of levels, which infers the sort of the types
    of levels ([parameter_sort]) *)
| alg_params_level :
  `( Γ ⊢aᵖ Δ ->
     Δ ++ Γ ⊢a A ⟹ LevelSortⁿ ->
     Γ ⊢aᵖ Δ ▹{ak_level} A )
where "Γ '⊢aᵖ' Δ" := (alg_params Γ Δ) : type_scope
with alg_unit : ctx -> gunit -> Prop :=
(** A body: its parameters, and its entries, each read as it stands in the
    expansion of the body before it.  What the body denotes can be
    abstracted over the parameters ([levels_abstractable]), as the
    declarative rule asks: [module A (n : ℕ) ≔ M], where [M] has
    [def v : Level ≔ 0l], is rejected, [module A (u : Level) ≔ M]
    accepted. *)
| alg_unit_body :
  `( Γ ⊢aᵖ Δ ->
     all_assumptions Δ ->
     Δ ++ Γ ⊢aᵇ Φ ⇝ Φx ->
     body_shape Φ Φ ->
     body_shape Φx Φx ->
     List.NoDup (gm_names Φ) ->
     levels_abstractable gc_deps gc_stack Γ Δ (me_lit (gu_open nil Φ)) ->
     Γ ⊢aᵘ gu_open Δ Φ )
(** An alias, its target abstractable over the parameters, as for a body *)
| alg_unit_alias :
  `( Γ ⊢aᵖ Δ ->
     all_assumptions Δ ->
     Δ ++ Γ ⊢aᵐ E ->
     levels_abstractable gc_deps gc_stack Γ Δ E ->
     Γ ⊢aᵘ gu_mk Δ (md_alias E) )
where "Γ '⊢aᵘ' U" := (alg_unit Γ U) : type_scope
(** [Γ ⊢aᵇ Φ ⇝ Φx]: the entries of [Φ] are well-formed in [Γ], each in the
    context the expansion of the body before it makes, and [Φx] is the
    expansion.  The entries a local open generates are not checked again:
    they are the members of a well-formed module at their types. *)
with alg_body : ctx -> gmod -> gmod -> Prop :=
| alg_body_nil :
  `( Γ ⊢aᵇ gm_nil ⇝ gm_nil )
(** A definition, of a type of the sort its tag [r] says *)
| alg_body_def :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢a A ⟹ UA ->
     is_sort_nf UA r u ->
     body_ctx Φx ++ Γ ⊢a M ⟸ A ->
     Γ ⊢aᵇ gm_ext Φ x (ge_def b pv r A (Some M)) ⇝ gm_ext Φx x (ge_def b pv r A (Some M)) )
| alg_body_mod :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢aᵘ U ->
     Γ ⊢aᵇ gm_ext Φ x (ge_mod pm U) ⇝ gm_ext Φx x (ge_mod pm U) )
(** A definition with a module part: its term part as a definition, its
    unit as a submodule. *)
| alg_body_dm :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     body_ctx Φx ++ Γ ⊢a M ⟸ A ->
     body_ctx Φx ++ Γ ⊢aᵘ U ->
     Γ ⊢aᵇ gm_ext Φ x (ge_def_mod pv A M U) ⇝ gm_ext Φx x (ge_def_mod pv A M U) )
| alg_body_open :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack (body_ctx Φx ++ Γ) H R ->
     mdesc_mod R = Some Rm ->
     items_gen gc_deps gc_stack (body_ctx Φx ++ Γ) H its gs ->
     items_ok its ->
     (** The entries the open stores are the ones its items generate, as
         [body_xp_open] has them *)
     Φg = gens_body gs ->
     Γ ⊢aᵇ gm_open Φ H its Φg ⇝ gens_append Φx 0 gs )
where "Γ '⊢aᵇ' Φ ⇝ Φx" := (alg_body Γ Φ Φx) : type_scope
with alg_modexp : ctx -> modexp -> Prop :=
| alg_modexp_unit :
  `( mdenote gc_deps gc_stack Γ (me_unit fp) R ->
     mdesc_mod_tele R = Some T ->
     Γ ⊢aᵐ me_unit fp )
| alg_modexp_var :
  `( Γ ∋ #x ≔ₘ U ->
     Γ ⊢aᵐ me_var x )
| alg_modexp_lit :
  `( Γ ⊢aᵘ U ->
     Γ ⊢aᵐ me_lit U )
| alg_modexp_mem :
  `( Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack Γ (me_mem H y) R ->
     mdesc_mod_tele R = Some T ->
     Γ ⊢aᵐ me_mem H y )
(** An argument is checked against the outermost parameter of the
    telescope. *)
| alg_modexp_app :
  `( Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack Γ H R ->
     mdesc_mod_tele R = Some T ->
     tele_view T = Some (B, T1) ->
     Γ ⊢a N ⟸ B ->
     Γ ⊢aᵐ me_app H N )
where "Γ '⊢aᵐ' H" := (alg_modexp Γ H) : type_scope.

Hint Constructors alg_type_check alg_type_infer alg_ext alg_params alg_unit alg_body alg_modexp : mctt.

End Fixed_GCtx.

Notation "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) : type_scope.
Notation "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope.
Notation "Γ '⊢aˣ' Ψ" := (alg_ext Γ Ψ) : type_scope.
Notation "Γ '⊢aᵖ' Δ" := (alg_params Γ Δ) : type_scope.
Notation "Γ '⊢aᵘ' U" := (alg_unit Γ U) : type_scope.
Notation "Γ '⊢aᵐ' H" := (alg_modexp Γ H) : type_scope.
Notation "Γ '⊢aᵇ' Φ ⇝ Φx" := (alg_body Γ Φ Φx) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer alg_ext alg_params alg_unit alg_body alg_modexp : mctt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop
with alg_ext_mut_ind := Induction for alg_ext Sort Prop
with alg_params_mut_ind := Induction for alg_params Sort Prop
with alg_unit_mut_ind := Induction for alg_unit Sort Prop
with alg_body_mut_ind := Induction for alg_body Sort Prop
with alg_modexp_mut_ind := Induction for alg_modexp Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind,
  alg_ext_mut_ind,
  alg_params_mut_ind,
  alg_unit_mut_ind,
  alg_body_mut_ind,
  alg_modexp_mut_ind.


(** ** User Expressions

    The expressions the type checker accepts.  Every [exp] is one
    ([user_exp_all]); the predicate exists because [type_check_closed] is
    indexed by it. *)
Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_univ :
  `( user_exp M ->
     user_exp (a_univ M) )
| user_exp_level :
  `( user_exp (a_level n) )
(** The sort of the types of levels *)
| user_exp_level_sort :
  `( user_exp a_level_sort )
| user_exp_llit :
  `( user_exp (a_llit n) )
| user_exp_succl :
  `( user_exp M ->
     user_exp (a_succl M) )
| user_exp_maxl :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_maxl M N) )
(** [Prop] *)
| user_exp_prop :
  `( user_exp a_prop )
| user_exp_True :
  `( user_exp a_True )
(** The introduction of [⊤] *)
| user_exp_tt :
  `( user_exp a_tt )
| user_exp_False :
  `( user_exp a_False )
(** Ex falso: its target and its proof *)
| user_exp_absurd :
  `( user_exp C ->
     user_exp M ->
     user_exp (a_absurd C M) )
(** A conjunction, its proofs and their components *)
| user_exp_and :
  `( user_exp P ->
     user_exp Q ->
     user_exp (a_and P Q) )
| user_exp_conj :
  `( user_exp P ->
     user_exp Q ->
     user_exp M ->
     user_exp N ->
     user_exp (a_conj P Q M N) )
| user_exp_left :
  `( user_exp M ->
     user_exp (a_left M) )
| user_exp_right :
  `( user_exp M ->
     user_exp (a_right M) )
| user_exp_indty :
  `( user_exp (a_ind p k) )
| user_exp_con :
  `( user_exp (a_con p k c) )
(** An eliminator: its uniform parameters, the scrutinee types, motives
    and branches of its blocks, and its scrutinee. *)
| user_exp_elim :
  `( (forall U, List.In U Us -> user_exp U) ->
     (forall b, List.In b Bks -> user_exp (eb_scrutinee_type b)) ->
     (forall b, List.In b Bks -> user_exp (eb_motive b)) ->
     (forall b br, List.In b Bks -> List.In br (eb_brs b) -> user_exp (snd br)) ->
     user_exp M ->
     user_exp (a_elim r p Us m Bks M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi κd κc A B) )
| user_exp_fn :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_fn A M) )
| user_exp_app :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_app M N) )
| user_exp_let :
  `( user_exp A ->
     user_exp M ->
     user_exp B ->
     user_exp (ℓ A ≔ M in B) )
| user_exp_let_mod :
  `( user_exp B ->
     user_exp (ℓₘ U in B) )
| user_exp_mem :
  `( user_exp (a_mem H x) )
| user_exp_vlookup :
  `( user_exp (a_var x) )
(** A record type's former *)
| user_exp_record :
  `( user_exp (a_record p) )
(** A record element: its type and its fields *)
| user_exp_tuple :
  `( user_exp T ->
     (forall fM, List.In fM fs -> user_exp (snd fM)) ->
     user_exp (a_tuple T fs) )
(** A field *)
| user_exp_proj :
  `( user_exp M ->
     user_exp (a_proj f M) ).

#[export]
Hint Constructors user_exp : mctt.

Lemma user_exp_all : forall M, user_exp M.
Proof.
  eapply proj1, (syn_mut_ind user_exp (fun _ => True)
    (fun b => match b with b_def A M => user_exp A /\ user_exp M | b_mod _ => True end)
    (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True));
    intros; try destruct_conjs; try match goal with b : binding |- _ => destruct b; cbn in *; destruct_conjs end;
    try lazymatch goal with
      | HU : List.Forall user_exp ?Us, HB : List.Forall _ ?Bks |- user_exp (a_elim _ _ ?Us _ ?Bks _) =>
          rewrite List.Forall_forall in HU, HB;
          constructor; [ exact HU
                       | intros b Hb; exact (proj1 (HB b Hb))
                       | intros b Hb; exact (proj1 (proj2 (HB b Hb)))
                       | intros b br Hb Hbr; exact (proj1 (List.Forall_forall _ _) (proj2 (proj2 (HB b Hb))) br Hbr)
                       | assumption ]
      | HF : List.Forall _ ?fs |- user_exp (a_tuple _ ?fs) =>
          rewrite List.Forall_forall in HF; constructor; [ assumption | exact HF ]
      end;
    mauto 3.
Qed.

#[export]
Hint Resolve user_exp_all : mctt.

Lemma user_exp_nf : forall M, user_exp (nf_to_exp M)
with user_exp_ne : forall M, user_exp (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.

#[export]
Hint Constructors is_univ_nf : mctt.
#[export]
Hint Resolve is_univ_nf_univ_nf : mctt.

(** The universes as normal forms, for the rewriting the universe cases need:
    the coercion [nf_to_exp] does not unfold by [rewrite] on its own. *)
Lemma nf_to_exp_typ : forall i, nf_to_exp Typeωⁿ@i = Typeω@i.
Proof. reflexivity. Qed.

Lemma nf_to_exp_univ : forall n, nf_to_exp Typeⁿ@n = Type@n.
Proof. reflexivity. Qed.

(** Normalises the universes a derivation reads back, whichever of the three
    spellings they are in. *)
Ltac simpl_univ_nf := rewrite ?nf_to_exp_univ_nf, ?nf_to_exp_typ, ?nf_to_exp_univ in *.
