From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Export Definitions.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Fresh.
Import Domain_Notations Fixed_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢a' M ⟸ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢aˣ' Ψ" (at level 70, Ψ at level 69).
Reserved Notation "Γ '⊢aᵘ' U" (at level 70, U at level 69).
Reserved Notation "Γ '⊢aᵐ' H" (at level 70, H at level 69).
Reserved Notation "Γ '⊢aᵇ' Φ ⇝ Φx" (at level 70, Φ at level 69, Φx at level 69).

Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [nfs_agree Γ Ms Rs Ts]: the terms [Ms] and [Rs] have, position by
    position, the same normal form at the types [Ts].  The eliminator's
    rule compares by it the uniform parameters its member's type has at
    the eliminator's uniform parameters with those of the type its
    scrutinee infers. *)
Inductive nfs_agree (Γ : ctx) : list exp -> list exp -> list typ -> Prop :=
(** No term *)
| nfs_agree_nil : nfs_agree Γ nil nil nil
(** The first terms have the normal form [W] at the first type, then the
    rest agree *)
| nfs_agree_cons : forall M R T W Ms Rs Ts,
    nbe_f Γ M T W ->
    nbe_f Γ R T W ->
    nfs_agree Γ Ms Rs Ts ->
    nfs_agree Γ (M :: Ms) (R :: Rs) (T :: Ts).

(** [alg_ty_conv Γ A B]: the types [A] and [B] have one normal form. *)
Definition alg_ty_conv (Γ : ctx) (A B : typ) : Prop := exists W, nbe_ty_f Γ A W /\ nbe_ty_f Γ B W.

Inductive alg_type_check : ctx -> typ -> exp -> Prop :=
| atc_ati :
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
| ati_typ :
  `( Γ ⊢a Typeω@i ⟹ Typeωⁿ@(S i) )
| ati_suniv :
  `( Γ ⊢a M ⟹ Levelⁿ@n ->
     nbe_ty_f Γ Type⟨succl M⟩ W ->
     Γ ⊢a Type⟨M⟩ ⟹ W )
(** The closed small types infer the least universe. *)
| ati_level :
  `( Γ ⊢a Level@n ⟹ Typeⁿ@0 )
(** A level literal is of the type of levels of its tier, the least one it
    is in; the two operations infer the types of levels of their arguments,
    and are of the larger. *)
| ati_llit :
  `( Γ ⊢a 𝕃ᵒ o ⟹ Levelⁿ@(fst o) )
| ati_succl :
  `( Γ ⊢a M ⟹ Levelⁿ@n ->
     Γ ⊢a succl M ⟹ Levelⁿ@n )
| ati_maxl :
  `( Γ ⊢a M ⟹ Levelⁿ@m ->
     Γ ⊢a N ⟹ Levelⁿ@n ->
     Γ ⊢a maxl M N ⟹ Levelⁿ@(Nat.max m n) )
| ati_True :
  `( Γ ⊢a ⊤ ⟹ Typeⁿ@0 )
| ati_true :
  `( Γ ⊢a ⋆ ⟹ ⊤ⁿ )
| ati_False :
  `( Γ ⊢a ⊥ ⟹ Typeⁿ@0 )
| ati_exfalso :
  `( Γ ▹ ⊥ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢a M ⟸ ⊥ ->
     nbe_ty_f Γ A[Id,,M] B ->
     Γ ⊢a efq M return A ⟹ B )
(** The type former of a declared member and a constructor of any member
    infer the normal forms of their closed types. *)
| ati_ind :
  `( ind_lookup gc_deps gc_stack p = Some D ->
     ind_member D k = Some Mk ->
     k < ind_ndecl D ->
     nbe_ty_f Γ (ind_ty D Mk) W ->
     Γ ⊢a a_ind p k ⟹ W )
| ati_con :
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
    annotations and the motives at one universe [Typeω@i], an annotation
    of the member's type there, the branches at their types.  The type is
    the normal form of the motive's instance. *)
| ati_elim :
  `( Γ ⊢a M ⟹ nf_indty pc k Rs ->
     ind_lookup gc_deps gc_stack p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     im_ref p m Mm = (pc, k) ->
     ind_lookup gc_deps gc_stack pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = List.length (ind_members D) ->
     List.length Us = ind_nu D ->
     (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
        Γ ⊢a U ⟸ T) ->
     nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs))
       (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
     Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_nm b = S (im_nn Mj)) ->
     (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
        tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ ⊢a Z ⟸ Typeω@i) ->
     (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        elim_mctx p D j Mj Us ++ Γ ⊢a eb_motive b ⟸ Typeω@i) ->
     (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
     (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
        n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat) ->
     (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
        elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊢a B ⟸ elim_bty p j Mj c gs (eb_motive b) Us) ->
     nbe_ty_f Γ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] T ->
     Γ ⊢a a_elim oq Us m Bks M ⟹ T )
(** A [Π] is at the join of the universes of its parts ([unf_pi_tm]): a
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
| ati_pi :
  `( Γ ⊢a A ⟹ UA ->
     Γ ▹ A ⊢a B ⟹ UB ->
     is_univ_nf UA u ->
     nbe_ty_f (Γ ▹ A) UB UB' ->
     is_univ_nf UB' v ->
     nbe_ty_f Γ (unf_pi_tm u v) W ->
     Γ ⊢a Π A B ⟹ W )
| ati_fn :
  `( Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ▹ A ⊢a M ⟹ B ->
     nbe_ty_f Γ A C ->
     Γ ⊢a λ A M ⟹ Πⁿ C B )
| ati_app :
  `( Γ ⊢a M ⟹ Πⁿ A B ->
     Γ ⊢a N ⟸ A ->
     nbe_ty_f Γ B[Id,,N] C ->
     Γ ⊢a M $ N ⟹ C )
(** A local definition: an annotation is a type and the body is checked
    against it; without one, the body infers the type.  Then the body of the
    [let].  The two cases are premises under the annotation they are about,
    so that the induction principle has a hypothesis for each. *)
| ati_let :
  `( let_ann oA A ->
     (oA = Some A -> Γ ⊢a A ⟹ UA) ->
     (oA = Some A -> is_univ_nf UA u) ->
     (oA = Some A -> Γ ⊢a M ⟸ A) ->
     (oA = None -> Γ ⊢a M ⟹ W) ->
     (oA = None -> A = nf_to_exp W) ->
     Γ ▸ A ≔ M ⊢a B ⟹ C ->
     nbe_ty_f Γ C[Id,,M] D ->
     Γ ⊢a a_let (b_def oA M) B ⟹ D )
| ati_let_mod :
  `( Γ ⊢aᵘ U ->
     Γ ▹ₘ U ⊢a B ⟹ C ->
     nbe_ty_f Γ C[Id ,,ₘ me_lit U] D ->
     Γ ⊢a ℓₘ U in B ⟹ D )
(** A member infers the normal form of the term part of what it denotes.
    Neither that type nor the member's δ-reduct is checked: of a well-formed
    module, the one is a type and the other inhabits it. *)
| ati_mem :
  `( Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack Γ (me_mem H x) R ->
     ds_ty R = Some A ->
     nbe_ty_f Γ A B ->
     Γ ⊢a a_mem H x ⟹ B )
| ati_vlookup :
  `( Γ ∋ #x : A ->
     nbe_ty_f Γ A B ->
     Γ ⊢a #x ⟹ B )
(** A record's type former infers the normal form of its closed type. *)
| ati_record :
  `( record_lookup gc_deps gc_stack p = Some R ->
     nbe_ty_f Γ (record_ty R) W ->
     Γ ⊢a a_record p ⟹ W )
(** A tuple: its annotation is a type whose normal form is the record
    type at normal parameters [Rs], and each field is checked at its type
    at [Rs] and the fields before it; the tuple infers that normal form. *)
| ati_tuple :
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
| ati_proj :
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
| aext_nil :
  `( Γ ⊢aˣ ⋅ )
| aext_ass :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢aˣ Ψ ▹ A )
| aext_def :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Ψ ++ Γ ⊢a M ⟸ A ->
     Γ ⊢aˣ Ψ ▸ A ≔ M )
| aext_mod :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢aᵘ U ->
     Γ ⊢aˣ Ψ ▹ₘ U )
where "Γ '⊢aˣ' Ψ" := (alg_ext Γ Ψ) : type_scope
with alg_unit : ctx -> gunit -> Prop :=
(** A body: its parameters, and its entries, each read as it stands in the
    expansion of the body before it. *)
| aunit_body :
  `( Γ ⊢aˣ Δ ->
     tele_ass Δ ->
     Δ ++ Γ ⊢aᵇ Φ ⇝ Φx ->
     body_shape Φ Φ ->
     body_shape Φx Φx ->
     List.NoDup (gm_names Φ) ->
     Γ ⊢aᵘ gu_open Δ Φ )
| aunit_alias :
  `( Γ ⊢aˣ Δ ->
     tele_ass Δ ->
     Δ ++ Γ ⊢aᵐ E ->
     Γ ⊢aᵘ gu_mk Δ (md_alias E) )
where "Γ '⊢aᵘ' U" := (alg_unit Γ U) : type_scope
(** [Γ ⊢aᵇ Φ ⇝ Φx]: the entries of [Φ] are well-formed in [Γ], each in the
    context the expansion of the body before it makes, and [Φx] is the
    expansion.  The entries a local open generates are not checked again:
    they are the members of a well-formed module at their types. *)
with alg_body : ctx -> gmod -> gmod -> Prop :=
| abody_nil :
  `( Γ ⊢aᵇ gm_nil ⇝ gm_nil )
| abody_def :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     body_ctx Φx ++ Γ ⊢a M ⟸ A ->
     Γ ⊢aᵇ gm_ext Φ x (ge_def b pv A (Some M)) ⇝ gm_ext Φx x (ge_def b pv A (Some M)) )
| abody_mod :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢aᵘ U ->
     Γ ⊢aᵇ gm_ext Φ x (ge_mod pm U) ⇝ gm_ext Φx x (ge_mod pm U) )
| abody_open :
  `( Γ ⊢aᵇ Φ ⇝ Φx ->
     body_ctx Φx ++ Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack (body_ctx Φx ++ Γ) H R ->
     ds_mod R = Some Rm ->
     items_gen gc_deps gc_stack false (body_ctx Φx ++ Γ) H its gs ->
     items_ok its ->
     Γ ⊢aᵇ gm_open Φ H its ⇝ gens_append Φx 0 gs )
where "Γ '⊢aᵇ' Φ ⇝ Φx" := (alg_body Γ Φ Φx) : type_scope
with alg_modexp : ctx -> modexp -> Prop :=
| amod_unit :
  `( mdenote gc_deps gc_stack Γ (me_unit fp) R ->
     ds_mtele R = Some T ->
     Γ ⊢aᵐ me_unit fp )
| amod_var :
  `( Γ ∋ #x ≔ₘ U ->
     Γ ⊢aᵐ me_var x )
| amod_lit :
  `( Γ ⊢aᵘ U ->
     Γ ⊢aᵐ me_lit U )
| amod_mem :
  `( Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack Γ (me_mem H y) R ->
     ds_mtele R = Some T ->
     Γ ⊢aᵐ me_mem H y )
(** An argument is checked against the outermost parameter of the
    telescope. *)
| amod_app :
  `( Γ ⊢aᵐ H ->
     mdenote gc_deps gc_stack Γ H R ->
     ds_mtele R = Some T ->
     tele_view T = Some (B, T1) ->
     Γ ⊢a N ⟸ B ->
     Γ ⊢aᵐ me_app H N )
where "Γ '⊢aᵐ' H" := (alg_modexp Γ H) : type_scope.

Hint Constructors alg_type_check alg_type_infer alg_ext alg_unit alg_body alg_modexp : mctt.

End Fixed_GCtx.

Notation "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) : type_scope.
Notation "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope.
Notation "Γ '⊢aˣ' Ψ" := (alg_ext Γ Ψ) : type_scope.
Notation "Γ '⊢aᵘ' U" := (alg_unit Γ U) : type_scope.
Notation "Γ '⊢aᵐ' H" := (alg_modexp Γ H) : type_scope.
Notation "Γ '⊢aᵇ' Φ ⇝ Φx" := (alg_body Γ Φ Φx) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer alg_ext alg_unit alg_body alg_modexp : mctt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop
with alg_ext_mut_ind := Induction for alg_ext Sort Prop
with alg_unit_mut_ind := Induction for alg_unit Sort Prop
with alg_body_mut_ind := Induction for alg_body Sort Prop
with alg_modexp_mut_ind := Induction for alg_modexp Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind,
  alg_ext_mut_ind,
  alg_unit_mut_ind,
  alg_body_mut_ind,
  alg_modexp_mut_ind.

(** The two instances of [ati_let], with an annotation and without one. *)
Section LetInstances.
  Context {GC : GCtx}.

  Lemma ati_let_some : forall Γ A UA u M B C D,
      Γ ⊢a A ⟹ UA ->
      is_univ_nf UA u ->
      Γ ⊢a M ⟸ A ->
      Γ ▸ A ≔ M ⊢a B ⟹ C ->
      nbe_ty_f Γ C[Id,,M] D ->
      Γ ⊢a ℓ A ≔ M in B ⟹ D.
  Proof.
    intros * HA Hu HM HB HD.
    eapply ati_let with (W := UA);
      [ right; reflexivity | intros _; exact HA | intros _; exact Hu | intros _; exact HM
      | discriminate | discriminate | exact HB | exact HD ].
  Qed.

  Lemma ati_let_none : forall Γ M (A : nf) B C D,
      Γ ⊢a M ⟹ A ->
      Γ ▸ (A : exp) ≔ M ⊢a B ⟹ C ->
      nbe_ty_f Γ C[Id,,M] D ->
      Γ ⊢a ℓ ≔ M in B ⟹ D.
  Proof.
    intros * HM HB HD.
    eapply ati_let with (W := A) (UA := A) (u := unl 0);
      [ left; reflexivity | discriminate | discriminate | discriminate
      | intros _; exact HM | intros _; reflexivity | exact HB | exact HD ].
  Qed.
End LetInstances.

#[export]
Hint Resolve ati_let_some ati_let_none : mctt.

(** The premises of [ati_let], read at the annotation: those about the other
    case are dropped, and those about this one are instantiated.  An
    annotation that is a constructor already fixes the type. *)
Ltac simpl_let_guards :=
  repeat match goal with
         | H : let_ann (Some _) _ |- _ => destruct H as [[=] | [= <-]]
         | H : let_ann None _ |- _ => clear H
         | H : ?x = ?x -> _ |- _ => specialize (H eq_refl)
         | H : None = Some _ -> _ |- _ => clear H
         | H : Some _ = None -> _ |- _ => clear H
         | H : ?A = nf_to_exp _ |- _ => is_var A; subst A
         end.

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
| user_exp_llit :
  `( user_exp (a_llit n) )
| user_exp_succl :
  `( user_exp M ->
     user_exp (a_succl M) )
| user_exp_maxl :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_maxl M N) )
| user_exp_True :
  `( user_exp a_True )
| user_exp_true :
  `( user_exp a_true )
| user_exp_False :
  `( user_exp a_False )
| user_exp_exfalso :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_exfalso A M) )
| user_exp_indty :
  `( user_exp (a_ind p k) )
| user_exp_con :
  `( user_exp (a_con p k c) )
| user_exp_nlit :
  `( user_exp (a_nlit n) )
| user_exp_ntok :
  `( user_exp a_ntok )
(** An eliminator: its uniform parameters, the annotations, motives and
    branches of its blocks, and its scrutinee. *)
| user_exp_elim :
  `( (forall U, List.In U Us -> user_exp U) ->
     (forall b Z, List.In b Bks -> eb_ann b = Some Z -> user_exp Z) ->
     (forall b, List.In b Bks -> user_exp (eb_motive b)) ->
     (forall b br, List.In b Bks -> List.In br (eb_brs b) -> user_exp (snd br)) ->
     user_exp M ->
     user_exp (a_elim oq Us m Bks M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi A B) )
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
| user_exp_let_infer :
  `( user_exp M ->
     user_exp B ->
     user_exp (ℓ ≔ M in B) )
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
    (fun b => match b with b_def oA M => (forall A, oA = Some A -> user_exp A) /\ user_exp M | b_mod _ => True end)
    (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True));
    intros; try destruct_conjs; try match goal with b : bnd |- _ => destruct b as [[] |]; destruct_conjs end;
    try lazymatch goal with
      | HU : List.Forall user_exp ?Us, HB : List.Forall _ ?Bks |- user_exp (a_elim _ ?Us _ ?Bks _) =>
          rewrite List.Forall_forall in HU, HB;
          constructor; [ exact HU
                       | intros b Z Hb HZ; exact (proj1 (HB b Hb) Z HZ)
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
