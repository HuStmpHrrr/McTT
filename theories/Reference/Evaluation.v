From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import Kinds.
Import Domain_Notations.

Generalizable All Variables.

(** * The Reference Evaluator

    The evaluation relations of [Core.Semantic.Evaluation] implemented
    literally: one function per relation, one match branch per rule, in the
    rule's order and with the rule's premises, over Core values and
    environments.  It is not extracted: [Extraction.Evaluation] is the
    evaluator the checker runs, and [Reference.Refinement] relates the
    two. *)


(** The termination orders mirror the evaluation relations, one for each, in
    the same global context, a constructor per rule.  Each premise that uses
    a value is quantified over the values its earlier premises evaluate to.
    A proof is never evaluated, so a term kept as a proof has no premise.
    The orders split their cases as the evaluator does: a closure lacking a
    first parameter, a chain of two selections or more, the outermost
    missing parameter as [tele_snoc] splits it off. *)

Inductive eval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
(** A universe *)
| eval_exp_order_typ :
  `( eval_exp_order Θ Ξ Typeω@i p )
(** A small universe evaluates its level. *)
| eval_exp_order_univ :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ Type⟨M⟩ p )
(** [Level] *)
| eval_exp_order_level :
  `( eval_exp_order Θ Ξ (Level@n) p )
(** The sort of the types of levels *)
| eval_exp_order_level_sort :
  `( eval_exp_order Θ Ξ LevelSort p )
(** A level literal *)
| eval_exp_order_llit :
  `( eval_exp_order Θ Ξ (𝕃ᵒ o) p )
(** A successor level: its argument *)
| eval_exp_order_succl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ (succl M) p )
(** A join of levels: both *)
| eval_exp_order_maxl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     eval_exp_order Θ Ξ (maxl M N) p )
(** An environment is total, so a variable always terminates. *)
| eval_exp_order_var :
  `( eval_exp_order Θ Ξ #x p )
(** [Prop] *)
| eval_exp_order_prop :
  `( eval_exp_order Θ Ξ Propₘ p )
(** [⊤] *)
| eval_exp_order_True :
  `( eval_exp_order Θ Ξ ⊤ p )
(** The introduction of [⊤], a proof: nothing evaluated *)
| eval_exp_order_tt :
  `( eval_exp_order Θ Ξ a_tt p )
(** [⊥] *)
| eval_exp_order_False :
  `( eval_exp_order Θ Ξ ⊥ p )
(** [efq]: its type only; its proof is not evaluated *)
| eval_exp_order_absurd :
  `( eval_exp_order Θ Ξ C p ->
     eval_exp_order Θ Ξ (efq M return C) p )
(** A [Σₚ]: its first component *)
| eval_exp_order_and :
  `( eval_exp_order Θ Ξ P p ->
     eval_exp_order Θ Ξ (Σₚ P Q) p )
(** The proof of a conjunction: nothing evaluated *)
| eval_exp_order_conj :
  `( eval_exp_order Θ Ξ (a_conj P Q M N) p )
(** The proof of its first component: nothing evaluated *)
| eval_exp_order_left :
  `( eval_exp_order Θ Ξ (a_left M) p )
(** The proof of its second component: nothing evaluated *)
| eval_exp_order_right :
  `( eval_exp_order Θ Ξ (a_right M) p )
(** A tagged proof: its proof *)
| eval_exp_order_proof_tag :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ (a_proof P M) p )
(** A type former of a group *)
| eval_exp_order_indty :
  `( eval_exp_order Θ Ξ (a_ind pq k) p )
(** A constructor that is a value of its own before any argument *)
| eval_exp_order_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     im_starts D Mk = true ->
     eval_exp_order Θ Ξ (a_con pq k c) p )
(** A constructor of a view of a group with no uniform parameters: the
    view's arguments are evaluated *)
| eval_exp_order_con_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_nu D = 0 ->
     eval_exps_order Θ Ξ Is nil ->
     eval_exp_order Θ Ξ (a_con pq j c) p )
(** The constructor of a record view of a group with no uniform
    parameters, of a record with fields: a value of its own *)
| eval_exp_order_con_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ind_nu D = 0 ->
     0 < List.length fl ->
     eval_exp_order Θ Ξ (a_con pq j c) p )
(** The constructor of a record view of a group with no uniform
    parameters, of a record without fields: the empty tuple *)
| eval_exp_order_con_rview_empty :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is nil ->
     ind_nu D = 0 ->
     eval_exp_order Θ Ξ (a_con pq j c) p )
(** The eliminator into types: its uniform parameters, its scrutinee, and
    the elimination *)
| eval_exp_order_elim :
  `( eval_exps_order Θ Ξ Us p ->
     eval_exp_order Θ Ξ M p ->
     (forall ups m, ⟦ Us ⟧* Θ ⍮ Ξ ⍮ p ↘ ups -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
        eval_elim_order Θ Ξ p pq ups Bks j m) ->
     eval_exp_order Θ Ξ (a_elim ak_relevant pq Us j Bks M) p )
(** An eliminator into propositions: nothing evaluated *)
| eval_exp_order_elim_proof :
  `( eval_exp_order Θ Ξ (a_elim ak_propositional pq Us j Bks M) p )
(** A [Π], at its kinds: its domain *)
| eval_exp_order_pi :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ (a_pi κd κc A B) p )
(** A function: its domain *)
| eval_exp_order_fn :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ (λ A M) p )
(** An application: the function, then, by the kind of the argument it
    takes, the argument and the application to it, or the application to
    the proof kept as it is *)
| eval_exp_order_app :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> evaluated_kind (arg_kind Θ Ξ m) -> eval_exp_order Θ Ξ N p) ->
     (forall m n, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> evaluated_kind (arg_kind Θ Ξ m) -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n ->
        eval_app_order Θ Ξ m n) ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> arg_kind Θ Ξ m = ak_propositional -> eval_app_order Θ Ξ m ⋆ᵈ⟨N, p⟩) ->
     eval_exp_order Θ Ξ (M $ N) p )
(** A local definition: its type, then, by the type's kind, its body and
    the rest, or the rest at the body kept as a proof *)
| eval_exp_order_let :
  `( eval_exp_order Θ Ξ A p ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> evaluated_kind (domain_kind a) -> eval_exp_order Θ Ξ M p) ->
     (forall a m, ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> evaluated_kind (domain_kind a) -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
        eval_exp_order Θ Ξ B (p ↦ m ⦂ entry_type_value a)) ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> domain_kind a = ak_propositional ->
        eval_exp_order Θ Ξ B (p ↦ ⋆ᵈ⟨M, p⟩ ⦂ entry_type_value a)) ->
     eval_exp_order Θ Ξ (ℓ A ≔ M in B) p )
(** A local module: its unit's closure, then the rest *)
| eval_exp_order_let_mod :
  `( eval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h -> eval_exp_order Θ Ξ B (p ↦ᵐ h ⦂ gu_mk Δ D)) ->
     eval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
(** A local definition with a module part: its type, its body and the
    closure of its unit, as its literal evaluates ([eval_me_lit]), then the
    rest.  The unit's premise is the closure's order, not the literal's:
    read off by inversion, the literal's would not be a subterm. *)
| eval_exp_order_let_dm :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ M p ->
     eval_close_order Θ Ξ Δ D p ->
     (forall a m h, ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h ->
        eval_exp_order Θ Ξ B (p ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ gu_mk Δ D)) ->
     eval_exp_order Θ Ξ (ℓᵈ A ≔ M ‖ (gu_mk Δ D) in B) p )
(** A member: the root of its module expression, the selection, the
    arguments, then the application to them *)
| eval_exp_order_mem :
  `( modexp_spine H = (R, args, pre) ->
     eval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     eval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> h ·ₜ* (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
        ⟦ args ⟧* Θ ⍮ Ξ ⍮ p ↘ ns -> eval_apps_order Θ Ξ f ns) ->
     eval_exp_order Θ Ξ (a_mem H x) p )
(** A record's type former is a value. *)
| eval_exp_order_record :
  `( eval_exp_order Θ Ξ (a_record pq) p )
(** A record element: its type, which finds a record, then the values of
    its fields at the record's kinds *)
| eval_exp_order_tuple :
  `( eval_exp_order Θ Ξ T p ->
     (forall t, ⟦ T ⟧ Θ ⍮ Ξ ⍮ p ↘ t -> exists pq ns R, t = d_record pq ns /\ record_lookup Θ Ξ pq = Some R) ->
     (forall pq ns R, ⟦ T ⟧ Θ ⍮ Ξ ⍮ p ↘ d_record pq ns -> record_lookup Θ Ξ pq = Some R ->
        eval_field_vals_order Θ Ξ (record_field_kinds R) (List.map snd fs) p) ->
     eval_exp_order Θ Ξ (a_tuple T fs) p )
(** A field: the value, then the field of it *)
| eval_exp_order_proj :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> eval_proj_order Θ Ξ f m) ->
     eval_exp_order Θ Ξ (a_proj f M) p )

(** The field [f] of a value, as [eval_proj] reads it *)
with eval_proj_order (Θ : gdeps) (Ξ : gstack) : string -> domain -> Prop :=
(** Of a tuple with the field *)
| eval_proj_order_tuple :
  `( field_lookup vs f <> None ->
     eval_proj_order Θ Ξ f (d_tuple vs) )
(** Of a neutral of a record type with the field: the projections of the
    fields up to it, which reach it *)
| eval_proj_order_neut :
  `( record_lookup Θ Ξ pq = Some R ->
     field_index (record_fields R) f = Some k ->
     eval_neutral_fields_order Θ Ξ m (env_tele nil (List.rev (record_params R)) ns) (List.firstn (S k) (record_fields R)) ->
     (forall rs, eval_neutral_fields Θ Ξ m (env_tele nil (List.rev (record_params R)) ns) (List.firstn (S k) (record_fields R)) rs ->
        List.nth_error rs k <> None) ->
     eval_proj_order Θ Ξ f (⇑ (d_record pq ns) m) )

(** The neutral projections at a list of fields, as [eval_neutral_fields]
    reads them *)
with eval_neutral_fields_order (Θ : gdeps) (Ξ : gstack) : domain_ne -> env -> list (string * exp) -> Prop :=
(** No field left *)
| eval_neutral_fields_order_nil :
  `( eval_neutral_fields_order Θ Ξ m p nil )
(** The next field's type, then the rest after its projection *)
| eval_neutral_fields_order_cons :
  `( eval_exp_order Θ Ξ T p ->
     (forall a, ⟦ T ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
        eval_neutral_fields_order Θ Ξ m (p ↦ ⇑ a (d_proj g m) ⦂ entry_type_closure T p) fl) ->
     eval_neutral_fields_order Θ Ξ m p ((g, T) :: fl) )

(** The eliminator of the group at [pq] at its member [j], on a value, as
    [eval_elim] reads it. *)
with eval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> Prop :=
(** On a saturated constructor: the recursive results, then the branch, at
    its typed entries.  The group's table of leaf paths is coherent, the
    gate [eval_elim_con] has: a premise of the domain, not a check the
    evaluator runs *)
| eval_elim_order_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_ref pq j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     ind_con Mj c = Some gs ->
     List.length vs = (im_np Dq Mk + List.length gs)%nat ->
     List.nth_error Bks j = Some b ->
     brs_lookup (eb_brs b) c = Some (n, B) ->
     n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat ->
     leaves_coherent D ->
     eval_ihs_order Θ Ξ p pq ups Bks gs (skipn (im_np Dq Mk) vs) ->
     (forall ihs, ⟦ihs skipn (im_np Dq Mk) vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs ->
        eval_exp_order Θ Ξ B (env_extend_typed p (branch_entries D Mj pq ups (blocks_motives Bks) p gs
                                                    (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs)) (skipn (im_np Dq Mk) vs) ihs))) ->
     eval_elim_order Θ Ξ p pq ups Bks j (d_con pc k c vs) )
(** On a neutral: the member stood for, then the motive's instance *)
| eval_elim_order_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_ref pq j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_binder_count b = S (im_nn Mk) ->
     eval_mref_order Θ Ξ pq ups j ->
     (forall cups, ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ (pc, k, cups) ->
        eval_exp_order Θ Ξ (eb_motive b)
          (env_extend_typed p (motive_entries D Mj ups (List.skipn (ind_nu Dq) as')
                                 (d_ind pc k (cups ++ List.skipn (ind_nu Dq) as')) (⇑ (d_ind pc k as') m)))) ->
     eval_elim_order Θ Ξ p pq ups Bks j (⇑ (d_ind pc k as') m) )

(** The recursive results of the arguments [vs] of kinds [gs] *)
with eval_ihs_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> list carg -> list domain -> Prop :=
(** No argument *)
| eval_ihs_order_nil :
  `( eval_ihs_order Θ Ξ p pq ups Bks nil nil )
(** A non-recursive argument: the rest *)
| eval_ihs_order_arg :
  `( eval_ihs_order Θ Ξ p pq ups Bks gs vs ->
     eval_ihs_order Θ Ξ p pq ups Bks (ca_arg r T :: gs) (v :: vs) )
(** A recursive argument: its results, then the rest *)
| eval_ihs_order_rec :
  `( eval_ih_order Θ Ξ p pq ups Bks t v ->
     eval_ihs_order Θ Ξ p pq ups Bks gs vs ->
     eval_ihs_order Θ Ξ p pq ups Bks (ca_rec t :: gs) (v :: vs) )

(** The recursive results of an argument of a shape *)
with eval_ih_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> Prop :=
(** At the end, at a member with a block: the eliminator at the member *)
| eval_ih_order_self :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     eval_elim_order Θ Ξ p pq ups Bks j v ->
     eval_ih_order Θ Ξ p pq ups Bks (pt_self j Ps) v )
(** At the end, at a record view: the projections, then their recursive
    results *)
| eval_ih_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     eval_projs_order Θ Ξ fl v ->
     (forall ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> eval_ihs_order Θ Ξ p pq ups Bks gs ws) ->
     eval_ih_order Θ Ξ p pq ups Bks (pt_self j Ps) v )
(** At a function shape: closures, one per leaf path of the rest *)
| eval_ih_order_pi :
  `( ind_lookup Θ Ξ pq = Some D ->
     eval_ih_order Θ Ξ p pq ups Bks (pt_pi B t) v )

(** The projections of a value at a list of fields *)
with eval_projs_order (Θ : gdeps) (Ξ : gstack) : list string -> domain -> Prop :=
(** No field *)
| eval_projs_order_nil :
  `( eval_projs_order Θ Ξ nil v )
(** The first field's projection, then the rest *)
| eval_projs_order_cons :
  `( eval_proj_order Θ Ξ f v ->
     eval_projs_order Θ Ξ fl v ->
     eval_projs_order Θ Ξ (f :: fl) v )

(** The member a member of a group stands for, as [eval_mref] reads it *)
with eval_mref_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> nat -> Prop :=
(** A declared member *)
| eval_mref_order_decl :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_decl pm ->
     eval_mref_order Θ Ξ pq ups j )
(** A view: the view's arguments at the uniform parameters *)
| eval_mref_order_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     eval_exps_order Θ Ξ Is (decl_env D ups) ->
     eval_mref_order Θ Ξ pq ups j )

(** The type of an argument of a shape *)
with eval_shape_type_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
(** At the end: the parameters, and the member stood for *)
| eval_shape_type_order_self :
  `( eval_exps_order Θ Ξ Ps p ->
     eval_mref_order Θ Ξ pq ups j ->
     eval_shape_type_order Θ Ξ pq ups p (pt_self j Ps) )
(** At the end, at a record view: the view's instance *)
| eval_shape_type_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     eval_exps_order Θ Ξ Is (decl_env D ups) ->
     eval_shape_type_order Θ Ξ pq ups p (pt_self j Ps) )
(** At a domain *)
| eval_shape_type_order_pi :
  `( eval_exp_order Θ Ξ B p ->
     eval_shape_type_order Θ Ξ pq ups p (pt_pi B t) )

(** The types of the recursive results of an argument of a shape *)
with eval_ihty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> ptyp -> domain -> Prop :=
(** At the end, at a member with a block: the parameters, then the
    member's motive *)
| eval_ihty_order_self :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     eval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ p ↘ bs ->
        eval_exp_order Θ Ξ (List.nth j As a_prop)
          (env_extend_typed pm (tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) bs ++
                                (v, entry_type_shape pq ups p (pt_self j Ps)) :: nil))) ->
     eval_ihty_order Θ Ξ pq ups pm As p (pt_self j Ps) v )
(** At the end, at a record view: the projections, then their recursive
    results' types *)
| eval_ihty_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     eval_projs_order Θ Ξ fl v ->
     (forall ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> eval_ihtys_order Θ Ξ pq ups pm As (decl_env D ups) gs ws) ->
     eval_ihty_order Θ Ξ pq ups pm As p (pt_self j Ps) v )
(** At a domain *)
| eval_ihty_order_pi :
  `( ind_lookup Θ Ξ pq = Some D ->
     eval_exp_order Θ Ξ B p ->
     eval_ihty_order Θ Ξ pq ups pm As p (pt_pi B t) v )

(** The types of the recursive results of a record view's fields *)
with eval_ihtys_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> list carg -> list domain -> Prop :=
(** No field *)
| eval_ihtys_order_nil :
  `( eval_ihtys_order Θ Ξ pq ups pm As p nil nil )
(** A non-recursive field: the rest, under it at its type *)
| eval_ihtys_order_arg :
  `( eval_ihtys_order Θ Ξ pq ups pm As (p ↦ v ⦂ entry_type_closure T p) gs vs ->
     eval_ihtys_order Θ Ξ pq ups pm As p (ca_arg r T :: gs) (v :: vs) )
(** A recursive field: its shape's, then the rest *)
| eval_ihtys_order_rec :
  `( eval_ihty_order Θ Ξ pq ups pm As p t v ->
     eval_ihtys_order Θ Ξ pq ups pm As p gs vs ->
     eval_ihtys_order Θ Ξ pq ups pm As p (ca_rec t :: gs) (v :: vs) )

(** Semantic application, as [eval_app] reads it *)
with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
(** A function: its body at the argument *)
| eval_app_order_fn :
  `( eval_exp_order Θ Ξ M (p ↦ n ⦂ entry_type_value a) ->
     eval_app_order Θ Ξ (λᵈ a p M) n )
(** A neutral at a [Π] into an evaluated kind: the codomain's instance *)
| eval_app_order_neut :
  `( evaluated_kind κc ->
     eval_exp_order Θ Ξ B (p ↦ n ⦂ entry_type_value a) ->
     eval_app_order Θ Ξ (⇑ (d_pi κd κc a p B) m) n )
(** A type former lacking a parameter *)
| eval_app_order_indty :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     eval_app_order Θ Ξ (d_ind pq k as') n )
(** A record's type former, before its last parameter *)
| eval_app_order_record :
  `( record_lookup Θ Ξ pq = Some R ->
     List.length ns < List.length (record_params R) ->
     eval_app_order Θ Ξ (d_record pq ns) n )
(** A constructor of a declared member *)
| eval_app_order_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length vs < (im_np D Mk + List.length gs)%nat ->
     eval_app_order Θ Ξ (d_con pq k c vs) n )
(** A constructor of a view, before its last uniform parameter *)
| eval_app_order_con_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) < ind_nu D ->
     eval_app_order Θ Ξ (d_con pq j c vs) n )
(** At its last uniform parameter: the view's arguments are evaluated *)
| eval_app_order_con_view_ups :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) = ind_nu D ->
     eval_exps_order Θ Ξ Is (decl_env D (vs ++ n :: nil)) ->
     eval_app_order Θ Ξ (d_con pq j c vs) n )
(** A constructor of a record view, before its last argument *)
| eval_app_order_con_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) < ind_nu D + List.length fl ->
     eval_app_order Θ Ξ (d_con pq j c vs) n )
(** At its last: the tuple of the fields *)
| eval_app_order_con_rview_full :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) = ind_nu D + List.length fl ->
     eval_app_order Θ Ξ (d_con pq j c vs) n )
(** The [i]-th recursive result of a function shape: those of the rest at
    the function's value, which has an [i]-th *)
| eval_app_order_ihfn :
  `( eval_app_order Θ Ξ f n ->
     (forall fn, $| f & n | Θ ⍮ Ξ ↘ fn -> eval_ih_order Θ Ξ p pq ups Bks t fn) ->
     (forall fn rs, $| f & n | Θ ⍮ Ξ ↘ fn -> ⟦ih fn of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ rs -> List.nth_error rs i <> None) ->
     eval_app_order Θ Ξ (d_ihfn p Bks pq ups t i f) n )
(** The family of the type of an argument of a function shape *)
| eval_app_order_shfam :
  `( eval_shape_type_order Θ Ξ pq ups (p ↦ n ⦂ entry_type_closure B p) t ->
     eval_app_order Θ Ξ (d_shfam pq ups p B t) n )
(** The [i]-th recursive result's family: those of the rest, which has an
    [i]-th *)
| eval_app_order_ihfam :
  `( eval_app_order Θ Ξ f n ->
     (forall fn, $| f & n | Θ ⍮ Ξ ↘ fn -> eval_ihty_order Θ Ξ pq ups pm As (p ↦ n ⦂ entry_type_closure B p) t fn) ->
     (forall fn as', $| f & n | Θ ⍮ Ξ ↘ fn -> ⟦ihty fn of t at pq ups under pm As ⟧ Θ ⍮ Ξ ⍮ p ↦ n ⦂ entry_type_closure B p ↘ as' ->
        List.nth_error as' i <> None) ->
     eval_app_order Θ Ξ (d_ihfam pm As pq ups p B t i f) n )
(** A member closure: its module at the argument, then the selection *)
| eval_app_order_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', $ᵐ| h & n | Θ ⍮ Ξ ↘ h' -> eval_selc_order Θ Ξ h' ch) ->
     eval_app_order Θ Ξ (d_member h ch) n )

(** A list of terms, as [eval_exps] reads it *)
with eval_exps_order (Θ : gdeps) (Ξ : gstack) : list exp -> env -> Prop :=
(** No term *)
| eval_exps_order_nil :
  `( eval_exps_order Θ Ξ nil p )
(** A term, then the rest *)
| eval_exps_order_cons :
  `( eval_exp_order Θ Ξ M p ->
     eval_exps_order Θ Ξ Ms p ->
     eval_exps_order Θ Ξ (M :: Ms) p )

(** A function applied to terms, as [eval_app_args] reads it *)
with eval_app_args_order (Θ : gdeps) (Ξ : gstack) : domain -> list exp -> env -> Prop :=
(** No argument *)
| eval_app_args_order_nil :
  `( eval_app_args_order Θ Ξ f nil p )
(** An evaluated argument: its value, the application to it, then the
    rest *)
| eval_app_args_order_evaluated :
  `( evaluated_kind (arg_kind Θ Ξ f) ->
     eval_exp_order Θ Ξ N p ->
     (forall n, ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_app_order Θ Ξ f n) ->
     (forall n g, ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> $| f & n | Θ ⍮ Ξ ↘ g -> eval_app_args_order Θ Ξ g Ns p) ->
     eval_app_args_order Θ Ξ f (N :: Ns) p )
(** A proof argument: the application to the proof, then the rest *)
| eval_app_args_order_proof :
  `( arg_kind Θ Ξ f = ak_propositional ->
     eval_app_order Θ Ξ f ⋆ᵈ⟨N, p⟩ ->
     (forall g, $| f & ⋆ᵈ⟨N, p⟩ | Θ ⍮ Ξ ↘ g -> eval_app_args_order Θ Ξ g Ns p) ->
     eval_app_args_order Θ Ξ f (N :: Ns) p )

(** The values of the fields of a record value, as [eval_field_vals]
    reads them *)
with eval_field_vals_order (Θ : gdeps) (Ξ : gstack) : list abs_kind -> list exp -> env -> Prop :=
(** No field *)
| eval_field_vals_order_nil :
  `( eval_field_vals_order Θ Ξ rs nil p )
(** A field of an evaluated kind: its value, then the rest *)
| eval_field_vals_order_evaluated :
  `( evaluated_kind (List.hd ak_relevant rs) ->
     eval_exp_order Θ Ξ M p ->
     eval_field_vals_order Θ Ξ (List.tl rs) Ms p ->
     eval_field_vals_order Θ Ξ rs (M :: Ms) p )
(** A propositional field: the rest *)
| eval_field_vals_order_proof :
  `( List.hd ak_relevant rs = ak_propositional ->
     eval_field_vals_order Θ Ξ (List.tl rs) Ms p ->
     eval_field_vals_order Θ Ξ rs (M :: Ms) p )

(** Application to a list of values, as [eval_apps] reads it *)
with eval_apps_order (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> Prop :=
(** No argument *)
| eval_apps_order_nil :
  `( eval_apps_order Θ Ξ m nil )
(** The first argument, then the rest *)
| eval_apps_order_cons :
  `( eval_app_order Θ Ξ m n ->
     (forall m1, $| m & n | Θ ⍮ Ξ ↘ m1 -> eval_apps_order Θ Ξ m1 args) ->
     eval_apps_order Θ Ξ m (n :: args) )

(** A module expression, as [eval_modexp] reads it *)
with eval_modexp_order (Θ : gdeps) (Ξ : gstack) : modexp -> env -> Prop :=
(** A module slot *)
| eval_modexp_order_var :
  `( eval_modexp_order Θ Ξ (me_var x) p )
(** A unit *)
| eval_modexp_order_unit :
  `( eval_modexp_order Θ Ξ (me_unit fp) p )
(** A literal unit: its closure *)
| eval_modexp_order_lit :
  `( eval_close_order Θ Ξ Δ D p ->
     eval_modexp_order Θ Ξ (me_lit (gu_mk Δ D)) p )
(** A submodule: the module, then the selection *)
| eval_modexp_order_mem :
  `( eval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selm_order Θ Ξ h y) ->
     eval_modexp_order Θ Ξ (me_mem H y) p )
(** An application: the module, the argument, then the application *)
| eval_modexp_order_app :
  `( eval_modexp_order Θ Ξ H p ->
     eval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_appm_order Θ Ξ h n) ->
     eval_modexp_order Θ Ξ (me_app H N) p )

(** The closure of a unit's definition, as [eval_close] reads it *)
with eval_close_order (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> Prop :=
(** A body *)
| eval_close_order_body :
  `( eval_close_order Θ Ξ Δ (md_body sm Φ) p )
(** An alias lacking a first parameter *)
| eval_close_order_alias :
  `( eval_close_order Θ Ξ (e :: Δ) (md_alias E) p )
(** An alias lacking none: its target *)
| eval_close_order_alias0 :
  `( eval_modexp_order Θ Ξ E p ->
     eval_close_order Θ Ξ nil (md_alias E) p )

(** A module value applied, as [eval_appm] reads it *)
with eval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
(** A global module *)
| eval_appm_order_global :
  `( eval_appm_order Θ Ξ (dm_global pq args) n )
(** The outermost missing parameter is split off as the evaluator splits
    it off ([tele_snoc]), so that the order of the rest is a premise of the
    order of the whole. *)
| eval_appm_order_local :
  `( tele_snoc Δ = Some (Δ0, ce_ass κ A) ->
     eval_close_order Θ Ξ Δ0 D (p ↦ n ⦂ entry_type_closure A p) ->
     eval_appm_order Θ Ξ (dm_local Δ D p) n )
(** A submodule closure: the module at the argument, then the selection *)
| eval_appm_order_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', $ᵐ| h & n | Θ ⍮ Ξ ↘ h' -> eval_selmc_order Θ Ξ h' ch) ->
     eval_appm_order Θ Ξ (dm_member h ch) n )

(** A module value applied to a list of values *)
with eval_appms_order (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> Prop :=
(** No argument *)
| eval_appms_order_nil :
  `( eval_appms_order Θ Ξ h nil )
(** The first argument, then the rest *)
| eval_appms_order_cons :
  `( eval_appm_order Θ Ξ h n ->
     (forall h1, $ᵐ| h & n | Θ ⍮ Ξ ↘ h1 -> eval_appms_order Θ Ξ h1 ns) ->
     eval_appms_order Θ Ξ h (n :: ns) )

(** A term member selected, as [eval_sel] reads it *)
with eval_sel_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
(** A term part of a global module ([gc_term]): it, closed, applied to the
    arguments *)
| eval_sel_order_global :
  `( module_saturated Θ Ξ pq args ->
     gc_term Θ Ξ (qname_app pq (x :: nil)) = Some M ->
     eval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ f -> eval_apps_order Θ Ξ f args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
(** An opaque definition or axiom of an evaluated kind: its type, then the
    neutral applied to the arguments *)
| eval_sel_order_global_neut :
  `( module_saturated Θ Ξ pq args ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv κ A B) ->
     evaluated_kind κ ->
     b = false \/ B = None ->
     eval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a -> eval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
(** A proof member of a global module at exactly its parameters: nothing
    evaluated *)
| eval_sel_order_global_proof :
  `( gc_loc Θ Ξ pq = Some (T, Φ) ->
     List.length args = List.length T ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv ak_propositional A B) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
(** The module of a member of a group, as a term: its type former, applied
    to the arguments *)
| eval_sel_order_global_ind :
  `( module_saturated Θ Ξ pq args ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app pq (x :: nil)) = Some (pg, k, D) ->
     eval_apps_order Θ Ξ (d_ind pg k nil) args ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
(** A member of a global module lacking a parameter: no recursion *)
| eval_sel_order_global_unsat :
  `( gc_loc Θ Ξ pq = Some (T, Φ) ->
     List.length args < List.length T ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
(** A member of a closure lacking a parameter: no recursion *)
| eval_sel_order_unsat :
  `( eval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
(** A term part of a saturated body of an evaluated kind ([entry_tm]),
    read in the expanded body *)
| eval_sel_order_body :
  `( gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     evaluated_kind (entry_kind E) ->
     eval_body_env_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_exp_order Θ Ξ M p') ->
     eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
(** A proof member of a saturated body: nothing evaluated *)
| eval_sel_order_body_proof :
  `( gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_kind E = ak_propositional ->
     eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
(** A member of a submodule closure: no recursion *)
| eval_sel_order_member :
  `( eval_sel_order Θ Ξ (dm_member h ch) x )
(** A record type of a global module, not a definition: its type former,
    applied to the arguments *)
| eval_sel_order_global_record :
  `( module_saturated Θ Ξ pq args ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     record_lookup Θ Ξ (qname_app pq (x :: nil)) = Some R ->
     eval_apps_order Θ Ξ (d_record (qname_app pq (x :: nil)) nil) args ->
     eval_sel_order Θ Ξ (dm_global pq args) x )

(** A submodule selected, as [eval_selm] reads it *)
with eval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
(** A submodule of a global module stored in place: no recursion *)
| eval_selm_order_global :
  `( gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
(** An alias submodule of a global module: its closure, then its
    application to the arguments *)
| eval_selm_order_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     eval_close_order Θ Ξ Δ D nil ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ nil ↘ h -> eval_appms_order Θ Ξ h args) ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
(** A submodule of a closure lacking a parameter: no recursion *)
| eval_selm_order_unsat :
  `( eval_selm_order Θ Ξ (dm_local (e :: Δ) D p) y )
(** A module part of a saturated body ([entry_unit]), read in the
    expanded body *)
| eval_selm_order_body :
  `( gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     eval_body_env_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_close_order Θ Ξ Δy Dy p') ->
     eval_selm_order Θ Ξ (dm_local nil (md_body sm Φ) p) y )
(** A submodule of a submodule closure: no recursion *)
| eval_selm_order_member :
  `( eval_selm_order Θ Ξ (dm_member h ch) y )

(** Selection along a chain to a term member *)
with eval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
(** The last selection, a term member *)
| eval_selc_order_one :
  `( eval_sel_order Θ Ξ h x ->
     eval_selc_order Θ Ξ h (x :: nil) )
(** A submodule, then the rest of the chain *)
| eval_selc_order_cons :
  `( eval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘ y Θ ⍮ Ξ ↘ h1 -> eval_selc_order Θ Ξ h1 (z :: ch)) ->
     eval_selc_order Θ Ξ h (y :: z :: ch) )

(** Selection along a chain to a submodule *)
with eval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
(** The empty chain *)
| eval_selmc_order_nil :
  `( eval_selmc_order Θ Ξ h nil )
(** A submodule, then the rest of the chain *)
| eval_selmc_order_cons :
  `( eval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘ y Θ ⍮ Ξ ↘ h1 -> eval_selmc_order Θ Ξ h1 ch) ->
     eval_selmc_order Θ Ξ h (y :: ch) )

(** The environment a body's members see, as [eval_body_env] reads it *)
with eval_body_env_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
(** The empty body *)
| eval_body_env_order_nil :
  `( eval_body_env_order Θ Ξ p gm_nil )
(** A definition, of the two rules [eval_body_env_def] and
    [eval_body_env_def_proof], which differ by its kind: the body before
    it, then, at an evaluated kind, its body.  One constructor for both,
    so that inverting it never fixes the kind, which the evaluator decides
    after the recursive call on the body before it. *)
| eval_body_env_order_def :
  `( eval_body_env_order Θ Ξ p Φ ->
     (evaluated_kind κ -> forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_exp_order Θ Ξ M p1) ->
     eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def b pv κ A (Some M))) )
(** A submodule: the body before it, then its unit's closure *)
| eval_body_env_order_mod :
  `( eval_body_env_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_close_order Θ Ξ Δy Dy p1) ->
     eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) )
(** A definition with a module part: its term and its unit's closure *)
| eval_body_env_order_dm :
  `( eval_body_env_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_exp_order Θ Ξ M p1) ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_close_order Θ Ξ Δy Dy p1) ->
     eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy))) ).

#[local]
Hint Constructors eval_exp_order eval_elim_order eval_ihs_order eval_ih_order eval_mref_order eval_shape_type_order eval_ihty_order eval_app_order eval_exps_order eval_apps_order
  eval_modexp_order eval_close_order eval_appm_order eval_appms_order eval_sel_order eval_selm_order eval_selc_order eval_selmc_order
  eval_body_env_order eval_proj_order eval_neutral_fields_order eval_projs_order eval_ihtys_order
  eval_field_vals_order eval_app_args_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_eval_all :=
  repeat match goal with
    | H1 : eval_exp ?T ?X ?M ?p ?m1, H2 : eval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_eval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_app ?T ?X ?m ?n ?r1, H2 : eval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_exps ?T ?X ?M ?p ?r1, H2 : eval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (@functional_eval T X))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_apps ?T ?X ?m ?n ?r1, H2 : eval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_eval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_modexp ?T ?X ?M ?p ?r1, H2 : eval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_close ?T ?X ?Δ ?D ?p ?r1, H2 : eval_close ?T ?X ?Δ ?D ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))) _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_appm ?T ?X ?m ?n ?r1, H2 : eval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_appms ?T ?X ?m ?n ?r1, H2 : eval_appms ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_sel ?T ?X ?m ?n ?r1, H2 : eval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selm ?T ?X ?m ?n ?r1, H2 : eval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selc ?T ?X ?m ?n ?r1, H2 : eval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selmc ?T ?X ?m ?n ?r1, H2 : eval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_body_env ?T ?X ?m ?n ?r1, H2 : eval_body_env ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_body_env _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_elim ?T ?X ?p ?pg ?u ?Bs ?j ?m ?r1, H2 : eval_elim ?T ?X ?p ?pg ?u ?Bs ?j ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_elim _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ihs ?T ?X ?p ?pg ?u ?Bs ?gs ?vs ?r1, H2 : eval_ihs ?T ?X ?p ?pg ?u ?Bs ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ihs _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ih ?T ?X ?p ?pg ?u ?Bs ?t ?v ?r1, H2 : eval_ih ?T ?X ?p ?pg ?u ?Bs ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ih _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_mref ?T ?X ?pg ?u ?j ?r1, H2 : eval_mref ?T ?X ?pg ?u ?j ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_mref _ _ _ _ _ H1 H2); subst; clear H2
    | H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst
    | H1 : eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_shape_type _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ihty ?T ?X ?p ?u ?ρm ?A ?ρ ?t ?v ?r1, H2 : eval_ihty ?T ?X ?p ?u ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ihty _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ihtys ?T ?X ?p ?u ?ρm ?A ?ρ ?gs ?vs ?r1, H2 : eval_ihtys ?T ?X ?p ?u ?ρm ?A ?ρ ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ihtys _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_projs ?T ?X ?fl ?v ?r1, H2 : eval_projs ?T ?X ?fl ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_projs _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    | H1 : eval_proj ?T ?X ?f ?m ?r1, H2 : eval_proj ?T ?X ?f ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_proj _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_neutral_fields ?T ?X ?m ?p ?fl ?r1, H2 : eval_neutral_fields ?T ?X ?m ?p ?fl ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_neutral_fields _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_field_vals ?T ?X ?rs ?Ms ?p ?r1, H2 : eval_field_vals ?T ?X ?rs ?Ms ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_field_vals _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_app_args ?T ?X ?f ?Ms ?p ?r1, H2 : eval_app_args ?T ?X ?f ?Ms ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_app_args _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_record _ _ = d_record _ _ |- _ => injection H; clear H; intros; subst
    end.

(** Every evaluation has an order: the evaluator terminates on what
    evaluates. *)
Lemma eval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms -> eval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*| m & ns | Θ ⍮ Ξ ↘ r -> eval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_modexp_order Θ Ξ H p) /\
    (forall Δ D p h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h -> eval_close_order Θ Ξ Δ D p) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> eval_appm_order Θ Ξ h n) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> eval_appms_order Θ Ξ h ns) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> eval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> eval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> eval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> eval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_body_env_order Θ Ξ p Φ) /\
    (forall p pq ups Bks j m r, ⟦elim m at j of pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_elim_order Θ Ξ p pq ups Bks j m) /\
    (forall p pq ups Bks gs vs ihs, ⟦ihs vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs -> eval_ihs_order Θ Ξ p pq ups Bks gs vs) /\
    (forall p pq ups Bks t v r, ⟦ih v of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_ih_order Θ Ξ p pq ups Bks t v) /\
    (forall pq ups j r, ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ r -> eval_mref_order Θ Ξ pq ups j) /\
    (forall pq ups p t a, ⟦shty t of pq ups ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_shape_type_order Θ Ξ pq ups p t) /\
    (forall pq ups pm As p t v a, ⟦ihty v of t at pq ups under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_ihty_order Θ Ξ pq ups pm As p t v) /\
    (forall f m r, eval_proj Θ Ξ f m r -> eval_proj_order Θ Ξ f m) /\
    (forall m p fl rs, eval_neutral_fields Θ Ξ m p fl rs -> eval_neutral_fields_order Θ Ξ m p fl) /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> eval_projs_order Θ Ξ fl v) /\
    (forall pq ups pm As p gs vs rs, ⟦ihtys vs of gs at pq ups under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ rs ->
       eval_ihtys_order Θ Ξ pq ups pm As p gs vs) /\
    (forall rs Ms p ms, eval_field_vals Θ Ξ rs Ms p ms -> eval_field_vals_order Θ Ξ rs Ms p) /\
    (forall f Ms p r, eval_app_args Θ Ξ f Ms p r -> eval_app_args_order Θ Ξ f Ms p).
Proof.
  intros Θ Ξ; apply eval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : eval_selc _ _ _ ?c _ |- eval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    (** A local definition with a module part: its unit's literal evaluates
        as the unit's closure ([eval_me_lit]). *)
    try match goal with Hm : ⟦ me_lit ?U ⟧ᵐ _ ⍮ _ ⍮ _ ↘ _, Ho : eval_modexp_order _ _ (me_lit ?U) _
          |- eval_exp_order _ _ (ℓᵈ _ ≔ _ ‖ ?U in _) _ =>
          inversion Hm; subst; inversion Ho; subst end;
    (** A proof is never an evaluated kind, nor the kind of an evaluated
        argument a proof's. *)
    solve [ econstructor; try eassumption; intros; functional_eval_all;
            first [ solve [ eauto using tele_snoc_app ]
                  | exfalso; eapply evaluated_kind_not_propositional; eassumption
                  | match goal with H : evaluated_kind ak_propositional |- _ => inversion H end
                  | congruence ]
          (** A tuple: its type finds the record, whose kinds direct its
              fields. *)
          | econstructor; [ eassumption | intros t Ht; functional_eval_all; eauto | intros; functional_eval_all; congruence ] ].
Qed.

Lemma eval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (eval_order_sound Θ Ξ)). Qed.

Lemma eval_app_order_sound : forall Θ Ξ m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (eval_order_sound Θ Ξ))). Qed.

Lemma eval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms -> eval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (eval_order_sound Θ Ξ)))). Qed.

Lemma eval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (eval_order_sound Θ Ξ)))))). Qed.

Lemma eval_shape_type_order_sound : forall Θ Ξ pq ups p t a, ⟦shty t of pq ups ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_shape_type_order Θ Ξ pq ups p t.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_ihty_order_sound : forall Θ Ξ pq ups pm As p t v a, ⟦ihty v of t at pq ups under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
    eval_ihty_order Θ Ξ pq ups pm As p t v.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_ih_order_sound : forall Θ Ξ p pq ups Bks t v r, ⟦ih v of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
    eval_ih_order Θ Ξ p pq ups Bks t v.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_mref_order_sound : forall Θ Ξ pq ups j r, ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ r -> eval_mref_order Θ Ξ pq ups j.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_proj_order_sound : forall Θ Ξ f m r, eval_proj Θ Ξ f m r -> eval_proj_order Θ Ξ f m.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_projs_order_sound : forall Θ Ξ fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> eval_projs_order Θ Ξ fl v.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_app_args_order_sound : forall Θ Ξ f Ms p r, eval_app_args Θ Ξ f Ms p r -> eval_app_args_order Θ Ξ f Ms p.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_app_order_sound eval_exps_order_sound eval_modexp_order_sound
  eval_shape_type_order_sound eval_ihty_order_sound eval_ih_order_sound eval_mref_order_sound
  eval_proj_order_sound eval_projs_order_sound eval_app_args_order_sound : mctt.

(** The member a member stands for is the one [im_ref] names. *)
Lemma eval_mref_im_ref : forall Θ Ξ p ups j pc k pre D Mj,
    ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (pc, k, pre) ->
    ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> im_ref p j Mj = (pc, k).
Proof.
  intros * Hm Hl Hj; inversion Hm; subst;
    match goal with H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
      rewrite H1 in H2; injection H2 as <- end;
    match goal with H1 : ind_member ?D ?j = Some _, H2 : ind_member ?D ?j = Some _ |- _ =>
      rewrite H1 in H2; injection H2 as <- end;
    unfold im_ref; match goal with H : im_head _ = _ |- _ => rewrite H end; reflexivity.
Qed.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

(** A prefix up to a name ends with the entry of that name. *)
Lemma gm_prefix_upto_ext : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 -> exists Φ0 E, Φ1 = gm_ext Φ0 y E.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg IHg]; intros * Hp; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as <-; eauto | eauto ].
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

(** Whether a kind is evaluated or a proposition's: the side condition that
    tells an evaluated rule from its proof twin *)
Definition evaluated_kind_decide (κ : abs_kind) : { evaluated_kind κ } + { κ = ak_propositional } :=
  match κ as k return { evaluated_kind k } + { k = ak_propositional } with
  | ak_relevant => left evaluated_kind_relevant
  | ak_propositional => right eq_refl
  | ak_level => left evaluated_kind_level
  end.

(** A path with no term part, resolving to a definition, resolves to an
    opaque one or an axiom. *)
Lemma gc_term_none_opaque : forall Θ Ξ p b pv κ A B, evaluated_kind κ ->
    gc_term Θ Ξ p = None -> gc_resolve Θ Ξ p = Some (ge_def b pv κ A B) -> b = false \/ B = None.
Proof.
  intros * Hk Ht Hr; destruct b, B as [M |]; auto.
  rewrite (gc_term_of_resolve _ _ _ _ _ _ _ Hk Hr) in Ht; discriminate.
Qed.

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** Whether the global module at [pq] lacks no parameter given [args],
      decided by where it is stored *)
  Definition module_saturated_r (pq : qname) (args : list domain) :
      { module_saturated Θ Ξ pq args } +
      { exists T Φ, gc_loc Θ Ξ pq = Some (T, Φ) /\ List.length args < List.length T }.
  Proof.
    destruct (gc_loc Θ Ξ pq) as [[T Φ] |] eqn:E.
    - destruct (Nat.ltb (List.length args) (List.length T)) eqn:Elt.
      + right; exists T, Φ; split; [ reflexivity | apply Nat.ltb_lt, Elt ].
      + left; intros T' Φ' Hl; rewrite E in Hl; injection Hl as <- _; apply Nat.ltb_ge, Elt.
    - left; intros T' Φ' Hl; rewrite E in Hl; discriminate.
  Defined.

  (** Whether a global module given [args] is given exactly the parameters
      of its location, with the location's telescope *)
  Definition module_exact_r (pq : qname) (args : list domain) :
      { T | exists Φ, gc_loc Θ Ξ pq = Some (T, Φ) /\ List.length args = List.length T } +
      { forall T Φ, gc_loc Θ Ξ pq = Some (T, Φ) -> List.length args <> List.length T }.
  Proof.
    destruct (gc_loc Θ Ξ pq) as [[T Φ] |] eqn:E.
    - destruct (Nat.eqb (List.length args) (List.length T)) eqn:Eq.
      + left; exists T, Φ; split; [ reflexivity | apply Nat.eqb_eq, Eq ].
      + right; intros T' Φ' Hl; injection Hl as <- _; apply Nat.eqb_neq, Eq.
    - right; intros T' Φ' Hl; discriminate.
  Defined.

  #[local]
  Ltac impl_obligation_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_args_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_close_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_appms_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_body_env_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_elim_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_mref_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_shape_type_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihty_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihtys_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_projs_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_proj_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_neutral_fields_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_field_vals_order _ _ _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obligation_glob :=
    repeat match goal with
      (** A term part an order records is a definition's body or a
          definition with a module part's term. *)
      | H1 : gc_term _ _ ?p = Some _, H2 : gc_term _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_term _ _ ?p = Some _, H2 : gc_term _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H : gc_term _ _ _ = Some _ |- _ =>
          destruct (gc_term_inv _ _ _ _ H) as [(? & ? & ? & ? & ?) | (? & ? & ? & ?)]; clear H
      | H1 : gc_entry _ _ ?p = Some (ge_def_mod _ _ _ _), H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H1) in H2; discriminate H2
      | H1 : gc_entry _ _ ?p = Some (ge_def_mod _ _ _ _), H2 : ind_mlookup _ _ ?p = Some _ |- _ =>
          exfalso; exact (ind_mlookup_not_def_mod _ _ _ _ _ _ _ _ H2 H1)
      | H1 : gc_entry _ _ ?p = Some (ge_def_mod _ _ _ _), H2 : record_lookup _ _ ?p = Some _ |- _ =>
          exfalso; exact (record_lookup_not_def_mod _ _ _ _ _ _ _ _ H2 H1)
      | H1 : entry_tm ?E = _, H2 : entry_tm ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : entry_unit ?E = _, H2 : entry_unit ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : entry_kind ?E = _, H2 : entry_kind ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | clear H2 ]
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_loc _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some (mr_alias _) |- _ =>
          exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
      | H1 : gc_loc _ _ ?p = Some _, H2 : gc_loc _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      (** A saturated module lacks no parameter. *)
      | H : exists T Φ, gc_loc _ _ ?p = Some (T, Φ) /\ _ |- _ =>
          let T := fresh "T" in let Φ := fresh "Φ" in destruct H as (T & Φ & ? & ?)
      | H : exists Φ, gc_loc _ _ ?p = Some (_, Φ) /\ _ |- _ =>
          let Φ := fresh "Φ" in destruct H as (Φ & ? & ?)
      | H1 : module_saturated _ _ ?p _, H2 : gc_loc _ _ ?p = Some (?T, _), H3 : _ < List.length ?T |- _ =>
          exfalso; specialize (H1 _ _ H2); lia
      | H1 : forall T Φ, gc_loc _ _ ?p = Some (T, Φ) -> _ <> _, H2 : gc_loc _ _ ?p = Some (_, _) |- _ =>
          exfalso; apply (H1 _ _ H2); assumption
      | H : tele_snoc _ = None |- _ => rewrite tele_snoc_app in H; discriminate H
      | H1 : tele_snoc ?Δ = Some _, H2 : tele_snoc ?Δ = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : tele_snoc ?Δ = Some _, H2 : tele_snoc ?Δ = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H : tele_snoc (_ ++ _ :: nil) = _ |- _ =>
          rewrite tele_snoc_app in H; injection H; clear H; intros; subst
      | H : tele_snoc nil = _ |- _ => discriminate H
      | H : tele_snoc ?Δ = Some _ |- _ => is_var Δ; apply tele_snoc_some in H; subst Δ
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      (** A prefix up to a name ends with that name's entry. *)
      | H : gm_prefix_upto _ _ = Some gm_nil |- _ =>
          destruct (gm_prefix_upto_ext _ _ _ H) as (? & ? & ?); discriminate
      | H : gm_prefix_upto _ _ = Some (gm_open _ _ _ _) |- _ =>
          destruct (gm_prefix_upto_ext _ _ _ H) as (? & ? & ?); discriminate
      (** The name of the entry found is the one looked up. *)
      | H : gm_prefix_upto _ ?x = Some (gm_ext _ ?y _) |- _ =>
          is_var y; assert_fails (constr_eq x y);
          let Hx := fresh "Hx" in
          destruct (gm_prefix_upto_ext _ _ _ H) as (? & ? & Hx); injection Hx; clear Hx; intros; subst y
      | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = None |- _ =>
          rewrite H1 in H2; discriminate H2
      (** The members of a group, their heads, their references and the
          blocks of an eliminator, looked up once. *)
      | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : im_starts ?D ?M = true, H2 : im_starts ?D ?M = false |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_view _ _ _ _, H3 : ind_nu _ = 0 |- _ =>
          unfold im_starts, im_is_decl in H1; rewrite H2, H3 in H1; discriminate H1
      | H1 : ind_mlookup _ _ ?p = Some _, H2 : ind_mlookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_mlookup _ _ ?p = Some _, H2 : ind_mlookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
      | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
      (** A record, its fields and the projections of a neutral, looked up
          once. *)
      | H1 : record_lookup _ _ ?p = Some _, H2 : record_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : record_lookup _ _ ?p = Some _, H2 : record_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : record_lookup _ _ ?p = Some _, H2 : ind_mlookup _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (record_lookup_not_ind _ _ _ _ H1) in H2; discriminate H2
      | H1 : field_index ?fs ?f = Some _, H2 : field_index ?fs ?f = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : field_index ?fs ?f = Some _, H2 : field_index ?fs ?f = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ?x <> None, H2 : ?x = None |- _ => exfalso; exact (H1 H2)
      | H : None <> None |- _ => exfalso; exact (H eq_refl)
      (** A record view, by its head; its one constructor. *)
      | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
          exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
      | H1 : im_is_rview ?M = true, H2 : im_head ?M = mh_decl _ |- _ =>
          exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
      | H1 : im_is_rview ?M = true, H2 : im_head ?M = mh_view _ _ _ _ |- _ =>
          exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
      | H : im_head ?M = mh_decl _ |- im_is_rview ?M = false => unfold im_is_rview; rewrite H; reflexivity
      | H : im_head ?M = mh_view _ _ _ _ |- im_is_rview ?M = false => unfold im_is_rview; rewrite H; reflexivity
      | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : im_starts ?D ?M = false, H2 : im_head ?M = mh_record _ _ _ |- ind_nu ?D = 0 =>
          unfold im_starts, im_is_decl in H1; rewrite H2 in H1; apply Bool.orb_false_elim in H1 as [_ H1];
          apply Nat.ltb_ge in H1; lia
      | H1 : im_starts ?D ?M = true, H2 : im_head ?M = mh_record _ _ _, H3 : ind_nu ?D = 0 |- _ =>
          unfold im_starts, im_is_decl in H1; rewrite H2, H3 in H1; discriminate H1
      (** An evaluated kind is no proposition's. *)
      | H1 : evaluated_kind ?k, H2 : ?k = ak_propositional |- _ =>
          exfalso; exact (evaluated_kind_not_propositional _ H1 H2)
      | H : evaluated_kind ak_propositional |- _ =>
          exfalso; exact (evaluated_kind_not_propositional _ H eq_refl)
      (** A kind decided a proposition's, fixed *)
      | H : ?k = ak_propositional |- _ => is_var k; subst k
      (** The member a stuck eliminator's member stands for is its own. *)
      | Hm : eval_mref _ _ ?p _ ?j (?pc', ?k', _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
        Hr : im_ref ?p ?j _ = (?pc, ?k) |- _ =>
          assert_fails (constr_eq pc pc');
          rewrite (eval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) in Hr; injection Hr; clear Hr; intros; subst
      end.

  (** What the order says of the values evaluation finds *)
  #[local]
  Ltac impl_obligation_exfalso :=
    repeat match goal with
      (** A record element's type finds a record. *)
      | H : forall t, eval_exp _ _ ?T ?p t -> exists _ _ _, t = d_record _ _ /\ _, Ht : eval_exp _ _ ?T ?p _ |- _ =>
          destruct (H _ Ht) as (? & ? & ? & ? & ?); clear H
      (** The projections of a neutral reach the field projected. *)
      | H : forall rs, eval_neutral_fields _ _ ?m ?p ?fl rs -> _, Hm : eval_neutral_fields _ _ ?m ?p ?fl _ |- _ =>
          specialize (H _ Hm)
      (** A function shape's recursive results, or their types, have the
          one applied. *)
      | H : forall fn rs, eval_app _ _ ?f ?n fn -> eval_ih _ _ _ _ _ _ _ fn rs -> _,
        Hf : eval_app _ _ ?f ?n ?fn, Hr : eval_ih _ _ _ _ _ _ _ ?fn ?rs |- _ =>
          specialize (H _ _ Hf Hr)
      | H : forall fn as', eval_app _ _ ?f ?n fn -> eval_ihty _ _ _ _ _ _ _ _ fn as' -> _,
        Hf : eval_app _ _ ?f ?n ?fn, Hr : eval_ihty _ _ _ _ _ _ _ _ ?fn ?ys |- _ =>
          specialize (H _ _ Hf Hr)
      end.

  #[local]
  Ltac impl_obligation_split :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_app_args_order _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_close_order _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_appms_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_body_env_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_elim_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_mref_order _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihs_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_shape_type_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihty_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihtys_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_projs_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_proj_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_neutral_fields_order _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_field_vals_order _ _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac impl_obligation_finish :=
    (** A term part, by its lookup, before the lookups are read off *)
    try solve [ eapply eval_sel_global; eassumption ];
    impl_obligation_exfalso;
    impl_obligation_glob;
    (** once more, at the lookups fixed *)
    impl_obligation_exfalso;
    impl_obligation_glob;
    try solve [ intuition discriminate ];
    try solve [ congruence ];
    try solve [ exfalso; lia ];
    (** An opaque member: no term part *)
    try solve [ eapply eval_sel_global_neut; eauto using gc_term_none_opaque ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
    (** A stuck eliminator: its member's reference, read off the member *)
    try solve [ eapply eval_elim_neut; eauto using eval_mref_im_ref ];
    (** A local definition with a module part: its unit's literal is the
        unit's closure ([eval_me_lit]) *)
    try solve [ eapply eval_exp_let_dm; [ eassumption | eassumption | eapply eval_me_lit; eassumption | eassumption ] ];
    try solve [ eauto ];
    try econstructor; eauto.

  #[local]
  Ltac eval_obligation :=
    intros; cbv beta in *;
    repeat impl_obligation_tac1;
    first [ (** An order premise read off by inversion: a subterm, as the
                structural recursion needs *)
            solve [ assumption ]
            (** The member a shape's end stands for: its order is a
                premise of the shape's, so the recursive call is on a
                subterm *)
          | lazymatch goal with |- eval_mref_order _ _ _ _ _ => solve [ impl_obligation_split; impl_obligation_finish ] end
          | solve [ impl_obligation_finish ]
          | solve [ impl_obligation_split; impl_obligation_finish ]
            (** At a shape's end, the member's reference rules out the
                other end's member *)
          | solve [ impl_obligation_split;
                    try (match goal with H : eval_mref_order _ _ _ _ _ |- _ => dependent destruction H end);
                    impl_obligation_finish ]
          | impl_obligation_finish ].

  (** An obligation whose conclusion is an order stays transparent, since
      the guard condition sees it in the recursive calls; any other is
      proved opaquely. *)
  #[local]
  Ltac eval_obligation_auto :=
    intros;
    lazymatch goal with
    | |- eval_exp_order _ _ _ _ => eval_obligation
    | |- eval_app_order _ _ _ _ => eval_obligation
    | |- eval_exps_order _ _ _ _ => eval_obligation
    | |- eval_app_args_order _ _ _ _ _ => eval_obligation
    | |- eval_apps_order _ _ _ _ => eval_obligation
    | |- eval_modexp_order _ _ _ _ => eval_obligation
    | |- eval_close_order _ _ _ _ _ => eval_obligation
    | |- eval_appm_order _ _ _ _ => eval_obligation
    | |- eval_appms_order _ _ _ _ => eval_obligation
    | |- eval_sel_order _ _ _ _ => eval_obligation
    | |- eval_selm_order _ _ _ _ => eval_obligation
    | |- eval_selc_order _ _ _ _ => eval_obligation
    | |- eval_selmc_order _ _ _ _ => eval_obligation
    | |- eval_body_env_order _ _ _ _ => eval_obligation
    | |- eval_elim_order _ _ _ _ _ _ _ _ => eval_obligation
    | |- eval_mref_order _ _ _ _ _ => eval_obligation
    | |- eval_ihs_order _ _ _ _ _ _ _ _ => eval_obligation
    | |- eval_ih_order _ _ _ _ _ _ _ _ => eval_obligation
    | |- eval_shape_type_order _ _ _ _ _ _ => eval_obligation
    | |- eval_ihty_order _ _ _ _ _ _ _ _ _ => eval_obligation
    | |- eval_ihtys_order _ _ _ _ _ _ _ _ _ => eval_obligation
    | |- eval_projs_order _ _ _ _ => eval_obligation
    | |- eval_proj_order _ _ _ _ => eval_obligation
    | |- eval_neutral_fields_order _ _ _ _ _ => eval_obligation
    | |- eval_field_vals_order _ _ _ _ _ => eval_obligation
    | |- _ => abstract eval_obligation
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations eval_exp_impl m p (H : eval_exp_order Θ Ξ m p) : { d | ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | a_typ i, p, H => exist _ (d_univ i) _
  | a_univ M, p, H =>
      let (l, Hl) := eval_exp_impl M p _ in
      exist _ (d_suniv l) _
  | a_level n, p, H => exist _ (d_level n) _
  | a_level_sort, p, H => exist _ d_level_sort _
  | a_llit o, p, H => exist _ (domain_level_lit o) _
  | a_succl M, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      exist _ (domain_level_suc m) _
  | a_maxl M N, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (n, Hn) := eval_exp_impl N p _ in
      exist _ (domain_level_max m n) _
  | a_var x, p, H => exist _ (env_var p x) _
  | a_prop, p, H => exist _ d_prop _
  | a_True, p, H => exist _ d_True _
  | a_tt, p, H => exist _ (d_proof a_tt p) _
  | a_False, p, H => exist _ d_False _
  | a_absurd C M, p, H =>
      let (c, Hc) := eval_exp_impl C p _ in
      exist _ (d_neut c (d_absurd c (d_proof M p))) _
  | a_and P Q, p, H =>
      let (a, Ha) := eval_exp_impl P p _ in
      exist _ (d_and a p Q) _
  | a_conj P Q M N, p, H => exist _ (d_proof (a_conj P Q M N) p) _
  | a_left M, p, H => exist _ (d_proof (a_left M) p) _
  | a_right M, p, H => exist _ (d_proof (a_right M) p) _
  | a_proof P M, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      exist _ m _
  | a_ind pq k, p, H => exist _ (d_ind pq k nil) _
  | a_con pq k c, p, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_starts D Mk) := {
        | exist _ true Es => exist _ (d_con pq k c nil) _
        | exist _ false Es with inspect (im_head Mk) := {
          | exist _ (mh_view qc k' Is vm) Eh =>
              let (cups, Hc) := eval_exps_impl Is nil _ in
              exist _ (d_con qc k' c cups) _
          | exist _ (mh_record qr Is (_ :: _)) Eh => exist _ (d_con pq k c nil) _
          | exist _ (mh_record qr Is nil) Eh => exist _ (d_tuple nil) _
          | exist _ (mh_decl _) Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | a_elim ak_relevant pq Us j Bks M, p, H with eval_exps_impl Us p _ := {
    | exist _ ups Hups with eval_exp_impl M p _ := {
      | exist _ m Hm =>
          let (r, Hr) := eval_elim_impl p pq ups Bks j m _ in
          exist _ r _ } }
  | a_elim ak_propositional pq Us j Bks M, p, H => exist _ (d_proof (a_elim ak_propositional pq Us j Bks M) p) _
  | a_elim ak_level pq Us j Bks M, p, H => False_rect _ _
  | a_pi κd κc A B, p, H =>
      let (a, Ha) := eval_exp_impl A p _ in
      exist _ (d_pi κd κc a p B) _
  | a_fn A M, p, H =>
      let (a, Ha) := eval_exp_impl A p _ in
      exist _ (d_fn a p M) _
  (** An application, by the kind of the argument the function takes *)
  | a_app M N, p, H with eval_exp_impl M p _ := {
    | exist _ m Hm with evaluated_kind_decide (arg_kind Θ Ξ m) := {
      | left Hk =>
          let (n, Hn) := eval_exp_impl N p _ in
          let (a, Ha) := eval_app_impl m n _ in
          exist _ a _
      | right Hk =>
          let (a, Ha) := eval_app_impl m (d_proof N p) _ in
          exist _ a _ } }
  (** A local definition, by the kind of its type *)
  | a_let (b_def A M) B, p, H with eval_exp_impl A p _ := {
    | exist _ a Ha with evaluated_kind_decide (domain_kind a) := {
      | left Hk =>
          let (m, Hm) := eval_exp_impl M p _ in
          let (r, Hr) := eval_exp_impl B (p ↦ m ⦂ entry_type_value a) _ in
          exist _ r _
      | right Hk =>
          let (r, Hr) := eval_exp_impl B (p ↦ d_proof M p ⦂ entry_type_value a) _ in
          exist _ r _ } }
  | a_let (b_mod (gu_mk Δ D)) B, p, H =>
      let (h, Hh) := eval_close_impl Δ D p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ᵐ h ⦂ gu_mk Δ D) _ in
      exist _ r _
  (** A local definition with a module part: its unit's literal evaluated
      by its one rule, the unit's closure ([eval_me_lit]) *)
  | a_let (b_def_mod A M (gu_mk Δ D)) B, p, H =>
      let (a, Ha) := eval_exp_impl A p _ in
      let (m, Hm) := eval_exp_impl M p _ in
      let (h, Hh) := eval_close_impl Δ D p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ gu_mk Δ D) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := eval_modexp_impl R p _ in
        let (f, Hf) := eval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := eval_exps_impl args p _ in
        let (r, Hr) := eval_apps_impl f ns _ in
        exist _ r _ }
  | a_record pq, p, H => exist _ (d_record pq nil) _
  (** A record element: its type finds the record, whose kinds direct the
      fields *)
  | a_tuple T fs, p, H with eval_exp_impl T p _ := {
    | exist _ (d_record pq ns) Ht with inspect (record_lookup Θ Ξ pq) := {
      | exist _ (Some R) El =>
          let (vs, Hvs) := eval_field_vals_impl (record_field_kinds R) (List.map snd fs) p _ in
          exist _ (d_tuple (List.combine (List.map fst fs) vs)) _
      | exist _ None El => False_rect _ _ }
    | exist _ _ Ht => False_rect _ _ }
  | a_proj f M, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_proj_impl f m _ in
      exist _ r _

  with eval_proj_impl f m (H : eval_proj_order Θ Ξ f m) : { r | eval_proj Θ Ξ f m r } by struct H :=
  | f, d_tuple vs, H with inspect (field_lookup vs f) := {
    | exist _ (Some r) E => exist _ r _
    | exist _ None E => False_rect _ _ }
  | f, d_neut (d_record pq ns) m, H with inspect (record_lookup Θ Ξ pq) := {
    | exist _ (Some R) El with inspect (field_index (record_fields R) f) := {
      | exist _ (Some k) Ek with eval_neutral_fields_impl m (env_tele nil (List.rev (record_params R)) ns)
                                   (List.firstn (S k) (record_fields R)) _ := {
        | exist _ rs Hrs with inspect (List.nth_error rs k) := {
          | exist _ (Some r) Er => exist _ r _
          | exist _ None Er => False_rect _ _ } }
      | exist _ None Ek => False_rect _ _ }
    | exist _ None El => False_rect _ _ }
  | f, _, H => False_rect _ _

  with eval_neutral_fields_impl m p fl (H : eval_neutral_fields_order Θ Ξ m p fl) :
      { rs | eval_neutral_fields Θ Ξ m p fl rs } by struct H :=
  | m, p, nil, H => exist _ nil _
  | m, p, (g, T) :: fl, H =>
      let (a, Ha) := eval_exp_impl T p _ in
      let (rs, Hrs) := eval_neutral_fields_impl m (p ↦ ⇑ a (d_proj g m) ⦂ entry_type_closure T p) fl _ in
      exist _ (⇑ a (d_proj g m) :: rs) _

  with eval_elim_impl p pq ups Bks j m (H : eval_elim_order Θ Ξ p pq ups Bks j m) :
      { r | ⟦elim m at j of pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, pq, ups, Bks, j, d_con pc k c vs, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (ind_lookup Θ Ξ pc) := {
        | exist _ (Some Dq) Edq with inspect (ind_member Dq k) := {
          | exist _ (Some Mk) Emk with inspect (ind_con Mj c) := {
            | exist _ (Some gs) Ec with inspect (List.nth_error Bks j) := {
              | exist _ (Some b) Eb with inspect (brs_lookup (eb_brs b) c) := {
                | exist _ (Some (n, B)) Ebr =>
                    let (ihs, Hihs) := eval_ihs_impl p pq ups Bks gs (skipn (im_np Dq Mk) vs) _ in
                    let (r, Hr) := eval_exp_impl B (env_extend_typed p (branch_entries D Mj pq ups (blocks_motives Bks) p gs
                                                     (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs)) (skipn (im_np Dq Mk) vs) ihs)) _ in
                    exist _ r _
                | exist _ None Ebr => False_rect _ _ }
              | exist _ None Eb => False_rect _ _ }
            | exist _ None Ec => False_rect _ _ }
          | exist _ None Emk => False_rect _ _ }
        | exist _ None Edq => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | p, pq, ups, Bks, j, d_neut (d_ind pc k as') m, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (ind_lookup Θ Ξ pc) := {
        | exist _ (Some Dq) Edq with inspect (List.nth_error Bks j) := {
          | exist _ (Some b) Eb with eval_mref_impl pq ups j _ := {
            | exist _ (pc', k', cups) Hr =>
                let (a, Ha) := eval_exp_impl (eb_motive b)
                                 (env_extend_typed p (motive_entries D Mj ups (List.skipn (ind_nu Dq) as')
                                                        (d_ind pc k (cups ++ List.skipn (ind_nu Dq) as'))
                                                        (⇑ (d_ind pc k as') m))) _ in
                exist _ (⇑ a (d_elim p Bks pq ups j as' m)) _ }
          | exist _ None Eb => False_rect _ _ }
        | exist _ None Edq => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | p, pq, ups, Bks, j, _, H => False_rect _ _

  with eval_ihs_impl p pq ups Bks gs vs (H : eval_ihs_order Θ Ξ p pq ups Bks gs vs) :
      { ihs | ⟦ihs vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs } by struct H :=
  | p, pq, ups, Bks, nil, nil, H => exist _ nil _
  | p, pq, ups, Bks, ca_arg r T :: gs, v :: vs, H =>
      let (ihs, Hihs) := eval_ihs_impl p pq ups Bks gs vs _ in
      exist _ ihs _
  | p, pq, ups, Bks, ca_rec t :: gs, v :: vs, H =>
      let (ih, Hih) := eval_ih_impl p pq ups Bks t v _ in
      let (ihs, Hihs) := eval_ihs_impl p pq ups Bks gs vs _ in
      exist _ (ih ++ ihs) _
  | p, pq, ups, Bks, _, _, H => False_rect _ _

  with eval_ih_impl p pq ups Bks t v (H : eval_ih_order Θ Ξ p pq ups Bks t v) :
      { rs | ⟦ih v of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ rs } by struct H :=
  | p, pq, ups, Bks, pt_self j Ps, v, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_is_rview Mj) := {
        | exist _ false Ev =>
            let (r, Hr) := eval_elim_impl p pq ups Bks j v _ in
            exist _ (r :: nil) _
        | exist _ true Ev with inspect (im_head Mj) := {
          | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
            | exist _ ((c, gs) :: nil) Ec =>
                let (ws, Hws) := eval_projs_impl fl v _ in
                let (rs, Hrs) := eval_ihs_impl p pq ups Bks gs ws _ in
                exist _ rs _
            | exist _ _ Ec => False_rect _ _ }
          | exist _ _ Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | p, pq, ups, Bks, pt_pi B t, v, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed =>
        exist _ (List.map (fun i => d_ihfn p Bks pq ups t i v) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))) _
    | exist _ None Ed => False_rect _ _ }

  with eval_projs_impl fl v (H : eval_projs_order Θ Ξ fl v) : { ws | ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws } by struct H :=
  | nil, v, H => exist _ nil _
  | f :: fl, v, H =>
      let (w, Hw) := eval_proj_impl f v _ in
      let (ws, Hws) := eval_projs_impl fl v _ in
      exist _ (w :: ws) _

  with eval_mref_impl pq ups j (H : eval_mref_order Θ Ξ pq ups j) : { r | ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ r } by struct H :=
  | pq, ups, j, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_decl _) Eh => exist _ (pq, j, ups) _
        | exist _ (mh_view qc k Is vm) Eh =>
            let (cups, Hc) := eval_exps_impl Is (decl_env D ups) _ in
            exist _ (qc, k, cups) _
        | exist _ (mh_record _ _ _) Eh => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }

  with eval_shape_type_impl pq ups p t (H : eval_shape_type_order Θ Ξ pq ups p t) : { a | ⟦shty t of pq ups ⟧ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pq, ups, p, pt_self j Ps, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh =>
            let (cups, Hc) := eval_exps_impl Is (decl_env D ups) _ in
            exist _ (d_record qr cups) _
        | exist _ _ Eh with eval_exps_impl Ps p _ := {
          | exist _ bs Hbs with eval_mref_impl pq ups j _ := {
            | exist _ (pc, k, pre) Hm => exist _ (d_ind pc k (pre ++ bs)) _ } } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | pq, ups, p, pt_pi B t, H =>
      let (b, Hb) := eval_exp_impl B p _ in
      exist _ (Πᵈ{ak_relevant} b (nil ↦ d_shfam pq ups p B t ⦂ entry_type_none) fam_cod) _

  with eval_ihty_impl pq ups pm As p t v (H : eval_ihty_order Θ Ξ pq ups pm As p t v) :
      { as' | ⟦ihty v of t at pq ups under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ as' } by struct H :=
  | pq, ups, pm, As, p, pt_self j Ps, v, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_is_rview Mj) := {
        | exist _ false Ev =>
            let (bs, Hbs) := eval_exps_impl Ps p _ in
            let (a, Ha) := eval_exp_impl (List.nth j As a_prop)
                             (env_extend_typed pm (tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) bs ++
                                                   (v, entry_type_shape pq ups p (pt_self j Ps)) :: nil)) _ in
            exist _ (a :: nil) _
        | exist _ true Ev with inspect (im_head Mj) := {
          | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
            | exist _ ((c, gs) :: nil) Ec =>
                let (ws, Hws) := eval_projs_impl fl v _ in
                let (rs, Hrs) := eval_ihtys_impl pq ups pm As (decl_env D ups) gs ws _ in
                exist _ rs _
            | exist _ _ Ec => False_rect _ _ }
          | exist _ _ Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | pq, ups, pm, As, p, pt_pi B t, v, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed =>
        let (b, Hb) := eval_exp_impl B p _ in
        exist _ (List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam pm As pq ups p B t i v ⦂ entry_type_none) fam_cod)
                   (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))) _
    | exist _ None Ed => False_rect _ _ }

  with eval_ihtys_impl pq ups pm As p gs vs (H : eval_ihtys_order Θ Ξ pq ups pm As p gs vs) :
      { rs | ⟦ihtys vs of gs at pq ups under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ rs } by struct H :=
  | pq, ups, pm, As, p, nil, nil, H => exist _ nil _
  | pq, ups, pm, As, p, ca_arg r T :: gs, v :: vs, H =>
      let (rs, Hrs) := eval_ihtys_impl pq ups pm As (p ↦ v ⦂ entry_type_closure T p) gs vs _ in
      exist _ rs _
  | pq, ups, pm, As, p, ca_rec t :: gs, v :: vs, H =>
      let (rs1, Hrs1) := eval_ihty_impl pq ups pm As p t v _ in
      let (rs, Hrs) := eval_ihtys_impl pq ups pm As p gs vs _ in
      exist _ (rs1 ++ rs) _
  | pq, ups, pm, As, p, _, _, H => False_rect _ _

  with eval_app_impl m n (H : eval_app_order Θ Ξ m n) : { d | $| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | d_fn a p M, n, H =>
      let (m, Hm) := eval_exp_impl M (p ↦ n ⦂ entry_type_value a) _ in
      exist _ m _
  | d_neut (d_pi κd κc a p B) m, n, H =>
      let (b, Hb) := eval_exp_impl B (p ↦ n ⦂ entry_type_value a) _ in
      exist _ (⇑ b (m $ᵈ ⇓ a n)) _
  | d_ind pq k as', n, H => exist _ (d_ind pq k (as' ++ n :: nil)) _
  | d_record pq ns, n, H => exist _ (d_record pq (ns ++ n :: nil)) _
  | d_con pq k c vs, n, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_head Mk) := {
        | exist _ (mh_decl _) Eh => exist _ (d_con pq k c (vs ++ n :: nil)) _
        | exist _ (mh_view qc k' Is vm) Eh with inspect (S (List.length vs) <? ind_nu D) := {
          | exist _ true El => exist _ (d_con pq k c (vs ++ n :: nil)) _
          | exist _ false El =>
              let (cups, Hc) := eval_exps_impl Is (decl_env D (vs ++ n :: nil)) _ in
              exist _ (d_con qc k' c cups) _ }
        | exist _ (mh_record qr Is fl) Eh with inspect (S (List.length vs) <? ind_nu D + List.length fl) := {
          | exist _ true El => exist _ (d_con pq k c (vs ++ n :: nil)) _
          | exist _ false El => exist _ (d_tuple (List.combine fl (List.skipn (ind_nu D) (vs ++ n :: nil)))) _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | d_ihfn p Bks pq ups t i f, n, H with eval_app_impl f n _ := {
    | exist _ fn Hfn with eval_ih_impl p pq ups Bks t fn _ := {
      | exist _ rs Hrs with inspect (List.nth_error rs i) := {
        | exist _ (Some r) Er => exist _ r _
        | exist _ None Er => False_rect _ _ } } }
  | d_shfam pq ups p B t, n, H =>
      let (a, Ha) := eval_shape_type_impl pq ups (p ↦ n ⦂ entry_type_closure B p) t _ in
      exist _ a _
  | d_ihfam pm As pq ups p B t i f, n, H with eval_app_impl f n _ := {
    | exist _ fn Hfn with eval_ihty_impl pq ups pm As (p ↦ n ⦂ entry_type_closure B p) t fn _ := {
      | exist _ as' Has with inspect (List.nth_error as' i) := {
        | exist _ (Some a) Ea => exist _ a _
        | exist _ None Ea => False_rect _ _ } } }
  | d_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selc_impl h' ch _ in
      exist _ r _
  | _, n, H => False_rect _ _

  with eval_exps_impl Ms p (H : eval_exps_order Θ Ξ Ms p) : { ms | ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (ms, Hms) := eval_exps_impl Ms p _ in
      exist _ (m :: ms) _

  (** A function applied to terms, by the kind of each argument it takes *)
  with eval_app_args_impl f Ms p (H : eval_app_args_order Θ Ξ f Ms p) : { r | eval_app_args Θ Ξ f Ms p r } by struct H :=
  | f, nil, p, H => exist _ f _
  | f, N :: Ns, p, H with evaluated_kind_decide (arg_kind Θ Ξ f) := {
    | left Hk =>
        let (n, Hn) := eval_exp_impl N p _ in
        let (g, Hg) := eval_app_impl f n _ in
        let (r, Hr) := eval_app_args_impl g Ns p _ in
        exist _ r _
    | right Hk =>
        let (g, Hg) := eval_app_impl f (d_proof N p) _ in
        let (r, Hr) := eval_app_args_impl g Ns p _ in
        exist _ r _ }

  with eval_field_vals_impl rs Ms p (H : eval_field_vals_order Θ Ξ rs Ms p) :
      { ms | eval_field_vals Θ Ξ rs Ms p ms } by struct H :=
  | rs, nil, p, H => exist _ nil _
  | rs, M :: Ms, p, H with evaluated_kind_decide (List.hd ak_relevant rs) := {
    | left Hk =>
        let (m, Hm) := eval_exp_impl M p _ in
        let (ms, Hms) := eval_field_vals_impl (List.tl rs) Ms p _ in
        exist _ (m :: ms) _
    | right Hk =>
        let (ms, Hms) := eval_field_vals_impl (List.tl rs) Ms p _ in
        exist _ (d_proof M p :: ms) _ }

  with eval_apps_impl m ns (H : eval_apps_order Θ Ξ m ns) : { r | $*| m & ns | Θ ⍮ Ξ ↘ r } by struct H :=
  | m, nil, H => exist _ m _
  | m, n :: ns, H =>
      let (m1, Hm1) := eval_app_impl m n _ in
      let (r, Hr) := eval_apps_impl m1 ns _ in
      exist _ r _

  with eval_modexp_impl M p (H : eval_modexp_order Θ Ξ M p) : { h | ⟦ M ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | me_var x, p, H => exist _ (env_mod p x) _
  | me_unit fp, p, H => exist _ (dm_global (q_abs fp nil) nil) _
  | me_lit (gu_mk Δ D), p, H =>
      let (h, Hh) := eval_close_impl Δ D p _ in
      exist _ h _
  | me_mem M y, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (r, Hr) := eval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (n, Hn) := eval_exp_impl N p _ in
      let (r, Hr) := eval_appm_impl h n _ in
      exist _ r _

  with eval_close_impl Δ D p (H : eval_close_order Θ Ξ Δ D p) : { h | ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  (** A body: the closure of its expansion *)
  | Δ, md_body sm Φ, p, H => exist _ (dm_local Δ (md_body sm (gm_expand Φ)) p) _
  | e :: Δ, md_alias E, p, H => exist _ (dm_local (e :: Δ) (md_alias E) p) _
  | nil, md_alias E, p, H =>
      let (h, Hh) := eval_modexp_impl E p _ in
      exist _ h _

  with eval_appm_impl h n (H : eval_appm_order Θ Ξ h n) : { r | $ᵐ| h & n | Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local Δ D p, n, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass κ A)) Es =>
        let (r, Hr) := eval_close_impl Δ0 D (p ↦ n ⦂ entry_type_closure A p) _ in
        exist _ r _
    | exist _ _ Es => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selmc_impl h' ch _ in
      exist _ r _

  with eval_appms_impl h ns (H : eval_appms_order Θ Ξ h ns) : { r | $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r } by struct H :=
  | h, nil, H => exist _ h _
  | h, n :: ns, H =>
      let (h1, Hh1) := eval_appm_impl h n _ in
      let (r, Hr) := eval_appms_impl h1 ns _ in
      exist _ r _

  with eval_sel_impl h x (H : eval_sel_order Θ Ξ h x) : { r | h ·ₜ x Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, x, H with module_saturated_r pq args := {
    (** A member of a global module lacking a parameter: a member closure *)
    | right Hu => exist _ (d_member (dm_global pq args) (x :: nil)) _
    | left Hs with inspect (gc_term Θ Ξ (qname_app pq (x :: nil))) := {
      (** A term part: it, applied to the arguments *)
      | exist _ (Some M) Et =>
          let (f, Hf) := eval_exp_impl M nil _ in
          let (r, Hr) := eval_apps_impl f args _ in
          exist _ r _
      | exist _ None Et with inspect (gc_resolve Θ Ξ (qname_app pq (x :: nil))) := {
        | exist _ (Some (ge_def b pv κ A B)) Er with evaluated_kind_decide κ := {
          (** An opaque definition or an axiom: a neutral, applied *)
          | left Hk =>
              let (a, Ha) := eval_exp_impl A nil _ in
              let (r, Hr) := eval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
              exist _ r _
          (** A proof member, at exactly the module's parameters: kept as
              the selection *)
          | right Hk with module_exact_r pq args := {
            | inleft (exist _ T HT) => exist _ (d_proof (member_proof x) (global_proof_env pq T args)) _
            | inright Hne => False_rect _ _ } }
        | exist _ (Some _) Er => False_rect _ _
        | exist _ None Er with inspect (ind_mlookup Θ Ξ (qname_app pq (x :: nil))) := {
          (** The module of a member of a group: its type former, applied *)
          | exist _ (Some (pg, k, D)) Ed =>
              let (r, Hr) := eval_apps_impl (d_ind pg k nil) args _ in
              exist _ r _
          | exist _ None Ed with inspect (record_lookup Θ Ξ (qname_app pq (x :: nil))) := {
            (** A record type: its type former, applied *)
            | exist _ (Some R) El =>
                let (r, Hr) := eval_apps_impl (d_record (qname_app pq (x :: nil)) nil) args _ in
                exist _ r _
            | exist _ None El => False_rect _ _ } } } } }
  | dm_local (e :: Δ) D p, x, H => exist _ (d_member (dm_local (e :: Δ) D p) (x :: nil)) _
  (** A member of a saturated body, read in its expansion *)
  | dm_local nil (md_body sm Φ) p, x, H with inspect (gm_prefix_upto (gm_expand Φ) x) := {
    | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_tm E) := {
      | exist _ (Some (A, M)) Et with evaluated_kind_decide (entry_kind E) := {
        | left Hk =>
            let (p', Hp') := eval_body_env_impl p Φ' _ in
            let (r, Hr) := eval_exp_impl M p' _ in
            exist _ r _
        (** A proof member: kept as the selection *)
        | right Hk =>
            exist _ (d_proof (member_proof x) (p ↦ᵐ dm_local nil (md_body sm Φ) p ⦂ gu_mk nil (md_body sm Φ))) _ }
      | exist _ None Et => False_rect _ _ }
    | exist _ _ P => False_rect _ _ }
  | dm_local nil (md_alias E) p, x, H => False_rect _ _
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with eval_selm_impl h y (H : eval_selm_order Θ Ξ h y) : { r | h ·ₘ y Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, y, H with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh) := eval_close_impl Δ D nil _ in
        let (r, Hr) := eval_appms_impl h args _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local (e :: Δ) D p, y, H => exist _ (dm_member (dm_local (e :: Δ) D p) (y :: nil)) _
  | dm_local nil (md_body sm Φ) p, y, H with inspect (gm_prefix_upto (gm_expand Φ) y) := {
    | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_unit E) := {
      | exist _ (Some (gu_mk Δy Dy)) Eu =>
          let (p', Hp') := eval_body_env_impl p Φ' _ in
          let (r, Hr) := eval_close_impl Δy Dy p' _ in
          exist _ r _
      | exist _ None Eu => False_rect _ _ }
    | exist _ _ P => False_rect _ _ }
  | dm_local nil (md_alias E) p, y, H => False_rect _ _
  | dm_member h ch, y, H => exist _ (dm_member h (ch ++ y :: nil)) _

  with eval_selc_impl h ch (H : eval_selc_order Θ Ξ h ch) : { r | h ·ₜ* ch Θ ⍮ Ξ ↘ r } by struct H :=
  | h, x :: nil, H =>
      let (r, Hr) := eval_sel_impl h x _ in
      exist _ r _
  | h, y :: ch, H =>
      let (h1, Hh1) := eval_selm_impl h y _ in
      let (r, Hr) := eval_selc_impl h1 ch _ in
      exist _ r _
  | h, nil, H => False_rect _ _

  with eval_selmc_impl h ch (H : eval_selmc_order Θ Ξ h ch) : { r | h ·ₘ* ch Θ ⍮ Ξ ↘ r } by struct H :=
  | h, nil, H => exist _ h _
  | h, y :: ch, H =>
      let (h1, Hh1) := eval_selm_impl h y _ in
      let (r, Hr) := eval_selmc_impl h1 ch _ in
      exist _ r _

  with eval_body_env_impl p Φ (H : eval_body_env_order Θ Ξ p Φ) : { p' | ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' } by struct H :=
  | p, gm_nil, H => exist _ p _
  (** A definition: the body before it, the first premise of both its
      rules, then by its kind *)
  | p, gm_ext Φ y (ge_def b pv κ A (Some M)), H with eval_body_env_impl p Φ _ := {
    | exist _ p1 Hp1 with evaluated_kind_decide κ := {
      | left Hk =>
          let (m, Hm) := eval_exp_impl M p1 _ in
          exist _ (p1 ↦ m ⦂ entry_type_closure A p1) _
      (** A definition tagged a proposition: kept as it is *)
      | right Hk => exist _ (p1 ↦ d_proof M p1 ⦂ entry_type_closure A p1) _ } }
  | p, gm_ext Φ y (ge_mod pm (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := eval_body_env_impl p Φ _ in
      let (h, Hh) := eval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵐ h ⦂ gu_mk Δy Dy) _
  | p, gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := eval_body_env_impl p Φ _ in
      let (m, Hm) := eval_exp_impl M p1 _ in
      let (h, Hh) := eval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵈ m ⦂ entry_type_closure A p1 ‖ h ⦂ gu_mk Δy Dy) _
  | p, _, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([eval_obligation]); one whose conclusion is not an order is proved
    opaquely ([eval_obligation_auto]). *)
Solve All Obligations with eval_obligation_auto.
End EvalImpl.

(** The [eval_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the evaluation orders and the functionality
    of evaluation. *)

#[local]
Ltac functional_eval_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_eval_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma eval_exp_impl_complete : forall Θ Ξ M p m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
    exists H H', eval_exp_impl Θ Ξ M p H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall Θ Ξ m n r,
    $| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', eval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.
