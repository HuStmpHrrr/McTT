From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Evaluation Readback.
From Mctt.Extraction Require Import Kinds.
From Mctt.Extraction Require Export Lookup.
Import Domain_Notations.

Generalizable All Variables.

(** * The Evaluator the Checker Runs

    The evaluator of the relation of [Extraction.FastEval]: the reference one
    ([Reference.Evaluation]) but for the eliminator of an inductive type,
    which at a constructor does not compute a recursive result that the
    branch does not read, one recursive argument at a time. *)

(** The termination orders mirror the evaluation relations, one for each, in
    the same global context.  A transparent global recurses into its resolved
    body; an alias recurses into its target.  Each premise that uses a value
    is quantified over the values its earlier premises evaluate to.  A
    proof is never evaluated, so a term kept as a proof has no premise. *)

Inductive eval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
| eval_exp_order_typ :
  `( eval_exp_order Θ Ξ Typeω@i p )
(** A small universe evaluates its level. *)
| eval_exp_order_univ :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ Type⟨M⟩ p )
(** An environment is total, so a variable always terminates. *)
| eval_exp_order_var :
  `( eval_exp_order Θ Ξ #x p )
| eval_exp_order_level :
  `( eval_exp_order Θ Ξ (Level@n) p )
| eval_exp_order_level_sort :
  `( eval_exp_order Θ Ξ LevelSort p )
| eval_exp_order_llit :
  `( eval_exp_order Θ Ξ (𝕃ᵒ o) p )
| eval_exp_order_succl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ (succl M) p )
| eval_exp_order_maxl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     eval_exp_order Θ Ξ (maxl M N) p )
(** [Prop] *)
| eval_exp_order_prop :
  `( eval_exp_order Θ Ξ Propₘ p )
| eval_exp_order_True :
  `( eval_exp_order Θ Ξ ⊤ p )
(** The introduction of [⊤], a proof: nothing evaluated *)
| eval_exp_order_tt :
  `( eval_exp_order Θ Ξ a_tt p )
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
(** The proofs of a conjunction and of its components: nothing evaluated *)
| eval_exp_order_conj :
  `( eval_exp_order Θ Ξ (a_conj P Q M N) p )
| eval_exp_order_left :
  `( eval_exp_order Θ Ξ (a_left M) p )
| eval_exp_order_right :
  `( eval_exp_order Θ Ξ (a_right M) p )
(** A [Π], at its kinds: its domain *)
| eval_exp_order_pi :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ (a_pi κd κc A B) p )
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
    the elimination at the group it names *)
| eval_exp_order_elim :
  `( eval_exps_order Θ Ξ Us p ->
     eval_exp_order Θ Ξ M p ->
     (forall ups m, ⟦ Us ⟧* Θ ⍮ Ξ ⍮ p ↘ ups -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
        eval_elim_order Θ Ξ p pq ups Bks j m) ->
     eval_exp_order Θ Ξ (a_elim ak_relevant pq Us j Bks M) p )
(** An eliminator into propositions: nothing evaluated *)
| eval_exp_order_elim_proof :
  `( eval_exp_order Θ Ξ (a_elim ak_propositional pq Us j Bks M) p )
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
| eval_exp_order_let_mod :
  `( eval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h -> eval_exp_order Θ Ξ B (p ↦ᵐ h ⦂ gu_mk Δ D)) ->
     eval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
(** A local definition with a module part: its type, its body and the
    closure of its unit, as its literal evaluates ([eval_me_lit]), then the
    rest.  The unit's premise is the closure's order, not the literal's,
    so that the order of the type is read off as a subterm. *)
| eval_exp_order_let_dm :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ M p ->
     eval_close_order Θ Ξ Δ D p ->
     (forall a m h, ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h ->
        eval_exp_order Θ Ξ B (p ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ gu_mk Δ D)) ->
     eval_exp_order Θ Ξ (ℓᵈ A ≔ M ‖ (gu_mk Δ D) in B) p )
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

(** The neutral projections at a list of fields, as [eval_neutral_fields] reads
    them *)
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
(** On a saturated constructor: the recursive results the branch reads,
    then the branch, at its typed entries.  The group's table of leaf
    paths is coherent, the gate [eval_elim_con] has: a premise of the
    domain, not a check the evaluator runs *)
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
(** A non-recursive argument *)
| eval_ihs_order_arg :
  `( eval_ihs_order Θ Ξ p pq ups Bks gs vs ->
     eval_ihs_order Θ Ξ p pq ups Bks (ca_arg r T :: gs) (v :: vs) )
(** A recursive argument: its results, then the rest *)
| eval_ihs_order_rec_case :
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
(** At the end, at a record view: the projections, then all their
    recursive results *)
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

with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| eval_app_order_fn :
  `( eval_exp_order Θ Ξ M (p ↦ n ⦂ entry_type_value a) ->
     eval_app_order Θ Ξ (λᵈ a p M) n )
(** A neutral at a [Π] into an evaluated kind: the codomain's instance *)
| eval_app_order_neut :
  `( evaluated_kind κc ->
     eval_exp_order Θ Ξ B (p ↦ n ⦂ entry_type_value a) ->
     eval_app_order Θ Ξ (⇑ (d_pi κd κc a p B) m) n )
| eval_app_order_indty :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     eval_app_order Θ Ξ (d_ind pq k as') n )
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
| eval_app_order_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', $ᵐ| h & n | Θ ⍮ Ξ ↘ h' -> eval_selc_order Θ Ξ h' ch) ->
     eval_app_order Θ Ξ (d_member h ch) n )
(** A record's type former, before its last parameter *)
| eval_app_order_record :
  `( record_lookup Θ Ξ pq = Some R ->
     List.length ns < List.length (record_params R) ->
     eval_app_order Θ Ξ (d_record pq ns) n )

with eval_exps_order (Θ : gdeps) (Ξ : gstack) : list exp -> env -> Prop :=
| eval_exps_order_nil :
  `( eval_exps_order Θ Ξ nil p )
| eval_exps_order_cons :
  `( eval_exp_order Θ Ξ M p ->
     eval_exps_order Θ Ξ Ms p ->
     eval_exps_order Θ Ξ (M :: Ms) p )

with eval_apps_order (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> Prop :=
| eval_apps_order_nil :
  `( eval_apps_order Θ Ξ m nil )
| eval_apps_order_cons :
  `( eval_app_order Θ Ξ m n ->
     (forall m1, $| m & n | Θ ⍮ Ξ ↘ m1 -> eval_apps_order Θ Ξ m1 args) ->
     eval_apps_order Θ Ξ m (n :: args) )

with eval_modexp_order (Θ : gdeps) (Ξ : gstack) : modexp -> env -> Prop :=
| eval_modexp_order_var :
  `( eval_modexp_order Θ Ξ (me_var x) p )
| eval_modexp_order_unit :
  `( eval_modexp_order Θ Ξ (me_unit fp) p )
| eval_modexp_order_lit :
  `( eval_close_order Θ Ξ Δ D p ->
     eval_modexp_order Θ Ξ (me_lit (gu_mk Δ D)) p )
| eval_modexp_order_mem :
  `( eval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selm_order Θ Ξ h y) ->
     eval_modexp_order Θ Ξ (me_mem H y) p )
| eval_modexp_order_app :
  `( eval_modexp_order Θ Ξ H p ->
     eval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_appm_order Θ Ξ h n) ->
     eval_modexp_order Θ Ξ (me_app H N) p )

with eval_close_order (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> Prop :=
| eval_close_order_body :
  `( eval_close_order Θ Ξ Δ (md_body sm Φ) p )
| eval_close_order_alias :
  `( eval_close_order Θ Ξ (e :: Δ) (md_alias E) p )
| eval_close_order_alias0 :
  `( eval_modexp_order Θ Ξ E p ->
     eval_close_order Θ Ξ nil (md_alias E) p )

with eval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| eval_appm_order_global :
  `( eval_appm_order Θ Ξ (dm_global pq args) n )
(** The outermost missing parameter is split off as the evaluator splits
    it off ([tele_snoc]), so that the order of the rest is a premise of the
    order of the whole. *)
| eval_appm_order_local :
  `( tele_snoc Δ = Some (Δ0, ce_ass κ A) ->
     eval_close_order Θ Ξ Δ0 D (p ↦ n ⦂ entry_type_closure A p) ->
     eval_appm_order Θ Ξ (dm_local Δ D p) n )
| eval_appm_order_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', $ᵐ| h & n | Θ ⍮ Ξ ↘ h' -> eval_selmc_order Θ Ξ h' ch) ->
     eval_appm_order Θ Ξ (dm_member h ch) n )

with eval_appms_order (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> Prop :=
| eval_appms_order_nil :
  `( eval_appms_order Θ Ξ h nil )
| eval_appms_order_cons :
  `( eval_appm_order Θ Ξ h n ->
     (forall h1, $ᵐ| h & n | Θ ⍮ Ξ ↘ h1 -> eval_appms_order Θ Ξ h1 ns) ->
     eval_appms_order Θ Ξ h (n :: ns) )

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

with eval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| eval_selm_order_global :
  `( gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
| eval_selm_order_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     eval_close_order Θ Ξ Δ D nil ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ nil ↘ h -> eval_appms_order Θ Ξ h args) ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
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
| eval_selm_order_member :
  `( eval_selm_order Θ Ξ (dm_member h ch) y )

with eval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| eval_selc_order_one :
  `( eval_sel_order Θ Ξ h x ->
     eval_selc_order Θ Ξ h (x :: nil) )
| eval_selc_order_cons :
  `( eval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘ y Θ ⍮ Ξ ↘ h1 -> eval_selc_order Θ Ξ h1 (z :: ch)) ->
     eval_selc_order Θ Ξ h (y :: z :: ch) )

with eval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| eval_selmc_order_nil :
  `( eval_selmc_order Θ Ξ h nil )
| eval_selmc_order_cons :
  `( eval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘ y Θ ⍮ Ξ ↘ h1 -> eval_selmc_order Θ Ξ h1 ch) ->
     eval_selmc_order Θ Ξ h (y :: ch) )

with eval_body_env_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| eval_body_env_order_nil :
  `( eval_body_env_order Θ Ξ p gm_nil )
(** A definition of an evaluated kind: the body before it, then its body *)
| eval_body_env_order_def :
  `( evaluated_kind κ ->
     eval_body_env_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_exp_order Θ Ξ M p1) ->
     eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def b pv κ A (Some M))) )
(** A definition tagged a proposition: the body before it *)
| eval_body_env_order_def_proof :
  `( eval_body_env_order Θ Ξ p Φ ->
     eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def b pv ak_propositional A (Some M))) )
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
  eval_field_vals_order : mctt.

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
        pose proof (functional_eval_exps _ _ _ _ H1 H2); subst; clear H2
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
        pose proof (functional_eval_field_vals _ _ _ _ _ _ H1 H2); subst; clear H2
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
    (forall p pq ups Bks gs vs ihs, ⟦ihs vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs ->
       eval_ihs_order Θ Ξ p pq ups Bks gs vs) /\
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
    (** The evaluator does not apply a function along terms. *)
    (forall f Ms p r, eval_app_args Θ Ξ f Ms p r -> True).
Proof.
  intros Θ Ξ; apply eval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : eval_selc _ _ _ ?c _ |- eval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    (** A proof is never an evaluated kind, nor the kind of an evaluated
        argument a proof's. *)
    solve [ econstructor; try eassumption; intros; functional_eval_all;
            first [ solve [ eauto using tele_snoc_app ]
                  | exfalso; eapply evaluated_kind_not_propositional; eassumption
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

Lemma eval_ihty_order_sound : forall Θ Ξ pq ups pm A p t v a, ⟦ihty v of t at pq ups under pm A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
    eval_ihty_order Θ Ξ pq ups pm A p t v.
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

#[export]
Hint Resolve eval_exp_order_sound eval_app_order_sound eval_exps_order_sound eval_modexp_order_sound
  eval_shape_type_order_sound eval_ihty_order_sound eval_ih_order_sound eval_mref_order_sound
  eval_proj_order_sound eval_projs_order_sound : mctt.

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

(** The recursive results of an argument are those of a group with a
    declaration. *)
Lemma eval_ih_order_lookup : forall Θ Ξ p pq ups Bks t v,
    eval_ih_order Θ Ξ p pq ups Bks t v -> exists D, ind_lookup Θ Ξ pq = Some D.
Proof. intros * H; inversion H; eauto. Qed.

(** ** Right Typed Entries

    The typed entries evaluation extends environments by are right when the
    values and environments they are made of are. *)
Section TypedEntriesOk.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** Typed values each right *)
  Definition fvalue_types_ok (vts : list (fdomain * fentry_type)) : Prop :=
    Forall (fun vt => fdomain_ok Θ Ξ (fst vt) /\ fentry_type_ok Θ Ξ (snd vt)) vts.

  Lemma fdecl_env_ok : forall D ups, Forall (fdomain_ok Θ Ξ) ups -> fenv_ok Θ Ξ (fdecl_env D ups).
  Proof. intros; unfold fdecl_env; apply fenv_tele_ok; [ constructor | assumption ]. Qed.

  Lemma fcargs_entries_ok : forall p ups vs ρ gs, Forall (fdomain_ok Θ Ξ) ups -> fenv_ok Θ Ξ ρ -> Forall (fdomain_ok Θ Ξ) vs ->
      fvalue_types_ok (fcargs_entries p ups ρ gs vs).
  Proof.
    intros p ups vs; induction vs as [| v vs IH]; intros ρ [| [r A | t] gs] Hu Hρ Hv; inversion Hv; subst; cbn; constructor.
    all: try (split; [ assumption | constructor; assumption ]).
    all: try (split; [ assumption | constructor ]).
    all: try (apply IH; [ assumption | | assumption ];
              first [ assumption | apply fextend_env_ok; [ assumption | assumption | constructor; assumption ] ]).
  Qed.

  Lemma fihs_types_ok : forall D p ups ρm As gs vs ρ, Forall (fdomain_ok Θ Ξ) ups -> fenv_ok Θ Ξ ρm -> fenv_ok Θ Ξ ρ ->
      Forall (fdomain_ok Θ Ξ) vs -> Forall (fentry_type_ok Θ Ξ) (fihs_types D p ups ρm As ρ gs vs).
  Proof.
    intros D p ups ρm As gs; induction gs as [| [r A | t] gs IH]; intros [| v vs] ρ Hu Hm Hρ Hv; cbn; try constructor;
      inversion Hv; subst.
    - apply IH; [ assumption | assumption | | assumption ]; apply fextend_env_ok; [ assumption | assumption | constructor; assumption ].
    - apply Forall_app; split; [ apply Forall_map, Forall_forall; intros; constructor; assumption | apply IH; assumption ].
  Qed.

  Lemma fpair_values_with_types_ok : forall vs ts, Forall (fdomain_ok Θ Ξ) vs -> Forall (fentry_type_ok Θ Ξ) ts ->
      fvalue_types_ok (fpair_values_with_types vs ts).
  Proof.
    induction vs as [| v vs IH]; intros ts Hv Ht; cbn; constructor; inversion Hv; subst.
    - split; [ assumption | destruct ts; cbn; [ constructor | inversion Ht; assumption ] ].
    - apply IH; [ assumption | destruct ts; cbn; [ constructor | inversion Ht; assumption ] ].
  Qed.

  Lemma ftele_entries_types_ok : forall vs ρ T, fenv_ok Θ Ξ ρ -> Forall (fdomain_ok Θ Ξ) vs -> fvalue_types_ok (ftele_entries ρ T vs).
  Proof. intros; apply ftele_entries_ok; assumption. Qed.

  Lemma fbranch_entries_ok : forall D Mj p ups As ρm gs ns vs ihs,
      Forall (fdomain_ok Θ Ξ) ups -> fenv_ok Θ Ξ ρm -> Forall (fdomain_ok Θ Ξ) ns -> Forall (fdomain_ok Θ Ξ) vs ->
      Forall (fdomain_ok Θ Ξ) ihs -> fvalue_types_ok (fbranch_entries D Mj p ups As ρm gs ns vs ihs).
  Proof.
    intros * Hu Hm Hn Hv Hi; unfold fbranch_entries, fvalue_types_ok.
    assert (Hd : fenv_ok Θ Ξ (fdecl_env D ups)) by (apply fdecl_env_ok; assumption).
    assert (Ht : fvalue_types_ok (ftele_entries (fdecl_env D ups) (List.rev (im_nparams Mj)) ns)) by (apply ftele_entries_types_ok; assumption).
    assert (Ha : fenv_ok Θ Ξ (fenv_extend_typed (fdecl_env D ups) (ftele_entries (fdecl_env D ups) (List.rev (im_nparams Mj)) ns)))
      by (apply fenv_extend_typed_ok; assumption).
    apply Forall_app; split; [ exact Ht |]; apply Forall_app; split;
      [ apply fcargs_entries_ok; assumption | apply fpair_values_with_types_ok; [ assumption | apply fihs_types_ok; assumption ] ].
  Qed.

  Lemma fmotive_entries_ok : forall D Mk ups ns a m, Forall (fdomain_ok Θ Ξ) ups -> Forall (fdomain_ok Θ Ξ) ns ->
      fdomain_ok Θ Ξ a -> fdomain_ok Θ Ξ m -> fvalue_types_ok (fmotive_entries D Mk ups ns a m).
  Proof.
    intros; unfold fmotive_entries, fvalue_types_ok; apply Forall_app; split;
      [ apply ftele_entries_types_ok; [ apply fdecl_env_ok |]; assumption | constructor; [ split; [| constructor ] | constructor ]; assumption ].
  Qed.

  Lemma fglobal_proof_env_ok : forall p T args, Forall (fdomain_ok Θ Ξ) args -> fenv_ok Θ Ξ (fglobal_proof_env p T args).
  Proof.
    intros; unfold fglobal_proof_env; apply fextend_env_mod_ok; [ apply fenv_tele_ok; [ constructor | assumption ] | constructor; assumption ].
  Qed.

  (** The environment of a branch, at the arguments of a constructor value
      split at its parameters: right ([fbranch_entries_ok]). *)
  Lemma fenv_extend_branch_ok : forall D Mj pq ups As ρ gs n1 n2 n3 vs ihs,
      fenv_ok Θ Ξ ρ -> Forall (fdomain_ok Θ Ξ) ups -> Forall (fdomain_ok Θ Ξ) vs -> Forall (fdomain_ok Θ Ξ) ihs ->
      fenv_ok Θ Ξ (fenv_extend_typed ρ (fbranch_entries D Mj pq ups As ρ gs (List.skipn n1 (List.firstn n2 vs)) (List.skipn n3 vs) ihs)).
  Proof.
    intros; apply fenv_extend_typed_ok; [ assumption | apply fbranch_entries_ok ];
      auto using Forall_skipn_intro, Forall_firstn_intro.
  Qed.

  (** The environment of the motive at a stuck scrutinee of a member type:
      right ([fmotive_entries_ok]). *)
  Lemma fenv_extend_motive_ok : forall ρ D Mj ups as' pc oDq k cups m n,
      fenv_ok Θ Ξ ρ -> Forall (fdomain_ok Θ Ξ) ups -> fdomain_ok Θ Ξ (fd_neut (fd_ind pc oDq k as') m) ->
      Forall (fdomain_ok Θ Ξ) cups ->
      fenv_ok Θ Ξ (fenv_extend_typed ρ (fmotive_entries D Mj ups (List.skipn n as') (fd_ind pc oDq k (cups ++ List.skipn n as'))
                                         (fd_neut (fd_ind pc oDq k as') m))).
  Proof.
    intros; ok_invert.
    apply fenv_extend_typed_ok; [ assumption | apply fmotive_entries_ok ]; eauto 8 using Forall_skipn_intro, Forall_app with mctt.
  Qed.
End TypedEntriesOk.

#[local] Hint Resolve fdecl_env_ok fbranch_entries_ok fmotive_entries_ok fglobal_proof_env_ok
  fenv_extend_branch_ok fenv_extend_motive_ok : mctt.
(** The erasure of an element found, for the obligations' [eauto] *)
#[local] Hint Resolve nth_error_map_some field_lookup_erase_some : core.
#[local] Hint Extern 1 => match goal with |- context [ List.length (List.map _ _) ] => rewrite List.length_map end : core.
#[local] Hint Resolve fdomain_kind_erase_eq : core.

(** A prefix up to a name ends with the entry of that name. *)
Lemma gm_prefix_upto_ext : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 -> exists Φ0 E, Φ1 = gm_ext Φ0 y E.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg IHg]; intros * Hp; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as <-; eauto | eauto ].
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

(** The operations on fast values, read through their erasure equations *)
#[local] Opaque fenv_var fenv_type fenv_mod fextend_env fextend_env_mod fextend_env_dm fenv_extend_typed fenv_tele
  fdomain_level_suc fdomain_level_max fdomain_level_lit fdm_clo fkinds_pads fkinds_body_entry carry
  fdecl_env fbranch_entries fmotive_entries fglobal_proof_env.

(** A value a definition stores, right: its body's fast evaluation in the
    empty environment, and right itself *)
Lemma stored_def_value : forall Θ Ξ b pv r A M v, fentry_values_ok Θ Ξ (fe_def b pv r A (Some M) (Some v)) ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ fenv_erase nil ↘ fdomain_erase v /\ fdomain_ok Θ Ξ v.
Proof. intros * [He Hv]; split; assumption. Qed.

(** Alike, of a definition with a module part, for its term *)
Lemma stored_dm_value : forall Θ Ξ pv A M u v, fentry_values_ok Θ Ξ (fe_def_mod pv A M u (Some v)) ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ fenv_erase nil ↘ fdomain_erase v /\ fdomain_ok Θ Ξ v.
Proof. intros * [[He Hv] _]; split; assumption. Qed.

Section EvalImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** A variable is looked up in the environment, without recursion. *)
  Definition fast_eval_var_impl x (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : eval_exp_order Θ Ξ #x (fenv_erase p)) :
      { d | ⟦ #x ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d }.
  Proof.
    exists (fenv_var p x); split; [ rewrite <- fenv_var_erase; apply eval_exp_var | apply fenv_var_ok, Hp ].
  Defined.

  (** The declaration of the group at [p], looked up through the cache
      [ck], as the declaration found with its equation or the absence of
      one: a value made of the declaration keeps the equation in the
      implementations' obligations. *)
  Definition decl_lookup (ck : lookup_cache Θ Ξ) (p : qname) :
      { D | ind_lookup Θ Ξ p = Some D } + { ind_lookup Θ Ξ p = None } :=
    match cache_lookup F ck p with
    | exist _ (Some D) E => inleft (exist _ D E)
    | exist _ None E => inright E
    end.

  (** The declaration of the group at [p] that a value carries, or else
      the one looked up through the cache [ck] *)
  Definition carried_lookup (ck : lookup_cache Θ Ξ) (p : qname) (oD : option ind_decl) (Hok : decl_carried_ok Θ Ξ p oD) :
      { D | ind_lookup Θ Ξ p = Some D } + { ind_lookup Θ Ξ p = None } :=
    match oD as o return decl_carried_ok Θ Ξ p o -> { D | ind_lookup Θ Ξ p = Some D } + { ind_lookup Θ Ξ p = None } with
    | Some D => fun Hok => inleft (exist _ D (Hok D eq_refl))
    | None => fun _ => decl_lookup ck p
    end Hok.

  (** [dmod_param_kind] of a fast module value, through the fast
      context's locations *)
  Fixpoint fdmod_param_kind (h : fdmod) : abs_kind :=
    match h with
    | fdm_local Δ _ _ => tele_param_kind (List.rev Δ) 0
    | fdm_global p args =>
        match proj1_sig (gc_loc_f F p) with
        | Some (T, _) => tele_param_kind (List.rev T) (List.length args)
        | None => ak_relevant
        end
    | fdm_member h _ => fdmod_param_kind h
    end.

  Lemma fdmod_param_kind_erase : forall h, dmod_param_kind Θ Ξ (fdmod_erase h) = fdmod_param_kind h.
  Proof.
    induction h as [p args | Δ D ρ | h IH ch]; cbn [fdmod_erase dmod_param_kind fdmod_param_kind]; [| reflexivity | exact IH ].
    destruct (gc_loc_f F p) as [o E]; cbn [proj1_sig]; rewrite E; destruct o as [[T t] |]; cbn; rewrite ?List.length_map; reflexivity.
  Qed.

  (** [arg_kind] of a fast value: a group's declaration read off the
      value, or looked up through the cache [ck]; a record's and a module
      location through the fast context *)
  Definition fast_arg_kind (ck : lookup_cache Θ Ξ) (f : fdomain) (Hf : fdomain_ok Θ Ξ f) :
      { κ | arg_kind Θ Ξ (fdomain_erase f) = κ }.
  Proof.
    refine (match f as f0 return fdomain_ok Θ Ξ f0 -> { κ | arg_kind Θ Ξ (fdomain_erase f0) = κ } with
            | fd_con p oD k c vs => fun Hf0 =>
                match carried_lookup ck p oD (fdomain_ok_con_carried _ _ _ _ _ _ _ Hf0) with
                | inleft (exist _ D E) =>
                    match ind_member D k as om return ind_member D k = om -> _ with
                    | Some Mk => fun Em =>
                        exist _ (if Nat.ltb (List.length vs) (con_param_count D Mk)
                                 then tele_param_kind (List.rev (im_params D Mk)) (List.length vs)
                                 else con_arg_kind Mk c (List.length vs - con_param_count D Mk)) _
                    | None => fun Em => exist _ ak_relevant _
                    end eq_refl
                | inright E => exist _ ak_relevant _
                end
            | fd_ind p oD k vs => fun Hf0 =>
                match carried_lookup ck p oD (fdomain_ok_ind_carried _ _ _ _ _ _ Hf0) with
                | inleft (exist _ D E) =>
                    match ind_member D k as om return ind_member D k = om -> _ with
                    | Some Mk => fun Em => exist _ (tele_param_kind (List.rev (im_params D Mk)) (List.length vs)) _
                    | None => fun Em => exist _ ak_relevant _
                    end eq_refl
                | inright E => exist _ ak_relevant _
                end
            | fd_record p ns => fun _ =>
                match record_lookup_f F p with
                | exist _ o E =>
                    exist _ (match o with
                             | Some R => tele_param_kind (List.rev (record_params R)) (List.length ns)
                             | None => ak_relevant
                             end) _
                end
            | fd_member h _ => fun _ => exist _ (fdmod_param_kind h) _
            | fd_fn a _ _ => fun _ => exist _ (fdomain_kind a) _
            | fd_neut (fd_pi _ _ a _ _) _ => fun _ => exist _ (fdomain_kind a) _
            | _ => fun _ => exist _ ak_relevant _
            end Hf).
    all: cbn [fdomain_erase arg_kind]; rewrite ?List.length_map, ?fdomain_kind_erase, ?fdmod_param_kind_erase; try reflexivity.
    all: rewrite ?E, ?Em; reflexivity.
  Defined.

  (** Whether the global module at [pq] lacks no parameter given [args],
      decided through the fast context *)
  Definition module_saturated_f (pq : qname) (args : list fdomain) :
      { module_saturated Θ Ξ pq (fdomains_erase args) } +
      { exists T Φ, gc_loc Θ Ξ pq = Some (T, Φ) /\ List.length (fdomains_erase args) < List.length T }.
  Proof.
    destruct (gc_loc_f F pq) as [[[T t] |] E].
    - destruct (Nat.ltb (List.length args) (List.length T)) eqn:Elt.
      + right; exists T, (decode_mod t); split; [ rewrite E; reflexivity | rewrite List.length_map; apply Nat.ltb_lt, Elt ].
      + left; intros T' Φ' Hl; rewrite E in Hl; cbn in Hl; injection Hl as <- _; rewrite List.length_map; apply Nat.ltb_ge, Elt.
    - left; intros T' Φ' Hl; rewrite E in Hl; discriminate.
  Defined.

  (** Whether a global module given [args] is given exactly the parameters
      of its location, with the location's telescope *)
  Definition module_exact_f (pq : qname) (args : list fdomain) :
      { T | exists Φ, gc_loc Θ Ξ pq = Some (T, Φ) /\ List.length (fdomains_erase args) = List.length T } +
      { forall T Φ, gc_loc Θ Ξ pq = Some (T, Φ) -> List.length (fdomains_erase args) <> List.length T }.
  Proof.
    destruct (gc_loc_f F pq) as [[[T t] |] E].
    - destruct (Nat.eqb (List.length args) (List.length T)) eqn:Eq.
      + left; exists T, (decode_mod t); split; [ rewrite E; reflexivity | rewrite List.length_map; apply Nat.eqb_eq, Eq ].
      + right; intros T' Φ' Hl; rewrite E in Hl; cbn in Hl; injection Hl as <- _; rewrite List.length_map; apply Nat.eqb_neq, Eq.
    - right; intros T' Φ' Hl; rewrite E in Hl; discriminate.
  Defined.

  #[local]
  Ltac impl_obligation_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_exps_order _ _ _ _ |- _ => progressive_invert H
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
      | H : gc_term _ _ _ = Some _ |- _ =>
          destruct (gc_term_inv _ _ _ _ H) as [(? & ? & ? & ? & ?) | (? & ? & ? & ?)]; clear H
      | H1 : entry_tm ?E = _, H2 : entry_tm ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : entry_unit ?E = _, H2 : entry_unit ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : entry_kind ?E = _, H2 : entry_kind ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | clear H2 ]
      | H1 : gc_entry _ _ ?p = Some _, H2 : gc_entry _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : gc_entry _ _ ?p = Some _, H2 : gc_entry _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H : gc_entry _ _ _ = Some (ge_def _ _ _ _ _) |- _ => apply gc_entry_def in H
      | H : gc_entry _ _ _ = Some (ge_ind _ _ _ _ _) |- _ =>
          let H1 := fresh "Hr" in let H2 := fresh "Hl" in destruct (gc_entry_ind _ _ _ _ _ _ _ _ H) as [H1 H2]; clear H
      | H : gc_entry ?T ?X ?p = _, H' : gc_resolve ?T ?X ?p = Some (ge_def _ _ _ _ _) |- _ =>
          apply gc_entry_def in H'; rewrite H in H'; discriminate H'
      | H : gc_entry ?T ?X ?p = _, H' : ind_mlookup ?T ?X ?p = Some _ |- _ =>
          let He := fresh "He" in destruct (ind_mlookup_entry _ _ _ _ _ _ H') as (? & ? & He); rewrite H in He; discriminate He
      | H : gc_entry ?T ?X ?p = Some (ge_def_mod _ _ _ _), H' : gc_resolve ?T ?X ?p = Some _ |- _ =>
          rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H) in H'; discriminate H'
      | H : gc_entry ?T ?X ?p = Some (ge_def_mod _ _ _ _), H' : ind_mlookup ?T ?X ?p = Some _ |- _ =>
          exfalso; exact (ind_mlookup_not_def_mod _ _ _ _ _ _ _ _ H' H)
      | H : gc_entry ?T ?X ?p = Some (ge_def_mod _ _ _ _), H' : record_lookup ?T ?X ?p = Some _ |- _ =>
          exfalso; exact (record_lookup_not_def_mod _ _ _ _ _ _ _ _ H' H)
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ind_lookup _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some (mr_alias _) |- _ =>
          exfalso; exact (ind_lookup_not_alias _ _ _ _ _ H1 H2)
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
          exfalso; specialize (H1 _ _ H2); rewrite ?List.length_map in *; lia
      | H1 : forall T Φ, gc_loc _ _ ?p = Some (T, Φ) -> _ <> _, H2 : gc_loc _ _ ?p = Some (_, _) |- _ =>
          exfalso; apply (H1 _ _ H2); rewrite ?List.length_map in *; assumption
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
      | H : gc_entry _ _ ?p = Some (ge_record _ _ _ _), H2 : record_lookup _ _ ?p = None |- _ =>
          rewrite (gc_entry_record _ _ _ _ _ _ _ H) in H2; discriminate H2
      | H : gc_entry ?T ?X ?p = Some ?E, H' : record_lookup ?T ?X ?p = Some _ |- _ =>
          lazymatch E with ge_record _ _ _ _ => fail | _ => idtac end;
          let He := fresh "He" in
          destruct (record_lookup_entry _ _ _ _ H') as [He | (? & ? & ? & He)]; rewrite H in He; discriminate He
      | H1 : record_lookup _ _ ?p = Some _, H2 : ind_mlookup _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (record_lookup_not_ind _ _ _ _ H1) in H2; discriminate H2
      | H1 : field_index ?fs ?f = Some _, H2 : field_index ?fs ?f = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : field_index ?fs ?f = Some _, H2 : field_index ?fs ?f = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ?x <> None, H2 : ?x = None |- _ => exfalso; exact (H1 H2)
      (** The length of the erasure of a list is the list's *)
      | H : context [ List.length (List.map _ _) ] |- _ => rewrite List.length_map in H
      | |- context [ List.length (List.map _ _) ] => rewrite List.length_map
      (** An element of the erasure of a list, found or not in the list *)
      | H : context [ List.nth_error (List.map _ _) _ ] |- _ => rewrite List.nth_error_map in H
      | H1 : context [ List.nth_error ?l ?n ], H2 : List.nth_error ?l ?n = _ |- _ =>
          lazymatch type of H1 with List.nth_error l n = _ => fail | _ => rewrite H2 in H1; cbn [option_map] in H1 end
      (** A field of the erasure of a record value, alike *)
      | H : context [ field_lookup (List.map (fun g => (fst g, fdomain_erase (snd g))) _) _ ] |- _ =>
          rewrite field_lookup_erase in H
      | H1 : context [ field_lookup ?l ?f ], H2 : field_lookup ?l ?f = _ |- _ =>
          lazymatch type of H1 with field_lookup l f = _ => fail | _ => rewrite H2 in H1; cbn [option_map] in H1 end
      | H : None <> None |- _ => exfalso; exact (H eq_refl)
      (** The group of a recursive result of a function shape has a
          declaration. *)
      | H : forall fn, eval_app _ _ ?f ?n fn -> eval_ih_order _ _ _ ?pq _ _ _ fn,
        Hf : eval_app _ _ ?f ?n _, E : ind_lookup _ _ ?pq = None |- _ =>
          exfalso; destruct (eval_ih_order_lookup _ _ _ _ _ _ _ _ (H _ Hf)) as (? & ?); congruence
      (** A record view, by its head; its one constructor. *)
      | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
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
      (** A kind found relevant or of levels is evaluated, read off the
          erasure too. *)
      | E : fdomain_kind ?a = ?κ |- _ =>
          lazymatch goal with _ : domain_kind (fdomain_erase a) = κ |- _ => fail | _ =>
            assert (domain_kind (fdomain_erase a) = κ) by (rewrite fdomain_kind_erase; exact E) end
      | E : ?k = ak_relevant |- _ =>
          lazymatch goal with _ : evaluated_kind k |- _ => fail | _ => assert (evaluated_kind k) by (rewrite E; constructor) end
      | E : ?k = ak_level |- _ =>
          lazymatch goal with _ : evaluated_kind k |- _ => fail | _ => assert (evaluated_kind k) by (rewrite E; constructor) end
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
    impl_obligation_exfalso;
    impl_obligation_glob;
    (** once more, at the lookups fixed *)
    impl_obligation_exfalso;
    impl_obligation_glob;
    cbn [gu_params] in *;
    try solve [ intuition discriminate ];
    try solve [ congruence ];
    try solve [ exfalso; lia ];
    try solve [ eapply eval_sel_global_neut; eauto ];
    (** A term part, by the lookups its branch fixed. *)
    try solve [ eapply eval_sel_global; [ eassumption | | eassumption | eassumption ]; unfold gc_term;
                repeat match goal with
                       | H : gc_resolve _ _ _ = _ |- context [gc_resolve _ _ _] => rewrite H
                       | H : gc_entry _ _ _ = Some (ge_def_mod _ _ _ _) |- context [gc_resolve _ _ _] =>
                           rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H)
                       | H : gc_entry _ _ _ = _ |- context [gc_entry _ _ _] => rewrite H
                       end; reflexivity ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
    (** A stuck eliminator: its member's reference, read off the member *)
    try solve [ eapply eval_elim_neut; eauto using eval_mref_im_ref ];
    try solve [ eauto ];
    try econstructor; eauto.

  (** The erasures read as Core values, and the results' two parts apart *)
  #[local]
  Ltac eval_obligation_norm :=
    intros;
    (** The recursive functions in scope are not needed by an obligation;
        dropped, the rewriting below has far less to go through. *)
    repeat match goal with f : _ |- _ => lazymatch type of f with context [@sig _ _] => clear f end end;
    cbv beta iota in *; cbn [option_map decode_entry fst snd] in *;
    ferase_norm;
    rewrite ?fbranch_entries_erase, ?fmotive_entries_erase, ?fdecl_env_erase, ?fglobal_proof_env_erase in *;
    rewrite ?ftele_entries_erase, ?fdecl_env_erase in *; cbn [fst snd] in *;
    (** once more, at the arguments those rewrites expose *)
    ferase_norm;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.

  (** The relation or the order, as for Core values *)
  #[local]
  Ltac eval_obligation_rel :=
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

  #[local]
  Ltac eval_obligation :=
    eval_obligation_norm;
    lazymatch goal with
    | |- _ /\ _ => split; [ eval_obligation_rel | ok_solve ]
    | |- fdomain_ok _ _ _ => ok_solve
    | |- fdomain_ne_ok _ _ _ => ok_solve
    | |- fdomain_nf_ok _ _ _ => ok_solve
    | |- fdentry_ok _ _ _ => ok_solve
    | |- fentry_type_ok _ _ _ => ok_solve
    | |- decl_carried_ok _ _ _ _ => ok_solve
    | |- fdmod_ok _ _ _ => ok_solve
    | |- fenv_ok _ _ _ => ok_solve
    | |- Forall _ _ => ok_solve
    | |- _ => eval_obligation_rel
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_eval_exp_impl m (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : eval_exp_order Θ Ξ m (fenv_erase p)) :
      { d | ⟦ m ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d } by struct H :=
  | Typeω@i, p, Hp, H => exist _ (fd_univ i) _
  | Type⟨M⟩, p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      exist _ (fd_suniv m) _
  | #x    , p, Hp, H => fast_eval_var_impl x p Hp H
  | Level@n, p, Hp, H => exist _ (fd_level n) _
  | LevelSort, p, Hp, H => exist _ fd_level_sort _
  | 𝕃ᵒ o  , p, Hp, H => exist _ (fdomain_level_lit o) _
  | succl M, p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      exist _ (fdomain_level_suc m) _
  | maxl M N, p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      let (n , Hn) := fast_eval_exp_impl N p Hp _ in
      exist _ (fdomain_level_max m n) _
  | Propₘ , p, Hp, H => exist _ fd_prop _
  | ⊤     , p, Hp, H => exist _ fd_True _
  (** Proofs: kept as they are *)
  | a_tt  , p, Hp, H => exist _ (fd_proof a_tt p) _
  | ⊥     , p, Hp, H => exist _ fd_False _
  (** [efq]: stuck at its type, on its proof kept as it is *)
  | efq M return C, p, Hp, H =>
      let (c, Hc) := fast_eval_exp_impl C p Hp _ in
      exist _ (fd_neut c (fd_absurd c (fd_proof M p))) _
  | Σₚ P Q, p, Hp, H =>
      let (a, Ha) := fast_eval_exp_impl P p Hp _ in
      exist _ (fd_and a p Q) _
  | a_conj P Q M N, p, Hp, H => exist _ (fd_proof (a_conj P Q M N) p) _
  | a_left M, p, Hp, H => exist _ (fd_proof (a_left M) p) _
  | a_right M, p, Hp, H => exist _ (fd_proof (a_right M) p) _
  | a_pi κd κc A B , p, Hp, H =>
      let (a , Ha) := fast_eval_exp_impl A p Hp _ in
      exist _ (fd_pi κd κc a p B) _
  | λ A M , p, Hp, H =>
      let (a , Ha) := fast_eval_exp_impl A p Hp _ in
      exist _ (fd_fn a p M) _
  | a_ind pq k, p, Hp, H => exist _ (fd_ind pq None k nil) _
  | a_con pq k c, p, Hp, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_starts D Mk) := {
        | exist _ true Es => exist _ (fd_con pq (carry D) k c nil) _
        | exist _ false Es with inspect (im_head Mk) := {
          | exist _ (mh_view qc k' Is vm) Eh =>
              let (cups, Hc) := fast_eval_exps_impl Is nil _ _ in
              exist _ (fd_con qc None k' c cups) _
          | exist _ (mh_record qr Is nil) Eh => exist _ (fd_tuple nil) _
          | exist _ (mh_record qr Is (_ :: _)) Eh => exist _ (fd_con pq (carry D) k c nil) _
          | exist _ (mh_decl _) Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  | a_elim ak_relevant pq Us j Bks M, p, Hp, H with fast_eval_exps_impl Us p Hp _ := {
    | exist _ ups Hups with fast_eval_exp_impl M p Hp _ := {
      | exist _ m Hm =>
          let (r, Hr) := fast_eval_elim_impl p pq ups Bks j m (fc_seed F) Hp _ _ _ in
          exist _ r _ } }
  (** An eliminator into propositions: a proof, kept as it is *)
  | a_elim ak_propositional pq Us j Bks M, p, Hp, H => exist _ (fd_proof (a_elim ak_propositional pq Us j Bks M) p) _
  | a_elim ak_level pq Us j Bks M, p, Hp, H => False_rect _ _
  (** An application, by the kind of the argument the function takes *)
  | M $ N   , p, Hp, H with fast_eval_exp_impl M p Hp _ := {
    | exist _ m Hm with fast_arg_kind (fc_seed F) m (proj2 Hm) := {
      | exist _ ak_propositional Er =>
          let (a, Ha) := fast_eval_app_impl m (fd_proof N p) _ _ _ in
          exist _ a _
      | exist _ ak_relevant Er =>
          let (n , Hn) := fast_eval_exp_impl N p Hp _ in
          let (a, Ha) := fast_eval_app_impl m n _ _ _ in
          exist _ a _
      | exist _ ak_level Er =>
          let (n , Hn) := fast_eval_exp_impl N p Hp _ in
          let (a, Ha) := fast_eval_app_impl m n _ _ _ in
          exist _ a _ } }
  (** A local definition, by the kind of its type *)
  | a_let (b_def A M) B, p, Hp, H with fast_eval_exp_impl A p Hp _ := {
    | exist _ a Ha with inspect (fdomain_kind a) := {
      | exist _ ak_propositional Ek =>
          let (r, Hr) := fast_eval_exp_impl B (fextend_env p (fd_proof M p) (fentry_type_value a)) _ _ in
          exist _ r _
      | exist _ ak_relevant Ek =>
          let (m, Hm) := fast_eval_exp_impl M p Hp _ in
          let (r, Hr) := fast_eval_exp_impl B (fextend_env p m (fentry_type_value a)) _ _ in
          exist _ r _
      | exist _ ak_level Ek =>
          let (m, Hm) := fast_eval_exp_impl M p Hp _ in
          let (r, Hr) := fast_eval_exp_impl B (fextend_env p m (fentry_type_value a)) _ _ in
          exist _ r _ } }
  | a_let (b_mod (gu_mk Δ D)) B, p, Hp, H =>
      let (h, Hh) := fast_eval_close_impl Δ D p Hp _ in
      let (r, Hr) := fast_eval_exp_impl B (fextend_env_mod p h (gu_mk Δ D)) _ _ in
      exist _ r _
  (** A local definition with a module part: its type, its body, its
      unit's literal, then the rest under both *)
  | a_let (b_def_mod A M (gu_mk Δ D)) B, p, Hp, H =>
      let (a, Ha) := fast_eval_exp_impl A p Hp _ in
      let (m, Hm) := fast_eval_exp_impl M p Hp _ in
      let (h, Hh) := fast_eval_close_impl Δ D p Hp _ in
      let (r, Hr) := fast_eval_exp_impl B (fextend_env_dm p m (fentry_type_value a) h (gu_mk Δ D)) _ _ in
      exist _ r _
  | a_mem M x, p, Hp, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := fast_eval_modexp_impl R p Hp _ in
        let (f, Hf) := fast_eval_selc_impl h (pre ++ x :: nil) _ _ in
        let (ns, Hns) := fast_eval_exps_impl args p Hp _ in
        let (r, Hr) := fast_eval_apps_impl f ns _ _ _ in
        exist _ r _ }
  | a_record pq, p, Hp, H => exist _ (fd_record pq nil) _
  (** A record element: its type finds the record, whose kinds direct the
      fields *)
  | a_tuple T fs, p, Hp, H with fast_eval_exp_impl T p Hp _ := {
    | exist _ (fd_record pq ns) Ht with record_lookup_f F pq := {
      | exist _ (Some R) El =>
          let (vs, Hvs) := fast_eval_field_vals_impl (record_field_kinds R) (List.map snd fs) p Hp _ in
          exist _ (fd_tuple (List.combine (List.map fst fs) vs)) _
      | exist _ None El => False_rect _ _ }
    | exist _ _ Ht => False_rect _ _ }
  | a_proj f M, p, Hp, H =>
      let (m, Hm) := fast_eval_exp_impl M p Hp _ in
      let (r, Hr) := fast_eval_proj_impl f m _ _ in
      exist _ r _

  with fast_eval_field_vals_impl rs Ms (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : eval_field_vals_order Θ Ξ rs Ms (fenv_erase p)) :
      { ms | eval_field_vals Θ Ξ rs Ms (fenv_erase p) (fdomains_erase ms) /\ Forall (fdomain_ok Θ Ξ) ms } by struct H :=
  | rs, nil, p, Hp, H => exist _ nil _
  | rs, M :: Ms, p, Hp, H with inspect (List.hd ak_relevant rs) := {
    | exist _ ak_propositional Er =>
        let (ms, Hms) := fast_eval_field_vals_impl (List.tl rs) Ms p Hp _ in
        exist _ (fd_proof M p :: ms) _
    | exist _ ak_relevant Er =>
        let (m, Hm) := fast_eval_exp_impl M p Hp _ in
        let (ms, Hms) := fast_eval_field_vals_impl (List.tl rs) Ms p Hp _ in
        exist _ (m :: ms) _
    | exist _ ak_level Er =>
        let (m, Hm) := fast_eval_exp_impl M p Hp _ in
        let (ms, Hms) := fast_eval_field_vals_impl (List.tl rs) Ms p Hp _ in
        exist _ (m :: ms) _ }

  with fast_eval_proj_impl f (m : fdomain) (Hm : fdomain_ok Θ Ξ m) (H : eval_proj_order Θ Ξ f (fdomain_erase m)) :
      { r | eval_proj Θ Ξ f (fdomain_erase m) (fdomain_erase r) /\ fdomain_ok Θ Ξ r } by struct H :=
  | f, fd_tuple vs, Hm, H with inspect (field_lookup vs f) := {
    | exist _ (Some r) E => exist _ r _
    | exist _ None E => False_rect _ _ }
  | f, fd_neut (fd_record pq ns) m, Hm, H with record_lookup_f F pq := {
    | exist _ (Some R) El with inspect (field_index (record_fields R) f) := {
      | exist _ (Some k) Ek with fast_eval_neutral_fields_impl m (fenv_tele nil (List.rev (record_params R)) ns)
                                   (List.firstn (S k) (record_fields R)) _ _ _ := {
        | exist _ rs Hrs with inspect (List.nth_error rs k) := {
          | exist _ (Some r) Er => exist _ r _
          | exist _ None Er => False_rect _ _ } }
      | exist _ None Ek => False_rect _ _ }
    | exist _ None El => False_rect _ _ }
  | f, _, Hm, H => False_rect _ _

  with fast_eval_neutral_fields_impl (m : fdomain_ne) (p : fenv) fl
      (Hm : fdomain_ne_ok Θ Ξ m) (Hp : fenv_ok Θ Ξ p)
      (H : eval_neutral_fields_order Θ Ξ (fdomain_ne_erase m) (fenv_erase p) fl) :
      { rs | eval_neutral_fields Θ Ξ (fdomain_ne_erase m) (fenv_erase p) fl (fdomains_erase rs) /\
             Forall (fdomain_ok Θ Ξ) rs } by struct H :=
  | m, p, nil, Hm, Hp, H => exist _ nil _
  | m, p, (g, T) :: fl, Hm, Hp, H =>
      let (a, Ha) := fast_eval_exp_impl T p Hp _ in
      let (rs, Hrs) := fast_eval_neutral_fields_impl m (fextend_env p (fd_neut a (fd_proj g m)) (fentry_type_closure T p)) fl Hm _ _ in
      exist _ (fd_neut a (fd_proj g m) :: rs) _

  (** The group of the eliminator is looked up through the cache [ck], and
      passed on as the cache of the container's lookup and of the
      recursive results: a lookup of the same name is a comparison. *)
  with fast_eval_elim_impl (p : fenv) pq (ups : list fdomain) Bks j (m : fdomain) (ck : lookup_cache Θ Ξ)
      (Hp : fenv_ok Θ Ξ p) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hm : fdomain_ok Θ Ξ m)
      (H : eval_elim_order Θ Ξ (fenv_erase p) pq (fdomains_erase ups) Bks j (fdomain_erase m)) :
      { r | ⟦elim fdomain_erase m at j of pq (fdomains_erase ups) Bks ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase r /\
            fdomain_ok Θ Ξ r } by struct H :=
  | p, pq, ups, Bks, j, fd_con pc oDq k c vs, ck, Hp, Hups, Hm, H with carried_lookup ck pc oDq (fdomain_ok_con_carried _ _ _ _ _ _ _ Hm) := {
    | inleft (exist _ Dq Edq) with decl_lookup (Some (exist _ (pc, Dq) Edq)) pq := {
      | inleft (exist _ D Ed) with inspect (ind_member D j) := {
        | exist _ (Some Mj) Em with inspect (ind_member Dq k) := {
          | exist _ (Some Mk) Emk with inspect (ind_con Mj c) := {
            | exist _ (Some gs) Ec with inspect (List.nth_error Bks j) := {
              | exist _ (Some b) Eb with inspect (brs_lookup (eb_brs b) c) := {
                | exist _ (Some (n, B)) Ebr =>
                    let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks gs (skipn (im_np Dq Mk) vs) D Ed Hp Hups _ _ in
                    let (r, Hr) := fast_eval_exp_impl B
                                     (fenv_extend_typed p (fbranch_entries D Mj pq ups (blocks_motives Bks) p gs
                                                             (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs)) (skipn (im_np Dq Mk) vs) ihs)) _ _ in
                    exist _ r _
                | exist _ None Ebr => False_rect _ _ }
              | exist _ None Eb => False_rect _ _ }
            | exist _ None Ec => False_rect _ _ }
          | exist _ None Emk => False_rect _ _ }
        | exist _ None Em => False_rect _ _ }
      | inright Ed => False_rect _ _ }
    | inright Edq => False_rect _ _ }
  | p, pq, ups, Bks, j, fd_neut (fd_ind pc oDq k as') m, ck, Hp, Hups, Hm, H with carried_lookup ck pc oDq (fdomain_ok_neut_ind_carried _ _ _ _ _ _ _ Hm) := {
    | inleft (exist _ Dq Edq) with decl_lookup (Some (exist _ (pc, Dq) Edq)) pq := {
      | inleft (exist _ D Ed) with inspect (ind_member D j) := {
        | exist _ (Some Mj) Em with inspect (List.nth_error Bks j) := {
          | exist _ (Some b) Eb with fast_eval_mref_impl pq ups j Hups _ := {
            | exist _ (mk_fast_member_reference pc' oD' k' cups) Hr =>
                let (a, Ha) := fast_eval_exp_impl (eb_motive b)
                                 (fenv_extend_typed p (fmotive_entries D Mj ups (List.skipn (ind_nu Dq) as')
                                                         (fd_ind pc oDq k (cups ++ List.skipn (ind_nu Dq) as'))
                                                         (fd_neut (fd_ind pc oDq k as') m))) _ _ in
                exist _ (fd_neut a (fd_elim p Bks pq D ups j as' m)) _ }
          | exist _ None Eb => False_rect _ _ }
        | exist _ None Em => False_rect _ _ }
      | inright Ed => False_rect _ _ }
    | inright Edq => False_rect _ _ }
  | p, pq, ups, Bks, j, _, ck, Hp, Hups, Hm, H => False_rect _ _

  (** The recursive results take the declaration of the group, which the
      eliminator has looked up already: no lookup per step *)
  with fast_eval_ihs_impl (p : fenv) pq (ups : list fdomain) Bks gs (vs : list fdomain) (D : ind_decl)
      (Ed : ind_lookup Θ Ξ pq = Some D)
      (Hp : fenv_ok Θ Ξ p) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : eval_ihs_order Θ Ξ (fenv_erase p) pq (fdomains_erase ups) Bks gs (fdomains_erase vs)) :
      { ihs | ⟦ihs fdomains_erase vs of gs under pq (fdomains_erase ups) Bks ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase ihs /\
              Forall (fdomain_ok Θ Ξ) ihs } by struct H :=
  | p, pq, ups, Bks, nil, nil, D, Ed, Hp, Hups, Hvs, H => exist _ nil _
  | p, pq, ups, Bks, ca_arg r T :: gs, v :: vs, D, Ed, Hp, Hups, Hvs, H =>
      let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks gs vs D Ed Hp Hups _ _ in
      exist _ ihs _
  | p, pq, ups, Bks, ca_rec t :: gs, v :: vs, D, Ed, Hp, Hups, Hvs, H =>
      let (ih, Hih) := fast_eval_ih_impl p pq ups Bks t v D Ed Hp Hups _ _ in
      let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks gs vs D Ed Hp Hups _ _ in
      exist _ (ih ++ ihs) _
  | p, pq, ups, Bks, _, _, D, Ed, Hp, Hups, Hvs, H => False_rect _ _

  with fast_eval_ih_impl (p : fenv) pq (ups : list fdomain) Bks t (v : fdomain) (D : ind_decl)
      (Ed : ind_lookup Θ Ξ pq = Some D)
      (Hp : fenv_ok Θ Ξ p) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hv : fdomain_ok Θ Ξ v)
      (H : eval_ih_order Θ Ξ (fenv_erase p) pq (fdomains_erase ups) Bks t (fdomain_erase v)) :
      { rs | ⟦ih fdomain_erase v of t under pq (fdomains_erase ups) Bks ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase rs /\
             Forall (fdomain_ok Θ Ξ) rs } by struct H :=
  | p, pq, ups, Bks, pt_self j Ps, v, D, Ed, Hp, Hups, Hv, H with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
          | exist _ ((c, gs) :: nil) Ec =>
              let (ws, Hws) := fast_eval_projs_impl fl v Hv _ in
              let (rs, Hrs) := fast_eval_ihs_impl p pq ups Bks gs ws D Ed Hp Hups _ _ in
              exist _ rs _
          | exist _ _ Ec => False_rect _ _ }
        | exist _ _ Eh =>
            let (r, Hr) := fast_eval_elim_impl p pq ups Bks j v (Some (exist _ (pq, D) Ed)) Hp Hups Hv _ in
            exist _ (r :: nil) _ }
      | exist _ None Em => False_rect _ _ }
  | p, pq, ups, Bks, pt_pi B t, v, D, Ed, Hp, Hups, Hv, H =>
        exist _ (List.map (fun i => fd_ihfn p Bks pq ups t i v) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))) _

  with fast_eval_projs_impl fl (v : fdomain) (Hv : fdomain_ok Θ Ξ v) (H : eval_projs_order Θ Ξ fl (fdomain_erase v)) :
      { ws | ⟦projs fl of fdomain_erase v ⟧ Θ ⍮ Ξ ↘ fdomains_erase ws /\ Forall (fdomain_ok Θ Ξ) ws } by struct H :=
  | nil, v, Hv, H => exist _ nil _
  | f :: fl, v, Hv, H =>
      let (w, Hw) := fast_eval_proj_impl f v Hv _ in
      let (ws, Hws) := fast_eval_projs_impl fl v Hv _ in
      exist _ (w :: ws) _

  (** The member a member stands for, with the declaration of its group
      when it is the member's own *)
  with fast_eval_mref_impl pq (ups : list fdomain) j (Hups : Forall (fdomain_ok Θ Ξ) ups)
      (H : eval_mref_order Θ Ξ pq (fdomains_erase ups) j) :
      { r : fast_member_reference |
        ⟦mref j of pq (fdomains_erase ups) ⟧ Θ ⍮ Ξ ↘ fast_member_reference_erase r /\ fast_member_reference_ok Θ Ξ r } by struct H :=
  | pq, ups, j, Hups, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_decl _) Eh => exist _ (mk_fast_member_reference pq (carry D) j ups) _
        | exist _ (mh_view qc k Is vm) Eh =>
            let (cups, Hc) := fast_eval_exps_impl Is (fdecl_env D ups) _ _ in
            exist _ (mk_fast_member_reference qc None k cups) _
        | exist _ (mh_record _ _ _) Eh => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }

  with fast_eval_shape_type_impl pq (ups : list fdomain) (p : fenv) t (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hp : fenv_ok Θ Ξ p)
      (H : eval_shape_type_order Θ Ξ pq (fdomains_erase ups) (fenv_erase p) t) :
      { a | ⟦shty t of pq (fdomains_erase ups) ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a } by struct H :=
  | pq, ups, p, pt_self j Ps, Hups, Hp, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh =>
            let (cups, Hc) := fast_eval_exps_impl Is (fdecl_env D ups) _ _ in
            exist _ (fd_record qr cups) _
        | exist _ _ Eh with fast_eval_exps_impl Ps p Hp _ := {
          | exist _ bs Hbs with fast_eval_mref_impl pq ups j Hups _ := {
            | exist _ (mk_fast_member_reference pc oD k pre) Hm => exist _ (fd_ind pc oD k (pre ++ bs)) _ } } }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  | pq, ups, p, pt_pi B t, Hups, Hp, H =>
      let (b, Hb) := fast_eval_exp_impl B p Hp _ in
      exist _ (fd_pi ak_relevant ak_relevant b (fextend_env nil (fd_shfam pq ups p B t) fentry_type_none) fam_cod) _

  with fast_eval_ihty_impl pq (ups : list fdomain) (pm : fenv) As (p : fenv) t (v : fdomain)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hpm : fenv_ok Θ Ξ pm) (Hp : fenv_ok Θ Ξ p) (Hv : fdomain_ok Θ Ξ v)
      (H : eval_ihty_order Θ Ξ pq (fdomains_erase ups) (fenv_erase pm) As (fenv_erase p) t (fdomain_erase v)) :
      { as' | ⟦ihty fdomain_erase v of t at pq (fdomains_erase ups) under (fenv_erase pm) As ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase as' /\
              Forall (fdomain_ok Θ Ξ) as' } by struct H :=
  | pq, ups, pm, As, p, pt_self j Ps, v, Hups, Hpm, Hp, Hv, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
          | exist _ ((c, gs) :: nil) Ec =>
              let (ws, Hws) := fast_eval_projs_impl fl v Hv _ in
              let (rs, Hrs) := fast_eval_ihtys_impl pq ups pm As (fdecl_env D ups) gs ws Hups Hpm _ _ _ in
              exist _ rs _
          | exist _ _ Ec => False_rect _ _ }
        | exist _ _ Eh =>
            let (bs, Hbs) := fast_eval_exps_impl Ps p Hp _ in
            let (a, Ha) := fast_eval_exp_impl (List.nth j As a_prop)
                             (fenv_extend_typed pm (ftele_entries (fdecl_env D ups) (List.rev (im_nparams Mj)) bs ++
                                                    (v, fentry_type_shape pq ups p (pt_self j Ps)) :: nil)) _ _ in
            exist _ (a :: nil) _ }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  | pq, ups, pm, As, p, pt_pi B t, v, Hups, Hpm, Hp, Hv, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) =>
        let (b, Hb) := fast_eval_exp_impl B p Hp _ in
        exist _ (List.map (fun i => fd_pi ak_relevant ak_relevant b (fextend_env nil (fd_ihfam pm As pq ups p B t i v) fentry_type_none) fam_cod)
                   (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))) _
    | inright Ed => False_rect _ _ }

  with fast_eval_ihtys_impl pq (ups : list fdomain) (pm : fenv) As (p : fenv) gs (vs : list fdomain)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hpm : fenv_ok Θ Ξ pm) (Hp : fenv_ok Θ Ξ p) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : eval_ihtys_order Θ Ξ pq (fdomains_erase ups) (fenv_erase pm) As (fenv_erase p) gs (fdomains_erase vs)) :
      { rs | ⟦ihtys fdomains_erase vs of gs at pq (fdomains_erase ups) under (fenv_erase pm) As ⟧ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase rs /\
             Forall (fdomain_ok Θ Ξ) rs } by struct H :=
  | pq, ups, pm, As, p, nil, nil, Hups, Hpm, Hp, Hvs, H => exist _ nil _
  | pq, ups, pm, As, p, ca_arg r T :: gs, v :: vs, Hups, Hpm, Hp, Hvs, H =>
      let (rs, Hrs) := fast_eval_ihtys_impl pq ups pm As (fextend_env p v (fentry_type_closure T p)) gs vs Hups Hpm _ _ _ in
      exist _ rs _
  | pq, ups, pm, As, p, ca_rec t :: gs, v :: vs, Hups, Hpm, Hp, Hvs, H =>
      let (rs1, Hrs1) := fast_eval_ihty_impl pq ups pm As p t v Hups Hpm Hp _ _ in
      let (rs, Hrs) := fast_eval_ihtys_impl pq ups pm As p gs vs Hups Hpm Hp _ _ in
      exist _ (rs1 ++ rs) _
  | pq, ups, pm, As, p, _, _, Hups, Hpm, Hp, Hvs, H => False_rect _ _

  with fast_eval_app_impl (m n : fdomain) (Hm : fdomain_ok Θ Ξ m) (Hn : fdomain_ok Θ Ξ n)
      (H : eval_app_order Θ Ξ (fdomain_erase m) (fdomain_erase n)) :
      { d | $| fdomain_erase m & fdomain_erase n | Θ ⍮ Ξ ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d } by struct H :=
  | fd_fn a p M, n, Hm, Hn, H =>
      let (m, Hm') := fast_eval_exp_impl M (fextend_env p n (fentry_type_value a)) _ _ in
      exist _ m _
  | fd_neut (fd_pi κd κc a p B) m, n, Hm, Hn, H =>
      let (b, Hb) := fast_eval_exp_impl B (fextend_env p n (fentry_type_value a)) _ _ in
      exist _ (fd_neut b (fd_app m (fd_dom a n))) _
  | fd_member h ch, n, Hm, Hn, H =>
      let (h', Hh') := fast_eval_appm_impl h n _ Hn _ in
      let (r, Hr) := fast_eval_selc_impl h' ch _ _ in
      exist _ r _
  | fd_ind pq oD k as', n, Hm, Hn, H => exist _ (fd_ind pq oD k (as' ++ n :: nil)) _
  | fd_con pq oD k c vs, n, Hm, Hn, H with carried_lookup (fc_seed F) pq oD (fdomain_ok_con_carried _ _ _ _ _ _ _ Hm) := {
    | inleft (exist _ D Ed) with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_head Mk) := {
        | exist _ (mh_decl _) Eh => exist _ (fd_con pq (carry D) k c (vs ++ n :: nil)) _
        | exist _ (mh_view qc k' Is vm) Eh with inspect (S (List.length vs) <? ind_nu D) := {
          | exist _ true El => exist _ (fd_con pq (carry D) k c (vs ++ n :: nil)) _
          | exist _ false El =>
              let (cups, Hc) := fast_eval_exps_impl Is (fdecl_env D (vs ++ n :: nil)) _ _ in
              exist _ (fd_con qc None k' c cups) _ }
        | exist _ (mh_record qr Is fl) Eh with inspect (S (List.length vs) <? ind_nu D + List.length fl) := {
          | exist _ true El => exist _ (fd_con pq (carry D) k c (vs ++ n :: nil)) _
          | exist _ false El => exist _ (fd_tuple (List.combine fl (List.skipn (ind_nu D) (vs ++ n :: nil)))) _ } }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  | fd_ihfn p Bks pq ups t i f, n, Hm, Hn, H with fast_eval_app_impl f n _ Hn _ := {
    | exist _ fn Hfn with decl_lookup (fc_seed F) pq := {
      | inleft (exist _ D Ed) with fast_eval_ih_impl p pq ups Bks t fn D Ed _ _ _ _ := {
        | exist _ rs Hrs with inspect (List.nth_error rs i) := {
          | exist _ (Some r) Er => exist _ r _
          | exist _ None Er => False_rect _ _ } }
      | inright Ed => False_rect _ _ } }
  | fd_shfam pq ups p B t, n, Hm, Hn, H =>
      let (a, Ha) := fast_eval_shape_type_impl pq ups (fextend_env p n (fentry_type_closure B p)) t _ _ _ in
      exist _ a _
  | fd_ihfam pm As pq ups p B t i f, n, Hm, Hn, H with fast_eval_app_impl f n _ Hn _ := {
    | exist _ fn Hfn with fast_eval_ihty_impl pq ups pm As (fextend_env p n (fentry_type_closure B p)) t fn _ _ _ _ _ := {
      | exist _ as' Has with inspect (List.nth_error as' i) := {
        | exist _ (Some a) Ea => exist _ a _
        | exist _ None Ea => False_rect _ _ } } }
  | fd_record pq ns, n, Hm, Hn, H => exist _ (fd_record pq (ns ++ n :: nil)) _
  | _, n, Hm, Hn, H => False_rect _ _

  with fast_eval_exps_impl Ms (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : eval_exps_order Θ Ξ Ms (fenv_erase p)) :
      { ms | ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase ms /\ Forall (fdomain_ok Θ Ξ) ms } by struct H :=
  | nil, p, Hp, H => exist _ nil _
  | M :: Ms, p, Hp, H =>
      let (m, Hm) := fast_eval_exp_impl M p Hp _ in
      let (ms, Hms) := fast_eval_exps_impl Ms p Hp _ in
      exist _ (m :: ms) _

  with fast_eval_apps_impl (m : fdomain) (ns : list fdomain) (Hm : fdomain_ok Θ Ξ m) (Hns : Forall (fdomain_ok Θ Ξ) ns)
      (H : eval_apps_order Θ Ξ (fdomain_erase m) (fdomains_erase ns)) :
      { r | $*| fdomain_erase m & fdomains_erase ns | Θ ⍮ Ξ ↘ fdomain_erase r /\ fdomain_ok Θ Ξ r } by struct H :=
  | m, nil, Hm, Hns, H => exist _ m _
  | m, n :: ns, Hm, Hns, H =>
      let (m1, Hm1) := fast_eval_app_impl m n Hm _ _ in
      let (r, Hr) := fast_eval_apps_impl m1 ns _ _ _ in
      exist _ r _

  with fast_eval_modexp_impl M (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : eval_modexp_order Θ Ξ M (fenv_erase p)) :
      { h | ⟦ M ⟧ᵐ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h } by struct H :=
  | me_var x, p, Hp, H => exist _ (fenv_mod p x) _
  | me_unit fp, p, Hp, H => exist _ (fdm_global (q_abs fp nil) nil) _
  | me_lit (gu_mk Δ D), p, Hp, H =>
      let (h, Hh) := fast_eval_close_impl Δ D p Hp _ in
      exist _ h _
  | me_mem M y, p, Hp, H =>
      let (h, Hh) := fast_eval_modexp_impl M p Hp _ in
      let (r, Hr) := fast_eval_selm_impl h y _ _ in
      exist _ r _
  | me_app M N, p, Hp, H =>
      let (h, Hh) := fast_eval_modexp_impl M p Hp _ in
      let (n, Hn) := fast_eval_exp_impl N p Hp _ in
      let (r, Hr) := fast_eval_appm_impl h n _ _ _ in
      exist _ r _

  with fast_eval_close_impl Δ D (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : eval_close_order Θ Ξ Δ D (fenv_erase p)) :
      { h | ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h } by struct H :=
  (** A body: the closure of its expansion *)
  | Δ, md_body sm Φ, p, Hp, H => exist _ (fdm_local Δ (md_body sm (gm_expand Φ)) p) _
  | nil, md_alias E, p, Hp, H =>
      let (h, Hh) := fast_eval_modexp_impl E p Hp _ in
      exist _ h _
  | e :: Δ, md_alias E, p, Hp, H => exist _ (fdm_local (e :: Δ) (md_alias E) p) _

  with fast_eval_appm_impl (h : fdmod) (n : fdomain) (Hh : fdmod_ok Θ Ξ h) (Hn : fdomain_ok Θ Ξ n)
      (H : eval_appm_order Θ Ξ (fdmod_erase h) (fdomain_erase n)) :
      { r | $ᵐ| fdmod_erase h & fdomain_erase n | Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | fdm_global pq args, n, Hh, Hn, H => exist _ (fdm_global pq (args ++ n :: nil)) _
  | fdm_local Δ D p, n, Hh, Hn, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass κ A)) Es =>
        let (r, Hr) := fast_eval_close_impl Δ0 D (fextend_env p n (fentry_type_closure A p)) _ _ in
        exist _ r _
    | exist _ _ Es => False_rect _ _ }
  | fdm_member h ch, n, Hh, Hn, H =>
      let (h', Hh') := fast_eval_appm_impl h n _ Hn _ in
      let (r, Hr) := fast_eval_selmc_impl h' ch _ _ in
      exist _ r _

  with fast_eval_appms_impl (h : fdmod) (ns : list fdomain) (Hh : fdmod_ok Θ Ξ h) (Hns : Forall (fdomain_ok Θ Ξ) ns)
      (H : eval_appms_order Θ Ξ (fdmod_erase h) (fdomains_erase ns)) :
      { r | $ᵐ*| fdmod_erase h & fdomains_erase ns | Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | h, nil, Hh, Hns, H => exist _ h _
  | h, n :: ns, Hh, Hns, H =>
      let (h1, Hh1) := fast_eval_appm_impl h n Hh _ _ in
      let (r, Hr) := fast_eval_appms_impl h1 ns _ _ _ in
      exist _ r _

  with fast_eval_sel_impl (h : fdmod) x (Hh : fdmod_ok Θ Ξ h) (H : eval_sel_order Θ Ξ (fdmod_erase h) x) :
      { r | fdmod_erase h ·ₜ x Θ ⍮ Ξ ↘ fdomain_erase r /\ fdomain_ok Θ Ξ r } by struct H :=
  (** A member of a global module lacking a parameter: a member closure *)
  | fdm_global pq args, x, Hh, H with module_saturated_f pq args := {
    | right Hu => exist _ (fd_member (fdm_global pq args) (x :: nil)) _
    | left Hs with gc_entry_with_values F (qname_app pq (x :: nil)) := {
    (** A proof member, at exactly the module's parameters: kept as the
        selection *)
    | exist _ (Some (fe_def _ _ ak_propositional _ _ _)) (conj E Ev) with module_exact_f pq args := {
      | inleft (exist _ T HT) => exist _ (fd_proof (member_proof x) (fglobal_proof_env pq T args)) _
      | inright Hne => False_rect _ _ }
    (** A transparent definition's stored value, applied *)
    | exist _ (Some (fe_def true pv κ A (Some M) (Some v))) (conj E Ev) =>
        let Hf := stored_def_value _ _ _ _ _ _ _ _ (Ev _ eq_refl) in
        let (r, Hr) := fast_eval_apps_impl v args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def true pv κ A (Some M) None)) (conj E Ev) =>
        let (f, Hf) := fast_eval_exp_impl M nil _ _ in
        let (r, Hr) := fast_eval_apps_impl f args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def true _ κ A None _)) (conj E Ev) =>
        let (a, Ha) := fast_eval_exp_impl A nil _ _ in
        let (r, Hr) := fast_eval_apps_impl (fd_neut a (fd_glob (qname_app pq (x :: nil)))) args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def false _ κ A B _)) (conj E Ev) =>
        let (a, Ha) := fast_eval_exp_impl A nil _ _ in
        let (r, Hr) := fast_eval_apps_impl (fd_neut a (fd_glob (qname_app pq (x :: nil)))) args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_mod _ _)) (conj E Ev) with ind_mlookup_f F (qname_app pq (x :: nil)) := {
      | exist _ (Some (pg, k, D)) El =>
          let (r, Hr) := fast_eval_apps_impl (fd_ind pg None k nil) args _ _ _ in
          exist _ r _
      | exist _ None El => False_rect _ _ }
    | exist _ (Some (fe_ind _ pg k D _)) (conj E Ev) =>
        let (r, Hr) := fast_eval_apps_impl (fd_ind pg None k nil) args _ _ _ in
        exist _ r _
    (** A definition with a module part's stored value, applied *)
    | exist _ (Some (fe_def_mod pv A M u (Some v))) (conj E Ev) =>
        let Hf := stored_dm_value _ _ _ _ _ _ _ (Ev _ eq_refl) in
        let (r, Hr) := fast_eval_apps_impl v args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def_mod _ _ M _ None)) (conj E Ev) =>
        let (f, Hf) := fast_eval_exp_impl M nil _ _ in
        let (r, Hr) := fast_eval_apps_impl f args _ _ _ in
        exist _ r _
    (** A stored record type: its type former *)
    | exist _ (Some (fe_record _ _ _ _)) (conj E Ev) with record_lookup_f F (qname_app pq (x :: nil)) := {
      | exist _ (Some R) Er =>
          let (r, Hr) := fast_eval_apps_impl (fd_record (qname_app pq (x :: nil)) nil) args _ _ _ in
          exist _ r _
      | exist _ None Er => False_rect _ _ }
    (** The open frame of a member's module or of a record type's module:
        its type former *)
    | exist _ None (conj E Ev) with ind_mlookup_f F (qname_app pq (x :: nil)) := {
      | exist _ (Some (pg, k, D)) El =>
          let (r, Hr) := fast_eval_apps_impl (fd_ind pg None k nil) args _ _ _ in
          exist _ r _
      | exist _ None El with record_lookup_f F (qname_app pq (x :: nil)) := {
        | exist _ (Some R) Er =>
            let (r, Hr) := fast_eval_apps_impl (fd_record (qname_app pq (x :: nil)) nil) args _ _ _ in
            exist _ r _
        | exist _ None Er => False_rect _ _ } } } }
  | fdm_local (e :: Δ) D p, x, Hh, H => exist _ (fd_member (fdm_local (e :: Δ) D p) (x :: nil)) _
  | fdm_local nil (md_alias E) p, x, Hh, H => False_rect _ _
  (** A member of a saturated body, read in its expansion *)
  | fdm_local nil (md_body sm Φ) p, x, Hh, H with inspect (gm_prefix_upto (gm_expand Φ) x) := {
    | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_tm E) := {
      | exist _ (Some (A, M)) Et with inspect (entry_kind E) := {
        (** A proof member: kept as the selection *)
        | exist _ ak_propositional Er =>
            exist _ (fd_proof (member_proof x) (fextend_env_mod p (fdm_local nil (md_body sm Φ) p) (gu_mk nil (md_body sm Φ)))) _
        | exist _ ak_relevant Er =>
            let (p', Hp') := fast_eval_body_env_impl p Φ' _ _ in
            let (r, Hr) := fast_eval_exp_impl M p' _ _ in
            exist _ r _
        | exist _ ak_level Er =>
            let (p', Hp') := fast_eval_body_env_impl p Φ' _ _ in
            let (r, Hr) := fast_eval_exp_impl M p' _ _ in
            exist _ r _ }
      | exist _ None Et => False_rect _ _ }
    | exist _ _ P => False_rect _ _ }
  | fdm_member h ch, x, Hh, H => exist _ (fd_member h (ch ++ x :: nil)) _

  with fast_eval_selm_impl (h : fdmod) y (Hh : fdmod_ok Θ Ξ h) (H : eval_selm_order Θ Ξ (fdmod_erase h) y) :
      { r | fdmod_erase h ·ₘ y Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | fdm_global pq args, y, Hh, H with gc_module_f F (qname_app pq (y :: nil)) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh') := fast_eval_close_impl Δ D nil _ _ in
        let (r, Hr) := fast_eval_appms_impl h args _ _ _ in
        exist _ r _
    | exist _ _ E => exist _ (fdm_global (qname_app pq (y :: nil)) args) _ }
  | fdm_local (e :: Δ) D p, y, Hh, H => exist _ (fdm_member (fdm_local (e :: Δ) D p) (y :: nil)) _
  | fdm_local nil (md_alias E) p, y, Hh, H => False_rect _ _
  | fdm_local nil (md_body sm Φ) p, y, Hh, H with inspect (gm_prefix_upto (gm_expand Φ) y) := {
    | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_unit E) := {
      | exist _ (Some (gu_mk Δy Dy)) Eu =>
          let (p', Hp') := fast_eval_body_env_impl p Φ' _ _ in
          let (r, Hr) := fast_eval_close_impl Δy Dy p' _ _ in
          exist _ r _
      | exist _ None Eu => False_rect _ _ }
    | exist _ _ P => False_rect _ _ }
  | fdm_member h ch, y, Hh, H => exist _ (fdm_member h (ch ++ y :: nil)) _

  with fast_eval_selc_impl (h : fdmod) ch (Hh : fdmod_ok Θ Ξ h) (H : eval_selc_order Θ Ξ (fdmod_erase h) ch) :
      { r | fdmod_erase h ·ₜ* ch Θ ⍮ Ξ ↘ fdomain_erase r /\ fdomain_ok Θ Ξ r } by struct H :=
  | h, x :: nil, Hh, H =>
      let (r, Hr) := fast_eval_sel_impl h x Hh _ in
      exist _ r _
  | h, y :: ch, Hh, H =>
      let (h1, Hh1) := fast_eval_selm_impl h y Hh _ in
      let (r, Hr) := fast_eval_selc_impl h1 ch _ _ in
      exist _ r _
  | h, nil, Hh, H => False_rect _ _

  with fast_eval_selmc_impl (h : fdmod) ch (Hh : fdmod_ok Θ Ξ h) (H : eval_selmc_order Θ Ξ (fdmod_erase h) ch) :
      { r | fdmod_erase h ·ₘ* ch Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | h, nil, Hh, H => exist _ h _
  | h, y :: ch, Hh, H =>
      let (h1, Hh1) := fast_eval_selm_impl h y Hh _ in
      let (r, Hr) := fast_eval_selmc_impl h1 ch _ _ in
      exist _ r _

  with fast_eval_body_env_impl (p : fenv) Φ (Hp : fenv_ok Θ Ξ p) (H : eval_body_env_order Θ Ξ (fenv_erase p) Φ) :
      { p' | ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fenv_erase p' /\ fenv_ok Θ Ξ p' } by struct H :=
  | p, gm_nil, Hp, H => exist _ p _
  (** A definition tagged a proposition: kept as it is *)
  | p, gm_ext Φ y (ge_def b pv ak_propositional A (Some M)), Hp, H =>
      let (p1, Hp1) := fast_eval_body_env_impl p Φ Hp _ in
      exist _ (fextend_env p1 (fd_proof M p1) (fentry_type_closure A p1)) _
  | p, gm_ext Φ y (ge_def b pv ak_relevant A (Some M)), Hp, H =>
      let (p1, Hp1) := fast_eval_body_env_impl p Φ Hp _ in
      let (m, Hm) := fast_eval_exp_impl M p1 _ _ in
      exist _ (fextend_env p1 m (fentry_type_closure A p1)) _
  | p, gm_ext Φ y (ge_def b pv ak_level A (Some M)), Hp, H =>
      let (p1, Hp1) := fast_eval_body_env_impl p Φ Hp _ in
      let (m, Hm) := fast_eval_exp_impl M p1 _ _ in
      exist _ (fextend_env p1 m (fentry_type_closure A p1)) _
  | p, gm_ext Φ y (ge_mod _ (gu_mk Δy Dy)), Hp, H =>
      let (p1, Hp1) := fast_eval_body_env_impl p Φ Hp _ in
      let (h, Hh) := fast_eval_close_impl Δy Dy p1 _ _ in
      exist _ (fextend_env_mod p1 h (gu_mk Δy Dy)) _
  | p, gm_ext Φ y (ge_def_mod _ A M (gu_mk Δy Dy)), Hp, H =>
      let (p1, Hp1) := fast_eval_body_env_impl p Φ Hp _ in
      let (m, Hm) := fast_eval_exp_impl M p1 _ _ in
      let (h, Hh) := fast_eval_close_impl Δy Dy p1 _ _ in
      exist _ (fextend_env_dm p1 m (fentry_type_closure A p1) h (gu_mk Δy Dy)) _
  | p, _, Hp, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([eval_obligation]).  They are transparent: the order premises are the
    arguments of the structural recursion. *)
Solve All Obligations with eval_obligation.
End EvalImpl.

Extraction Inline fast_eval_exp_impl_functional
  fast_eval_elim_impl_functional
  fast_eval_ihs_impl_functional
  fast_eval_ih_impl_functional
  fast_eval_mref_impl_functional
  fast_eval_shape_type_impl_functional
  fast_eval_ihty_impl_functional
  fast_eval_app_impl_functional
  fast_eval_exps_impl_functional
  fast_eval_apps_impl_functional
  fast_eval_modexp_impl_functional
  fast_eval_close_impl_functional
  fast_eval_appm_impl_functional
  fast_eval_appms_impl_functional
  fast_eval_sel_impl_functional
  fast_eval_selm_impl_functional
  fast_eval_selc_impl_functional
  fast_eval_selmc_impl_functional
  fast_eval_body_env_impl_functional
  fast_eval_field_vals_impl_functional.
