From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval Kinds.
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

Inductive fast_eval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
| fast_eval_exp_order_typ :
  `( fast_eval_exp_order Θ Ξ Typeω@i p )
(** A small universe evaluates its level. *)
| fast_eval_exp_order_univ :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exp_order Θ Ξ Type⟨M⟩ p )
(** An environment is total, so a variable always terminates. *)
| fast_eval_exp_order_var :
  `( fast_eval_exp_order Θ Ξ #x p )
| fast_eval_exp_order_level :
  `( fast_eval_exp_order Θ Ξ (Level@n) p )
| fast_eval_exp_order_level_sort :
  `( fast_eval_exp_order Θ Ξ LevelSort p )
| fast_eval_exp_order_llit :
  `( fast_eval_exp_order Θ Ξ (𝕃ᵒ o) p )
| fast_eval_exp_order_succl :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exp_order Θ Ξ (succl M) p )
| fast_eval_exp_order_maxl :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exp_order Θ Ξ N p ->
     fast_eval_exp_order Θ Ξ (maxl M N) p )
(** [Prop] *)
| fast_eval_exp_order_prop :
  `( fast_eval_exp_order Θ Ξ Propₘ p )
| fast_eval_exp_order_True :
  `( fast_eval_exp_order Θ Ξ ⊤ p )
(** The introduction of [⊤], a proof: nothing evaluated *)
| fast_eval_exp_order_tt :
  `( fast_eval_exp_order Θ Ξ a_tt p )
| fast_eval_exp_order_False :
  `( fast_eval_exp_order Θ Ξ ⊥ p )
(** [efq]: its type only; its proof is not evaluated *)
| fast_eval_exp_order_absurd :
  `( fast_eval_exp_order Θ Ξ C p ->
     fast_eval_exp_order Θ Ξ (efq M return C) p )
(** A [Σₚ]: its first component *)
| fast_eval_exp_order_and :
  `( fast_eval_exp_order Θ Ξ P p ->
     fast_eval_exp_order Θ Ξ (Σₚ P Q) p )
(** The proofs of a conjunction and of its components: nothing evaluated *)
| fast_eval_exp_order_conj :
  `( fast_eval_exp_order Θ Ξ (a_conj P Q M N) p )
| fast_eval_exp_order_left :
  `( fast_eval_exp_order Θ Ξ (a_left M) p )
| fast_eval_exp_order_right :
  `( fast_eval_exp_order Θ Ξ (a_right M) p )
(** A [Π], at its kinds: its domain *)
| fast_eval_exp_order_pi :
  `( fast_eval_exp_order Θ Ξ A p ->
     fast_eval_exp_order Θ Ξ (a_pi κd κc A B) p )
| fast_eval_exp_order_indty :
  `( fast_eval_exp_order Θ Ξ (a_ind pq k) p )
(** A constructor that is a value of its own before any argument *)
| fast_eval_exp_order_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     im_starts D Mk = true ->
     fast_eval_exp_order Θ Ξ (a_con pq k c) p )
(** A constructor of a view of a group with no uniform parameters: the
    view's arguments are evaluated *)
| fast_eval_exp_order_con_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_nu D = 0 ->
     fast_eval_exps_order Θ Ξ Is nil ->
     fast_eval_exp_order Θ Ξ (a_con pq j c) p )
(** The constructor of a record view of a group with no uniform
    parameters, of a record with fields: a value of its own *)
| fast_eval_exp_order_con_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ind_nu D = 0 ->
     0 < List.length fl ->
     fast_eval_exp_order Θ Ξ (a_con pq j c) p )
(** The constructor of a record view of a group with no uniform
    parameters, of a record without fields: the empty tuple *)
| fast_eval_exp_order_con_rview_empty :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is nil ->
     ind_nu D = 0 ->
     fast_eval_exp_order Θ Ξ (a_con pq j c) p )
(** The eliminator into types: its uniform parameters, its scrutinee, and
    the elimination at the group it names *)
| fast_eval_exp_order_elim :
  `( fast_eval_exps_order Θ Ξ Us p ->
     fast_eval_exp_order Θ Ξ M p ->
     (forall ups m, ⟦ Us ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ups -> ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m ->
        fast_eval_elim_order Θ Ξ p pq ups Bks j m) ->
     fast_eval_exp_order Θ Ξ (a_elim ak_relevant pq Us j Bks M) p )
(** An eliminator into propositions: nothing evaluated *)
| fast_eval_exp_order_elim_proof :
  `( fast_eval_exp_order Θ Ξ (a_elim ak_propositional pq Us j Bks M) p )
(** A function: its domain *)
| fast_eval_exp_order_fn :
  `( fast_eval_exp_order Θ Ξ A p ->
     fast_eval_exp_order Θ Ξ (λ A M) p )
(** An application: the function, then, by the kind of the argument it
    takes, the argument and the application to it, or the application to
    the proof kept as it is *)
| fast_eval_exp_order_app :
  `( fast_eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> evaluated_kind (arg_kind Θ Ξ m) -> fast_eval_exp_order Θ Ξ N p) ->
     (forall m n, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> evaluated_kind (arg_kind Θ Ξ m) -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n ->
        fast_eval_app_order Θ Ξ m n) ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> arg_kind Θ Ξ m = ak_propositional -> fast_eval_app_order Θ Ξ m ⋆ᵈ⟨N, p⟩) ->
     fast_eval_exp_order Θ Ξ (M $ N) p )
(** A local definition: its type, then, by the type's kind, its body and
    the rest, or the rest at the body kept as a proof *)
| fast_eval_exp_order_let :
  `( fast_eval_exp_order Θ Ξ A p ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> evaluated_kind (domain_kind a) -> fast_eval_exp_order Θ Ξ M p) ->
     (forall a m, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> evaluated_kind (domain_kind a) -> ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m ->
        fast_eval_exp_order Θ Ξ B (p ↦ m ⦂ entry_type_value a)) ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> domain_kind a = ak_propositional ->
        fast_eval_exp_order Θ Ξ B (p ↦ ⋆ᵈ⟨M, p⟩ ⦂ entry_type_value a)) ->
     fast_eval_exp_order Θ Ξ (ℓ A ≔ M in B) p )
| fast_eval_exp_order_let_mod :
  `( fast_eval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_exp_order Θ Ξ B (p ↦ᵐ h ⦂ gu_mk Δ D)) ->
     fast_eval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
| fast_eval_exp_order_mem :
  `( modexp_spine H = (R, args, pre) ->
     fast_eval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     fast_eval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> h ·ₜ*ᶠ (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
        ⟦ args ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ns -> fast_eval_apps_order Θ Ξ f ns) ->
     fast_eval_exp_order Θ Ξ (a_mem H x) p )
(** A record's type former is a value. *)
| fast_eval_exp_order_record :
  `( fast_eval_exp_order Θ Ξ (a_record pq) p )
(** A record element: its type, which finds a record, then the values of
    its fields at the record's kinds *)
| fast_eval_exp_order_tuple :
  `( fast_eval_exp_order Θ Ξ T p ->
     (forall t, ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ t -> exists pq ns R, t = d_record pq ns /\ record_lookup Θ Ξ pq = Some R) ->
     (forall pq ns R, ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d_record pq ns -> record_lookup Θ Ξ pq = Some R ->
        fast_eval_field_vals_order Θ Ξ (record_field_kinds R) (List.map snd fs) p) ->
     fast_eval_exp_order Θ Ξ (a_tuple T fs) p )
(** A field: the value, then the field of it *)
| fast_eval_exp_order_proj :
  `( fast_eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> fast_eval_proj_order Θ Ξ f m) ->
     fast_eval_exp_order Θ Ξ (a_proj f M) p )

(** The values of the fields of a record value, as [fast_eval_field_vals]
    reads them *)
with fast_eval_field_vals_order (Θ : gdeps) (Ξ : gstack) : list abs_kind -> list exp -> env -> Prop :=
(** No field *)
| fast_eval_field_vals_order_nil :
  `( fast_eval_field_vals_order Θ Ξ rs nil p )
(** A field of an evaluated kind: its value, then the rest *)
| fast_eval_field_vals_order_evaluated :
  `( evaluated_kind (List.hd ak_relevant rs) ->
     fast_eval_exp_order Θ Ξ M p ->
     fast_eval_field_vals_order Θ Ξ (List.tl rs) Ms p ->
     fast_eval_field_vals_order Θ Ξ rs (M :: Ms) p )
(** A propositional field: the rest *)
| fast_eval_field_vals_order_proof :
  `( List.hd ak_relevant rs = ak_propositional ->
     fast_eval_field_vals_order Θ Ξ (List.tl rs) Ms p ->
     fast_eval_field_vals_order Θ Ξ rs (M :: Ms) p )

(** The field [f] of a value, as [fast_eval_proj] reads it *)
with fast_eval_proj_order (Θ : gdeps) (Ξ : gstack) : string -> domain -> Prop :=
(** Of a tuple with the field *)
| fast_eval_proj_order_tuple :
  `( field_lookup vs f <> None ->
     fast_eval_proj_order Θ Ξ f (d_tuple vs) )
(** Of a neutral of a record type with the field: the projections of the
    fields up to it, which reach it *)
| fast_eval_proj_order_neut :
  `( record_lookup Θ Ξ pq = Some R ->
     field_index (record_fields R) f = Some k ->
     fast_eval_neutral_fields_order Θ Ξ m (env_tele nil (List.rev (record_params R)) ns) (List.firstn (S k) (record_fields R)) ->
     (forall rs, fast_eval_neutral_fields Θ Ξ m (env_tele nil (List.rev (record_params R)) ns) (List.firstn (S k) (record_fields R)) rs ->
        List.nth_error rs k <> None) ->
     fast_eval_proj_order Θ Ξ f (⇑ (d_record pq ns) m) )

(** The neutral projections at a list of fields, as [fast_eval_neutral_fields] reads
    them *)
with fast_eval_neutral_fields_order (Θ : gdeps) (Ξ : gstack) : domain_ne -> env -> list (string * exp) -> Prop :=
(** No field left *)
| fast_eval_neutral_fields_order_nil :
  `( fast_eval_neutral_fields_order Θ Ξ m p nil )
(** The next field's type, then the rest after its projection *)
| fast_eval_neutral_fields_order_cons :
  `( fast_eval_exp_order Θ Ξ T p ->
     (forall a, ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a ->
        fast_eval_neutral_fields_order Θ Ξ m (p ↦ ⇑ a (d_proj g m) ⦂ entry_type_closure T p) fl) ->
     fast_eval_neutral_fields_order Θ Ξ m p ((g, T) :: fl) )

(** The eliminator of the group at [pq] at its member [j], on a value, as
    [fast_eval_elim] reads it. *)
with fast_eval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> Prop :=
(** On a saturated constructor: the recursive results the branch reads,
    then the branch, at its typed entries.  The group's table of leaf
    paths is coherent, the gate [fast_eval_elim_con] has: a premise of the
    domain, not a check the evaluator runs *)
| fast_eval_elim_order_con :
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
     fast_eval_ihs_order Θ Ξ p pq ups Bks (Some B) gs (skipn (im_np Dq Mk) vs) ->
     (forall ihs, ⟦ihsᶠ skipn (im_np Dq Mk) vs of gs under pq ups Bks for (Some B) ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs ->
        fast_eval_exp_order Θ Ξ B (env_extend_typed p (branch_entries D Mj pq ups (blocks_motives Bks) p gs
                                                     (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs)) (skipn (im_np Dq Mk) vs) ihs))) ->
     fast_eval_elim_order Θ Ξ p pq ups Bks j (d_con pc k c vs) )
(** On a neutral: the member stood for, then the motive's instance *)
| fast_eval_elim_order_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_ref pq j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_binder_count b = S (im_nn Mk) ->
     fast_eval_mref_order Θ Ξ pq ups j ->
     (forall cups, ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, cups) ->
        fast_eval_exp_order Θ Ξ (eb_motive b)
          (env_extend_typed p (motive_entries D Mj ups (List.skipn (ind_nu Dq) as')
                                 (d_ind pc k (cups ++ List.skipn (ind_nu Dq) as')) (⇑ (d_ind pc k as') m)))) ->
     fast_eval_elim_order Θ Ξ p pq ups Bks j (⇑ (d_ind pc k as') m) )

(** The recursive results of the arguments [vs] of kinds [gs], for the
    branch [oB] ([None]: all of them) *)
with fast_eval_ihs_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> option exp -> list carg -> list domain -> Prop :=
(** No argument *)
| fast_eval_ihs_order_nil :
  `( fast_eval_ihs_order Θ Ξ p pq ups Bks oB nil nil )
(** A non-recursive argument *)
| fast_eval_ihs_order_arg :
  `( fast_eval_ihs_order Θ Ξ p pq ups Bks oB gs vs ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB (ca_arg r T :: gs) (v :: vs) )
(** A recursive argument the branch reads one result of: its results,
    then the rest *)
| fast_eval_ihs_order_rec_case :
  `( ind_lookup Θ Ξ pq = Some D ->
     ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t)) = false ->
     fast_eval_ih_order Θ Ξ p pq ups Bks t v ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB gs vs ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB (ca_rec t :: gs) (v :: vs) )
(** One it reads none of: the rest only *)
| fast_eval_ihs_order_skip :
  `( ind_lookup Θ Ξ pq = Some D ->
     ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t)) = true ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB gs vs ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB (ca_rec t :: gs) (v :: vs) )

(** The recursive results of an argument of a shape *)
with fast_eval_ih_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> Prop :=
(** At the end, at a member with a block: the eliminator at the member *)
| fast_eval_ih_order_self :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     fast_eval_elim_order Θ Ξ p pq ups Bks j v ->
     fast_eval_ih_order Θ Ξ p pq ups Bks (pt_self j Ps) v )
(** At the end, at a record view: the projections, then all their
    recursive results *)
| fast_eval_ih_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     fast_eval_projs_order Θ Ξ fl v ->
     (forall ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_eval_ihs_order Θ Ξ p pq ups Bks None gs ws) ->
     fast_eval_ih_order Θ Ξ p pq ups Bks (pt_self j Ps) v )
(** At a function shape: closures, one per leaf path of the rest *)
| fast_eval_ih_order_pi :
  `( ind_lookup Θ Ξ pq = Some D ->
     fast_eval_ih_order Θ Ξ p pq ups Bks (pt_pi B t) v )

(** The projections of a value at a list of fields *)
with fast_eval_projs_order (Θ : gdeps) (Ξ : gstack) : list string -> domain -> Prop :=
(** No field *)
| fast_eval_projs_order_nil :
  `( fast_eval_projs_order Θ Ξ nil v )
(** The first field's projection, then the rest *)
| fast_eval_projs_order_cons :
  `( fast_eval_proj_order Θ Ξ f v ->
     fast_eval_projs_order Θ Ξ fl v ->
     fast_eval_projs_order Θ Ξ (f :: fl) v )

(** The member a member of a group stands for, as [fast_eval_mref] reads it *)
with fast_eval_mref_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> nat -> Prop :=
(** A declared member *)
| fast_eval_mref_order_decl :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_decl pm ->
     fast_eval_mref_order Θ Ξ pq ups j )
(** A view: the view's arguments at the uniform parameters *)
| fast_eval_mref_order_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     fast_eval_exps_order Θ Ξ Is (decl_env D ups) ->
     fast_eval_mref_order Θ Ξ pq ups j )

(** The type of an argument of a shape *)
with fast_eval_shape_type_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
(** At the end: the parameters, and the member stood for *)
| fast_eval_shape_type_order_self :
  `( fast_eval_exps_order Θ Ξ Ps p ->
     fast_eval_mref_order Θ Ξ pq ups j ->
     fast_eval_shape_type_order Θ Ξ pq ups p (pt_self j Ps) )
(** At the end, at a record view: the view's instance *)
| fast_eval_shape_type_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     fast_eval_exps_order Θ Ξ Is (decl_env D ups) ->
     fast_eval_shape_type_order Θ Ξ pq ups p (pt_self j Ps) )
(** At a domain *)
| fast_eval_shape_type_order_pi :
  `( fast_eval_exp_order Θ Ξ B p ->
     fast_eval_shape_type_order Θ Ξ pq ups p (pt_pi B t) )

(** The types of the recursive results of an argument of a shape *)
with fast_eval_ihty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> ptyp -> domain -> Prop :=
(** At the end, at a member with a block: the parameters, then the
    member's motive *)
| fast_eval_ihty_order_self :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     fast_eval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ bs ->
        fast_eval_exp_order Θ Ξ (List.nth j As a_prop)
          (env_extend_typed pm (tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) bs ++
                                (v, entry_type_shape pq ups p (pt_self j Ps)) :: nil))) ->
     fast_eval_ihty_order Θ Ξ pq ups pm As p (pt_self j Ps) v )
(** At the end, at a record view: the projections, then their recursive
    results' types *)
| fast_eval_ihty_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     fast_eval_projs_order Θ Ξ fl v ->
     (forall ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_eval_ihtys_order Θ Ξ pq ups pm As (decl_env D ups) gs ws) ->
     fast_eval_ihty_order Θ Ξ pq ups pm As p (pt_self j Ps) v )
(** At a domain *)
| fast_eval_ihty_order_pi :
  `( ind_lookup Θ Ξ pq = Some D ->
     fast_eval_exp_order Θ Ξ B p ->
     fast_eval_ihty_order Θ Ξ pq ups pm As p (pt_pi B t) v )

(** The types of the recursive results of a record view's fields *)
with fast_eval_ihtys_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> list carg -> list domain -> Prop :=
(** No field *)
| fast_eval_ihtys_order_nil :
  `( fast_eval_ihtys_order Θ Ξ pq ups pm As p nil nil )
(** A non-recursive field: the rest, under it at its type *)
| fast_eval_ihtys_order_arg :
  `( fast_eval_ihtys_order Θ Ξ pq ups pm As (p ↦ v ⦂ entry_type_closure T p) gs vs ->
     fast_eval_ihtys_order Θ Ξ pq ups pm As p (ca_arg r T :: gs) (v :: vs) )
(** A recursive field: its shape's, then the rest *)
| fast_eval_ihtys_order_rec :
  `( fast_eval_ihty_order Θ Ξ pq ups pm As p t v ->
     fast_eval_ihtys_order Θ Ξ pq ups pm As p gs vs ->
     fast_eval_ihtys_order Θ Ξ pq ups pm As p (ca_rec t :: gs) (v :: vs) )

with fast_eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| fast_eval_app_order_fn :
  `( fast_eval_exp_order Θ Ξ M (p ↦ n ⦂ entry_type_value a) ->
     fast_eval_app_order Θ Ξ (λᵈ a p M) n )
(** A neutral at a [Π] into an evaluated kind: the codomain's instance *)
| fast_eval_app_order_neut :
  `( evaluated_kind κc ->
     fast_eval_exp_order Θ Ξ B (p ↦ n ⦂ entry_type_value a) ->
     fast_eval_app_order Θ Ξ (⇑ (d_pi κd κc a p B) m) n )
| fast_eval_app_order_indty :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     fast_eval_app_order Θ Ξ (d_ind pq k as') n )
(** A constructor of a declared member *)
| fast_eval_app_order_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length vs < (im_np D Mk + List.length gs)%nat ->
     fast_eval_app_order Θ Ξ (d_con pq k c vs) n )
(** A constructor of a view, before its last uniform parameter *)
| fast_eval_app_order_con_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) < ind_nu D ->
     fast_eval_app_order Θ Ξ (d_con pq j c vs) n )
(** At its last uniform parameter: the view's arguments are evaluated *)
| fast_eval_app_order_con_view_ups :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) = ind_nu D ->
     fast_eval_exps_order Θ Ξ Is (decl_env D (vs ++ n :: nil)) ->
     fast_eval_app_order Θ Ξ (d_con pq j c vs) n )
(** A constructor of a record view, before its last argument *)
| fast_eval_app_order_con_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) < ind_nu D + List.length fl ->
     fast_eval_app_order Θ Ξ (d_con pq j c vs) n )
(** At its last: the tuple of the fields *)
| fast_eval_app_order_con_rview_full :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) = ind_nu D + List.length fl ->
     fast_eval_app_order Θ Ξ (d_con pq j c vs) n )
(** The [i]-th recursive result of a function shape: those of the rest at
    the function's value, which has an [i]-th *)
| fast_eval_app_order_ihfn :
  `( fast_eval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> fast_eval_ih_order Θ Ξ p pq ups Bks t fn) ->
     (forall fn rs, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> ⟦ihᶠ fn of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ rs -> List.nth_error rs i <> None) ->
     fast_eval_app_order Θ Ξ (d_ihfn p Bks pq ups t i f) n )
| fast_eval_app_order_shfam :
  `( fast_eval_shape_type_order Θ Ξ pq ups (p ↦ n ⦂ entry_type_closure B p) t ->
     fast_eval_app_order Θ Ξ (d_shfam pq ups p B t) n )
(** The [i]-th recursive result's family: those of the rest, which has an
    [i]-th *)
| fast_eval_app_order_ihfam :
  `( fast_eval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> fast_eval_ihty_order Θ Ξ pq ups pm As (p ↦ n ⦂ entry_type_closure B p) t fn) ->
     (forall fn as', $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> ⟦ihtyᶠ fn of t at pq ups under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ n ⦂ entry_type_closure B p ↘ as' ->
        List.nth_error as' i <> None) ->
     fast_eval_app_order Θ Ξ (d_ihfam pm As pq ups p B t i f) n )
| fast_eval_app_order_member :
  `( fast_eval_appm_order Θ Ξ h n ->
     (forall h', $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' -> fast_eval_selc_order Θ Ξ h' ch) ->
     fast_eval_app_order Θ Ξ (d_member h ch) n )
(** A record's type former, before its last parameter *)
| fast_eval_app_order_record :
  `( record_lookup Θ Ξ pq = Some R ->
     List.length ns < List.length (record_params R) ->
     fast_eval_app_order Θ Ξ (d_record pq ns) n )

with fast_eval_exps_order (Θ : gdeps) (Ξ : gstack) : list exp -> env -> Prop :=
| fast_eval_exps_order_nil :
  `( fast_eval_exps_order Θ Ξ nil p )
| fast_eval_exps_order_cons :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exps_order Θ Ξ Ms p ->
     fast_eval_exps_order Θ Ξ (M :: Ms) p )

with fast_eval_apps_order (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> Prop :=
| fast_eval_apps_order_nil :
  `( fast_eval_apps_order Θ Ξ m nil )
| fast_eval_apps_order_cons :
  `( fast_eval_app_order Θ Ξ m n ->
     (forall m1, $ᶠ| m & n | Θ ⍮ Ξ ↘ m1 -> fast_eval_apps_order Θ Ξ m1 args) ->
     fast_eval_apps_order Θ Ξ m (n :: args) )

with fast_eval_modexp_order (Θ : gdeps) (Ξ : gstack) : modexp -> env -> Prop :=
| fast_eval_modexp_order_var :
  `( fast_eval_modexp_order Θ Ξ (me_var x) p )
| fast_eval_modexp_order_unit :
  `( fast_eval_modexp_order Θ Ξ (me_unit fp) p )
| fast_eval_modexp_order_lit :
  `( fast_eval_close_order Θ Ξ Δ D p ->
     fast_eval_modexp_order Θ Ξ (me_lit (gu_mk Δ D)) p )
| fast_eval_modexp_order_mem :
  `( fast_eval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_selm_order Θ Ξ h y) ->
     fast_eval_modexp_order Θ Ξ (me_mem H y) p )
| fast_eval_modexp_order_app :
  `( fast_eval_modexp_order Θ Ξ H p ->
     fast_eval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> fast_eval_appm_order Θ Ξ h n) ->
     fast_eval_modexp_order Θ Ξ (me_app H N) p )

with fast_eval_close_order (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> Prop :=
| fast_eval_close_order_body :
  `( fast_eval_close_order Θ Ξ Δ (md_body sm Φ) p )
| fast_eval_close_order_alias :
  `( fast_eval_close_order Θ Ξ (e :: Δ) (md_alias E) p )
| fast_eval_close_order_alias0 :
  `( fast_eval_modexp_order Θ Ξ E p ->
     fast_eval_close_order Θ Ξ nil (md_alias E) p )

with fast_eval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| fast_eval_appm_order_global :
  `( fast_eval_appm_order Θ Ξ (dm_global pq args) n )
(** The outermost missing parameter is split off as the evaluator splits
    it off ([tele_snoc]), so that the order of the rest is a premise of the
    order of the whole. *)
| fast_eval_appm_order_local :
  `( tele_snoc Δ = Some (Δ0, ce_ass κ A) ->
     fast_eval_close_order Θ Ξ Δ0 D (p ↦ n ⦂ entry_type_closure A p) ->
     fast_eval_appm_order Θ Ξ (dm_local Δ D p) n )
| fast_eval_appm_order_member :
  `( fast_eval_appm_order Θ Ξ h n ->
     (forall h', $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' -> fast_eval_selmc_order Θ Ξ h' ch) ->
     fast_eval_appm_order Θ Ξ (dm_member h ch) n )

with fast_eval_appms_order (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> Prop :=
| fast_eval_appms_order_nil :
  `( fast_eval_appms_order Θ Ξ h nil )
| fast_eval_appms_order_cons :
  `( fast_eval_appm_order Θ Ξ h n ->
     (forall h1, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h1 -> fast_eval_appms_order Θ Ξ h1 ns) ->
     fast_eval_appms_order Θ Ξ h (n :: ns) )

with fast_eval_sel_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
(** A term part of a global module ([gc_term]): it, closed, applied to the
    arguments *)
| fast_eval_sel_order_global :
  `( module_saturated Θ Ξ pq args ->
     gc_term Θ Ξ (qname_app pq (x :: nil)) = Some M ->
     fast_eval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f -> fast_eval_apps_order Θ Ξ f args) ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
(** An opaque definition or axiom of an evaluated kind: its type, then the
    neutral applied to the arguments *)
| fast_eval_sel_order_global_neut :
  `( module_saturated Θ Ξ pq args ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv κ A B) ->
     evaluated_kind κ ->
     b = false \/ B = None ->
     fast_eval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ a -> fast_eval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
(** A proof member of a global module at exactly its parameters: nothing
    evaluated *)
| fast_eval_sel_order_global_proof :
  `( gc_loc Θ Ξ pq = Some (T, Φ) ->
     List.length args = List.length T ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv ak_propositional A B) ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
| fast_eval_sel_order_global_ind :
  `( module_saturated Θ Ξ pq args ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app pq (x :: nil)) = Some (pg, k, D) ->
     fast_eval_apps_order Θ Ξ (d_ind pg k nil) args ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
(** A member of a global module lacking a parameter: no recursion *)
| fast_eval_sel_order_global_unsat :
  `( gc_loc Θ Ξ pq = Some (T, Φ) ->
     List.length args < List.length T ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
| fast_eval_sel_order_unsat :
  `( fast_eval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
(** A term part of a saturated body of an evaluated kind ([entry_tm]),
    read in the expanded body *)
| fast_eval_sel_order_body :
  `( gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     evaluated_kind (entry_kind E) ->
     fast_eval_body_env_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> fast_eval_exp_order Θ Ξ M p') ->
     fast_eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
(** A proof member of a saturated body: nothing evaluated *)
| fast_eval_sel_order_body_proof :
  `( gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_kind E = ak_propositional ->
     fast_eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
| fast_eval_sel_order_member :
  `( fast_eval_sel_order Θ Ξ (dm_member h ch) x )
(** A record type of a global module, not a definition: its type former,
    applied to the arguments *)
| fast_eval_sel_order_global_record :
  `( module_saturated Θ Ξ pq args ->
     gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     record_lookup Θ Ξ (qname_app pq (x :: nil)) = Some R ->
     fast_eval_apps_order Θ Ξ (d_record (qname_app pq (x :: nil)) nil) args ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )

with fast_eval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| fast_eval_selm_order_global :
  `( gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     fast_eval_selm_order Θ Ξ (dm_global pq args) y )
| fast_eval_selm_order_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     fast_eval_close_order Θ Ξ Δ D nil ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ nil ↘ h -> fast_eval_appms_order Θ Ξ h args) ->
     fast_eval_selm_order Θ Ξ (dm_global pq args) y )
| fast_eval_selm_order_unsat :
  `( fast_eval_selm_order Θ Ξ (dm_local (e :: Δ) D p) y )
(** A module part of a saturated body ([entry_unit]), read in the
    expanded body *)
| fast_eval_selm_order_body :
  `( gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     fast_eval_body_env_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> fast_eval_close_order Θ Ξ Δy Dy p') ->
     fast_eval_selm_order Θ Ξ (dm_local nil (md_body sm Φ) p) y )
| fast_eval_selm_order_member :
  `( fast_eval_selm_order Θ Ξ (dm_member h ch) y )

with fast_eval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fast_eval_selc_order_one :
  `( fast_eval_sel_order Θ Ξ h x ->
     fast_eval_selc_order Θ Ξ h (x :: nil) )
| fast_eval_selc_order_cons :
  `( fast_eval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 -> fast_eval_selc_order Θ Ξ h1 (z :: ch)) ->
     fast_eval_selc_order Θ Ξ h (y :: z :: ch) )

with fast_eval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fast_eval_selmc_order_nil :
  `( fast_eval_selmc_order Θ Ξ h nil )
| fast_eval_selmc_order_cons :
  `( fast_eval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 -> fast_eval_selmc_order Θ Ξ h1 ch) ->
     fast_eval_selmc_order Θ Ξ h (y :: ch) )

with fast_eval_body_env_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| fast_eval_body_env_order_nil :
  `( fast_eval_body_env_order Θ Ξ p gm_nil )
(** A definition of an evaluated kind: the body before it, then its body *)
| fast_eval_body_env_order_def :
  `( evaluated_kind κ ->
     fast_eval_body_env_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_exp_order Θ Ξ M p1) ->
     fast_eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def b pv κ A (Some M))) )
(** A definition tagged a proposition: the body before it *)
| fast_eval_body_env_order_def_proof :
  `( fast_eval_body_env_order Θ Ξ p Φ ->
     fast_eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def b pv ak_propositional A (Some M))) )
| fast_eval_body_env_order_mod :
  `( fast_eval_body_env_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_close_order Θ Ξ Δy Dy p1) ->
     fast_eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) )
(** A definition with a module part: its term and its unit's closure *)
| fast_eval_body_env_order_dm :
  `( fast_eval_body_env_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_exp_order Θ Ξ M p1) ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_close_order Θ Ξ Δy Dy p1) ->
     fast_eval_body_env_order Θ Ξ p (gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy))) ).

#[local]
Hint Constructors fast_eval_exp_order fast_eval_elim_order fast_eval_ihs_order fast_eval_ih_order fast_eval_mref_order fast_eval_shape_type_order fast_eval_ihty_order fast_eval_app_order fast_eval_exps_order fast_eval_apps_order
  fast_eval_modexp_order fast_eval_close_order fast_eval_appm_order fast_eval_appms_order fast_eval_sel_order fast_eval_selm_order fast_eval_selc_order fast_eval_selmc_order
  fast_eval_body_env_order fast_eval_proj_order fast_eval_neutral_fields_order fast_eval_projs_order fast_eval_ihtys_order
  fast_eval_field_vals_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_fast_eval_all :=
  repeat match goal with
    | H1 : fast_eval_exp ?T ?X ?M ?p ?m1, H2 : fast_eval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_fast_eval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_app ?T ?X ?m ?n ?r1, H2 : fast_eval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_exps ?T ?X ?M ?p ?r1, H2 : fast_eval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_exps _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_apps ?T ?X ?m ?n ?r1, H2 : fast_eval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_fast_eval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_modexp ?T ?X ?M ?p ?r1, H2 : fast_eval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_close ?T ?X ?Δ ?D ?p ?r1, H2 : fast_eval_close ?T ?X ?Δ ?D ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X)))))) _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_appm ?T ?X ?m ?n ?r1, H2 : fast_eval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_appms ?T ?X ?m ?n ?r1, H2 : fast_eval_appms ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_sel ?T ?X ?m ?n ?r1, H2 : fast_eval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_selm ?T ?X ?m ?n ?r1, H2 : fast_eval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_selc ?T ?X ?m ?n ?r1, H2 : fast_eval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_selmc ?T ?X ?m ?n ?r1, H2 : fast_eval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_fast_eval T X)))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_body_env ?T ?X ?m ?n ?r1, H2 : fast_eval_body_env ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_body_env _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_elim ?T ?X ?p ?pg ?u ?Bs ?j ?m ?r1, H2 : fast_eval_elim ?T ?X ?p ?pg ?u ?Bs ?j ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_elim _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_ihs ?T ?X ?p ?pg ?u ?Bs ?B ?gs ?vs ?r1, H2 : fast_eval_ihs ?T ?X ?p ?pg ?u ?Bs ?B ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_ihs _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_ih ?T ?X ?p ?pg ?u ?Bs ?t ?v ?r1, H2 : fast_eval_ih ?T ?X ?p ?pg ?u ?Bs ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_ih _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_mref ?T ?X ?pg ?u ?j ?r1, H2 : fast_eval_mref ?T ?X ?pg ?u ?j ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_mref _ _ _ _ _ H1 H2); subst; clear H2
    | H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst
    | H1 : fast_eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : fast_eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_shape_type _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_ihty ?T ?X ?p ?u ?ρm ?A ?ρ ?t ?v ?r1, H2 : fast_eval_ihty ?T ?X ?p ?u ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_ihty _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_ihtys ?T ?X ?p ?u ?ρm ?A ?ρ ?gs ?vs ?r1, H2 : fast_eval_ihtys ?T ?X ?p ?u ?ρm ?A ?ρ ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_ihtys _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_projs ?T ?X ?fl ?v ?r1, H2 : fast_eval_projs ?T ?X ?fl ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_projs _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    | H1 : fast_eval_proj ?T ?X ?f ?m ?r1, H2 : fast_eval_proj ?T ?X ?f ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_proj _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_neutral_fields ?T ?X ?m ?p ?fl ?r1, H2 : fast_eval_neutral_fields ?T ?X ?m ?p ?fl ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_neutral_fields _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_field_vals ?T ?X ?rs ?Ms ?p ?r1, H2 : fast_eval_field_vals ?T ?X ?rs ?Ms ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_field_vals _ _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_record _ _ = d_record _ _ |- _ => injection H; clear H; intros; subst
    end.

(** Every evaluation has an order: the evaluator terminates on what
    evaluates. *)
Lemma fast_eval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_exp_order Θ Ξ m p) /\
    (forall m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> fast_eval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> fast_eval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*ᶠ| m & ns | Θ ⍮ Ξ ↘ r -> fast_eval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_modexp_order Θ Ξ H p) /\
    (forall Δ D p h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_close_order Θ Ξ Δ D p) /\
    (forall h n r, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r -> fast_eval_appm_order Θ Ξ h n) /\
    (forall h ns r, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r -> fast_eval_appms_order Θ Ξ h ns) /\
    (forall h x r, h ·ₜᶠ x Θ ⍮ Ξ ↘ r -> fast_eval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘᶠ y Θ ⍮ Ξ ↘ r -> fast_eval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r -> fast_eval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r -> fast_eval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> fast_eval_body_env_order Θ Ξ p Φ) /\
    (forall p pq ups Bks j m r, ⟦elimᶠ m at j of pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> fast_eval_elim_order Θ Ξ p pq ups Bks j m) /\
    (forall p pq ups Bks B gs vs ihs, ⟦ihsᶠ vs of gs under pq ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs ->
       fast_eval_ihs_order Θ Ξ p pq ups Bks B gs vs) /\
    (forall p pq ups Bks t v r, ⟦ihᶠ v of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> fast_eval_ih_order Θ Ξ p pq ups Bks t v) /\
    (forall pq ups j r, ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ r -> fast_eval_mref_order Θ Ξ pq ups j) /\
    (forall pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_shape_type_order Θ Ξ pq ups p t) /\
    (forall pq ups pm As p t v a, ⟦ihtyᶠ v of t at pq ups under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_ihty_order Θ Ξ pq ups pm As p t v) /\
    (forall f m r, fast_eval_proj Θ Ξ f m r -> fast_eval_proj_order Θ Ξ f m) /\
    (forall m p fl rs, fast_eval_neutral_fields Θ Ξ m p fl rs -> fast_eval_neutral_fields_order Θ Ξ m p fl) /\
    (forall fl v ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_eval_projs_order Θ Ξ fl v) /\
    (forall pq ups pm As p gs vs rs, ⟦ihtysᶠ vs of gs at pq ups under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ rs ->
       fast_eval_ihtys_order Θ Ξ pq ups pm As p gs vs) /\
    (forall rs Ms p ms, fast_eval_field_vals Θ Ξ rs Ms p ms -> fast_eval_field_vals_order Θ Ξ rs Ms p) /\
    (** The evaluator does not apply a function along terms. *)
    (forall f Ms p r, fast_eval_app_args Θ Ξ f Ms p r -> True).
Proof.
  intros Θ Ξ; apply fast_eval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : fast_eval_selc _ _ _ ?c _ |- fast_eval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    (** A proof is never an evaluated kind, nor the kind of an evaluated
        argument a proof's. *)
    solve [ econstructor; try eassumption; intros; functional_fast_eval_all;
            first [ solve [ eauto using tele_snoc_app ]
                  | exfalso; eapply evaluated_kind_not_propositional; eassumption
                  | congruence ]
          (** A tuple: its type finds the record, whose kinds direct its
              fields. *)
          | econstructor; [ eassumption | intros t Ht; functional_fast_eval_all; eauto | intros; functional_fast_eval_all; congruence ] ].
Qed.

Lemma fast_eval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (fast_eval_order_sound Θ Ξ)). Qed.

Lemma fast_eval_app_order_sound : forall Θ Ξ m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> fast_eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (fast_eval_order_sound Θ Ξ))). Qed.

Lemma fast_eval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> fast_eval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (fast_eval_order_sound Θ Ξ)))). Qed.

Lemma fast_eval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (fast_eval_order_sound Θ Ξ)))))). Qed.

Lemma fast_eval_shape_type_order_sound : forall Θ Ξ pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_shape_type_order Θ Ξ pq ups p t.
Proof. intros Θ Ξ; pose proof (fast_eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_eval_ihty_order_sound : forall Θ Ξ pq ups pm A p t v a, ⟦ihtyᶠ v of t at pq ups under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a ->
    fast_eval_ihty_order Θ Ξ pq ups pm A p t v.
Proof. intros Θ Ξ; pose proof (fast_eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_eval_ih_order_sound : forall Θ Ξ p pq ups Bks t v r, ⟦ihᶠ v of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r ->
    fast_eval_ih_order Θ Ξ p pq ups Bks t v.
Proof. intros Θ Ξ; pose proof (fast_eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_eval_mref_order_sound : forall Θ Ξ pq ups j r, ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ r -> fast_eval_mref_order Θ Ξ pq ups j.
Proof. intros Θ Ξ; pose proof (fast_eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_eval_proj_order_sound : forall Θ Ξ f m r, fast_eval_proj Θ Ξ f m r -> fast_eval_proj_order Θ Ξ f m.
Proof. intros Θ Ξ; pose proof (fast_eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_eval_projs_order_sound : forall Θ Ξ fl v ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_eval_projs_order Θ Ξ fl v.
Proof. intros Θ Ξ; pose proof (fast_eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve fast_eval_exp_order_sound fast_eval_app_order_sound fast_eval_exps_order_sound fast_eval_modexp_order_sound
  fast_eval_shape_type_order_sound fast_eval_ihty_order_sound fast_eval_ih_order_sound fast_eval_mref_order_sound
  fast_eval_proj_order_sound fast_eval_projs_order_sound : mctt.

(** The member a member stands for is the one [im_ref] names. *)
Lemma fast_eval_mref_im_ref : forall Θ Ξ p ups j pc k pre D Mj,
    ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) ->
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
Lemma fast_eval_ih_order_lookup : forall Θ Ξ p pq ups Bks t v,
    fast_eval_ih_order Θ Ξ p pq ups Bks t v -> exists D, ind_lookup Θ Ξ pq = Some D.
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
End TypedEntriesOk.

#[local] Hint Resolve fdecl_env_ok fbranch_entries_ok fmotive_entries_ok fglobal_proof_env_ok : mctt.
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
    ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase nil ↘ fdomain_erase v /\ fdomain_ok Θ Ξ v.
Proof. intros * [He Hv]; split; assumption. Qed.

(** Alike, of a definition with a module part, for its term *)
Lemma stored_dm_value : forall Θ Ξ pv A M u v, fentry_values_ok Θ Ξ (fe_def_mod pv A M u (Some v)) ->
    ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase nil ↘ fdomain_erase v /\ fdomain_ok Θ Ξ v.
Proof. intros * [[He Hv] _]; split; assumption. Qed.

Section EvalImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** A variable is looked up in the environment, without recursion. *)
  Definition fast_eval_var_impl x (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : fast_eval_exp_order Θ Ξ #x (fenv_erase p)) :
      { d | ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d }.
  Proof.
    exists (fenv_var p x); split; [ rewrite <- fenv_var_erase; apply fast_eval_exp_var | apply fenv_var_ok, Hp ].
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
    | H : fast_eval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_close_order _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_appms_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_body_env_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_elim_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_mref_order _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_shape_type_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ihty_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ihtys_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_projs_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_proj_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_neutral_fields_order _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_field_vals_order _ _ _ _ _ |- _ => progressive_invert H
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
      | H : forall fn, fast_eval_app _ _ ?f ?n fn -> fast_eval_ih_order _ _ _ ?pq _ _ _ fn,
        Hf : fast_eval_app _ _ ?f ?n _, E : ind_lookup _ _ ?pq = None |- _ =>
          exfalso; destruct (fast_eval_ih_order_lookup _ _ _ _ _ _ _ _ (H _ Hf)) as (? & ?); congruence
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
      (** The member a stuck eliminator's member stands for is its own. *)
      | Hm : fast_eval_mref _ _ ?p _ ?j (?pc', ?k', _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
        Hr : im_ref ?p ?j _ = (?pc, ?k) |- _ =>
          assert_fails (constr_eq pc pc');
          rewrite (fast_eval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) in Hr; injection Hr; clear Hr; intros; subst
      end.

  (** What the order says of the values evaluation finds *)
  #[local]
  Ltac impl_obligation_exfalso :=
    repeat match goal with
      (** A record element's type finds a record. *)
      | H : forall t, fast_eval_exp _ _ ?T ?p t -> exists _ _ _, t = d_record _ _ /\ _, Ht : fast_eval_exp _ _ ?T ?p _ |- _ =>
          destruct (H _ Ht) as (? & ? & ? & ? & ?); clear H
      (** The projections of a neutral reach the field projected. *)
      | H : forall rs, fast_eval_neutral_fields _ _ ?m ?p ?fl rs -> _, Hm : fast_eval_neutral_fields _ _ ?m ?p ?fl _ |- _ =>
          specialize (H _ Hm)
      (** A function shape's recursive results, or their types, have the
          one applied. *)
      | H : forall fn rs, fast_eval_app _ _ ?f ?n fn -> fast_eval_ih _ _ _ _ _ _ _ fn rs -> _,
        Hf : fast_eval_app _ _ ?f ?n ?fn, Hr : fast_eval_ih _ _ _ _ _ _ _ ?fn ?rs |- _ =>
          specialize (H _ _ Hf Hr)
      | H : forall fn as', fast_eval_app _ _ ?f ?n fn -> fast_eval_ihty _ _ _ _ _ _ _ _ fn as' -> _,
        Hf : fast_eval_app _ _ ?f ?n ?fn, Hr : fast_eval_ihty _ _ _ _ _ _ _ _ ?fn ?ys |- _ =>
          specialize (H _ _ Hf Hr)
      end.

  #[local]
  Ltac impl_obligation_split :=
    match goal with
    | H : fast_eval_exp_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_close_order _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_appms_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_body_env_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_elim_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_mref_order _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_shape_type_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ihty_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ihtys_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_projs_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_proj_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_neutral_fields_order _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_field_vals_order _ _ _ _ _ |- _ => dependent destruction H
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
    try solve [ eapply fast_eval_sel_global_neut; eauto ];
    (** A term part, by the lookups its branch fixed. *)
    try solve [ eapply fast_eval_sel_global; [ eassumption | | eassumption | eassumption ]; unfold gc_term;
                repeat match goal with
                       | H : gc_resolve _ _ _ = _ |- context [gc_resolve _ _ _] => rewrite H
                       | H : gc_entry _ _ _ = Some (ge_def_mod _ _ _ _) |- context [gc_resolve _ _ _] =>
                           rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H)
                       | H : gc_entry _ _ _ = _ |- context [gc_entry _ _ _] => rewrite H
                       end; reflexivity ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
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
    repeat match goal with H : _ /\ _ |- _ => destruct H end.

  (** The relation or the order, as for Core values *)
  #[local]
  Ltac eval_obligation_rel :=
    repeat impl_obligation_tac1;
    first [ (** The member a shape's end stands for: its order is a
                premise of the shape's, so the recursive call is on a
                subterm *)
            lazymatch goal with |- fast_eval_mref_order _ _ _ _ _ => solve [ impl_obligation_split; impl_obligation_finish ] end
          | solve [ impl_obligation_finish ]
          | solve [ impl_obligation_split; impl_obligation_finish ]
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
End EvalImpl.
