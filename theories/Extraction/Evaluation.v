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
    body, which [feeo_glob_delta] records; an alias recurses into its target.
    Each premise that uses a value is quantified over the values its earlier
    premises evaluate to. *)

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
| fast_eval_exp_order_llit :
  `( fast_eval_exp_order Θ Ξ (𝕃ᵒ o) p )
| fast_eval_exp_order_succl :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exp_order Θ Ξ (succl M) p )
| fast_eval_exp_order_maxl :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exp_order Θ Ξ N p ->
     fast_eval_exp_order Θ Ξ (maxl M N) p )
| fast_eval_exp_order_True :
  `( fast_eval_exp_order Θ Ξ ⊤ p )
| fast_eval_exp_order_true :
  `( fast_eval_exp_order Θ Ξ ⋆ p )
| fast_eval_exp_order_False :
  `( fast_eval_exp_order Θ Ξ ⊥ p )
(** The scrutinee of [efq] must evaluate to a neutral, since no other value
    has a rule. *)
| fast_eval_exp_order_exfalso :
  `( fast_eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> exists b n, m = ⇑ b n) ->
     (forall b m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ⇑ b m -> fast_eval_exp_order Θ Ξ A (p ↦ ⇑ b m)) ->
     fast_eval_exp_order Θ Ξ (efq M return A) p )
| fast_eval_exp_order_pi :
  `( fast_eval_exp_order Θ Ξ A p ->
     fast_eval_exp_order Θ Ξ (Π A B) p )
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
     fast_eval_exps_order Θ Ξ Is (env_args nil nil) ->
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
(** The eliminator: its uniform parameters, its scrutinee, whose value
    names the group it eliminates by, and the elimination. *)
| fast_eval_exp_order_elim :
  `( fast_eval_exps_order Θ Ξ Us p ->
     fast_eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> exists pq, elim_grp_of oq m = Some pq) ->
     (forall ups m pq, ⟦ Us ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ups -> ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> elim_grp_of oq m = Some pq ->
        fast_eval_elim_order Θ Ξ p pq ups Bks j m) ->
     fast_eval_exp_order Θ Ξ (a_elim oq Us j Bks M) p )
| fast_eval_exp_order_fn :
  `( fast_eval_exp_order Θ Ξ (λ A M) p )
| fast_eval_exp_order_app :
  `( fast_eval_exp_order Θ Ξ M p ->
     fast_eval_exp_order Θ Ξ N p ->
     (forall m n, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> fast_eval_app_order Θ Ξ m n) ->
     fast_eval_exp_order Θ Ξ (M $ N) p )
| fast_eval_exp_order_let :
  `( fast_eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> fast_eval_exp_order Θ Ξ B (p ↦ m)) ->
     fast_eval_exp_order Θ Ξ (a_let (b_def oA M) B) p )
| fast_eval_exp_order_let_mod :
  `( fast_eval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_exp_order Θ Ξ B (p ↦ᵐ h)) ->
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
(** A record element: the values of its fields *)
| fast_eval_exp_order_tuple :
  `( fast_eval_exps_order Θ Ξ (List.map snd fs) p ->
     fast_eval_exp_order Θ Ξ (a_tuple T fs) p )
(** A field: the value, then the field of it *)
| fast_eval_exp_order_proj :
  `( fast_eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> fast_eval_proj_order Θ Ξ f m) ->
     fast_eval_exp_order Θ Ξ (a_proj f M) p )

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
     fast_eval_nflds_order Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil ->
     (forall rs, fast_eval_nflds Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil rs -> List.nth_error rs k <> None) ->
     fast_eval_proj_order Θ Ξ f (⇑ (d_record pq ns) m) )

(** The neutral projections at a list of fields, as [fast_eval_nflds] reads
    them *)
with fast_eval_nflds_order (Θ : gdeps) (Ξ : gstack) : list domain -> domain_ne -> list (string * exp) -> list domain -> Prop :=
(** No field left *)
| fast_eval_nflds_order_nil :
  `( fast_eval_nflds_order Θ Ξ ns m nil pre )
(** The next field's type, then the rest after its projection *)
| fast_eval_nflds_order_cons :
  `( fast_eval_exp_order Θ Ξ T (env_args nil (ns ++ pre)) ->
     (forall a, ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ env_args nil (ns ++ pre) ↘ a ->
        fast_eval_nflds_order Θ Ξ ns m fl (pre ++ ⇑ a (d_proj g m) :: nil)) ->
     fast_eval_nflds_order Θ Ξ ns m ((g, T) :: fl) pre )

(** The eliminator of the group at [pq] at its member [j], on a value, as
    [fast_eval_elim] reads it. *)
with fast_eval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> Prop :=
(** On a saturated constructor: the recursive results the branch reads,
    then the branch.  The group's table of leaf paths is coherent, the
    gate [fast_eval_elim_con] has: a premise of the domain, not a check the
    evaluator runs *)
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
        fast_eval_exp_order Θ Ξ B (env_args p (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs) ++ skipn (im_np Dq Mk) vs ++ ihs))) ->
     fast_eval_elim_order Θ Ξ p pq ups Bks j (d_con pc k c vs) )
(** On a neutral: the motive's instance *)
| fast_eval_elim_order_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_ref pq j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_nm b = S (im_nn Mk) ->
     fast_eval_exp_order Θ Ξ (eb_motive b) (env_args p (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil)) ->
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
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB (ca_arg T :: gs) (v :: vs) )
(** A recursive argument the branch reads one result of: its results,
    then the rest *)
| fast_eval_ihs_order_rec_case :
  `( ind_lookup Θ Ξ pq = Some D ->
     ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = false ->
     fast_eval_ih_order Θ Ξ p pq ups Bks t v ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB gs vs ->
     fast_eval_ihs_order Θ Ξ p pq ups Bks oB (ca_rec t :: gs) (v :: vs) )
(** One it reads none of: the rest only *)
| fast_eval_ihs_order_skip :
  `( ind_lookup Θ Ξ pq = Some D ->
     ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = true ->
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
     fast_eval_exps_order Θ Ξ Is (env_args nil ups) ->
     fast_eval_mref_order Θ Ξ pq ups j )

(** The type of an argument of a shape *)
with fast_eval_shty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
(** At the end: the parameters, and the member stood for *)
| fast_eval_shty_order_self :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     fast_eval_exps_order Θ Ξ Ps p ->
     fast_eval_mref_order Θ Ξ pq ups j ->
     fast_eval_shty_order Θ Ξ pq ups p (pt_self j Ps) )
(** At the end, at a record view: the view's instance *)
| fast_eval_shty_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     fast_eval_exps_order Θ Ξ Is (env_args nil ups) ->
     fast_eval_shty_order Θ Ξ pq ups p (pt_self j Ps) )
(** At a domain *)
| fast_eval_shty_order_pi :
  `( fast_eval_exp_order Θ Ξ B p ->
     fast_eval_shty_order Θ Ξ pq ups p (pt_pi B t) )

(** The types of the recursive results of an argument of a shape *)
with fast_eval_ihty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> ptyp -> domain -> Prop :=
(** At the end, at a member with a block: the parameters, then the
    member's motive *)
| fast_eval_ihty_order_self :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     fast_eval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ bs -> fast_eval_exp_order Θ Ξ (List.nth j As a_True) (env_args pm (bs ++ v :: nil))) ->
     fast_eval_ihty_order Θ Ξ pq ups pm As p (pt_self j Ps) v )
(** At the end, at a record view: the projections, then their recursive
    results' types *)
| fast_eval_ihty_order_rview :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     fast_eval_projs_order Θ Ξ fl v ->
     (forall ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_eval_ihtys_order Θ Ξ pq ups pm As (env_args nil ups) gs ws) ->
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
(** A non-recursive field: the rest, under it *)
| fast_eval_ihtys_order_arg :
  `( fast_eval_ihtys_order Θ Ξ pq ups pm As (p ↦ v) gs vs ->
     fast_eval_ihtys_order Θ Ξ pq ups pm As p (ca_arg T :: gs) (v :: vs) )
(** A recursive field: its shape's, then the rest *)
| fast_eval_ihtys_order_rec :
  `( fast_eval_ihty_order Θ Ξ pq ups pm As p t v ->
     fast_eval_ihtys_order Θ Ξ pq ups pm As p gs vs ->
     fast_eval_ihtys_order Θ Ξ pq ups pm As p (ca_rec t :: gs) (v :: vs) )

with fast_eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| fast_eval_app_order_fn :
  `( fast_eval_exp_order Θ Ξ M (p ↦ n) ->
     fast_eval_app_order Θ Ξ λᵈ p M n )
| fast_eval_app_order_neut :
  `( fast_eval_exp_order Θ Ξ B (p ↦ n) ->
     fast_eval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
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
     fast_eval_exps_order Θ Ξ Is (env_args nil (vs ++ n :: nil)) ->
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
  `( fast_eval_shty_order Θ Ξ pq ups (p ↦ n) t ->
     fast_eval_app_order Θ Ξ (d_shfam pq ups p t) n )
(** The [i]-th recursive result's family: those of the rest, which has an
    [i]-th *)
| fast_eval_app_order_ihfam :
  `( fast_eval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> fast_eval_ihty_order Θ Ξ pq ups pm As (p ↦ n) t fn) ->
     (forall fn as', $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> ⟦ihtyᶠ fn of t at pq ups under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ n ↘ as' ->
        List.nth_error as' i <> None) ->
     fast_eval_app_order Θ Ξ (d_ihfam pm As pq ups p t i f) n )
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
  `( tele_snoc Δ = Some (Δ0, ce_ass A) ->
     fast_eval_close_order Θ Ξ Δ0 D (p ↦ n) ->
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
  `( gc_term Θ Ξ (qname_app pq (x :: nil)) = Some M ->
     fast_eval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f -> fast_eval_apps_order Θ Ξ f args) ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
| fast_eval_sel_order_global_neut :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     fast_eval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ a -> fast_eval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
| fast_eval_sel_order_global_ind :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app pq (x :: nil)) = Some (pg, k, D) ->
     fast_eval_apps_order Θ Ξ (d_ind pg k nil) args ->
     fast_eval_sel_order Θ Ξ (dm_global pq args) x )
| fast_eval_sel_order_unsat :
  `( fast_eval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
(** A term part of a saturated body ([entry_tm]) *)
| fast_eval_sel_order_body :
  `( kinds_body_xp Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     fast_eval_benv_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> fast_eval_exp_order Θ Ξ M p') ->
     fast_eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
| fast_eval_sel_order_member :
  `( fast_eval_sel_order Θ Ξ (dm_member h ch) x )
(** A record type of a global module, not a definition: its type former,
    applied to the arguments *)
| fast_eval_sel_order_global_record :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
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
(** A module part of a saturated body ([entry_unit]) *)
| fast_eval_selm_order_body :
  `( kinds_body_xp Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     fast_eval_benv_order Θ Ξ p Φ' ->
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

with fast_eval_benv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| fast_eval_benv_order_nil :
  `( fast_eval_benv_order Θ Ξ p gm_nil )
| fast_eval_benv_order_def :
  `( fast_eval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_exp_order Θ Ξ M p1) ->
     fast_eval_benv_order Θ Ξ p (gm_ext Φ y (ge_def b pv A (Some M))) )
| fast_eval_benv_order_mod :
  `( fast_eval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_close_order Θ Ξ Δy Dy p1) ->
     fast_eval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) )
(** A definition with a module part: its term and its unit's closure *)
| fast_eval_benv_order_dm :
  `( fast_eval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_exp_order Θ Ξ M p1) ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> fast_eval_close_order Θ Ξ Δy Dy p1) ->
     fast_eval_benv_order Θ Ξ p (gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy))) ).

#[local]
Hint Constructors fast_eval_exp_order fast_eval_elim_order fast_eval_ihs_order fast_eval_ih_order fast_eval_mref_order fast_eval_shty_order fast_eval_ihty_order fast_eval_app_order fast_eval_exps_order fast_eval_apps_order
  fast_eval_modexp_order fast_eval_close_order fast_eval_appm_order fast_eval_appms_order fast_eval_sel_order fast_eval_selm_order fast_eval_selc_order fast_eval_selmc_order
  fast_eval_benv_order fast_eval_proj_order fast_eval_nflds_order fast_eval_projs_order fast_eval_ihtys_order : mctt.

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
        pose proof (proj1 (proj2 (proj2 (@functional_fast_eval T X))) _ _ _ H1 _ H2); subst; clear H2
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
    | H1 : kinds_body_xp ?T ?X ?p ?Φ ?r1, H2 : kinds_body_xp ?T ?X ?p ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_kinds_body_xp _ _ _ _ H1 H2); subst; clear H2
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
    | H1 : fast_eval_benv ?T ?X ?m ?n ?r1, H2 : fast_eval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_benv _ _ _ _ H1 H2); subst; clear H2
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
    | H1 : fast_eval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : fast_eval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_shty _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_ihty ?T ?X ?p ?u ?ρm ?A ?ρ ?t ?v ?r1, H2 : fast_eval_ihty ?T ?X ?p ?u ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_ihty _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_ihtys ?T ?X ?p ?u ?ρm ?A ?ρ ?gs ?vs ?r1, H2 : fast_eval_ihtys ?T ?X ?p ?u ?ρm ?A ?ρ ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_ihtys _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_projs ?T ?X ?fl ?v ?r1, H2 : fast_eval_projs ?T ?X ?fl ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_projs _ _ _ _ H1 H2); subst; clear H2
    | H1 : kinds_items_gen ?T ?X ?p ?E ?its ?g1, H2 : kinds_items_gen ?T ?X ?p ?E ?its ?g2 |- _ =>
        assert_fails (constr_eq g1 g2);
        pose proof (functional_kinds_items_gen _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    | H1 : fast_eval_proj ?T ?X ?f ?m ?r1, H2 : fast_eval_proj ?T ?X ?f ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_proj _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_nflds ?T ?X ?ns ?m ?fl ?pre ?r1, H2 : fast_eval_nflds ?T ?X ?ns ?m ?fl ?pre ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_fast_eval_nflds _ _ _ _ _ _ H1 H2); subst; clear H2
    end.

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
    (forall p Φ p', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> fast_eval_benv_order Θ Ξ p Φ) /\
    (forall p pq ups Bks j m r, ⟦elimᶠ m at j of pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> fast_eval_elim_order Θ Ξ p pq ups Bks j m) /\
    (forall p pq ups Bks B gs vs ihs, ⟦ihsᶠ vs of gs under pq ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs ->
       fast_eval_ihs_order Θ Ξ p pq ups Bks B gs vs) /\
    (forall p pq ups Bks t v r, ⟦ihᶠ v of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> fast_eval_ih_order Θ Ξ p pq ups Bks t v) /\
    (forall pq ups j r, ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ r -> fast_eval_mref_order Θ Ξ pq ups j) /\
    (forall pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_shty_order Θ Ξ pq ups p t) /\
    (forall pq ups pm As p t v a, ⟦ihtyᶠ v of t at pq ups under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_ihty_order Θ Ξ pq ups pm As p t v) /\
    (forall f m r, fast_eval_proj Θ Ξ f m r -> fast_eval_proj_order Θ Ξ f m) /\
    (forall ns m fl pre rs, fast_eval_nflds Θ Ξ ns m fl pre rs -> fast_eval_nflds_order Θ Ξ ns m fl pre) /\
    (forall fl v ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_eval_projs_order Θ Ξ fl v) /\
    (forall pq ups pm As p gs vs rs, ⟦ihtysᶠ vs of gs at pq ups under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ rs ->
       fast_eval_ihtys_order Θ Ξ pq ups pm As p gs vs).
Proof.
  intros Θ Ξ; apply fast_eval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : fast_eval_selc _ _ _ ?c _ |- fast_eval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    solve [ eapply fast_eval_sel_order_global_neut; eauto; intros; functional_fast_eval_all; eauto
          (** A shape's end at a member with a block: the member its type
              stands for has one, not a record view. *)
          | match goal with H : fast_eval_mref _ _ ?pq _ ?j _ |- fast_eval_shty_order _ _ ?pq _ _ (pt_self ?j _) =>
              inversion H; subst; eapply fast_eval_shty_order_self; try eassumption;
              unfold im_is_rview; match goal with Hh : im_head _ = _ |- _ => rewrite Hh end; reflexivity end
          | econstructor; try eassumption; intros; functional_fast_eval_all; eauto using kinds_items_gen_order_sound, tele_snoc_app
          (** The projections of a neutral reach the field projected. *)
          | econstructor; try eassumption; intros; functional_fast_eval_all; congruence
          (** The eliminator: the group the scrutinee's value names, once. *)
          | econstructor; try eassumption; intros; functional_fast_eval_all;
            first [ eexists; eassumption
                  | match goal with H1 : elim_grp_of ?o ?m = Some _, H2 : elim_grp_of ?o ?m = Some _ |- _ =>
                      rewrite H1 in H2; injection H2 as <-; assumption end ] ].
Qed.

Lemma fast_eval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (fast_eval_order_sound Θ Ξ)). Qed.

Lemma fast_eval_app_order_sound : forall Θ Ξ m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> fast_eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (fast_eval_order_sound Θ Ξ))). Qed.

Lemma fast_eval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> fast_eval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (fast_eval_order_sound Θ Ξ)))). Qed.

Lemma fast_eval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> fast_eval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (fast_eval_order_sound Θ Ξ)))))). Qed.

Lemma fast_eval_shty_order_sound : forall Θ Ξ pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> fast_eval_shty_order Θ Ξ pq ups p t.
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
  fast_eval_shty_order_sound fast_eval_ihty_order_sound fast_eval_ih_order_sound fast_eval_mref_order_sound
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

(** The environment of a branch: the non-uniform parameters, the
    arguments and the recursive results ([fast_eval_elim_con]), the member
    being [M] of the group [D].  Without parameters, the arguments are all
    the values, which are not copied. *)
Definition elim_env (p : env) (D : ind_decl) (M : imember) (vs ihs : list domain) : env :=
  match im_params D M with
  | nil => env_args (env_args p vs) ihs
  | _ => env_args p (skipn (ind_nu D) (firstn (im_np D M) vs) ++ skipn (im_np D M) vs ++ ihs)
  end.

Lemma elim_env_eq : forall p D M vs ihs,
    elim_env p D M vs ihs = env_args p (skipn (ind_nu D) (firstn (im_np D M) vs) ++ skipn (im_np D M) vs ++ ihs).
Proof.
  intros; unfold elim_env.
  destruct (im_params D M) eqn:E; [| reflexivity ].
  unfold im_params in E; apply app_eq_nil in E as [E1 E2].
  assert (Hu : ind_nu D = 0) by (unfold ind_nu; rewrite E2; reflexivity).
  assert (Hn : im_np D M = 0) by (unfold im_np, im_nn; rewrite E1, Hu; reflexivity).
  rewrite Hn, Hu; cbn [firstn skipn]; rewrite app_nil_l, env_args_app; reflexivity.
Qed.

(** The recursive results of an argument are those of a group with a
    declaration. *)
Lemma fast_eval_ih_order_lookup : forall Θ Ξ p pq ups Bks t v,
    fast_eval_ih_order Θ Ξ p pq ups Bks t v -> exists D, ind_lookup Θ Ξ pq = Some D.
Proof. intros * H; inversion H; eauto. Qed.

(** [elim_env]'s twin, on fast values *)
Definition felim_env (p : fenv) (D : ind_decl) (M : imember) (vs ihs : list fdomain) : fenv :=
  match im_params D M with
  | nil => fenv_args (fenv_args p vs) ihs
  | _ => fenv_args p (skipn (ind_nu D) (firstn (im_np D M) vs) ++ skipn (im_np D M) vs ++ ihs)
  end.

Lemma felim_env_erase : forall p D M vs ihs,
    fenv_erase (felim_env p D M vs ihs) = elim_env (fenv_erase p) D M (fdomains_erase vs) (fdomains_erase ihs).
Proof.
  intros; unfold felim_env, elim_env; destruct (im_params D M); rewrite ?fenv_args_erase; [ reflexivity |].
  rewrite !List.map_app, skipn_map, firstn_map, skipn_map; reflexivity.
Qed.

Lemma felim_env_ok : forall Θ Ξ p D M vs ihs, fenv_ok Θ Ξ p -> Forall (fdomain_ok Θ Ξ) vs -> Forall (fdomain_ok Θ Ξ) ihs ->
    fenv_ok Θ Ξ (felim_env p D M vs ihs).
Proof.
  intros; unfold felim_env; destruct (im_params D M); apply fenv_args_ok; auto using fenv_args_ok.
  apply Forall_app_intro; [ apply Forall_skipn_intro, Forall_firstn_intro; assumption |].
  apply Forall_app_intro; [ apply Forall_skipn_intro |]; assumption.
Qed.

#[local] Hint Resolve felim_env_ok : mctt.
(** The erasure of an element found, for the obligations' [eauto] *)
#[local] Hint Resolve nth_error_map_some field_lookup_erase_some : core.
#[local] Hint Extern 1 => match goal with |- context [ List.length (List.map _ _) ] => rewrite List.length_map end : core.

(** A prefix up to a name ends with the entry of that name. *)
Lemma gm_prefix_upto_ext : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 -> exists Φ0 E, Φ1 = gm_ext Φ0 y E.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * Hp; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as <-; eauto | eauto ].
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

#[local] Hint Resolve kinds_body_xp_order_sound : core.

(** The operations on fast values, read through their erasure equations *)
#[local] Opaque fenv_var fenv_mod fextend_env fextend_env_mod fextend_env_dm fenv_args fdlvl_suc fdlvl_max
  fdlvl_lit fdm_clo fkinds_placeholders fkinds_body_entry fkinds_items_gen_env felim_grp_of carry.

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
  Definition decl_lookup (ck : lk_cache Θ Ξ) (p : qname) :
      { D | ind_lookup Θ Ξ p = Some D } + { ind_lookup Θ Ξ p = None } :=
    match cache_lookup F ck p with
    | exist _ (Some D) E => inleft (exist _ D E)
    | exist _ None E => inright E
    end.

  (** The declaration of the group at [p] that a value carries, or else
      the one looked up through the cache [ck] *)
  Definition carried_lookup (ck : lk_cache Θ Ξ) (p : qname) (oD : option ind_decl) (Hok : decl_carried_ok Θ Ξ p oD) :
      { D | ind_lookup Θ Ξ p = Some D } + { ind_lookup Θ Ξ p = None } :=
    match oD as o return decl_carried_ok Θ Ξ p o -> { D | ind_lookup Θ Ξ p = Some D } + { ind_lookup Θ Ξ p = None } with
    | Some D => fun Hok => inleft (exist _ D (Hok D eq_refl))
    | None => fun _ => decl_lookup ck p
    end Hok.



  #[local]
  Ltac impl_obl_tac1 :=
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
    | H : fast_eval_benv_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_elim_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_mref_order _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_shty_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ihty_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_ihtys_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_projs_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_proj_order _ _ _ _ |- _ => progressive_invert H
    | H : fast_eval_nflds_order _ _ _ _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
      (** A term part an order records is a definition's body or a
          definition with a module part's term. *)
      | H : gc_term _ _ _ = Some _ |- _ =>
          destruct (gc_term_inv _ _ _ _ H) as [(? & ? & ?) | (? & ? & ? & ?)]; clear H
      | H1 : entry_tm ?E = _, H2 : entry_tm ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : entry_unit ?E = _, H2 : entry_unit ?E = _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : gc_entry _ _ ?p = Some _, H2 : gc_entry _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : gc_entry _ _ ?p = Some _, H2 : gc_entry _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H : gc_entry _ _ _ = Some (ge_def _ _ _ _) |- _ => apply gc_entry_def in H
      | H : gc_entry _ _ _ = Some (ge_ind _ _ _ _ _) |- _ =>
          let H1 := fresh "Hr" in let H2 := fresh "Hl" in destruct (gc_entry_ind _ _ _ _ _ _ _ _ H) as [H1 H2]; clear H
      | H : gc_entry ?T ?X ?p = _, H' : gc_resolve ?T ?X ?p = Some (ge_def _ _ _ _) |- _ =>
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
      | H1 : kinds_body_xp _ _ ?p ?Φ ?r1, H2 : kinds_body_xp _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); pose proof (functional_kinds_body_xp _ _ _ _ H1 H2); subst; clear H2
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
      | H : gm_prefix_upto _ _ = Some (gm_open _ _ _) |- _ =>
          destruct (gm_prefix_upto_ext _ _ _ H) as (? & ? & ?); discriminate
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
      | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H : Nat.compare _ _ = Eq |- _ => apply Nat.compare_eq in H
      | H : Nat.compare _ _ = Lt |- _ => apply Nat.compare_lt_iff in H
      | H : Nat.compare _ _ = Gt |- _ => apply Nat.compare_gt_iff in H
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
      | H1 : elim_grp_of ?o ?m = Some _, H2 : elim_grp_of ?o ?m = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : elim_grp_of ?o ?m = Some _, H2 : elim_grp_of ?o ?m = None |- _ =>
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
      end.

  (** The [efq] case: the order says that the scrutinee evaluates to a
      neutral, which rules out every other value. *)
  #[local]
  Ltac impl_obl_exfalso :=
    repeat match goal with
      | H : forall m, fast_eval_exp _ _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : fast_eval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      (** The eliminator's scrutinee names a group. *)
      | H : forall m, fast_eval_exp _ _ ?M ?p m -> exists _, elim_grp_of _ m = Some _, Hm : fast_eval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ?); clear H
      (** The projections of a neutral reach the field projected. *)
      | H : forall rs, fast_eval_nflds _ _ ?ns ?m ?fl ?pre rs -> _, Hm : fast_eval_nflds _ _ ?ns ?m ?fl ?pre _ |- _ =>
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
  Ltac impl_obl_split :=
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
    | H : fast_eval_benv_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_elim_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_mref_order _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_shty_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ihty_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_ihtys_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_projs_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_proj_order _ _ _ _ |- _ => dependent destruction H
    | H : fast_eval_nflds_order _ _ _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac impl_obl_finish :=
    impl_obl_exfalso;
    impl_obl_glob;
    (** once more, at the lookups fixed *)
    impl_obl_exfalso;
    impl_obl_glob;
    cbn [gu_params] in *;
    try solve [ intuition discriminate ];
    (** The two rules of the eliminator at a successor exclude each other. *)
    try solve [ congruence ];
    try solve [ exfalso; lia ];
    try solve [ eapply fast_eval_sel_global_neut; eauto ];
    (** A term part, by the lookups its branch fixed. *)
    try solve [ eapply fast_eval_sel_global; [| eassumption | eassumption ]; unfold gc_term;
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
  Ltac ev_norm :=
    intros; cbv beta iota in *; cbn [option_map dec_entry fst snd] in *;
    rewrite ?felim_env_erase in *; ferase_norm;
    rewrite ?elim_env_eq in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.

  (** The relation or the order, as for Core values *)
  #[local]
  Ltac ev_rel :=
    repeat impl_obl_tac1;
    first [ (** The member a shape's end stands for: its order is a
                premise of the shape's, so the recursive call is on a
                subterm *)
            lazymatch goal with |- fast_eval_mref_order _ _ _ _ _ => solve [ impl_obl_split; impl_obl_finish ] end
          | solve [ impl_obl_finish ]
          | solve [ impl_obl_split; impl_obl_finish ]
          | impl_obl_finish ].

  #[local]
  Ltac ev_obl :=
    ev_norm;
    lazymatch goal with
    | |- _ /\ _ => split; [ ev_rel | ok_solve ]
    | |- fdomain_ok _ _ _ => ok_solve
    | |- fdomain_ne_ok _ _ _ => ok_solve
    | |- fdomain_nf_ok _ _ _ => ok_solve
    | |- fdentry_ok _ _ _ => ok_solve
    | |- decl_carried_ok _ _ _ _ => ok_solve
    | |- fdmod_ok _ _ _ => ok_solve
    | |- fenv_ok _ _ _ => ok_solve
    | |- Forall _ _ => ok_solve
    | |- _ => ev_rel
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_eval_exp_impl m (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : fast_eval_exp_order Θ Ξ m (fenv_erase p)) :
      { d | ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d } by struct H :=
  | Typeω@i, p, Hp, H => exist _ (fd_univ i) _
  | Type⟨M⟩, p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      exist _ (fd_suniv m) _
  | #x    , p, Hp, H => fast_eval_var_impl x p Hp H
  | Level@n, p, Hp, H => exist _ (fd_level n) _
  | 𝕃ᵒ o  , p, Hp, H => exist _ (fdlvl_lit o) _
  | succl M, p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      exist _ (fdlvl_suc m) _
  | maxl M N, p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      let (n , Hn) := fast_eval_exp_impl N p Hp _ in
      exist _ (fdlvl_max m n) _
  | ⊤     , p, Hp, H => exist _ fd_True _
  | ⋆     , p, Hp, H => exist _ fd_true _
  | ⊥     , p, Hp, H => exist _ fd_False _
  | efq M return A, p, Hp, H with fast_eval_exp_impl M p Hp _ := {
    | exist _ (fd_neut b m) Hm =>
        let (a, Ha) := fast_eval_exp_impl A (fextend_env p (fd_neut b m)) _ _ in
        exist _ (fd_neut a (fd_exfalso p A m)) _
    | exist _ _ Hm => False_rect _ _ }
  | Π A B , p, Hp, H =>
      let (r , Hr) := fast_eval_exp_impl A p Hp _ in
      exist _ (fd_pi r p B) _
  | λ A M , p, Hp, H => exist _ (fd_fn p M) _
  | a_ind pq k, p, Hp, H => exist _ (fd_ind pq None k nil) _
  | a_con pq k c, p, Hp, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_starts D Mk) := {
        | exist _ true Es => exist _ (fd_con pq (carry D) k c nil) _
        | exist _ false Es with inspect (im_head Mk) := {
          | exist _ (mh_view qc k' Is vm) Eh =>
              let (cups, Hc) := fast_eval_exps_impl Is (fenv_args nil nil) _ _ in
              exist _ (fd_con qc None k' c cups) _
          | exist _ (mh_record qr Is nil) Eh => exist _ (fd_tuple nil) _
          | exist _ (mh_record qr Is (_ :: _)) Eh => exist _ (fd_con pq (carry D) k c nil) _
          | exist _ (mh_decl _) Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  (** A literal is generated before it is ever evaluated. *)
  | a_ntok, p, Hp, H => False_rect _ _
  | a_nlit _, p, Hp, H => False_rect _ _
  | a_elim oq Us j Bks M, p, Hp, H with fast_eval_exps_impl Us p Hp _ := {
    | exist _ ups Hups with fast_eval_exp_impl M p Hp _ := {
      | exist _ m Hm with inspect (felim_grp_of oq m) := {
        | exist _ (Some pq) Eg =>
            let (r, Hr) := fast_eval_elim_impl p pq ups Bks j m (fc_seed F) Hp _ _ _ in
            exist _ r _
        | exist _ None Eg => False_rect _ _ } } }
  | M $ N   , p, Hp, H =>
      let (m , Hm) := fast_eval_exp_impl M p Hp _ in
      let (n , Hn) := fast_eval_exp_impl N p Hp _ in
      let (a, Ha) := fast_eval_app_impl m n _ _ _ in
      exist _ a _
  | a_let (b_def oA M) B, p, Hp, H =>
      let (m, Hm) := fast_eval_exp_impl M p Hp _ in
      let (r, Hr) := fast_eval_exp_impl B (fextend_env p m) _ _ in
      exist _ r _
  | a_let (b_mod (gu_mk Δ D)) B, p, Hp, H =>
      let (h, Hh) := fast_eval_close_impl Δ D p Hp _ in
      let (r, Hr) := fast_eval_exp_impl B (fextend_env_mod p h) _ _ in
      exist _ r _
  | a_mem M x, p, Hp, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := fast_eval_modexp_impl R p Hp _ in
        let (f, Hf) := fast_eval_selc_impl h (pre ++ x :: nil) _ _ in
        let (ns, Hns) := fast_eval_exps_impl args p Hp _ in
        let (r, Hr) := fast_eval_apps_impl f ns _ _ _ in
        exist _ r _ }
  | a_record pq, p, Hp, H => exist _ (fd_record pq nil) _
  | a_tuple T fs, p, Hp, H =>
      let (vs, Hvs) := fast_eval_exps_impl (List.map snd fs) p Hp _ in
      exist _ (fd_tuple (List.combine (List.map fst fs) vs)) _
  | a_proj f M, p, Hp, H =>
      let (m, Hm) := fast_eval_exp_impl M p Hp _ in
      let (r, Hr) := fast_eval_proj_impl f m _ _ in
      exist _ r _

  with fast_eval_proj_impl f (m : fdomain) (Hm : fdomain_ok Θ Ξ m) (H : fast_eval_proj_order Θ Ξ f (fdomain_erase m)) :
      { r | fast_eval_proj Θ Ξ f (fdomain_erase m) (fdomain_erase r) /\ fdomain_ok Θ Ξ r } by struct H :=
  | f, fd_tuple vs, Hm, H with inspect (field_lookup vs f) := {
    | exist _ (Some r) E => exist _ r _
    | exist _ None E => False_rect _ _ }
  | f, fd_neut (fd_record pq ns) m, Hm, H with record_lookup_f F pq := {
    | exist _ (Some R) El with inspect (field_index (record_fields R) f) := {
      | exist _ (Some k) Ek with fast_eval_nflds_impl ns m (List.firstn (S k) (record_fields R)) nil _ _ _ _ := {
        | exist _ rs Hrs with inspect (List.nth_error rs k) := {
          | exist _ (Some r) Er => exist _ r _
          | exist _ None Er => False_rect _ _ } }
      | exist _ None Ek => False_rect _ _ }
    | exist _ None El => False_rect _ _ }
  | f, _, Hm, H => False_rect _ _

  with fast_eval_nflds_impl (ns : list fdomain) (m : fdomain_ne) fl (pre : list fdomain)
      (Hns : Forall (fdomain_ok Θ Ξ) ns) (Hm : fdomain_ne_ok Θ Ξ m) (Hpre : Forall (fdomain_ok Θ Ξ) pre)
      (H : fast_eval_nflds_order Θ Ξ (fdomains_erase ns) (fdomain_ne_erase m) fl (fdomains_erase pre)) :
      { rs | fast_eval_nflds Θ Ξ (fdomains_erase ns) (fdomain_ne_erase m) fl (fdomains_erase pre) (fdomains_erase rs) /\
             Forall (fdomain_ok Θ Ξ) rs } by struct H :=
  | ns, m, nil, pre, Hns, Hm, Hpre, H => exist _ nil _
  | ns, m, (g, T) :: fl, pre, Hns, Hm, Hpre, H =>
      let (a, Ha) := fast_eval_exp_impl T (fenv_args nil (ns ++ pre)) _ _ in
      let (rs, Hrs) := fast_eval_nflds_impl ns m fl (pre ++ fd_neut a (fd_proj g m) :: nil) Hns Hm _ _ in
      exist _ (fd_neut a (fd_proj g m) :: rs) _

  (** The group of the eliminator is looked up through the cache [ck], and
      passed on as the cache of the container's lookup and of the
      recursive results: a lookup of the same name is a comparison. *)
  with fast_eval_elim_impl (p : fenv) pq (ups : list fdomain) Bks j (m : fdomain) (ck : lk_cache Θ Ξ)
      (Hp : fenv_ok Θ Ξ p) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hm : fdomain_ok Θ Ξ m)
      (H : fast_eval_elim_order Θ Ξ (fenv_erase p) pq (fdomains_erase ups) Bks j (fdomain_erase m)) :
      { r | ⟦elimᶠ fdomain_erase m at j of pq (fdomains_erase ups) Bks ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase r /\
            fdomain_ok Θ Ξ r } by struct H :=
  | p, pq, ups, Bks, j, fd_con pc oDq k c vs, ck, Hp, Hups, Hm, H with carried_lookup ck pc oDq (fdomain_ok_con_carried _ _ _ _ _ _ _ Hm) := {
    | inleft (exist _ Dq Edq) with decl_lookup (Some (exist _ (pc, Dq) Edq)) pq := {
      | inleft (exist _ D Ed) with inspect (ind_member D j) := {
        | exist _ (Some Mj) Em with inspect (ind_member Dq k) := {
          | exist _ (Some Mk) Emk with inspect (ind_con Mj c) := {
            | exist _ (Some gs) Ec with inspect (List.nth_error Bks j) := {
              | exist _ (Some b) Eb with inspect (brs_lookup (eb_brs b) c) := {
                | exist _ (Some (n, B)) Ebr =>
                    let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks (Some B) gs (skipn (im_np Dq Mk) vs) D Ed Hp Hups _ _ in
                    let (r, Hr) := fast_eval_exp_impl B (felim_env p Dq Mk vs ihs) _ _ in
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
      | inleft (exist _ D Ed) with inspect (List.nth_error Bks j) := {
        | exist _ (Some b) Eb =>
            let (a, Ha) := fast_eval_exp_impl (eb_motive b) (fenv_args p (skipn (ind_nu Dq) as' ++ fd_neut (fd_ind pc oDq k as') m :: nil)) _ _ in
            exist _ (fd_neut a (fd_elim p Bks pq D ups j as' m)) _
        | exist _ None Eb => False_rect _ _ }
      | inright Ed => False_rect _ _ }
    | inright Edq => False_rect _ _ }
  | p, pq, ups, Bks, j, _, ck, Hp, Hups, Hm, H => False_rect _ _

  (** The recursive results take the declaration of the group, which the
      eliminator has looked up already: no lookup per step *)
  with fast_eval_ihs_impl (p : fenv) pq (ups : list fdomain) Bks oB gs (vs : list fdomain) (D : ind_decl)
      (Ed : ind_lookup Θ Ξ pq = Some D)
      (Hp : fenv_ok Θ Ξ p) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : fast_eval_ihs_order Θ Ξ (fenv_erase p) pq (fdomains_erase ups) Bks oB gs (fdomains_erase vs)) :
      { ihs | ⟦ihsᶠ fdomains_erase vs of gs under pq (fdomains_erase ups) Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase ihs /\
              Forall (fdomain_ok Θ Ξ) ihs } by struct H :=
  | p, pq, ups, Bks, oB, nil, nil, D, Ed, Hp, Hups, Hvs, H => exist _ nil _
  | p, pq, ups, Bks, oB, ca_arg T :: gs, v :: vs, D, Ed, Hp, Hups, Hvs, H =>
      let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks oB gs vs D Ed Hp Hups _ _ in
      exist _ ihs _
  | p, pq, ups, Bks, oB, ca_rec t :: gs, v :: vs, D, Ed, Hp, Hups, Hvs, H
        with inspect (ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t))) := {
      (** The branch reads none of the argument's recursive results: they
          are not computed. *)
      | exist _ true E =>
          let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks oB gs vs D Ed Hp Hups _ _ in
          exist _ (List.repeat (fd_univ 0) (List.length (shape_leaves (rv_leaves D) 0 t)) ++ ihs) _
      | exist _ false E =>
          let (ih, Hih) := fast_eval_ih_impl p pq ups Bks t v D Ed Hp Hups _ _ in
          let (ihs, Hihs) := fast_eval_ihs_impl p pq ups Bks oB gs vs D Ed Hp Hups _ _ in
          exist _ (ih ++ ihs) _ }
  | p, pq, ups, Bks, oB, _, _, D, Ed, Hp, Hups, Hvs, H => False_rect _ _

  with fast_eval_ih_impl (p : fenv) pq (ups : list fdomain) Bks t (v : fdomain) (D : ind_decl)
      (Ed : ind_lookup Θ Ξ pq = Some D)
      (Hp : fenv_ok Θ Ξ p) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hv : fdomain_ok Θ Ξ v)
      (H : fast_eval_ih_order Θ Ξ (fenv_erase p) pq (fdomains_erase ups) Bks t (fdomain_erase v)) :
      { rs | ⟦ihᶠ fdomain_erase v of t under pq (fdomains_erase ups) Bks ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase rs /\
             Forall (fdomain_ok Θ Ξ) rs } by struct H :=
  | p, pq, ups, Bks, pt_self j Ps, v, D, Ed, Hp, Hups, Hv, H with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
          | exist _ ((c, gs) :: nil) Ec =>
              let (ws, Hws) := fast_eval_projs_impl fl v Hv _ in
              let (rs, Hrs) := fast_eval_ihs_impl p pq ups Bks None gs ws D Ed Hp Hups _ _ in
              exist _ rs _
          | exist _ _ Ec => False_rect _ _ }
        | exist _ _ Eh =>
            let (r, Hr) := fast_eval_elim_impl p pq ups Bks j v (Some (exist _ (pq, D) Ed)) Hp Hups Hv _ in
            exist _ (r :: nil) _ }
      | exist _ None Em => False_rect _ _ }
  | p, pq, ups, Bks, pt_pi B t, v, D, Ed, Hp, Hups, Hv, H =>
        exist _ (List.map (fun i => fd_ihfn p Bks pq ups t i v) (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t)))) _

  with fast_eval_projs_impl fl (v : fdomain) (Hv : fdomain_ok Θ Ξ v) (H : fast_eval_projs_order Θ Ξ fl (fdomain_erase v)) :
      { ws | ⟦projsᶠ fl of fdomain_erase v ⟧ᶠ Θ ⍮ Ξ ↘ fdomains_erase ws /\ Forall (fdomain_ok Θ Ξ) ws } by struct H :=
  | nil, v, Hv, H => exist _ nil _
  | f :: fl, v, Hv, H =>
      let (w, Hw) := fast_eval_proj_impl f v Hv _ in
      let (ws, Hws) := fast_eval_projs_impl fl v Hv _ in
      exist _ (w :: ws) _

  (** The member a member stands for, with the declaration of its group
      when it is the member's own *)
  with fast_eval_mref_impl pq (ups : list fdomain) j (Hups : Forall (fdomain_ok Θ Ξ) ups)
      (H : fast_eval_mref_order Θ Ξ pq (fdomains_erase ups) j) :
      { r : fast_member_reference |
        ⟦mrefᶠ j of pq (fdomains_erase ups) ⟧ᶠ Θ ⍮ Ξ ↘ fast_member_reference_erase r /\ fast_member_reference_ok Θ Ξ r } by struct H :=
  | pq, ups, j, Hups, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_decl _) Eh => exist _ (mk_fast_member_reference pq (carry D) j ups) _
        | exist _ (mh_view qc k Is vm) Eh =>
            let (cups, Hc) := fast_eval_exps_impl Is (fenv_args nil ups) _ _ in
            exist _ (mk_fast_member_reference qc None k cups) _
        | exist _ (mh_record _ _ _) Eh => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }

  with fast_eval_shty_impl pq (ups : list fdomain) (p : fenv) t (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hp : fenv_ok Θ Ξ p)
      (H : fast_eval_shty_order Θ Ξ pq (fdomains_erase ups) (fenv_erase p) t) :
      { a | ⟦shtyᶠ t of pq (fdomains_erase ups) ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a } by struct H :=
  | pq, ups, p, pt_self j Ps, Hups, Hp, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh =>
            let (cups, Hc) := fast_eval_exps_impl Is (fenv_args nil ups) _ _ in
            exist _ (fd_record qr cups) _
        | exist _ _ Eh with fast_eval_exps_impl Ps p Hp _ := {
          | exist _ bs Hbs with fast_eval_mref_impl pq ups j Hups _ := {
            | exist _ (mk_fast_member_reference pc oD k pre) Hm => exist _ (fd_ind pc oD k (pre ++ bs)) _ } } }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  | pq, ups, p, pt_pi B t, Hups, Hp, H =>
      let (b, Hb) := fast_eval_exp_impl B p Hp _ in
      exist _ (fd_pi b (fde_term (fd_shfam pq ups p t) :: nil) fam_cod) _

  with fast_eval_ihty_impl pq (ups : list fdomain) (pm : fenv) As (p : fenv) t (v : fdomain)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hpm : fenv_ok Θ Ξ pm) (Hp : fenv_ok Θ Ξ p) (Hv : fdomain_ok Θ Ξ v)
      (H : fast_eval_ihty_order Θ Ξ pq (fdomains_erase ups) (fenv_erase pm) As (fenv_erase p) t (fdomain_erase v)) :
      { as' | ⟦ihtyᶠ fdomain_erase v of t at pq (fdomains_erase ups) under (fenv_erase pm) As ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase as' /\
              Forall (fdomain_ok Θ Ξ) as' } by struct H :=
  | pq, ups, pm, As, p, pt_self j Ps, v, Hups, Hpm, Hp, Hv, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
          | exist _ ((c, gs) :: nil) Ec =>
              let (ws, Hws) := fast_eval_projs_impl fl v Hv _ in
              let (rs, Hrs) := fast_eval_ihtys_impl pq ups pm As (fenv_args nil ups) gs ws Hups Hpm _ _ _ in
              exist _ rs _
          | exist _ _ Ec => False_rect _ _ }
        | exist _ _ Eh =>
            let (bs, Hbs) := fast_eval_exps_impl Ps p Hp _ in
            let (a, Ha) := fast_eval_exp_impl (List.nth j As a_True) (fenv_args pm (bs ++ v :: nil)) _ _ in
            exist _ (a :: nil) _ }
      | exist _ None Em => False_rect _ _ }
    | inright Ed => False_rect _ _ }
  | pq, ups, pm, As, p, pt_pi B t, v, Hups, Hpm, Hp, Hv, H with decl_lookup (fc_seed F) pq := {
    | inleft (exist _ D Ed) =>
        let (b, Hb) := fast_eval_exp_impl B p Hp _ in
        exist _ (List.map (fun i => fd_pi b (fde_term (fd_ihfam pm As pq ups p t i v) :: nil) fam_cod)
                   (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t)))) _
    | inright Ed => False_rect _ _ }

  with fast_eval_ihtys_impl pq (ups : list fdomain) (pm : fenv) As (p : fenv) gs (vs : list fdomain)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hpm : fenv_ok Θ Ξ pm) (Hp : fenv_ok Θ Ξ p) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : fast_eval_ihtys_order Θ Ξ pq (fdomains_erase ups) (fenv_erase pm) As (fenv_erase p) gs (fdomains_erase vs)) :
      { rs | ⟦ihtysᶠ fdomains_erase vs of gs at pq (fdomains_erase ups) under (fenv_erase pm) As ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase rs /\
             Forall (fdomain_ok Θ Ξ) rs } by struct H :=
  | pq, ups, pm, As, p, nil, nil, Hups, Hpm, Hp, Hvs, H => exist _ nil _
  | pq, ups, pm, As, p, ca_arg T :: gs, v :: vs, Hups, Hpm, Hp, Hvs, H =>
      let (rs, Hrs) := fast_eval_ihtys_impl pq ups pm As (fextend_env p v) gs vs Hups Hpm _ _ _ in
      exist _ rs _
  | pq, ups, pm, As, p, ca_rec t :: gs, v :: vs, Hups, Hpm, Hp, Hvs, H =>
      let (rs1, Hrs1) := fast_eval_ihty_impl pq ups pm As p t v Hups Hpm Hp _ _ in
      let (rs, Hrs) := fast_eval_ihtys_impl pq ups pm As p gs vs Hups Hpm Hp _ _ in
      exist _ (rs1 ++ rs) _
  | pq, ups, pm, As, p, _, _, Hups, Hpm, Hp, Hvs, H => False_rect _ _

  with fast_eval_app_impl (m n : fdomain) (Hm : fdomain_ok Θ Ξ m) (Hn : fdomain_ok Θ Ξ n)
      (H : fast_eval_app_order Θ Ξ (fdomain_erase m) (fdomain_erase n)) :
      { d | $ᶠ| fdomain_erase m & fdomain_erase n | Θ ⍮ Ξ ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d } by struct H :=
  | fd_fn p M, n, Hm, Hn, H =>
      let (m, Hm') := fast_eval_exp_impl M (fextend_env p n) _ _ in
      exist _ m _
  | fd_neut (fd_pi a p B) m, n, Hm, Hn, H =>
      let (b, Hb) := fast_eval_exp_impl B (fextend_env p n) _ _ in
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
              let (cups, Hc) := fast_eval_exps_impl Is (fenv_args nil (vs ++ n :: nil)) _ _ in
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
  | fd_shfam pq ups p t, n, Hm, Hn, H =>
      let (a, Ha) := fast_eval_shty_impl pq ups (fextend_env p n) t _ _ _ in
      exist _ a _
  | fd_ihfam pm As pq ups p t i f, n, Hm, Hn, H with fast_eval_app_impl f n _ Hn _ := {
    | exist _ fn Hfn with fast_eval_ihty_impl pq ups pm As (fextend_env p n) t fn _ _ _ _ _ := {
      | exist _ as' Has with inspect (List.nth_error as' i) := {
        | exist _ (Some a) Ea => exist _ a _
        | exist _ None Ea => False_rect _ _ } } }
  | fd_record pq ns, n, Hm, Hn, H => exist _ (fd_record pq (ns ++ n :: nil)) _
  | _, n, Hm, Hn, H => False_rect _ _

  with fast_eval_exps_impl Ms (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : fast_eval_exps_order Θ Ξ Ms (fenv_erase p)) :
      { ms | ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdomains_erase ms /\ Forall (fdomain_ok Θ Ξ) ms } by struct H :=
  | nil, p, Hp, H => exist _ nil _
  | M :: Ms, p, Hp, H =>
      let (m, Hm) := fast_eval_exp_impl M p Hp _ in
      let (ms, Hms) := fast_eval_exps_impl Ms p Hp _ in
      exist _ (m :: ms) _

  with fast_eval_apps_impl (m : fdomain) (ns : list fdomain) (Hm : fdomain_ok Θ Ξ m) (Hns : Forall (fdomain_ok Θ Ξ) ns)
      (H : fast_eval_apps_order Θ Ξ (fdomain_erase m) (fdomains_erase ns)) :
      { r | $*ᶠ| fdomain_erase m & fdomains_erase ns | Θ ⍮ Ξ ↘ fdomain_erase r /\ fdomain_ok Θ Ξ r } by struct H :=
  | m, nil, Hm, Hns, H => exist _ m _
  | m, n :: ns, Hm, Hns, H =>
      let (m1, Hm1) := fast_eval_app_impl m n Hm _ _ in
      let (r, Hr) := fast_eval_apps_impl m1 ns _ _ _ in
      exist _ r _

  with fast_eval_modexp_impl M (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : fast_eval_modexp_order Θ Ξ M (fenv_erase p)) :
      { h | ⟦ M ⟧ᵐᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h } by struct H :=
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

  with fast_eval_close_impl Δ D (p : fenv) (Hp : fenv_ok Θ Ξ p) (H : fast_eval_close_order Θ Ξ Δ D (fenv_erase p)) :
      { h | ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h } by struct H :=
  | Δ, md_body sm Φ, p, Hp, H => exist _ (fdm_local Δ (md_body sm Φ) p) _
  | nil, md_alias E, p, Hp, H =>
      let (h, Hh) := fast_eval_modexp_impl E p Hp _ in
      exist _ h _
  | e :: Δ, md_alias E, p, Hp, H => exist _ (fdm_local (e :: Δ) (md_alias E) p) _

  with fast_eval_appm_impl (h : fdmod) (n : fdomain) (Hh : fdmod_ok Θ Ξ h) (Hn : fdomain_ok Θ Ξ n)
      (H : fast_eval_appm_order Θ Ξ (fdmod_erase h) (fdomain_erase n)) :
      { r | $ᵐᶠ| fdmod_erase h & fdomain_erase n | Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | fdm_global pq args, n, Hh, Hn, H => exist _ (fdm_global pq (args ++ n :: nil)) _
  | fdm_local Δ D p, n, Hh, Hn, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass A)) Es =>
        let (r, Hr) := fast_eval_close_impl Δ0 D (fextend_env p n) _ _ in
        exist _ r _
    | exist _ _ Es => False_rect _ _ }
  | fdm_member h ch, n, Hh, Hn, H =>
      let (h', Hh') := fast_eval_appm_impl h n _ Hn _ in
      let (r, Hr) := fast_eval_selmc_impl h' ch _ _ in
      exist _ r _

  with fast_eval_appms_impl (h : fdmod) (ns : list fdomain) (Hh : fdmod_ok Θ Ξ h) (Hns : Forall (fdomain_ok Θ Ξ) ns)
      (H : fast_eval_appms_order Θ Ξ (fdmod_erase h) (fdomains_erase ns)) :
      { r | $ᵐ*ᶠ| fdmod_erase h & fdomains_erase ns | Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | h, nil, Hh, Hns, H => exist _ h _
  | h, n :: ns, Hh, Hns, H =>
      let (h1, Hh1) := fast_eval_appm_impl h n Hh _ _ in
      let (r, Hr) := fast_eval_appms_impl h1 ns _ _ _ in
      exist _ r _

  with fast_eval_sel_impl (h : fdmod) x (Hh : fdmod_ok Θ Ξ h) (H : fast_eval_sel_order Θ Ξ (fdmod_erase h) x) :
      { r | fdmod_erase h ·ₜᶠ x Θ ⍮ Ξ ↘ fdomain_erase r /\ fdomain_ok Θ Ξ r } by struct H :=
  | fdm_global pq args, x, Hh, H with gc_entry_f F (qname_app pq (x :: nil)) := {
    | exist _ (Some (fe_def true pv A (Some M))) E =>
        let (f, Hf) := fast_eval_exp_impl M nil _ _ in
        let (r, Hr) := fast_eval_apps_impl f args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def true _ A None)) E =>
        let (a, Ha) := fast_eval_exp_impl A nil _ _ in
        let (r, Hr) := fast_eval_apps_impl (fd_neut a (fd_glob (qname_app pq (x :: nil)))) args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def false _ A B)) E =>
        let (a, Ha) := fast_eval_exp_impl A nil _ _ in
        let (r, Hr) := fast_eval_apps_impl (fd_neut a (fd_glob (qname_app pq (x :: nil)))) args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_mod _ _)) E with ind_mlookup_f F (qname_app pq (x :: nil)) := {
      | exist _ (Some (pg, k, D)) El =>
          let (r, Hr) := fast_eval_apps_impl (fd_ind pg None k nil) args _ _ _ in
          exist _ r _
      | exist _ None El => False_rect _ _ }
    | exist _ (Some (fe_ind _ pg k D _)) E =>
        let (r, Hr) := fast_eval_apps_impl (fd_ind pg None k nil) args _ _ _ in
        exist _ r _
    | exist _ (Some (fe_def_mod _ _ M _)) E =>
        let (f, Hf) := fast_eval_exp_impl M nil _ _ in
        let (r, Hr) := fast_eval_apps_impl f args _ _ _ in
        exist _ r _
    (** A stored record type: its type former *)
    | exist _ (Some (fe_record _ _ _ _)) E with record_lookup_f F (qname_app pq (x :: nil)) := {
      | exist _ (Some R) Er =>
          let (r, Hr) := fast_eval_apps_impl (fd_record (qname_app pq (x :: nil)) nil) args _ _ _ in
          exist _ r _
      | exist _ None Er => False_rect _ _ }
    (** The open frame of a member's module or of a record type's module:
        its type former *)
    | exist _ None E with ind_mlookup_f F (qname_app pq (x :: nil)) := {
      | exist _ (Some (pg, k, D)) El =>
          let (r, Hr) := fast_eval_apps_impl (fd_ind pg None k nil) args _ _ _ in
          exist _ r _
      | exist _ None El with record_lookup_f F (qname_app pq (x :: nil)) := {
        | exist _ (Some R) Er =>
            let (r, Hr) := fast_eval_apps_impl (fd_record (qname_app pq (x :: nil)) nil) args _ _ _ in
            exist _ r _
        | exist _ None Er => False_rect _ _ } } }
  | fdm_local (e :: Δ) D p, x, Hh, H => exist _ (fd_member (fdm_local (e :: Δ) D p) (x :: nil)) _
  | fdm_local nil (md_alias E) p, x, Hh, H => False_rect _ _
  | fdm_local nil (md_body sm Φ) p, x, Hh, H with kinds_body_xp_impl F p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx x) := {
      | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_tm E) := {
        | exist _ (Some (A, M)) Et =>
            let (p', Hp') := fast_eval_benv_impl p Φ' _ _ in
            let (r, Hr) := fast_eval_exp_impl M p' _ _ in
            exist _ r _
        | exist _ None Et => False_rect _ _ }
      | exist _ _ P => False_rect _ _ } }
  | fdm_member h ch, x, Hh, H => exist _ (fd_member h (ch ++ x :: nil)) _

  with fast_eval_selm_impl (h : fdmod) y (Hh : fdmod_ok Θ Ξ h) (H : fast_eval_selm_order Θ Ξ (fdmod_erase h) y) :
      { r | fdmod_erase h ·ₘᶠ y Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | fdm_global pq args, y, Hh, H with gc_module_f F (qname_app pq (y :: nil)) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh') := fast_eval_close_impl Δ D nil _ _ in
        let (r, Hr) := fast_eval_appms_impl h args _ _ _ in
        exist _ r _
    | exist _ _ E => exist _ (fdm_global (qname_app pq (y :: nil)) args) _ }
  | fdm_local (e :: Δ) D p, y, Hh, H => exist _ (fdm_member (fdm_local (e :: Δ) D p) (y :: nil)) _
  | fdm_local nil (md_alias E) p, y, Hh, H => False_rect _ _
  | fdm_local nil (md_body sm Φ) p, y, Hh, H with kinds_body_xp_impl F p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx y) := {
      | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_unit E) := {
        | exist _ (Some (gu_mk Δy Dy)) Eu =>
            let (p', Hp') := fast_eval_benv_impl p Φ' _ _ in
            let (r, Hr) := fast_eval_close_impl Δy Dy p' _ _ in
            exist _ r _
        | exist _ None Eu => False_rect _ _ }
      | exist _ _ P => False_rect _ _ } }
  | fdm_member h ch, y, Hh, H => exist _ (fdm_member h (ch ++ y :: nil)) _

  with fast_eval_selc_impl (h : fdmod) ch (Hh : fdmod_ok Θ Ξ h) (H : fast_eval_selc_order Θ Ξ (fdmod_erase h) ch) :
      { r | fdmod_erase h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ fdomain_erase r /\ fdomain_ok Θ Ξ r } by struct H :=
  | h, x :: nil, Hh, H =>
      let (r, Hr) := fast_eval_sel_impl h x Hh _ in
      exist _ r _
  | h, y :: ch, Hh, H =>
      let (h1, Hh1) := fast_eval_selm_impl h y Hh _ in
      let (r, Hr) := fast_eval_selc_impl h1 ch _ _ in
      exist _ r _
  | h, nil, Hh, H => False_rect _ _

  with fast_eval_selmc_impl (h : fdmod) ch (Hh : fdmod_ok Θ Ξ h) (H : fast_eval_selmc_order Θ Ξ (fdmod_erase h) ch) :
      { r | fdmod_erase h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ fdmod_erase r /\ fdmod_ok Θ Ξ r } by struct H :=
  | h, nil, Hh, H => exist _ h _
  | h, y :: ch, Hh, H =>
      let (h1, Hh1) := fast_eval_selm_impl h y Hh _ in
      let (r, Hr) := fast_eval_selmc_impl h1 ch _ _ in
      exist _ r _

  with fast_eval_benv_impl (p : fenv) Φ (Hp : fenv_ok Θ Ξ p) (H : fast_eval_benv_order Θ Ξ (fenv_erase p) Φ) :
      { p' | ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ fenv_erase p ↘ fenv_erase p' /\ fenv_ok Θ Ξ p' } by struct H :=
  | p, gm_nil, Hp, H => exist _ p _
  | p, gm_ext Φ y (ge_def b pv A (Some M)), Hp, H =>
      let (p1, Hp1) := fast_eval_benv_impl p Φ Hp _ in
      let (m, Hm) := fast_eval_exp_impl M p1 _ _ in
      exist _ (fextend_env p1 m) _
  | p, gm_ext Φ y (ge_def b pv A None), Hp, H => False_rect _ _
  | p, gm_ext Φ y (ge_mod _ (gu_mk Δy Dy)), Hp, H =>
      let (p1, Hp1) := fast_eval_benv_impl p Φ Hp _ in
      let (h, Hh) := fast_eval_close_impl Δy Dy p1 _ _ in
      exist _ (fextend_env_mod p1 h) _
  | p, gm_ext Φ y (ge_def_mod _ A M (gu_mk Δy Dy)), Hp, H =>
      let (p1, Hp1) := fast_eval_benv_impl p Φ Hp _ in
      let (m, Hm) := fast_eval_exp_impl M p1 _ _ in
      let (h, Hh) := fast_eval_close_impl Δy Dy p1 _ _ in
      exist _ (fextend_env_dm p1 m h) _
  | p, gm_open Φ E its, Hp, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([ev_obl]).  They are transparent: the order premises are the
    arguments of the structural recursion. *)
Solve All Obligations with ev_obl.
End EvalImpl.

Extraction Inline fast_eval_exp_impl_functional
  fast_eval_elim_impl_functional
  fast_eval_ihs_impl_functional
  fast_eval_ih_impl_functional
  fast_eval_mref_impl_functional
  fast_eval_shty_impl_functional
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
  fast_eval_benv_impl_functional.
