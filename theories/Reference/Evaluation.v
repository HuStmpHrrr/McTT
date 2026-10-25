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

    The evaluator of [Core.Semantic.Evaluation], with its termination orders.
    It is not extracted: [Extraction.Evaluation] is the evaluator that is, of
    the relation of [Extraction.FastEval], and [Reference.Refinement] relates
    the two.  The orders here are those of the specification of
    normalization ([Extraction.NbE]). *)


(** The termination orders mirror the evaluation relations, one for each, in
    the same global context.  A transparent global recurses into its resolved
    body, which [eval_sel_order_global] records; a saturated alias recurses into its
    target.  Each premise that uses a value is quantified over the values its
    earlier premises evaluate to.  The orders split their cases as the
    evaluator does: a closure lacking a first parameter, a chain of two
    selections or more, the outermost missing parameter as [tele_snoc]
    splits it off. *)

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
| eval_exp_order_llit :
  `( eval_exp_order Θ Ξ (𝕃ᵒ o) p )
| eval_exp_order_succl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ (succl M) p )
| eval_exp_order_maxl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     eval_exp_order Θ Ξ (maxl M N) p )
| eval_exp_order_True :
  `( eval_exp_order Θ Ξ ⊤ p )
| eval_exp_order_true :
  `( eval_exp_order Θ Ξ ⋆ p )
| eval_exp_order_False :
  `( eval_exp_order Θ Ξ ⊥ p )
(** The scrutinee of [efq] must evaluate to a neutral, since no other value
    has a rule. *)
| eval_exp_order_exfalso :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> exists b n, m = ⇑ b n) ->
     (forall b m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ ⇑ b m -> eval_exp_order Θ Ξ A (p ↦ ⇑ b m)) ->
     eval_exp_order Θ Ξ (efq M return A) p )
| eval_exp_order_pi :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ (Π A B) p )
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
     eval_exps_order Θ Ξ Is (env_args nil nil) ->
     eval_exp_order Θ Ξ (a_con pq j c) p )
(** The eliminator: its uniform parameters, its scrutinee, whose value
    names the group it eliminates by, and the elimination. *)
| eval_exp_order_elim :
  `( eval_exps_order Θ Ξ Us p ->
     eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> exists pq, elim_grp_of oq m = Some pq) ->
     (forall ups m pq, ⟦ Us ⟧* Θ ⍮ Ξ ⍮ p ↘ ups -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> elim_grp_of oq m = Some pq ->
        eval_elim_order Θ Ξ p pq ups Bks j m) ->
     eval_exp_order Θ Ξ (a_elim oq Us j Bks M) p )
| eval_exp_order_fn :
  `( eval_exp_order Θ Ξ (λ A M) p )
| eval_exp_order_app :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     (forall m n, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_app_order Θ Ξ m n) ->
     eval_exp_order Θ Ξ (M $ N) p )
| eval_exp_order_let :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> eval_exp_order Θ Ξ B (p ↦ m)) ->
     eval_exp_order Θ Ξ (a_let (b_def oA M) B) p )
| eval_exp_order_let_mod :
  `( eval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h -> eval_exp_order Θ Ξ B (p ↦ᵐ h)) ->
     eval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
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
(** A record element: the values of its fields *)
| eval_exp_order_tuple :
  `( eval_exps_order Θ Ξ (List.map snd fs) p ->
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
     eval_nflds_order Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil ->
     (forall rs, eval_nflds Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil rs -> List.nth_error rs k <> None) ->
     eval_proj_order Θ Ξ f (⇑ (d_record pq ns) m) )

(** The neutral projections at a list of fields, as [eval_nflds] reads
    them *)
with eval_nflds_order (Θ : gdeps) (Ξ : gstack) : list domain -> domain_ne -> list (string * exp) -> list domain -> Prop :=
(** No field left *)
| eval_nflds_order_nil :
  `( eval_nflds_order Θ Ξ ns m nil pre )
(** The next field's type, then the rest after its projection *)
| eval_nflds_order_cons :
  `( eval_exp_order Θ Ξ T (env_args nil (ns ++ pre)) ->
     (forall a, ⟦ T ⟧ Θ ⍮ Ξ ⍮ env_args nil (ns ++ pre) ↘ a ->
        eval_nflds_order Θ Ξ ns m fl (pre ++ ⇑ a (d_proj g m) :: nil)) ->
     eval_nflds_order Θ Ξ ns m ((g, T) :: fl) pre )

(** The eliminator of the group at [pq] at its member [j], on a value, as
    [eval_elim] reads it. *)
with eval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> Prop :=
(** On a saturated constructor: the recursive results, then the branch *)
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
     n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat ->
     eval_ihs_order Θ Ξ p pq ups Bks gs (skipn (im_np Dq Mk) vs) ->
     (forall ihs, ⟦ihs skipn (im_np Dq Mk) vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs ->
        eval_exp_order Θ Ξ B (env_args p (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs) ++ skipn (im_np Dq Mk) vs ++ ihs))) ->
     eval_elim_order Θ Ξ p pq ups Bks j (d_con pc k c vs) )
(** On a neutral: the motive's instance *)
| eval_elim_order_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_ref pq j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_nm b = S (im_nn Mk) ->
     eval_exp_order Θ Ξ (eb_motive b) (env_args p (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil)) ->
     eval_elim_order Θ Ξ p pq ups Bks j (⇑ (d_ind pc k as') m) )

(** The recursive results of the arguments [vs] of kinds [gs] *)
with eval_ihs_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> list carg -> list domain -> Prop :=
(** No argument *)
| eval_ihs_order_nil :
  `( eval_ihs_order Θ Ξ p pq ups Bks nil nil )
(** A non-recursive argument *)
| eval_ihs_order_arg :
  `( eval_ihs_order Θ Ξ p pq ups Bks gs vs ->
     eval_ihs_order Θ Ξ p pq ups Bks (ca_arg T :: gs) (v :: vs) )
(** A recursive argument: its result, then the rest *)
| eval_ihs_order_rec_case :
  `( eval_ih_order Θ Ξ p pq ups Bks t v ->
     eval_ihs_order Θ Ξ p pq ups Bks gs vs ->
     eval_ihs_order Θ Ξ p pq ups Bks (ca_rec t :: gs) (v :: vs) )

(** The recursive result of an argument of a shape *)
with eval_ih_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> Prop :=
(** At the end: the eliminator at the member *)
| eval_ih_order_self :
  `( eval_elim_order Θ Ξ p pq ups Bks j v ->
     eval_ih_order Θ Ξ p pq ups Bks (pt_self j Ps) v )
(** At a function shape: a closure *)
| eval_ih_order_pi :
  `( eval_ih_order Θ Ξ p pq ups Bks (pt_pi B t) v )

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
     eval_exps_order Θ Ξ Is (env_args nil ups) ->
     eval_mref_order Θ Ξ pq ups j )

(** The type of an argument of a shape *)
with eval_shty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
(** At the end: the parameters, and the member stood for *)
| eval_shty_order_self :
  `( eval_exps_order Θ Ξ Ps p ->
     eval_mref_order Θ Ξ pq ups j ->
     eval_shty_order Θ Ξ pq ups p (pt_self j Ps) )
(** At a domain *)
| eval_shty_order_pi :
  `( eval_exp_order Θ Ξ B p ->
     eval_shty_order Θ Ξ pq ups p (pt_pi B t) )

(** The type of the recursive result of an argument of a shape *)
with eval_ihty_order (Θ : gdeps) (Ξ : gstack) : env -> list exp -> env -> ptyp -> domain -> Prop :=
(** At the end: the parameters, then the member's motive *)
| eval_ihty_order_self :
  `( eval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ p ↘ bs -> eval_exp_order Θ Ξ (List.nth j As a_True) (env_args pm (bs ++ v :: nil))) ->
     eval_ihty_order Θ Ξ pm As p (pt_self j Ps) v )
(** At a domain *)
| eval_ihty_order_pi :
  `( eval_exp_order Θ Ξ B p ->
     eval_ihty_order Θ Ξ pm As p (pt_pi B t) v )

with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| eval_app_order_fn :
  `( eval_exp_order Θ Ξ M (p ↦ n) ->
     eval_app_order Θ Ξ λᵈ p M n )
| eval_app_order_neut :
  `( eval_exp_order Θ Ξ B (p ↦ n) ->
     eval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
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
     eval_exps_order Θ Ξ Is (env_args nil (vs ++ n :: nil)) ->
     eval_app_order Θ Ξ (d_con pq j c vs) n )
| eval_app_order_ihfn :
  `( eval_app_order Θ Ξ f n ->
     (forall fn, $| f & n | Θ ⍮ Ξ ↘ fn -> eval_ih_order Θ Ξ p pq ups Bks t fn) ->
     eval_app_order Θ Ξ (d_ihfn p Bks pq ups t f) n )
| eval_app_order_shfam :
  `( eval_shty_order Θ Ξ pq ups (p ↦ n) t ->
     eval_app_order Θ Ξ (d_shfam pq ups p t) n )
| eval_app_order_ihfam :
  `( eval_app_order Θ Ξ f n ->
     (forall fn, $| f & n | Θ ⍮ Ξ ↘ fn -> eval_ihty_order Θ Ξ pm As (p ↦ n) t fn) ->
     eval_app_order Θ Ξ (d_ihfam pm As p t f) n )
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
  `( tele_snoc Δ = Some (Δ0, ce_ass A) ->
     eval_close_order Θ Ξ Δ0 D (p ↦ n) ->
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
  `( gc_term Θ Ξ (qname_app pq (x :: nil)) = Some M ->
     eval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ f -> eval_apps_order Θ Ξ f args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eval_sel_order_global_neut :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     eval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a -> eval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eval_sel_order_global_ind :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app pq (x :: nil)) = Some (pg, k, D) ->
     eval_apps_order Θ Ξ (d_ind pg k nil) args ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eval_sel_order_unsat :
  `( eval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
(** A term part of a saturated body ([entry_tm]) *)
| eval_sel_order_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     eval_benv_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_exp_order Θ Ξ M p') ->
     eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
| eval_sel_order_member :
  `( eval_sel_order Θ Ξ (dm_member h ch) x )
(** A record type of a global module, not a definition: its type former,
    applied to the arguments *)
| eval_sel_order_global_record :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
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
(** A module part of a saturated body ([entry_unit]) *)
| eval_selm_order_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     eval_benv_order Θ Ξ p Φ' ->
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

with eval_benv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| eval_benv_order_nil :
  `( eval_benv_order Θ Ξ p gm_nil )
| eval_benv_order_def :
  `( eval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_exp_order Θ Ξ M p1) ->
     eval_benv_order Θ Ξ p (gm_ext Φ y (ge_def b pv A (Some M))) )
| eval_benv_order_mod :
  `( eval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_close_order Θ Ξ Δy Dy p1) ->
     eval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) )
(** A definition with a module part: its term and its unit's closure *)
| eval_benv_order_dm :
  `( eval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_exp_order Θ Ξ M p1) ->
     (forall p1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p1 -> eval_close_order Θ Ξ Δy Dy p1) ->
     eval_benv_order Θ Ξ p (gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy))) ).

#[local]
Hint Constructors eval_exp_order eval_elim_order eval_ihs_order eval_ih_order eval_mref_order eval_shty_order eval_ihty_order eval_app_order eval_exps_order eval_apps_order
  eval_modexp_order eval_close_order eval_appm_order eval_appms_order eval_sel_order eval_selm_order eval_selc_order eval_selmc_order
  eval_benv_order eval_proj_order eval_nflds_order : mctt.

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
    | H1 : kbody ?T ?X ?p ?Φ ?r1, H2 : kbody ?T ?X ?p ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_kbody _ _ _ _ H1 H2); subst; clear H2
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
    | H1 : eval_benv ?T ?X ?m ?n ?r1, H2 : eval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_benv _ _ _ _ H1 H2); subst; clear H2
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
    | H1 : eval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : eval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_shty _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r1, H2 : eval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ihty _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : kgens ?T ?X ?p ?E ?its ?g1, H2 : kgens ?T ?X ?p ?E ?its ?g2 |- _ =>
        assert_fails (constr_eq g1 g2);
        pose proof (functional_kgens _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    | H1 : eval_proj ?T ?X ?f ?m ?r1, H2 : eval_proj ?T ?X ?f ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_proj _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_nflds ?T ?X ?ns ?m ?fl ?pre ?r1, H2 : eval_nflds ?T ?X ?ns ?m ?fl ?pre ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_nflds _ _ _ _ _ _ H1 H2); subst; clear H2
    end.

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
    (forall p Φ p', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_benv_order Θ Ξ p Φ) /\
    (forall p pq ups Bks j m r, ⟦elim m at j of pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_elim_order Θ Ξ p pq ups Bks j m) /\
    (forall p pq ups Bks gs vs ihs, ⟦ihs vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs -> eval_ihs_order Θ Ξ p pq ups Bks gs vs) /\
    (forall p pq ups Bks t v r, ⟦ih v of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_ih_order Θ Ξ p pq ups Bks t v) /\
    (forall pq ups j r, ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ r -> eval_mref_order Θ Ξ pq ups j) /\
    (forall pq ups p t a, ⟦shty t of pq ups ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_shty_order Θ Ξ pq ups p t) /\
    (forall pm As p t v a, ⟦ihty v of t under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_ihty_order Θ Ξ pm As p t v) /\
    (forall f m r, eval_proj Θ Ξ f m r -> eval_proj_order Θ Ξ f m) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs -> eval_nflds_order Θ Ξ ns m fl pre).
Proof.
  intros Θ Ξ; apply eval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : eval_selc _ _ _ ?c _ |- eval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    solve [ eapply eval_sel_order_global_neut; eauto; intros; functional_eval_all; eauto
          | econstructor; try eassumption; intros; functional_eval_all; eauto using kgens_order_sound, tele_snoc_app
          (** The projections of a neutral reach the field projected. *)
          | econstructor; try eassumption; intros; functional_eval_all; congruence
          (** The eliminator: the group the scrutinee's value names, once. *)
          | econstructor; try eassumption; intros; functional_eval_all;
            first [ eexists; eassumption
                  | match goal with H1 : elim_grp_of ?o ?m = Some _, H2 : elim_grp_of ?o ?m = Some _ |- _ =>
                      rewrite H1 in H2; injection H2 as <-; assumption end ] ].
Qed.

Lemma eval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (eval_order_sound Θ Ξ)). Qed.

Lemma eval_app_order_sound : forall Θ Ξ m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (eval_order_sound Θ Ξ))). Qed.

Lemma eval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms -> eval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (eval_order_sound Θ Ξ)))). Qed.

Lemma eval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (eval_order_sound Θ Ξ)))))). Qed.

Lemma eval_shty_order_sound : forall Θ Ξ pq ups p t a, ⟦shty t of pq ups ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_shty_order Θ Ξ pq ups p t.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_ihty_order_sound : forall Θ Ξ pm As p t v a, ⟦ihty v of t under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_ihty_order Θ Ξ pm As p t v.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_app_order_sound eval_exps_order_sound eval_modexp_order_sound
  eval_shty_order_sound eval_ihty_order_sound : mctt.

Lemma eval_ih_order_sound : forall Θ Ξ p pq ups Bks t v r, ⟦ih v of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
    eval_ih_order Θ Ξ p pq ups Bks t v.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_mref_order_sound : forall Θ Ξ pq ups j r, ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ r -> eval_mref_order Θ Ξ pq ups j.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_proj_order_sound : forall Θ Ξ f m r, eval_proj Θ Ξ f m r -> eval_proj_order Θ Ξ f m.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve eval_ih_order_sound eval_mref_order_sound eval_proj_order_sound : mctt.

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
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * Hp; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as <-; eauto | eauto ].
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

#[local] Hint Resolve kbody_order_sound : core.

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A variable is looked up in the environment, without recursion. *)
  Definition eval_var_impl x p (H : eval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply eval_exp_var.
  Defined.

  #[local]
  Ltac impl_obl_tac1 :=
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
    | H : eval_benv_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_elim_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_mref_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_shty_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihty_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_proj_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_nflds_order _ _ _ _ _ _ |- _ => progressive_invert H
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
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_entry _ _ ?p = Some _, H2 : gc_entry _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_entry _ _ ?p = Some (ge_def_mod _ _ _ _), H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H1) in H2; discriminate H2
      | H1 : ind_mlookup _ _ ?p = Some _, H2 : gc_entry _ _ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
          exfalso; exact (ind_mlookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
      | H1 : record_lookup _ _ ?p = Some _, H2 : gc_entry _ _ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
          exfalso; exact (record_lookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
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
      | H1 : kbody _ _ ?p ?Φ ?r1, H2 : kbody _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); pose proof (functional_kbody _ _ _ _ H1 H2); subst; clear H2
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
      | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = None |- _ =>
          rewrite H1 in H2; discriminate H2
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
      end.

  (** The [efq] case: the order says that the scrutinee evaluates to a
      neutral, which rules out every other value. *)
  #[local]
  Ltac impl_obl_exfalso :=
    repeat match goal with
      | H : forall m, eval_exp _ _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : eval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      (** The eliminator's scrutinee names a group. *)
      | H : forall m, eval_exp _ _ ?M ?p m -> exists _, elim_grp_of _ m = Some _, Hm : eval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ?); clear H
      (** The projections of a neutral reach the field projected. *)
      | H : forall rs, eval_nflds _ _ ?ns ?m ?fl ?pre rs -> _, Hm : eval_nflds _ _ ?ns ?m ?fl ?pre _ |- _ =>
          specialize (H _ Hm)
      end.

  #[local]
  Ltac impl_obl_split :=
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
    | H : eval_benv_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_elim_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_mref_order _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihs_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_shty_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihty_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_proj_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_nflds_order _ _ _ _ _ _ |- _ => dependent destruction H
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
    try solve [ exfalso; lia ];
    try solve [ eapply eval_sel_global_neut; eauto ];
    (** A term part, by the lookups its branch fixed. *)
    try solve [ eapply eval_sel_global; [| eassumption | eassumption ]; unfold gc_term;
                repeat match goal with
                       | H : gc_resolve _ _ _ = _ |- context [gc_resolve _ _ _] => rewrite H
                       | H : gc_entry _ _ _ = _ |- context [gc_entry _ _ _] => rewrite H
                       end; reflexivity ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
    try solve [ eauto ];
    try econstructor; eauto.

  #[local]
  Ltac ev_obl :=
    intros; cbv beta in *;
    repeat impl_obl_tac1;
    first [ solve [ impl_obl_finish ]
          | solve [ impl_obl_split; impl_obl_finish ]
          | impl_obl_finish ].

  (** An obligation whose conclusion is an order stays transparent, since
      the guard condition sees it in the recursive calls; any other is
      proved opaquely. *)
  #[local]
  Ltac ev_obl_auto :=
    intros;
    lazymatch goal with
    | |- eval_exp_order _ _ _ _ => ev_obl
    | |- eval_app_order _ _ _ _ => ev_obl
    | |- eval_exps_order _ _ _ _ => ev_obl
    | |- eval_apps_order _ _ _ _ => ev_obl
    | |- eval_modexp_order _ _ _ _ => ev_obl
    | |- eval_close_order _ _ _ _ _ => ev_obl
    | |- eval_appm_order _ _ _ _ => ev_obl
    | |- eval_appms_order _ _ _ _ => ev_obl
    | |- eval_sel_order _ _ _ _ => ev_obl
    | |- eval_selm_order _ _ _ _ => ev_obl
    | |- eval_selc_order _ _ _ _ => ev_obl
    | |- eval_selmc_order _ _ _ _ => ev_obl
    | |- eval_benv_order _ _ _ _ => ev_obl
    | |- eval_elim_order _ _ _ _ _ _ _ _ => ev_obl
    | |- eval_mref_order _ _ _ _ _ => ev_obl
    | |- eval_ihs_order _ _ _ _ _ _ _ _ => ev_obl
    | |- eval_ih_order _ _ _ _ _ _ _ _ => ev_obl
    | |- eval_shty_order _ _ _ _ _ _ => ev_obl
    | |- eval_ihty_order _ _ _ _ _ _ _ => ev_obl
    | |- eval_proj_order _ _ _ _ => ev_obl
    | |- eval_nflds_order _ _ _ _ _ _ => ev_obl
    | |- _ => abstract ev_obl
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations eval_exp_impl m p (H : eval_exp_order Θ Ξ m p) : { d | ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | Typeω@i, p, H => exist _ 𝕌ω@i _
  | Type⟨M⟩, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      exist _ 𝕌@m _
  | #x    , p, H => eval_var_impl x p H
  | Level@n, p, H => exist _ (Levelᵈ@n) _
  | 𝕃ᵒ o  , p, H => exist _ (dlvl_lit o) _
  | succl M, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      exist _ (dlvl_suc m) _
  | maxl M N, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      exist _ (dlvl_max m n) _
  | ⊤     , p, H => exist _ ⊤ᵈ _
  | ⋆     , p, H => exist _ ⋆ᵈ _
  | ⊥     , p, H => exist _ ⊥ᵈ _
  | efq M return A, p, H with eval_exp_impl M p _ := {
    | exist _ (⇑ b m) Hm =>
        let (a, Ha) := eval_exp_impl A (p ↦ ⇑ b m) _ in
        exist _ ⇑ a (efqᵈ m under p return A) _
    | exist _ _ Hm => False_rect _ _ }
  | Π A B , p, H =>
      let (r , Hr) := eval_exp_impl A p _ in
      exist _ Πᵈ r p B _
  | λ A M , p, H => exist _ λᵈ p M _
  | a_ind pq k, p, H => exist _ (d_ind pq k nil) _
  | a_con pq k c, p, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_starts D Mk) := {
        | exist _ true Es => exist _ (d_con pq k c nil) _
        | exist _ false Es with inspect (im_head Mk) := {
          | exist _ (mh_view qc k' Is vm) Eh =>
              let (cups, Hc) := eval_exps_impl Is (env_args nil nil) _ in
              exist _ (d_con qc k' c cups) _
          | exist _ (mh_decl _) Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  (** A literal is generated before it is ever evaluated. *)
  | a_ntok, p, H => False_rect _ _
  | a_nlit _, p, H => False_rect _ _
  | a_elim oq Us j Bks M, p, H with eval_exps_impl Us p _ := {
    | exist _ ups Hups with eval_exp_impl M p _ := {
      | exist _ m Hm with inspect (elim_grp_of oq m) := {
        | exist _ (Some pq) Eg =>
            let (r, Hr) := eval_elim_impl p pq ups Bks j m _ in
            exist _ r _
        | exist _ None Eg => False_rect _ _ } } }
  | M $ N   , p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      let (a, Ha) := eval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | a_let (b_mod (gu_mk Δ D)) B, p, H =>
      let (h, Hh) := eval_close_impl Δ D p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ᵐ h) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := eval_modexp_impl R p _ in
        let (f, Hf) := eval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := eval_exps_impl args p _ in
        let (r, Hr) := eval_apps_impl f ns _ in
        exist _ r _ }
  | a_record pq, p, H => exist _ (d_record pq nil) _
  | a_tuple T fs, p, H =>
      let (vs, Hvs) := eval_exps_impl (List.map snd fs) p _ in
      exist _ (d_tuple (List.combine (List.map fst fs) vs)) _
  | a_proj f M, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_proj_impl f m _ in
      exist _ r _

  with eval_proj_impl f m (H : eval_proj_order Θ Ξ f m) : { r | eval_proj Θ Ξ f m r } by struct H :=
  | f, d_tuple vs, H with inspect (field_lookup vs f) := {
    | exist _ (Some r) E => exist _ r _
    | exist _ None E => False_rect _ _ }
  | f, ⇑ (d_record pq ns) m, H with inspect (record_lookup Θ Ξ pq) := {
    | exist _ (Some R) El with inspect (field_index (record_fields R) f) := {
      | exist _ (Some k) Ek with eval_nflds_impl ns m (List.firstn (S k) (record_fields R)) nil _ := {
        | exist _ rs Hrs with inspect (List.nth_error rs k) := {
          | exist _ (Some r) Er => exist _ r _
          | exist _ None Er => False_rect _ _ } }
      | exist _ None Ek => False_rect _ _ }
    | exist _ None El => False_rect _ _ }
  | f, _, H => False_rect _ _

  with eval_nflds_impl ns m fl pre (H : eval_nflds_order Θ Ξ ns m fl pre) :
      { rs | eval_nflds Θ Ξ ns m fl pre rs } by struct H :=
  | ns, m, nil, pre, H => exist _ nil _
  | ns, m, (g, T) :: fl, pre, H =>
      let (a, Ha) := eval_exp_impl T (env_args nil (ns ++ pre)) _ in
      let (rs, Hrs) := eval_nflds_impl ns m fl (pre ++ ⇑ a (d_proj g m) :: nil) _ in
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
                    let (r, Hr) := eval_exp_impl B (env_args p (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs) ++
                                                                 skipn (im_np Dq Mk) vs ++ ihs)) _ in
                    exist _ r _
                | exist _ None Ebr => False_rect _ _ }
              | exist _ None Eb => False_rect _ _ }
            | exist _ None Ec => False_rect _ _ }
          | exist _ None Emk => False_rect _ _ }
        | exist _ None Edq => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | p, pq, ups, Bks, j, ⇑ (d_ind pc k as') m, H with inspect (ind_lookup Θ Ξ pc) := {
    | exist _ (Some Dq) Edq with inspect (List.nth_error Bks j) := {
      | exist _ (Some b) Eb =>
          let (a, Ha) := eval_exp_impl (eb_motive b) (env_args p (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil)) _ in
          exist _ (⇑ a (d_elim p Bks pq ups j as' m)) _
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Edq => False_rect _ _ }
  | p, pq, ups, Bks, j, _, H => False_rect _ _

  with eval_ihs_impl p pq ups Bks gs vs (H : eval_ihs_order Θ Ξ p pq ups Bks gs vs) :
      { ihs | ⟦ihs vs of gs under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs } by struct H :=
  | p, pq, ups, Bks, nil, nil, H => exist _ nil _
  | p, pq, ups, Bks, ca_arg T :: gs, v :: vs, H =>
      let (ihs, Hihs) := eval_ihs_impl p pq ups Bks gs vs _ in
      exist _ ihs _
  | p, pq, ups, Bks, ca_rec t :: gs, v :: vs, H =>
      let (ih, Hih) := eval_ih_impl p pq ups Bks t v _ in
      let (ihs, Hihs) := eval_ihs_impl p pq ups Bks gs vs _ in
      exist _ (ih :: ihs) _
  | p, pq, ups, Bks, _, _, H => False_rect _ _

  with eval_ih_impl p pq ups Bks t v (H : eval_ih_order Θ Ξ p pq ups Bks t v) :
      { r | ⟦ih v of t under pq ups Bks ⟧ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, pq, ups, Bks, pt_self j Ps, v, H =>
      let (r, Hr) := eval_elim_impl p pq ups Bks j v _ in
      exist _ r _
  | p, pq, ups, Bks, pt_pi B t, v, H => exist _ (d_ihfn p Bks pq ups t v) _

  with eval_mref_impl pq ups j (H : eval_mref_order Θ Ξ pq ups j) : { r | ⟦mref j of pq ups ⟧ Θ ⍮ Ξ ↘ r } by struct H :=
  | pq, ups, j, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_decl _) Eh => exist _ (pq, j, ups) _
        | exist _ (mh_view qc k Is vm) Eh =>
            let (cups, Hc) := eval_exps_impl Is (env_args nil ups) _ in
            exist _ (qc, k, cups) _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }

  with eval_shty_impl pq ups p t (H : eval_shty_order Θ Ξ pq ups p t) : { a | ⟦shty t of pq ups ⟧ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pq, ups, p, pt_self j Ps, H with eval_exps_impl Ps p _ := {
    | exist _ bs Hbs with eval_mref_impl pq ups j _ := {
      | exist _ (pc, k, pre) Hm => exist _ (d_ind pc k (pre ++ bs)) _ } }
  | pq, ups, p, pt_pi B t, H =>
      let (b, Hb) := eval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_shfam pq ups p t) fam_cod) _

  with eval_ihty_impl pm As p t v (H : eval_ihty_order Θ Ξ pm As p t v) : { a | ⟦ihty v of t under pm As ⟧ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pm, As, p, pt_self j Ps, v, H =>
      let (bs, Hbs) := eval_exps_impl Ps p _ in
      let (a, Ha) := eval_exp_impl (List.nth j As a_True) (env_args pm (bs ++ v :: nil)) _ in
      exist _ a _
  | pm, As, p, pt_pi B t, v, H =>
      let (b, Hb) := eval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_ihfam pm As p t v) fam_cod) _

  with eval_app_impl m n (H : eval_app_order Θ Ξ m n) : { d | $| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | λᵈ p M        , n, H =>
      let (m, Hm) := eval_exp_impl M (p ↦ n) _ in
      exist _ m _
  | ⇑ (Πᵈ a p B) m, n, H =>
      let (b, Hb) := eval_exp_impl B (p ↦ n) _ in
      exist _ ⇑ b (m $ᵈ ⇓ a n) _
  | d_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selc_impl h' ch _ in
      exist _ r _
  | d_ind pq k as', n, H => exist _ (d_ind pq k (as' ++ n :: nil)) _
  | d_con pq k c vs, n, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_head Mk) := {
        | exist _ (mh_decl _) Eh => exist _ (d_con pq k c (vs ++ n :: nil)) _
        | exist _ (mh_view qc k' Is vm) Eh with inspect (S (List.length vs) <? ind_nu D) := {
          | exist _ true El => exist _ (d_con pq k c (vs ++ n :: nil)) _
          | exist _ false El =>
              let (cups, Hc) := eval_exps_impl Is (env_args nil (vs ++ n :: nil)) _ in
              exist _ (d_con qc k' c cups) _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | d_ihfn p Bks pq ups t f, n, H =>
      let (fn, Hfn) := eval_app_impl f n _ in
      let (r, Hr) := eval_ih_impl p pq ups Bks t fn _ in
      exist _ r _
  | d_shfam pq ups p t, n, H =>
      let (a, Ha) := eval_shty_impl pq ups (p ↦ n) t _ in
      exist _ a _
  | d_ihfam pm As p t f, n, H =>
      let (fn, Hfn) := eval_app_impl f n _ in
      let (a, Ha) := eval_ihty_impl pm As (p ↦ n) t fn _ in
      exist _ a _
  | d_record pq ns, n, H => exist _ (d_record pq (ns ++ n :: nil)) _
  | _, n, H => False_rect _ _

  with eval_exps_impl Ms p (H : eval_exps_order Θ Ξ Ms p) : { ms | ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (ms, Hms) := eval_exps_impl Ms p _ in
      exist _ (m :: ms) _

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
  | Δ, md_body sm Φ, p, H => exist _ (dm_local Δ (md_body sm Φ) p) _
  | nil, md_alias E, p, H =>
      let (h, Hh) := eval_modexp_impl E p _ in
      exist _ h _
  | e :: Δ, md_alias E, p, H => exist _ (dm_local (e :: Δ) (md_alias E) p) _

  with eval_appm_impl h n (H : eval_appm_order Θ Ξ h n) : { r | $ᵐ| h & n | Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local Δ D p, n, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass A)) Es =>
        let (r, Hr) := eval_close_impl Δ0 D (p ↦ n) _ in
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
  | dm_global pq args, x, H with inspect (gc_resolve Θ Ξ (qname_app pq (x :: nil))) := {
    | exist _ (Some (ge_def true pv A (Some M))) E =>
        let (f, Hf) := eval_exp_impl M nil _ in
        let (r, Hr) := eval_apps_impl f args _ in
        exist _ r _
    | exist _ (Some (ge_def true _ A None)) E =>
        let (a, Ha) := eval_exp_impl A nil _ in
        let (r, Hr) := eval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_def false _ A B)) E =>
        let (a, Ha) := eval_exp_impl A nil _ in
        let (r, Hr) := eval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_mod _ _)) E => False_rect _ _
    | exist _ (Some (ge_ind _ _ _ _ _)) E => False_rect _ _
    | exist _ (Some (ge_def_mod _ _ _ _)) E => False_rect _ _
    | exist _ (Some (ge_record _ _ _ _)) E => False_rect _ _
    | exist _ None E with inspect (ind_mlookup Θ Ξ (qname_app pq (x :: nil))) := {
      | exist _ (Some (pg, k, D)) Ed =>
          let (r, Hr) := eval_apps_impl (d_ind pg k nil) args _ in
          exist _ r _
      (** A record type: its type former *)
      | exist _ None Ed with inspect (record_lookup Θ Ξ (qname_app pq (x :: nil))) := {
        | exist _ (Some R) Er =>
            let (r, Hr) := eval_apps_impl (d_record (qname_app pq (x :: nil)) nil) args _ in
            exist _ r _
        (** A definition with a module part: its term *)
        | exist _ None Er with inspect (gc_entry Θ Ξ (qname_app pq (x :: nil))) := {
          | exist _ (Some (ge_def_mod _ _ M _)) Ea =>
              let (f, Hf) := eval_exp_impl M nil _ in
              let (r, Hr) := eval_apps_impl f args _ in
              exist _ r _
          | exist _ _ Ea => False_rect _ _ } } } }
  | dm_local (e :: Δ) D p, x, H => exist _ (d_member (dm_local (e :: Δ) D p) (x :: nil)) _
  | dm_local nil (md_alias E) p, x, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, x, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx x) := {
      | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_tm E) := {
        | exist _ (Some (A, M)) Et =>
            let (p', Hp') := eval_benv_impl p Φ' _ in
            let (r, Hr) := eval_exp_impl M p' _ in
            exist _ r _
        | exist _ None Et => False_rect _ _ }
      | exist _ _ P => False_rect _ _ } }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with eval_selm_impl h y (H : eval_selm_order Θ Ξ h y) : { r | h ·ₘ y Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, y, H with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh) := eval_close_impl Δ D nil _ in
        let (r, Hr) := eval_appms_impl h args _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local (e :: Δ) D p, y, H => exist _ (dm_member (dm_local (e :: Δ) D p) (y :: nil)) _
  | dm_local nil (md_alias E) p, y, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, y, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx y) := {
      | exist _ (Some (gm_ext Φ' _ E)) P with inspect (entry_unit E) := {
        | exist _ (Some (gu_mk Δy Dy)) Eu =>
            let (p', Hp') := eval_benv_impl p Φ' _ in
            let (r, Hr) := eval_close_impl Δy Dy p' _ in
            exist _ r _
        | exist _ None Eu => False_rect _ _ }
      | exist _ _ P => False_rect _ _ } }
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

  with eval_benv_impl p Φ (H : eval_benv_order Θ Ξ p Φ) : { p' | ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y (ge_def b pv A (Some M)), H =>
      let (p1, Hp1) := eval_benv_impl p Φ _ in
      let (m, Hm) := eval_exp_impl M p1 _ in
      exist _ (p1 ↦ m) _
  | p, gm_ext Φ y (ge_def b pv A None), H => False_rect _ _
  | p, gm_ext Φ y (ge_mod _ (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := eval_benv_impl p Φ _ in
      let (h, Hh) := eval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵐ h) _
  | p, gm_ext Φ y (ge_def_mod _ A M (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := eval_benv_impl p Φ _ in
      let (m, Hm) := eval_exp_impl M p1 _ in
      let (h, Hh) := eval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵈ m ‖ h) _
  | p, gm_open Φ E its, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([ev_obl]); one whose conclusion is not an order is proved
    opaquely ([ev_obl_auto]). *)
Solve All Obligations with ev_obl_auto.
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
