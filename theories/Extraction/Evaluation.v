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

Inductive feval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
| feeo_typ :
  `( feval_exp_order Θ Ξ Typeω@i p )
(** A small universe evaluates its level. *)
| feeo_univ :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ Type⟨M⟩ p )
(** An environment is total, so a variable always terminates. *)
| feeo_var :
  `( feval_exp_order Θ Ξ #x p )
| feeo_level :
  `( feval_exp_order Θ Ξ (Level@n) p )
| feeo_llit :
  `( feval_exp_order Θ Ξ (𝕃ᵒ o) p )
| feeo_succl :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ (succl M) p )
| feeo_maxl :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ N p ->
     feval_exp_order Θ Ξ (maxl M N) p )
| feeo_True :
  `( feval_exp_order Θ Ξ ⊤ p )
| feeo_true :
  `( feval_exp_order Θ Ξ ⋆ p )
| feeo_False :
  `( feval_exp_order Θ Ξ ⊥ p )
(** The scrutinee of [efq] must evaluate to a neutral, since no other value
    has a rule. *)
| feeo_exfalso :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> exists b n, m = ⇑ b n) ->
     (forall b m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ⇑ b m -> feval_exp_order Θ Ξ A (p ↦ ⇑ b m)) ->
     feval_exp_order Θ Ξ (efq M return A) p )
| feeo_pi :
  `( feval_exp_order Θ Ξ A p ->
     feval_exp_order Θ Ξ (Π A B) p )
| feeo_indty :
  `( feval_exp_order Θ Ξ (a_ind pq k) p )
(** A constructor that is a value of its own before any argument *)
| feeo_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     im_starts D Mk = true ->
     feval_exp_order Θ Ξ (a_con pq k c) p )
(** A constructor of a view of a group with no uniform parameters: the
    view's arguments are evaluated *)
| feeo_con_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_nu D = 0 ->
     feval_exps_order Θ Ξ Is (env_args nil nil) ->
     feval_exp_order Θ Ξ (a_con pq j c) p )
(** The eliminator: its uniform parameters, its scrutinee, whose value
    names the group it eliminates by, and the elimination. *)
| feeo_elim :
  `( feval_exps_order Θ Ξ Us p ->
     feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> exists pq, elim_grp_of oq m = Some pq) ->
     (forall ups m pq, ⟦ Us ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ups -> ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> elim_grp_of oq m = Some pq ->
        feval_elim_order Θ Ξ p pq ups Bks j m) ->
     feval_exp_order Θ Ξ (a_elim oq Us j Bks M) p )
| feeo_fn :
  `( feval_exp_order Θ Ξ (λ A M) p )
| feeo_app :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ N p ->
     (forall m n, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> feval_app_order Θ Ξ m n) ->
     feval_exp_order Θ Ξ (M $ N) p )
| feeo_let :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> feval_exp_order Θ Ξ B (p ↦ m)) ->
     feval_exp_order Θ Ξ (a_let (b_def oA M) B) p )
| feeo_let_mod :
  `( feval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_exp_order Θ Ξ B (p ↦ᵐ h)) ->
     feval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
| feeo_mem :
  `( modexp_spine H = (R, args, pre) ->
     feval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     feval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> h ·ₜ*ᶠ (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
        ⟦ args ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ns -> feval_apps_order Θ Ξ f ns) ->
     feval_exp_order Θ Ξ (a_mem H x) p )
(** A record's type former is a value. *)
| feeo_record :
  `( feval_exp_order Θ Ξ (a_record pq) p )
(** A record element: the values of its fields *)
| feeo_tuple :
  `( feval_exps_order Θ Ξ (List.map snd fs) p ->
     feval_exp_order Θ Ξ (a_tuple T fs) p )
(** A field: the value, then the field of it *)
| feeo_proj :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> feval_proj_order Θ Ξ f m) ->
     feval_exp_order Θ Ξ (a_proj f M) p )

(** The field [f] of a value, as [feval_proj] reads it *)
with feval_proj_order (Θ : gdeps) (Ξ : gstack) : string -> domain -> Prop :=
(** Of a tuple with the field *)
| fepo_tuple :
  `( field_lookup vs f <> None ->
     feval_proj_order Θ Ξ f (d_tuple vs) )
(** Of a neutral of a record type with the field: the projections of the
    fields up to it, which reach it *)
| fepo_neut :
  `( record_lookup Θ Ξ pq = Some R ->
     field_index (record_fields R) f = Some k ->
     feval_nflds_order Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil ->
     (forall rs, feval_nflds Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil rs -> List.nth_error rs k <> None) ->
     feval_proj_order Θ Ξ f (⇑ (d_record pq ns) m) )

(** The neutral projections at a list of fields, as [feval_nflds] reads
    them *)
with feval_nflds_order (Θ : gdeps) (Ξ : gstack) : list domain -> domain_ne -> list (string * exp) -> list domain -> Prop :=
(** No field left *)
| feno_nil :
  `( feval_nflds_order Θ Ξ ns m nil pre )
(** The next field's type, then the rest after its projection *)
| feno_cons :
  `( feval_exp_order Θ Ξ T (env_args nil (ns ++ pre)) ->
     (forall a, ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ env_args nil (ns ++ pre) ↘ a ->
        feval_nflds_order Θ Ξ ns m fl (pre ++ ⇑ a (d_proj g m) :: nil)) ->
     feval_nflds_order Θ Ξ ns m ((g, T) :: fl) pre )

(** The eliminator of the group at [pq] at its member [j], on a value, as
    [feval_elim] reads it. *)
with feval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> Prop :=
(** On a saturated constructor: the recursive results the branch reads,
    then the branch *)
| feelo_con :
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
     feval_ihs_order Θ Ξ p pq ups Bks B gs (skipn (im_np Dq Mk) vs) ->
     (forall ihs, ⟦ihsᶠ skipn (im_np Dq Mk) vs of gs under pq ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs ->
        feval_exp_order Θ Ξ B (env_args p (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs) ++ skipn (im_np Dq Mk) vs ++ ihs))) ->
     feval_elim_order Θ Ξ p pq ups Bks j (d_con pc k c vs) )
(** On a neutral: the motive's instance *)
| feelo_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_ref pq j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_nm b = S (im_nn Mk) ->
     feval_exp_order Θ Ξ (eb_motive b) (env_args p (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil)) ->
     feval_elim_order Θ Ξ p pq ups Bks j (⇑ (d_ind pc k as') m) )

(** The recursive results of the arguments [vs] of kinds [gs], for the
    branch [B] *)
with feval_ihs_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> exp -> list carg -> list domain -> Prop :=
(** No argument *)
| feiho_nil :
  `( feval_ihs_order Θ Ξ p pq ups Bks B nil nil )
(** A non-recursive argument *)
| feiho_arg :
  `( feval_ihs_order Θ Ξ p pq ups Bks B gs vs ->
     feval_ihs_order Θ Ξ p pq ups Bks B (ca_arg T :: gs) (v :: vs) )
(** A recursive argument the branch reads: its result, then the rest *)
| feiho_rec :
  `( exp_freshb (cargs_nrec gs) B = false ->
     feval_ih_order Θ Ξ p pq ups Bks t v ->
     feval_ihs_order Θ Ξ p pq ups Bks B gs vs ->
     feval_ihs_order Θ Ξ p pq ups Bks B (ca_rec t :: gs) (v :: vs) )
(** One it does not read: the rest only *)
| feiho_skip :
  `( exp_freshb (cargs_nrec gs) B = true ->
     feval_ihs_order Θ Ξ p pq ups Bks B gs vs ->
     feval_ihs_order Θ Ξ p pq ups Bks B (ca_rec t :: gs) (v :: vs) )

(** The recursive result of an argument of a shape *)
with feval_ih_order (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> Prop :=
(** At the end: the eliminator at the member *)
| feio_self :
  `( feval_elim_order Θ Ξ p pq ups Bks j v ->
     feval_ih_order Θ Ξ p pq ups Bks (pt_self j Ps) v )
(** At a function shape: a closure *)
| feio_pi :
  `( feval_ih_order Θ Ξ p pq ups Bks (pt_pi B t) v )

(** The member a member of a group stands for, as [feval_mref] reads it *)
with feval_mref_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> nat -> Prop :=
(** A declared member *)
| femro_decl :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_decl pm ->
     feval_mref_order Θ Ξ pq ups j )
(** A view: the view's arguments at the uniform parameters *)
| femro_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     feval_exps_order Θ Ξ Is (env_args nil ups) ->
     feval_mref_order Θ Ξ pq ups j )

(** The type of an argument of a shape *)
with feval_shty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
(** At the end: the parameters, and the member stood for *)
| festo_self :
  `( feval_exps_order Θ Ξ Ps p ->
     feval_mref_order Θ Ξ pq ups j ->
     feval_shty_order Θ Ξ pq ups p (pt_self j Ps) )
(** At a domain *)
| festo_pi :
  `( feval_exp_order Θ Ξ B p ->
     feval_shty_order Θ Ξ pq ups p (pt_pi B t) )

(** The type of the recursive result of an argument of a shape *)
with feval_ihty_order (Θ : gdeps) (Ξ : gstack) : env -> list exp -> env -> ptyp -> domain -> Prop :=
(** At the end: the parameters, then the member's motive *)
| feityo_self :
  `( feval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ bs -> feval_exp_order Θ Ξ (List.nth j As a_True) (env_args pm (bs ++ v :: nil))) ->
     feval_ihty_order Θ Ξ pm As p (pt_self j Ps) v )
(** At a domain *)
| feityo_pi :
  `( feval_exp_order Θ Ξ B p ->
     feval_ihty_order Θ Ξ pm As p (pt_pi B t) v )

with feval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| feao_fn :
  `( feval_exp_order Θ Ξ M (p ↦ n) ->
     feval_app_order Θ Ξ λᵈ p M n )
| feao_neut :
  `( feval_exp_order Θ Ξ B (p ↦ n) ->
     feval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
| feao_indty :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     feval_app_order Θ Ξ (d_ind pq k as') n )
(** A constructor of a declared member *)
| feao_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length vs < (im_np D Mk + List.length gs)%nat ->
     feval_app_order Θ Ξ (d_con pq k c vs) n )
(** A constructor of a view, before its last uniform parameter *)
| feao_con_view :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) < ind_nu D ->
     feval_app_order Θ Ξ (d_con pq j c vs) n )
(** At its last uniform parameter: the view's arguments are evaluated *)
| feao_con_view_ups :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) = ind_nu D ->
     feval_exps_order Θ Ξ Is (env_args nil (vs ++ n :: nil)) ->
     feval_app_order Θ Ξ (d_con pq j c vs) n )
| feao_ihfn :
  `( feval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> feval_ih_order Θ Ξ p pq ups Bks t fn) ->
     feval_app_order Θ Ξ (d_ihfn p Bks pq ups t f) n )
| feao_shfam :
  `( feval_shty_order Θ Ξ pq ups (p ↦ n) t ->
     feval_app_order Θ Ξ (d_shfam pq ups p t) n )
| feao_ihfam :
  `( feval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> feval_ihty_order Θ Ξ pm As (p ↦ n) t fn) ->
     feval_app_order Θ Ξ (d_ihfam pm As p t f) n )
| feao_member :
  `( feval_appm_order Θ Ξ h n ->
     (forall h', $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' -> feval_selc_order Θ Ξ h' ch) ->
     feval_app_order Θ Ξ (d_member h ch) n )
(** A record's type former, before its last parameter *)
| feao_record :
  `( record_lookup Θ Ξ pq = Some R ->
     List.length ns < List.length (record_params R) ->
     feval_app_order Θ Ξ (d_record pq ns) n )

with feval_exps_order (Θ : gdeps) (Ξ : gstack) : list exp -> env -> Prop :=
| feso_nil :
  `( feval_exps_order Θ Ξ nil p )
| feso_cons :
  `( feval_exp_order Θ Ξ M p ->
     feval_exps_order Θ Ξ Ms p ->
     feval_exps_order Θ Ξ (M :: Ms) p )

with feval_apps_order (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> Prop :=
| feaso_nil :
  `( feval_apps_order Θ Ξ m nil )
| feaso_cons :
  `( feval_app_order Θ Ξ m n ->
     (forall m1, $ᶠ| m & n | Θ ⍮ Ξ ↘ m1 -> feval_apps_order Θ Ξ m1 args) ->
     feval_apps_order Θ Ξ m (n :: args) )

with feval_modexp_order (Θ : gdeps) (Ξ : gstack) : modexp -> env -> Prop :=
| femo_var :
  `( feval_modexp_order Θ Ξ (me_var x) p )
| femo_unit :
  `( feval_modexp_order Θ Ξ (me_unit fp) p )
| femo_lit :
  `( feval_close_order Θ Ξ Δ D p ->
     feval_modexp_order Θ Ξ (me_lit (gu_mk Δ D)) p )
| femo_mem :
  `( feval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selm_order Θ Ξ h y) ->
     feval_modexp_order Θ Ξ (me_mem H y) p )
| femo_app :
  `( feval_modexp_order Θ Ξ H p ->
     feval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> feval_appm_order Θ Ξ h n) ->
     feval_modexp_order Θ Ξ (me_app H N) p )

with feval_close_order (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> Prop :=
| feclo_body :
  `( feval_close_order Θ Ξ Δ (md_body sm Φ) p )
| feclo_alias :
  `( feval_close_order Θ Ξ (e :: Δ) (md_alias E) p )
| feclo_alias0 :
  `( feval_modexp_order Θ Ξ E p ->
     feval_close_order Θ Ξ nil (md_alias E) p )

with feval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| feapo_global :
  `( feval_appm_order Θ Ξ (dm_global pq args) n )
(** The outermost missing parameter is split off as the evaluator splits
    it off ([tele_snoc]), so that the order of the rest is a premise of the
    order of the whole. *)
| feapo_local :
  `( tele_snoc Δ = Some (Δ0, ce_ass A) ->
     feval_close_order Θ Ξ Δ0 D (p ↦ n) ->
     feval_appm_order Θ Ξ (dm_local Δ D p) n )
| feapo_member :
  `( feval_appm_order Θ Ξ h n ->
     (forall h', $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' -> feval_selmc_order Θ Ξ h' ch) ->
     feval_appm_order Θ Ξ (dm_member h ch) n )

with feval_appms_order (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> Prop :=
| feamo_nil :
  `( feval_appms_order Θ Ξ h nil )
| feamo_cons :
  `( feval_appm_order Θ Ξ h n ->
     (forall h1, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h1 -> feval_appms_order Θ Ξ h1 ns) ->
     feval_appms_order Θ Ξ h (n :: ns) )

with feval_sel_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| feslo_global :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def true pv A (Some M)) ->
     feval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f -> feval_apps_order Θ Ξ f args) ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_global_neut :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     feval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ a -> feval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_global_ind :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app pq (x :: nil)) = Some (pg, k, D) ->
     feval_apps_order Θ Ξ (d_ind pg k nil) args ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_global_ind_alias :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_alias_lookup Θ Ξ (qname_app pq (x :: nil)) = Some (Δ, pm, pt, k, Ns) ->
     feval_exp_order Θ Ξ (ctx_fn Δ (apps (a_ind pt k) Ns)) nil ->
     (forall f, ⟦ ctx_fn Δ (apps (a_ind pt k) Ns) ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f -> feval_apps_order Θ Ξ f args) ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_unsat :
  `( feval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
| feslo_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     feval_benv_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_exp_order Θ Ξ M p') ->
     feval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
| feslo_member :
  `( feval_sel_order Θ Ξ (dm_member h ch) x )
(** A record type of a global module, not a definition: its type former,
    applied to the arguments *)
| feslo_global_record :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     record_lookup Θ Ξ (qname_app pq (x :: nil)) = Some R ->
     feval_apps_order Θ Ξ (d_record (qname_app pq (x :: nil)) nil) args ->
     feval_sel_order Θ Ξ (dm_global pq args) x )

with feval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| fesmo_global :
  `( gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     feval_selm_order Θ Ξ (dm_global pq args) y )
| fesmo_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     feval_close_order Θ Ξ Δ D nil ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ nil ↘ h -> feval_appms_order Θ Ξ h args) ->
     feval_selm_order Θ Ξ (dm_global pq args) y )
| fesmo_unsat :
  `( feval_selm_order Θ Ξ (dm_local (e :: Δ) D p) y )
| fesmo_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm (gu_mk Δy Dy))) ->
     feval_benv_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_close_order Θ Ξ Δy Dy p') ->
     feval_selm_order Θ Ξ (dm_local nil (md_body sm Φ) p) y )
| fesmo_member :
  `( feval_selm_order Θ Ξ (dm_member h ch) y )

with feval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fesco_one :
  `( feval_sel_order Θ Ξ h x ->
     feval_selc_order Θ Ξ h (x :: nil) )
| fesco_cons :
  `( feval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 -> feval_selc_order Θ Ξ h1 (z :: ch)) ->
     feval_selc_order Θ Ξ h (y :: z :: ch) )

with feval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fesmco_nil :
  `( feval_selmc_order Θ Ξ h nil )
| fesmco_cons :
  `( feval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 -> feval_selmc_order Θ Ξ h1 ch) ->
     feval_selmc_order Θ Ξ h (y :: ch) )

with feval_benv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| febo_nil :
  `( feval_benv_order Θ Ξ p gm_nil )
| febo_def :
  `( feval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> feval_exp_order Θ Ξ M p1) ->
     feval_benv_order Θ Ξ p (gm_ext Φ y (ge_def b pv A (Some M))) )
| febo_mod :
  `( feval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> feval_close_order Θ Ξ Δy Dy p1) ->
     feval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) ).

#[local]
Hint Constructors feval_exp_order feval_elim_order feval_ihs_order feval_ih_order feval_mref_order feval_shty_order feval_ihty_order feval_app_order feval_exps_order feval_apps_order
  feval_modexp_order feval_close_order feval_appm_order feval_appms_order feval_sel_order feval_selm_order feval_selc_order feval_selmc_order
  feval_benv_order feval_proj_order feval_nflds_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_feval_all :=
  repeat match goal with
    | H1 : feval_exp ?T ?X ?M ?p ?m1, H2 : feval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_feval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_app ?T ?X ?m ?n ?r1, H2 : feval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_exps ?T ?X ?M ?p ?r1, H2 : feval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (@functional_feval T X))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_apps ?T ?X ?m ?n ?r1, H2 : feval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_feval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_modexp ?T ?X ?M ?p ?r1, H2 : feval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_close ?T ?X ?Δ ?D ?p ?r1, H2 : feval_close ?T ?X ?Δ ?D ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))) _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_appm ?T ?X ?m ?n ?r1, H2 : feval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_appms ?T ?X ?m ?n ?r1, H2 : feval_appms ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : kbody ?T ?X ?p ?Φ ?r1, H2 : kbody ?T ?X ?p ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_kbody _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_sel ?T ?X ?m ?n ?r1, H2 : feval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selm ?T ?X ?m ?n ?r1, H2 : feval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selc ?T ?X ?m ?n ?r1, H2 : feval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selmc ?T ?X ?m ?n ?r1, H2 : feval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_benv ?T ?X ?m ?n ?r1, H2 : feval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_benv _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_elim ?T ?X ?p ?pg ?u ?Bs ?j ?m ?r1, H2 : feval_elim ?T ?X ?p ?pg ?u ?Bs ?j ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_elim _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_ihs ?T ?X ?p ?pg ?u ?Bs ?B ?gs ?vs ?r1, H2 : feval_ihs ?T ?X ?p ?pg ?u ?Bs ?B ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_ihs _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_ih ?T ?X ?p ?pg ?u ?Bs ?t ?v ?r1, H2 : feval_ih ?T ?X ?p ?pg ?u ?Bs ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_ih _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_mref ?T ?X ?pg ?u ?j ?r1, H2 : feval_mref ?T ?X ?pg ?u ?j ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_mref _ _ _ _ _ H1 H2); subst; clear H2
    | H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst
    | H1 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_shty _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r1, H2 : feval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_ihty _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : kgens ?T ?X ?p ?E ?its ?g1, H2 : kgens ?T ?X ?p ?E ?its ?g2 |- _ =>
        assert_fails (constr_eq g1 g2);
        pose proof (functional_kgens _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    | H1 : feval_proj ?T ?X ?f ?m ?r1, H2 : feval_proj ?T ?X ?f ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_proj _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_nflds ?T ?X ?ns ?m ?fl ?pre ?r1, H2 : feval_nflds ?T ?X ?ns ?m ?fl ?pre ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_nflds _ _ _ _ _ _ H1 H2); subst; clear H2
    end.

Lemma feval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_exp_order Θ Ξ m p) /\
    (forall m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> feval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> feval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*ᶠ| m & ns | Θ ⍮ Ξ ↘ r -> feval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_modexp_order Θ Ξ H p) /\
    (forall Δ D p h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_close_order Θ Ξ Δ D p) /\
    (forall h n r, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r -> feval_appm_order Θ Ξ h n) /\
    (forall h ns r, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r -> feval_appms_order Θ Ξ h ns) /\
    (forall h x r, h ·ₜᶠ x Θ ⍮ Ξ ↘ r -> feval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘᶠ y Θ ⍮ Ξ ↘ r -> feval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r -> feval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r -> feval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_benv_order Θ Ξ p Φ) /\
    (forall p pq ups Bks j m r, ⟦elimᶠ m at j of pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> feval_elim_order Θ Ξ p pq ups Bks j m) /\
    (forall p pq ups Bks B gs vs ihs, ⟦ihsᶠ vs of gs under pq ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs ->
       feval_ihs_order Θ Ξ p pq ups Bks B gs vs) /\
    (forall p pq ups Bks t v r, ⟦ihᶠ v of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> feval_ih_order Θ Ξ p pq ups Bks t v) /\
    (forall pq ups j r, ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ r -> feval_mref_order Θ Ξ pq ups j) /\
    (forall pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_shty_order Θ Ξ pq ups p t) /\
    (forall pm As p t v a, ⟦ihtyᶠ v of t under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_ihty_order Θ Ξ pm As p t v) /\
    (forall f m r, feval_proj Θ Ξ f m r -> feval_proj_order Θ Ξ f m) /\
    (forall ns m fl pre rs, feval_nflds Θ Ξ ns m fl pre rs -> feval_nflds_order Θ Ξ ns m fl pre).
Proof.
  intros Θ Ξ; apply feval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : feval_selc _ _ _ ?c _ |- feval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    solve [ eapply feslo_global_neut; eauto; intros; functional_feval_all; eauto
          | econstructor; try eassumption; intros; functional_feval_all; eauto using kgens_order_sound, tele_snoc_app
          (** The projections of a neutral reach the field projected. *)
          | econstructor; try eassumption; intros; functional_feval_all; congruence
          (** The eliminator: the group the scrutinee's value names, once. *)
          | econstructor; try eassumption; intros; functional_feval_all;
            first [ eexists; eassumption
                  | match goal with H1 : elim_grp_of ?o ?m = Some _, H2 : elim_grp_of ?o ?m = Some _ |- _ =>
                      rewrite H1 in H2; injection H2 as <-; assumption end ] ].
Qed.

Lemma feval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (feval_order_sound Θ Ξ)). Qed.

Lemma feval_app_order_sound : forall Θ Ξ m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> feval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (feval_order_sound Θ Ξ))). Qed.

Lemma feval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> feval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (feval_order_sound Θ Ξ)))). Qed.

Lemma feval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (feval_order_sound Θ Ξ)))))). Qed.

Lemma feval_shty_order_sound : forall Θ Ξ pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_shty_order Θ Ξ pq ups p t.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma feval_ihty_order_sound : forall Θ Ξ pm A p t v a, ⟦ihtyᶠ v of t under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_ihty_order Θ Ξ pm A p t v.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma feval_ih_order_sound : forall Θ Ξ p pq ups Bks t v r, ⟦ihᶠ v of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r ->
    feval_ih_order Θ Ξ p pq ups Bks t v.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma feval_mref_order_sound : forall Θ Ξ pq ups j r, ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ r -> feval_mref_order Θ Ξ pq ups j.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma feval_proj_order_sound : forall Θ Ξ f m r, feval_proj Θ Ξ f m r -> feval_proj_order Θ Ξ f m.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve feval_exp_order_sound feval_app_order_sound feval_exps_order_sound feval_modexp_order_sound
  feval_shty_order_sound feval_ihty_order_sound feval_ih_order_sound feval_mref_order_sound
  feval_proj_order_sound : mctt.

(** The member a member stands for is the one [im_ref] names. *)
Lemma feval_mref_im_ref : forall Θ Ξ p ups j pc k pre D Mj,
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
    arguments and the recursive results ([feval_elim_con]), the member
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
  Context {F : FCtx Θ Ξ}.


  (** A variable is looked up in the environment, without recursion. *)
  Definition feval_var_impl x p (H : feval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply feval_exp_var.
  Defined.



  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : feval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_close_order _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_appms_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_benv_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_elim_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_mref_order _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_shty_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_ihty_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_proj_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_nflds_order _ _ _ _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
      | H : gc_entry _ _ _ = Some (ge_def _ _ _ _) |- _ => apply gc_entry_def in H
      | H : gc_entry _ _ _ = Some (ge_ind _ _ _ _ _) |- _ =>
          let H1 := fresh "Hr" in let H2 := fresh "Hl" in destruct (gc_entry_ind _ _ _ _ _ _ _ _ H) as [H1 H2]; clear H
      | H : gc_entry ?T ?X ?p = _, H' : gc_resolve ?T ?X ?p = Some (ge_def _ _ _ _) |- _ =>
          apply gc_entry_def in H'; rewrite H in H'; discriminate H'
      | H : gc_entry ?T ?X ?p = _, H' : ind_mlookup ?T ?X ?p = Some _ |- _ =>
          let He := fresh "He" in destruct (ind_mlookup_entry _ _ _ _ _ _ H') as (? & ? & He); rewrite H in He; discriminate He
      | H : gc_entry _ _ _ = Some (ge_ind_alias _ _ _ _ _ _) |- _ =>
          let H1 := fresh "Hr" in let H2 := fresh "Ha" in destruct (gc_entry_ind_alias _ _ _ _ _ _ _ _ _ H) as [H1 H2]; clear H
      | H : gc_entry ?T ?X ?p = _, H' : ind_alias_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite ind_alias_lookup_entry, H in H'; cbn in H'; discriminate H'
      | H1 : ind_alias_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_alias_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (ind_lookup_not_ind_alias _ _ _ _ H1) in H2; discriminate H2
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
      | H1 : ind_mlookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (ind_mlookup_not_ind_alias _ _ _ _ H1) in H2; discriminate H2
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
      | H1 : record_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (record_lookup_not_ind_alias _ _ _ _ H1) in H2; discriminate H2
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
      | H : forall m, feval_exp _ _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : feval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      (** The eliminator's scrutinee names a group. *)
      | H : forall m, feval_exp _ _ ?M ?p m -> exists _, elim_grp_of _ m = Some _, Hm : feval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ?); clear H
      (** The projections of a neutral reach the field projected. *)
      | H : forall rs, feval_nflds _ _ ?ns ?m ?fl ?pre rs -> _, Hm : feval_nflds _ _ ?ns ?m ?fl ?pre _ |- _ =>
          specialize (H _ Hm)
      end.

  #[local]
  Ltac impl_obl_split :=
    match goal with
    | H : feval_exp_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_close_order _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_appms_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_benv_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_elim_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_mref_order _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_shty_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_ihty_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_proj_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_nflds_order _ _ _ _ _ _ |- _ => dependent destruction H
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
    try solve [ eapply feval_sel_global_neut; eauto ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
    try solve [ eauto ];
    try econstructor; eauto.


  #[local]
  Ltac ev_obl :=
    intros; cbv beta in *;
    rewrite ?elim_env_eq in *;
    repeat impl_obl_tac1;
    first [ solve [ impl_obl_finish ]
          | solve [ impl_obl_split; impl_obl_finish ]
          | impl_obl_finish ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations feval_exp_impl m p (H : feval_exp_order Θ Ξ m p) : { d | ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | Typeω@i, p, H => exist _ 𝕌ω@i _
  | Type⟨M⟩, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      exist _ 𝕌@m _
  | #x    , p, H => feval_var_impl x p H
  | Level@n, p, H => exist _ (Levelᵈ@n) _
  | 𝕃ᵒ o  , p, H => exist _ (dlvl_lit o) _
  | succl M, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      exist _ (dlvl_suc m) _
  | maxl M N, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      let (n , Hn) := feval_exp_impl N p _ in
      exist _ (dlvl_max m n) _
  | ⊤     , p, H => exist _ ⊤ᵈ _
  | ⋆     , p, H => exist _ ⋆ᵈ _
  | ⊥     , p, H => exist _ ⊥ᵈ _
  | efq M return A, p, H with feval_exp_impl M p _ := {
    | exist _ (⇑ b m) Hm =>
        let (a, Ha) := feval_exp_impl A (p ↦ ⇑ b m) _ in
        exist _ ⇑ a (efqᵈ m under p return A) _
    | exist _ _ Hm => False_rect _ _ }
  | Π A B , p, H =>
      let (r , Hr) := feval_exp_impl A p _ in
      exist _ Πᵈ r p B _
  | λ A M , p, H => exist _ λᵈ p M _
  | a_ind pq k, p, H => exist _ (d_ind pq k nil) _
  | a_con pq k c, p, H with cache_lookup Θ Ξ (@fc_seed Θ Ξ F) pq := {
    | exist _ (Some D) Ed with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_starts D Mk) := {
        | exist _ true Es => exist _ (d_con pq k c nil) _
        | exist _ false Es with inspect (im_head Mk) := {
          | exist _ (mh_view qc k' Is vm) Eh =>
              let (cups, Hc) := feval_exps_impl Is (env_args nil nil) _ in
              exist _ (d_con qc k' c cups) _
          | exist _ (mh_decl _) Eh => False_rect _ _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  (** A literal is generated before it is ever evaluated. *)
  | a_ntok, p, H => False_rect _ _
  | a_nlit _, p, H => False_rect _ _
  | a_elim oq Us j Bks M, p, H with feval_exps_impl Us p _ := {
    | exist _ ups Hups with feval_exp_impl M p _ := {
      | exist _ m Hm with inspect (elim_grp_of oq m) := {
        | exist _ (Some pq) Eg =>
            let (r, Hr) := feval_elim_impl p pq ups Bks j m (@fc_seed Θ Ξ F) _ in
            exist _ r _
        | exist _ None Eg => False_rect _ _ } } }
  | M $ N   , p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      let (n , Hn) := feval_exp_impl N p _ in
      let (a, Ha) := feval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (r, Hr) := feval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | a_let (b_mod (gu_mk Δ D)) B, p, H =>
      let (h, Hh) := feval_close_impl Δ D p _ in
      let (r, Hr) := feval_exp_impl B (p ↦ᵐ h) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := feval_modexp_impl R p _ in
        let (f, Hf) := feval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := feval_exps_impl args p _ in
        let (r, Hr) := feval_apps_impl f ns _ in
        exist _ r _ }
  | a_record pq, p, H => exist _ (d_record pq nil) _
  | a_tuple T fs, p, H =>
      let (vs, Hvs) := feval_exps_impl (List.map snd fs) p _ in
      exist _ (d_tuple (List.combine (List.map fst fs) vs)) _
  | a_proj f M, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (r, Hr) := feval_proj_impl f m _ in
      exist _ r _

  with feval_proj_impl f m (H : feval_proj_order Θ Ξ f m) : { r | feval_proj Θ Ξ f m r } by struct H :=
  | f, d_tuple vs, H with inspect (field_lookup vs f) := {
    | exist _ (Some r) E => exist _ r _
    | exist _ None E => False_rect _ _ }
  | f, ⇑ (d_record pq ns) m, H with inspect (record_lookup Θ Ξ pq) := {
    | exist _ (Some R) El with inspect (field_index (record_fields R) f) := {
      | exist _ (Some k) Ek with feval_nflds_impl ns m (List.firstn (S k) (record_fields R)) nil _ := {
        | exist _ rs Hrs with inspect (List.nth_error rs k) := {
          | exist _ (Some r) Er => exist _ r _
          | exist _ None Er => False_rect _ _ } }
      | exist _ None Ek => False_rect _ _ }
    | exist _ None El => False_rect _ _ }
  | f, _, H => False_rect _ _

  with feval_nflds_impl ns m fl pre (H : feval_nflds_order Θ Ξ ns m fl pre) :
      { rs | feval_nflds Θ Ξ ns m fl pre rs } by struct H :=
  | ns, m, nil, pre, H => exist _ nil _
  | ns, m, (g, T) :: fl, pre, H =>
      let (a, Ha) := feval_exp_impl T (env_args nil (ns ++ pre)) _ in
      let (rs, Hrs) := feval_nflds_impl ns m fl (pre ++ ⇑ a (d_proj g m) :: nil) _ in
      exist _ (⇑ a (d_proj g m) :: rs) _

  (** The group of the eliminator is looked up through the cache [ck], and
      passed on as the cache of the container's lookup and of the
      recursive results: a lookup of the same name is a comparison. *)
  with feval_elim_impl p pq ups Bks j m (ck : lk_cache Θ Ξ) (H : feval_elim_order Θ Ξ p pq ups Bks j m) :
      { r | ⟦elimᶠ m at j of pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, pq, ups, Bks, j, d_con pc k c vs, ck, H with cache_lookup Θ Ξ ck pq := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with cache_lookup Θ Ξ (Some (exist _ (pq, D) Ed)) pc := {
        | exist _ (Some Dq) Edq with inspect (ind_member Dq k) := {
          | exist _ (Some Mk) Emk with inspect (ind_con Mj c) := {
            | exist _ (Some gs) Ec with inspect (List.nth_error Bks j) := {
              | exist _ (Some b) Eb with inspect (brs_lookup (eb_brs b) c) := {
                | exist _ (Some (n, B)) Ebr =>
                    let (ihs, Hihs) := feval_ihs_impl p pq ups Bks B gs (skipn (im_np Dq Mk) vs) (Some (exist _ (pq, D) Ed)) _ in
                    let (r, Hr) := feval_exp_impl B (elim_env p Dq Mk vs ihs) _ in
                    exist _ r _
                | exist _ None Ebr => False_rect _ _ }
              | exist _ None Eb => False_rect _ _ }
            | exist _ None Ec => False_rect _ _ }
          | exist _ None Emk => False_rect _ _ }
        | exist _ None Edq => False_rect _ _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | p, pq, ups, Bks, j, ⇑ (d_ind pc k as') m, ck, H with cache_lookup Θ Ξ ck pc := {
    | exist _ (Some Dq) Edq with inspect (List.nth_error Bks j) := {
      | exist _ (Some b) Eb =>
          let (a, Ha) := feval_exp_impl (eb_motive b) (env_args p (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil)) _ in
          exist _ (⇑ a (d_elim p Bks pq ups j as' m)) _
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Edq => False_rect _ _ }
  | p, pq, ups, Bks, j, _, ck, H => False_rect _ _

  with feval_ihs_impl p pq ups Bks B gs vs (ck : lk_cache Θ Ξ) (H : feval_ihs_order Θ Ξ p pq ups Bks B gs vs) :
      { ihs | ⟦ihsᶠ vs of gs under pq ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs } by struct H :=
  | p, pq, ups, Bks, B, nil, nil, ck, H => exist _ nil _
  | p, pq, ups, Bks, B, ca_arg T :: gs, v :: vs, ck, H =>
      let (ihs, Hihs) := feval_ihs_impl p pq ups Bks B gs vs ck _ in
      exist _ ihs _
  | p, pq, ups, Bks, B, ca_rec t :: gs, v :: vs, ck, H with inspect (exp_freshb (cargs_nrec gs) B) := {
    (** The branch does not read the recursive result: it is not
        computed. *)
    | exist _ true E =>
        let (ihs, Hihs) := feval_ihs_impl p pq ups Bks B gs vs ck _ in
        exist _ (𝕌ω@0 :: ihs) _
    | exist _ false E =>
        let (ih, Hih) := feval_ih_impl p pq ups Bks t v ck _ in
        let (ihs, Hihs) := feval_ihs_impl p pq ups Bks B gs vs ck _ in
        exist _ (ih :: ihs) _ }
  | p, pq, ups, Bks, B, _, _, ck, H => False_rect _ _

  with feval_ih_impl p pq ups Bks t v (ck : lk_cache Θ Ξ) (H : feval_ih_order Θ Ξ p pq ups Bks t v) :
      { r | ⟦ihᶠ v of t under pq ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, pq, ups, Bks, pt_self j Ps, v, ck, H =>
      let (r, Hr) := feval_elim_impl p pq ups Bks j v ck _ in
      exist _ r _
  | p, pq, ups, Bks, pt_pi B t, v, ck, H => exist _ (d_ihfn p Bks pq ups t v) _

  with feval_mref_impl pq ups j (H : feval_mref_order Θ Ξ pq ups j) : { r | ⟦mrefᶠ j of pq ups ⟧ᶠ Θ ⍮ Ξ ↘ r } by struct H :=
  | pq, ups, j, H with cache_lookup Θ Ξ (@fc_seed Θ Ξ F) pq := {
    | exist _ (Some D) Ed with inspect (ind_member D j) := {
      | exist _ (Some Mj) Em with inspect (im_head Mj) := {
        | exist _ (mh_decl _) Eh => exist _ (pq, j, ups) _
        | exist _ (mh_view qc k Is vm) Eh =>
            let (cups, Hc) := feval_exps_impl Is (env_args nil ups) _ in
            exist _ (qc, k, cups) _ }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }

  with feval_shty_impl pq ups p t (H : feval_shty_order Θ Ξ pq ups p t) : { a | ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pq, ups, p, pt_self j Ps, H with feval_exps_impl Ps p _ := {
    | exist _ bs Hbs with feval_mref_impl pq ups j _ := {
      | exist _ (pc, k, pre) Hm => exist _ (d_ind pc k (pre ++ bs)) _ } }
  | pq, ups, p, pt_pi B t, H =>
      let (b, Hb) := feval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_shfam pq ups p t) fam_cod) _

  with feval_ihty_impl pm As p t v (H : feval_ihty_order Θ Ξ pm As p t v) : { a | ⟦ihtyᶠ v of t under pm As ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pm, As, p, pt_self j Ps, v, H =>
      let (bs, Hbs) := feval_exps_impl Ps p _ in
      let (a, Ha) := feval_exp_impl (List.nth j As a_True) (env_args pm (bs ++ v :: nil)) _ in
      exist _ a _
  | pm, As, p, pt_pi B t, v, H =>
      let (b, Hb) := feval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_ihfam pm As p t v) fam_cod) _

  with feval_app_impl m n (H : feval_app_order Θ Ξ m n) : { d | $ᶠ| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | λᵈ p M        , n, H =>
      let (m, Hm) := feval_exp_impl M (p ↦ n) _ in
      exist _ m _
  | ⇑ (Πᵈ a p B) m, n, H =>
      let (b, Hb) := feval_exp_impl B (p ↦ n) _ in
      exist _ ⇑ b (m $ᵈ ⇓ a n) _
  | d_member h ch, n, H =>
      let (h', Hh') := feval_appm_impl h n _ in
      let (r, Hr) := feval_selc_impl h' ch _ in
      exist _ r _
  | d_ind pq k as', n, H => exist _ (d_ind pq k (as' ++ n :: nil)) _
  | d_con pq k c vs, n, H with cache_lookup Θ Ξ (@fc_seed Θ Ξ F) pq := {
    | exist _ (Some D) Ed with inspect (ind_member D k) := {
      | exist _ (Some Mk) Em with inspect (im_head Mk) := {
        | exist _ (mh_decl _) Eh => exist _ (d_con pq k c (vs ++ n :: nil)) _
        | exist _ (mh_view qc k' Is vm) Eh with inspect (S (List.length vs) <? ind_nu D) := {
          | exist _ true El => exist _ (d_con pq k c (vs ++ n :: nil)) _
          | exist _ false El =>
              let (cups, Hc) := feval_exps_impl Is (env_args nil (vs ++ n :: nil)) _ in
              exist _ (d_con qc k' c cups) _ } }
      | exist _ None Em => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | d_ihfn p Bks pq ups t f, n, H =>
      let (fn, Hfn) := feval_app_impl f n _ in
      let (r, Hr) := feval_ih_impl p pq ups Bks t fn (@fc_seed Θ Ξ F) _ in
      exist _ r _
  | d_shfam pq ups p t, n, H =>
      let (a, Ha) := feval_shty_impl pq ups (p ↦ n) t _ in
      exist _ a _
  | d_ihfam pm As p t f, n, H =>
      let (fn, Hfn) := feval_app_impl f n _ in
      let (a, Ha) := feval_ihty_impl pm As (p ↦ n) t fn _ in
      exist _ a _
  | d_record pq ns, n, H => exist _ (d_record pq (ns ++ n :: nil)) _
  | _, n, H => False_rect _ _

  with feval_exps_impl Ms p (H : feval_exps_order Θ Ξ Ms p) : { ms | ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (ms, Hms) := feval_exps_impl Ms p _ in
      exist _ (m :: ms) _

  with feval_apps_impl m ns (H : feval_apps_order Θ Ξ m ns) : { r | $*ᶠ| m & ns | Θ ⍮ Ξ ↘ r } by struct H :=
  | m, nil, H => exist _ m _
  | m, n :: ns, H =>
      let (m1, Hm1) := feval_app_impl m n _ in
      let (r, Hr) := feval_apps_impl m1 ns _ in
      exist _ r _

  with feval_modexp_impl M p (H : feval_modexp_order Θ Ξ M p) : { h | ⟦ M ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | me_var x, p, H => exist _ (env_mod p x) _
  | me_unit fp, p, H => exist _ (dm_global (q_abs fp nil) nil) _
  | me_lit (gu_mk Δ D), p, H =>
      let (h, Hh) := feval_close_impl Δ D p _ in
      exist _ h _
  | me_mem M y, p, H =>
      let (h, Hh) := feval_modexp_impl M p _ in
      let (r, Hr) := feval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := feval_modexp_impl M p _ in
      let (n, Hn) := feval_exp_impl N p _ in
      let (r, Hr) := feval_appm_impl h n _ in
      exist _ r _

  with feval_close_impl Δ D p (H : feval_close_order Θ Ξ Δ D p) : { h | ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | Δ, md_body sm Φ, p, H => exist _ (dm_local Δ (md_body sm Φ) p) _
  | nil, md_alias E, p, H =>
      let (h, Hh) := feval_modexp_impl E p _ in
      exist _ h _
  | e :: Δ, md_alias E, p, H => exist _ (dm_local (e :: Δ) (md_alias E) p) _

  with feval_appm_impl h n (H : feval_appm_order Θ Ξ h n) : { r | $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local Δ D p, n, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass A)) Es =>
        let (r, Hr) := feval_close_impl Δ0 D (p ↦ n) _ in
        exist _ r _
    | exist _ _ Es => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := feval_appm_impl h n _ in
      let (r, Hr) := feval_selmc_impl h' ch _ in
      exist _ r _

  with feval_appms_impl h ns (H : feval_appms_order Θ Ξ h ns) : { r | $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r } by struct H :=
  | h, nil, H => exist _ h _
  | h, n :: ns, H =>
      let (h1, Hh1) := feval_appm_impl h n _ in
      let (r, Hr) := feval_appms_impl h1 ns _ in
      exist _ r _

  with feval_sel_impl h x (H : feval_sel_order Θ Ξ h x) : { r | h ·ₜᶠ x Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, x, H with gc_entry_f Θ Ξ (qname_app pq (x :: nil)) := {
    | exist _ (Some (ge_def true pv A (Some M))) E =>
        let (f, Hf) := feval_exp_impl M nil _ in
        let (r, Hr) := feval_apps_impl f args _ in
        exist _ r _
    | exist _ (Some (ge_def true _ A None)) E =>
        let (a, Ha) := feval_exp_impl A nil _ in
        let (r, Hr) := feval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_def false _ A B)) E =>
        let (a, Ha) := feval_exp_impl A nil _ in
        let (r, Hr) := feval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_mod _ _)) E with inspect (ind_mlookup Θ Ξ (qname_app pq (x :: nil))) := {
      | exist _ (Some (pg, k, D)) El =>
          let (r, Hr) := feval_apps_impl (d_ind pg k nil) args _ in
          exist _ r _
      | exist _ None El => False_rect _ _ }
    | exist _ (Some (ge_ind _ pg k D _)) E =>
        let (r, Hr) := feval_apps_impl (d_ind pg k nil) args _ in
        exist _ r _
    | exist _ (Some (ge_ind_alias _ Δ _ pt k Ns)) E =>
        let (f, Hf) := feval_exp_impl (ctx_fn Δ (apps (a_ind pt k) Ns)) nil _ in
        let (r, Hr) := feval_apps_impl f args _ in
        exist _ r _
    (** A stored record type: its type former *)
    | exist _ (Some (ge_record _ _ _ _)) E with inspect (record_lookup Θ Ξ (qname_app pq (x :: nil))) := {
      | exist _ (Some R) Er =>
          let (r, Hr) := feval_apps_impl (d_record (qname_app pq (x :: nil)) nil) args _ in
          exist _ r _
      | exist _ None Er => False_rect _ _ }
    (** The open frame of a member's module or of a record type's module:
        its type former *)
    | exist _ None E with inspect (ind_mlookup Θ Ξ (qname_app pq (x :: nil))) := {
      | exist _ (Some (pg, k, D)) El =>
          let (r, Hr) := feval_apps_impl (d_ind pg k nil) args _ in
          exist _ r _
      | exist _ None El with inspect (record_lookup Θ Ξ (qname_app pq (x :: nil))) := {
        | exist _ (Some R) Er =>
            let (r, Hr) := feval_apps_impl (d_record (qname_app pq (x :: nil)) nil) args _ in
            exist _ r _
        | exist _ None Er => False_rect _ _ } } }
  | dm_local (e :: Δ) D p, x, H => exist _ (d_member (dm_local (e :: Δ) D p) (x :: nil)) _
  | dm_local nil (md_alias E) p, x, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, x, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def b pv A (Some M)))) P =>
          let (p', Hp') := feval_benv_impl p Φ' _ in
          let (r, Hr) := feval_exp_impl M p' _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ } }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with feval_selm_impl h y (H : feval_selm_order Θ Ξ h y) : { r | h ·ₘᶠ y Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, y, H with gc_module_f Θ Ξ (qname_app pq (y :: nil)) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh) := feval_close_impl Δ D nil _ in
        let (r, Hr) := feval_appms_impl h args _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local (e :: Δ) D p, y, H => exist _ (dm_member (dm_local (e :: Δ) D p) (y :: nil)) _
  | dm_local nil (md_alias E) p, y, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, y, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx y) := {
      | exist _ (Some (gm_ext Φ' _ (ge_mod pm (gu_mk Δy Dy)))) P =>
          let (p', Hp') := feval_benv_impl p Φ' _ in
          let (r, Hr) := feval_close_impl Δy Dy p' _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ } }
  | dm_member h ch, y, H => exist _ (dm_member h (ch ++ y :: nil)) _

  with feval_selc_impl h ch (H : feval_selc_order Θ Ξ h ch) : { r | h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r } by struct H :=
  | h, x :: nil, H =>
      let (r, Hr) := feval_sel_impl h x _ in
      exist _ r _
  | h, y :: ch, H =>
      let (h1, Hh1) := feval_selm_impl h y _ in
      let (r, Hr) := feval_selc_impl h1 ch _ in
      exist _ r _
  | h, nil, H => False_rect _ _

  with feval_selmc_impl h ch (H : feval_selmc_order Θ Ξ h ch) : { r | h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r } by struct H :=
  | h, nil, H => exist _ h _
  | h, y :: ch, H =>
      let (h1, Hh1) := feval_selm_impl h y _ in
      let (r, Hr) := feval_selmc_impl h1 ch _ in
      exist _ r _

  with feval_benv_impl p Φ (H : feval_benv_order Θ Ξ p Φ) : { p' | ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y (ge_def b pv A (Some M)), H =>
      let (p1, Hp1) := feval_benv_impl p Φ _ in
      let (m, Hm) := feval_exp_impl M p1 _ in
      exist _ (p1 ↦ m) _
  | p, gm_ext Φ y (ge_def b pv A None), H => False_rect _ _
  | p, gm_ext Φ y (ge_mod _ (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := feval_benv_impl p Φ _ in
      let (h, Hh) := feval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵐ h) _
  | p, gm_open Φ E its, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([ev_obl]).  They are transparent: the order premises are the
    arguments of the structural recursion. *)
Solve All Obligations with ev_obl.
End EvalImpl.

Extraction Inline feval_exp_impl_functional
  feval_elim_impl_functional
  feval_ihs_impl_functional
  feval_ih_impl_functional
  feval_mref_impl_functional
  feval_shty_impl_functional
  feval_ihty_impl_functional
  feval_app_impl_functional
  feval_exps_impl_functional
  feval_apps_impl_functional
  feval_modexp_impl_functional
  feval_close_impl_functional
  feval_appm_impl_functional
  feval_appms_impl_functional
  feval_sel_impl_functional
  feval_selm_impl_functional
  feval_selc_impl_functional
  feval_selmc_impl_functional
  feval_benv_impl_functional.

(** The [feval_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the evaluation orders and the functionality
    of evaluation. *)

#[local]
Ltac functional_feval_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_feval_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma feval_exp_impl_complete : forall Θ Ξ {F : FCtx Θ Ξ} M p m,
    ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m ->
    exists H H', feval_exp_impl Θ Ξ M p H = exist _ m H'.
Proof.
  intros; functional_feval_complete.
Qed.

Lemma feval_app_impl_complete : forall Θ Ξ {F : FCtx Θ Ξ} m n r,
    $ᶠ| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', feval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_feval_complete.
Qed.
