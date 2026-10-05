From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import GlobalCtx Members.
From Mctt.Core.Semantic Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

(** The termination orders mirror the evaluation relations, one for each, in
    the same global context.  An unsealed constant recurses into its body,
    which is closed; an alias recurses into its target.  Each premise that
    uses a value is quantified over the values its earlier premises evaluate
    to. *)

Inductive eval_exp_order (Θ : gctx) : exp -> env -> Prop :=
| eeo_typ :
  `( eval_exp_order Θ Type@i p )
(** An environment is total, so a variable always terminates. *)
| eeo_var :
  `( eval_exp_order Θ #x p )
| eeo_nat :
  `( eval_exp_order Θ ℕ p )
| eeo_zero :
  `( eval_exp_order Θ zero p )
| eeo_succ :
  `( eval_exp_order Θ M p ->
     eval_exp_order Θ succ M p )
| eeo_natrec :
  `( eval_exp_order Θ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ p ↘ m -> eval_natrec_order Θ A MZ MS m p) ->
     eval_exp_order Θ rec M return A | zero -> MZ | succ -> MS end p )
| eeo_True :
  `( eval_exp_order Θ ⊤ p )
| eeo_true :
  `( eval_exp_order Θ ⋆ p )
| eeo_False :
  `( eval_exp_order Θ ⊥ p )
(** The scrutinee of [efq] must evaluate to a neutral, since no other value
    has a rule. *)
| eeo_exfalso :
  `( eval_exp_order Θ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ p ↘ m -> exists b n, m = ⇑ b n) ->
     (forall b m, ⟦ M ⟧ Θ ⍮ p ↘ ⇑ b m -> eval_exp_order Θ A (p ↦ ⇑ b m)) ->
     eval_exp_order Θ (efq M return A) p )
| eeo_pi :
  `( eval_exp_order Θ A p ->
     eval_exp_order Θ (Π A B) p )
| eeo_fn :
  `( eval_exp_order Θ (λ A M) p )
| eeo_app :
  `( eval_exp_order Θ M p ->
     eval_exp_order Θ N p ->
     (forall m n, ⟦ M ⟧ Θ ⍮ p ↘ m -> ⟦ N ⟧ Θ ⍮ p ↘ n -> eval_app_order Θ m n) ->
     eval_exp_order Θ (M $ N) p )
| eeo_let :
  `( eval_exp_order Θ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ p ↘ m -> eval_exp_order Θ B (p ↦ m)) ->
     eval_exp_order Θ (a_let (b_def oA M) B) p )
| eeo_let_mod :
  `( eval_exp_order Θ B (p ↦ᵐ dm_of p U) ->
     eval_exp_order Θ (ℓₘ U in B) p )
| eeo_mem :
  `( modexp_spine H = (R, args, pre) ->
     eval_modexp_order Θ R p ->
     (forall h, ⟦ R ⟧ᵐ Θ ⍮ p ↘ h -> eval_selc_order Θ h (pre ++ x :: nil)) ->
     eval_exps_order Θ args p ->
     (forall h f ns, ⟦ R ⟧ᵐ Θ ⍮ p ↘ h -> eval_selc Θ h (pre ++ x :: nil) f ->
        eval_exps Θ args p ns -> eval_apps_order Θ f ns) ->
     eval_exp_order Θ (a_mem H x) p )
(** A sealed constant, or an axiom, is a neutral at its closed type. *)
| eeo_const :
  `( gc_const Θ c = Some (A, oM, b) ->
     b = false \/ oM = None ->
     eval_exp_order Θ A nil ->
     eval_exp_order Θ (a_const c) p )
| eeo_const_unfold :
  `( gc_const Θ c = Some (A, Some M, true) ->
     eval_exp_order Θ M nil ->
     eval_exp_order Θ (a_const c) p )

with eval_natrec_order (Θ : gctx) : exp -> exp -> exp -> domain -> env -> Prop :=
| eno_zero :
  `( eval_exp_order Θ MZ p ->
     eval_natrec_order Θ A MZ MS zeroᵈ p )
| eno_succ :
  `( eval_natrec_order Θ A MZ MS b p ->
     (forall r, ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ p ↘ r -> eval_exp_order Θ MS (p ↦ b ↦ r)) ->
     eval_natrec_order Θ A MZ MS succᵈ b p )
| eno_neut :
  `( eval_exp_order Θ MZ p ->
     eval_exp_order Θ A (p ↦ ⇑ a m) ->
     eval_natrec_order Θ A MZ MS ⇑ a m p )

with eval_app_order (Θ : gctx) : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order Θ M (p ↦ n) ->
     eval_app_order Θ λᵈ p M n )
| eao_neut :
  `( eval_exp_order Θ B (p ↦ n) ->
     eval_app_order Θ ⇑ (Πᵈ a p B) m n )
| eao_member :
  `( eval_appm_order Θ h n ->
     (forall h', eval_appm Θ h n h' -> eval_selc_order Θ h' ch) ->
     eval_app_order Θ (d_member h ch) n )

with eval_exps_order (Θ : gctx) : list exp -> env -> Prop :=
| eso_nil :
  `( eval_exps_order Θ nil p )
| eso_cons :
  `( eval_exp_order Θ M p ->
     eval_exps_order Θ Ms p ->
     eval_exps_order Θ (M :: Ms) p )

with eval_apps_order (Θ : gctx) : domain -> list domain -> Prop :=
| easo_nil :
  `( eval_apps_order Θ m nil )
| easo_cons :
  `( eval_app_order Θ m n ->
     (forall m1, $| m & n | Θ ↘ m1 -> eval_apps_order Θ m1 args) ->
     eval_apps_order Θ m (n :: args) )

with eval_modexp_order (Θ : gctx) : modexp -> env -> Prop :=
| emo_var :
  `( eval_modexp_order Θ (me_var x) p )
| emo_unit :
  `( gc_unit Θ fp = Some U ->
     eval_modexp_order Θ (me_unit fp) p )
| emo_lit :
  `( eval_modexp_order Θ (me_lit U) p )
| emo_mem :
  `( eval_modexp_order Θ H p ->
     (forall h, ⟦ H ⟧ᵐ Θ ⍮ p ↘ h -> eval_selm_order Θ h y) ->
     eval_modexp_order Θ (me_mem H y) p )
| emo_app :
  `( eval_modexp_order Θ H p ->
     eval_exp_order Θ N p ->
     (forall h n, ⟦ H ⟧ᵐ Θ ⍮ p ↘ h -> ⟦ N ⟧ Θ ⍮ p ↘ n -> eval_appm_order Θ h n) ->
     eval_modexp_order Θ (me_app H N) p )

with eval_appm_order (Θ : gctx) : dmod -> domain -> Prop :=
| eapo_body :
  `( List.length args < List.length Δ ->
     eval_appm_order Θ (dm_body p Δ Φ args) n )
| eapo_alias_unsat :
  `( List.length args < List.length Δ ->
     eval_appm_order Θ (dm_alias p Δ E args) n )
| eapo_alias :
  `( List.length args = List.length Δ ->
     eval_modexp_order Θ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐ Θ ⍮ env_args p args ↘ h -> eval_appm_order Θ h n) ->
     eval_appm_order Θ (dm_alias p Δ E args) n )
| eapo_member :
  `( eval_appm_order Θ h n ->
     (forall h', eval_appm Θ h n h' -> eval_selmc_order Θ h' ch) ->
     eval_appm_order Θ (dm_member h ch) n )

with eval_sel_order (Θ : gctx) : dmod -> string -> Prop :=
| eslo_unsat :
  `( dm_unsat h ->
     eval_sel_order Θ h x )
| eslo_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def pv A (Some M))) ->
     eval_exp_order Θ M (env_args p args ↦ᵐ dm_body (env_args p args) nil Φ' nil) ->
     eval_sel_order Θ (dm_body p Δ Φ args) x )
| eslo_alias :
  `( List.length args = List.length Δ ->
     eval_modexp_order Θ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐ Θ ⍮ env_args p args ↘ h -> eval_sel_order Θ h x) ->
     eval_sel_order Θ (dm_alias p Δ E args) x )
| eslo_member :
  `( eval_sel_order Θ (dm_member h ch) x )

with eval_selm_order (Θ : gctx) : dmod -> string -> Prop :=
| esmo_unsat :
  `( dm_unsat h ->
     eval_selm_order Θ h y )
| esmo_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     eval_selm_order Θ (dm_body p Δ Φ args) y )
| esmo_alias :
  `( List.length args = List.length Δ ->
     eval_modexp_order Θ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐ Θ ⍮ env_args p args ↘ h -> eval_selm_order Θ h y) ->
     eval_selm_order Θ (dm_alias p Δ E args) y )
| esmo_member :
  `( eval_selm_order Θ (dm_member h ch) y )

with eval_selc_order (Θ : gctx) : dmod -> list string -> Prop :=
| esco_one :
  `( eval_sel_order Θ h x ->
     eval_selc_order Θ h (x :: nil) )
| esco_cons :
  `( ch <> nil ->
     eval_selm_order Θ h y ->
     (forall h1, eval_selm Θ h y h1 -> eval_selc_order Θ h1 ch) ->
     eval_selc_order Θ h (y :: ch) )

with eval_selmc_order (Θ : gctx) : dmod -> list string -> Prop :=
| esmco_nil :
  `( eval_selmc_order Θ h nil )
| esmco_cons :
  `( eval_selm_order Θ h y ->
     (forall h1, eval_selm Θ h y h1 -> eval_selmc_order Θ h1 ch) ->
     eval_selmc_order Θ h (y :: ch) ).

#[local]
Hint Constructors eval_exp_order eval_natrec_order eval_app_order eval_exps_order eval_apps_order
  eval_modexp_order eval_appm_order eval_sel_order eval_selm_order eval_selc_order eval_selmc_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_eval_all :=
  repeat match goal with
    | H1 : eval_exp ?T ?M ?p ?m1, H2 : eval_exp ?T ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_eval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_natrec ?T ?A ?MZ ?MS ?m ?p ?r1, H2 : eval_natrec ?T ?A ?MZ ?MS ?m ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_natrec _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_app ?T ?m ?n ?r1, H2 : eval_app ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_exps ?T ?M ?p ?r1, H2 : eval_exps ?T ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_eval T)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_apps ?T ?m ?n ?r1, H2 : eval_apps ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_eval T))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_modexp ?T ?M ?p ?r1, H2 : eval_modexp ?T ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_appm ?T ?m ?n ?r1, H2 : eval_appm ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_sel ?T ?m ?n ?r1, H2 : eval_sel ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selm ?T ?m ?n ?r1, H2 : eval_selm ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selc ?T ?m ?n ?r1, H2 : eval_selc ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selmc ?T ?m ?n ?r1, H2 : eval_selmc ?T ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    end.

Lemma eval_order_sound : forall Θ,
    (forall m p a, ⟦ m ⟧ Θ ⍮ p ↘ a -> eval_exp_order Θ m p) /\
    (forall A MZ MS m p r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ p ↘ r ->
       eval_natrec_order Θ A MZ MS m p) /\
    (forall m n r, $| m & n | Θ ↘ r -> eval_app_order Θ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧* Θ ⍮ p ↘ ms -> eval_exps_order Θ Ms p) /\
    (forall m ns r, $*| m & ns | Θ ↘ r -> eval_apps_order Θ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐ Θ ⍮ p ↘ h -> eval_modexp_order Θ H p) /\
    (forall h n r, $ᵐ| h & n | Θ ↘ r -> eval_appm_order Θ h n) /\
    (forall h x r, h ·ₜ x Θ ↘ r -> eval_sel_order Θ h x) /\
    (forall h y r, h ·ₘ y Θ ↘ r -> eval_selm_order Θ h y) /\
    (forall h ch r, h ·ₜ* ch Θ ↘ r -> eval_selc_order Θ h ch) /\
    (forall h ch r, h ·ₘ* ch Θ ↘ r -> eval_selmc_order Θ h ch).
Proof.
  intros Θ; apply eval_mut_ind; intros;
    try solve [ econstructor; try eassumption; intros; functional_eval_all; eauto
              | eapply eeo_const_unfold; eauto ].
  - (* a chain of one more selection is not empty *)
    eapply esco_cons; [| eauto | intros; functional_eval_all; eauto ].
    match goal with H : eval_selc _ _ ?c _ |- ?c <> nil => inversion H; discriminate end.
Qed.

Lemma eval_exp_order_sound : forall Θ m p a, ⟦ m ⟧ Θ ⍮ p ↘ a -> eval_exp_order Θ m p.
Proof. intros Θ; exact (proj1 (eval_order_sound Θ)). Qed.

Lemma eval_natrec_order_sound : forall Θ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ p ↘ r ->
    eval_natrec_order Θ A MZ MS m p.
Proof. intros Θ; exact (proj1 (proj2 (eval_order_sound Θ))). Qed.

Lemma eval_app_order_sound : forall Θ m n r, $| m & n | Θ ↘ r -> eval_app_order Θ m n.
Proof. intros Θ; exact (proj1 (proj2 (proj2 (eval_order_sound Θ)))). Qed.

Lemma eval_modexp_order_sound : forall Θ H p h, ⟦ H ⟧ᵐ Θ ⍮ p ↘ h -> eval_modexp_order Θ H p.
Proof. intros Θ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (eval_order_sound Θ))))))). Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_natrec_order_sound eval_app_order_sound eval_modexp_order_sound : mctt.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Section EvalImpl.
  Variables (Θ : gctx).

  (** A variable is looked up in the environment, without recursion. *)
  Definition eval_var_impl x p (H : eval_exp_order Θ #x p) : { d | ⟦ #x ⟧ Θ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply eval_exp_var.
  Defined.

  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ |- _ => progressive_invert H
    | H : eval_natrec_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ |- _ => progressive_invert H
    | H : eval_exps_order _ _ _ |- _ => progressive_invert H
    | H : eval_apps_order _ _ _ |- _ => progressive_invert H
    | H : eval_modexp_order _ _ _ |- _ => progressive_invert H
    | H : eval_appm_order _ _ _ |- _ => progressive_invert H
    | H : eval_sel_order _ _ _ |- _ => progressive_invert H
    | H : eval_selm_order _ _ _ |- _ => progressive_invert H
    | H : eval_selc_order _ _ _ |- _ => progressive_invert H
    | H : eval_selmc_order _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
      | H1 : gc_const _ ?p = Some _, H2 : gc_const _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_const _ ?p = Some _, H2 : gc_const _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_unit _ ?p = Some _, H2 : gc_unit _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_unit _ ?p = Some _, H2 : gc_unit _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H : Nat.compare _ _ = Eq |- _ => apply Nat.compare_eq in H
      | H : Nat.compare _ _ = Lt |- _ => apply Nat.compare_lt_iff in H
      | H : Nat.compare _ _ = Gt |- _ => apply Nat.compare_gt_iff in H
      end.

  (** The [efq] case: the order says that the scrutinee evaluates to a
      neutral, which rules out every other value. *)
  #[local]
  Ltac impl_obl_exfalso :=
    repeat match goal with
      | H : forall m, eval_exp _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : eval_exp _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      end.

  #[local]
  Ltac impl_obl_split :=
    match goal with
    | H : eval_exp_order _ _ _ |- _ => dependent destruction H
    | H : eval_natrec_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_app_order _ _ _ |- _ => dependent destruction H
    | H : eval_modexp_order _ _ _ |- _ => dependent destruction H
    | H : eval_appm_order _ _ _ |- _ => dependent destruction H
    | H : eval_sel_order _ _ _ |- _ => dependent destruction H
    | H : eval_selm_order _ _ _ |- _ => dependent destruction H
    | H : eval_selc_order _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac impl_obl_finish :=
    impl_obl_exfalso;
    impl_obl_glob;
    cbn [gu_params dm_unsat] in *;
    try solve [ intuition discriminate ];
    try solve [ exfalso; lia ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    try solve [ eauto ];
    try econstructor; eauto.


  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    repeat impl_obl_tac1;
    first [ solve [ impl_obl_finish ]
          | solve [ impl_obl_split; impl_obl_finish ]
          | impl_obl_finish ].

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations eval_exp_impl m p (H : eval_exp_order Θ m p) : { d | ⟦ m ⟧ Θ ⍮ p ↘ d } by struct H :=
  | Type@i, p, H => exist _ 𝕌@i _
  | #x    , p, H => eval_var_impl x p H
  | ℕ     , p, H => exist _ ℕᵈ _
  | zero  , p, H => exist _ zeroᵈ _
  | succ m, p, H =>
      let (r , Hr) := eval_exp_impl m p _ in
      exist _ succᵈ r _
  | rec M return A | zero -> MZ | succ -> MS end, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (r, Hr)  := eval_natrec_impl A MZ MS m p _ in
      exist _ r _
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
  | M $ N   , p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      let (a, Ha) := eval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | ℓₘ U in B, p, H =>
      let (r, Hr) := eval_exp_impl B (p ↦ᵐ dm_of p U) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := eval_modexp_impl R p _ in
        let (f, Hf) := eval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := eval_exps_impl args p _ in
        let (r, Hr) := eval_apps_impl f ns _ in
        exist _ r _ }
  | a_const c, p, H with inspect (gc_const Θ c) := {
    | exist _ (Some (A, Some M, true)) E =>
        let (r, Hr) := eval_exp_impl M nil _ in
        exist _ r _
    | exist _ (Some (A, Some M, false)) E =>
        let (a, Ha) := eval_exp_impl A nil _ in
        exist _ (⇑ a (d_glob c)) _
    | exist _ (Some (A, None, b)) E =>
        let (a, Ha) := eval_exp_impl A nil _ in
        exist _ (⇑ a (d_glob c)) _
    | exist _ None E => False_rect _ _ }

  with eval_natrec_impl A MZ MS m p (H : eval_natrec_order Θ A MZ MS m p) : { d | ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ p ↘ d } by struct H :=
  | A, MZ, MS, zeroᵈ  , p, H =>
      let (mz, Hmz) := eval_exp_impl MZ p _ in
      exist _ mz _
  | A, MZ, MS, succᵈ m, p, H =>
      let (mr, Hmr) := eval_natrec_impl A MZ MS m p _ in
      let (r, Hr) := eval_exp_impl MS (p ↦ m ↦ mr) _ in
      exist _ r _
  | A, MZ, MS, ⇑ a m , p, H =>
      let (mz, Hmz) := eval_exp_impl MZ p _ in
      let (mA, HmA) := eval_exp_impl A (p ↦ ⇑ a m) _ in
      exist _ ⇑ mA recᵈ m under p return A | zero -> mz | succ -> MS end _
  | A, MZ, MS, _, p, H => False_rect _ _

  with eval_app_impl m n (H : eval_app_order Θ m n) : { d | $| m & n | Θ ↘ d } by struct H :=
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
  | _, n, H => False_rect _ _

  with eval_exps_impl Ms p (H : eval_exps_order Θ Ms p) : { ms | eval_exps Θ Ms p ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (ms, Hms) := eval_exps_impl Ms p _ in
      exist _ (m :: ms) _

  with eval_apps_impl m ns (H : eval_apps_order Θ m ns) : { r | eval_apps Θ m ns r } by struct H :=
  | m, nil, H => exist _ m _
  | m, n :: ns, H =>
      let (m1, Hm1) := eval_app_impl m n _ in
      let (r, Hr) := eval_apps_impl m1 ns _ in
      exist _ r _

  with eval_modexp_impl M p (H : eval_modexp_order Θ M p) : { h | ⟦ M ⟧ᵐ Θ ⍮ p ↘ h } by struct H :=
  | me_var x, p, H => exist _ (env_mod p x) _
  | me_unit fp, p, H with inspect (gc_unit Θ fp) := {
    | exist _ (Some U) E => exist _ (dm_of nil U) _
    | exist _ None E => False_rect _ _ }
  | me_lit U, p, H => exist _ (dm_of p U) _
  | me_mem M y, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (r, Hr) := eval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (n, Hn) := eval_exp_impl N p _ in
      let (r, Hr) := eval_appm_impl h n _ in
      exist _ r _

  with eval_appm_impl h n (H : eval_appm_order Θ h n) : { r | eval_appm Θ h n r } by struct H :=
  | dm_body p Δ Φ args, n, H => exist _ (dm_body p Δ Φ (args ++ n :: nil)) _
  | dm_alias p Δ E args, n, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_alias p Δ E (args ++ n :: nil)) _
    | exist _ Eq C =>
        let (h, Hh) := eval_modexp_impl E (env_args p args) _ in
        let (r, Hr) := eval_appm_impl h n _ in
        exist _ r _
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selmc_impl h' ch _ in
      exist _ r _

  with eval_sel_impl h x (H : eval_sel_order Θ h x) : { r | eval_sel Θ h x r } by struct H :=
  | dm_body p Δ Φ args, x, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (d_member (dm_body p Δ Φ args) (x :: nil)) _
    | exist _ Eq C with inspect (gm_prefix_upto Φ x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def pv A (Some M)))) P =>
          let (r, Hr) := eval_exp_impl M (env_args p args ↦ᵐ dm_body (env_args p args) nil Φ' nil) _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ }
    | exist _ Gt C => False_rect _ _ }
  | dm_alias p Δ E args, x, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (d_member (dm_alias p Δ E args) (x :: nil)) _
    | exist _ Eq C =>
        let (h, Hh) := eval_modexp_impl E (env_args p args) _ in
        let (r, Hr) := eval_sel_impl h x _ in
        exist _ r _
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with eval_selm_impl h y (H : eval_selm_order Θ h y) : { r | eval_selm Θ h y r } by struct H :=
  | dm_body p Δ Φ args, y, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_member (dm_body p Δ Φ args) (y :: nil)) _
    | exist _ Eq C with inspect (gm_prefix_upto Φ y) := {
      | exist _ (Some (gm_ext Φ' _ (ge_mod _ Uy))) P =>
          exist _ (dm_of (env_args p args ↦ᵐ dm_body (env_args p args) nil Φ' nil) Uy) _
      | exist _ _ P => False_rect _ _ }
    | exist _ Gt C => False_rect _ _ }
  | dm_alias p Δ E args, y, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_member (dm_alias p Δ E args) (y :: nil)) _
    | exist _ Eq C =>
        let (h, Hh) := eval_modexp_impl E (env_args p args) _ in
        let (r, Hr) := eval_selm_impl h y _ in
        exist _ r _
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, y, H => exist _ (dm_member h (ch ++ y :: nil)) _

  with eval_selc_impl h ch (H : eval_selc_order Θ h ch) : { r | eval_selc Θ h ch r } by struct H :=
  | h, x :: nil, H =>
      let (r, Hr) := eval_sel_impl h x _ in
      exist _ r _
  | h, y :: ch, H =>
      let (h1, Hh1) := eval_selm_impl h y _ in
      let (r, Hr) := eval_selc_impl h1 ch _ in
      exist _ r _
  | h, nil, H => False_rect _ _

  with eval_selmc_impl h ch (H : eval_selmc_order Θ h ch) : { r | eval_selmc Θ h ch r } by struct H :=
  | h, nil, H => exist _ h _
  | h, y :: ch, H =>
      let (h1, Hh1) := eval_selm_impl h y _ in
      let (r, Hr) := eval_selmc_impl h1 ch _ in
      exist _ r _.
End EvalImpl.

Extraction Inline eval_exp_impl_functional
  eval_natrec_impl_functional
  eval_app_impl_functional
  eval_exps_impl_functional
  eval_apps_impl_functional
  eval_modexp_impl_functional
  eval_appm_impl_functional
  eval_sel_impl_functional
  eval_selm_impl_functional
  eval_selc_impl_functional
  eval_selmc_impl_functional.

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

Lemma eval_exp_impl_complete : forall Θ M p m,
    ⟦ M ⟧ Θ ⍮ p ↘ m ->
    exists H H', eval_exp_impl Θ M p H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_natrec_impl_complete : forall Θ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ p ↘ r ->
    exists H H', eval_natrec_impl Θ A MZ MS m p H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall Θ m n r,
    $| m & n | Θ ↘ r ->
    exists H H', eval_app_impl Θ m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.
