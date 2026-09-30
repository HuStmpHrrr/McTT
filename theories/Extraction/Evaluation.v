From Equations Require Import Equations.
From Stdlib Require Import List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import GlobalCtx.
From Mctt.Core.Semantic Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

(** The termination orders mirror [eval_exp], [eval_natrec] and [eval_app],
    relative to the same global context.  A transparent global recurses into
    its resolved body, which is what the δ order records. *)

Inductive eval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
| eeo_typ :
  `( eval_exp_order Θ Ξ Type@i p )
(** An environment is total, so a variable always terminates. *)
| eeo_var :
  `( eval_exp_order Θ Ξ #x p )
| eeo_nat :
  `( eval_exp_order Θ Ξ ℕ p )
| eeo_zero :
  `( eval_exp_order Θ Ξ zero p )
| eeo_succ :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ succ M p )
| eeo_natrec :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> eval_natrec_order Θ Ξ A MZ MS m p) ->
     eval_exp_order Θ Ξ rec M return A | zero -> MZ | succ -> MS end p )
| eeo_pi :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ (Π A B) p )
| eeo_fn :
  `( eval_exp_order Θ Ξ (λ A M) p )
| eeo_app :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     (forall m n, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_app_order Θ Ξ m n) ->
     eval_exp_order Θ Ξ (M $ N) p )
| eeo_glob_delta :
  `( gc_resolve Θ Ξ pth = Some (Δ, ge_def true pv A (Some M)) ->
     eval_exp_order Θ Ξ (ctx_fn Δ M) nil ->
     eval_exp_order Θ Ξ (a_glob pth) p )
| eeo_glob_neut :
  `( gc_resolve Θ Ξ pth = Some (Δ, ge_def b pv A B) ->
     b = false \/ B = None ->
     eval_exp_order Θ Ξ (ctx_pi Δ A) nil ->
     eval_exp_order Θ Ξ (a_glob pth) p )
| eeo_param :
  `( gs_param Ξ lp = Some T ->
     eval_exp_order Θ Ξ T nil ->
     eval_exp_order Θ Ξ (a_param lp) p )

with eval_natrec_order (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> Prop :=
| eno_zero :
  `( eval_exp_order Θ Ξ MZ p ->
     eval_natrec_order Θ Ξ A MZ MS zeroᵈ p )
| eno_succ :
  `( eval_natrec_order Θ Ξ A MZ MS b p ->
     (forall r, ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_exp_order Θ Ξ MS (p ↦ b ↦ r)) ->
     eval_natrec_order Θ Ξ A MZ MS succᵈ b p )
| eno_neut :
  `( eval_exp_order Θ Ξ MZ p ->
     eval_exp_order Θ Ξ A (p ↦ ⇑ a m) ->
     eval_natrec_order Θ Ξ A MZ MS ⇑ a m p )

with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order Θ Ξ M (p ↦ n) ->
     eval_app_order Θ Ξ λᵈ p M n )
| eao_neut :
  `( eval_exp_order Θ Ξ B (p ↦ n) ->
     eval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n ).

#[local]
Hint Constructors eval_exp_order eval_natrec_order eval_app_order : mctt.

Lemma eval_exp_order_sound : forall Θ Ξ m p a,
    ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
    eval_exp_order Θ Ξ m p
with eval_natrec_order_sound : forall Θ Ξ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
    eval_natrec_order Θ Ξ A MZ MS m p
with eval_app_order_sound: forall Θ Ξ m n r,
  $| m & n | Θ ⍮ Ξ ↘ r ->
  eval_app_order Θ Ξ m n.
Proof.
  - clear eval_exp_order_sound; induction 1;
      solve [ eapply eeo_glob_neut; eauto
            | econstructor; intros; functional_eval_rewrite_clear; eauto ].
  - clear eval_natrec_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; eauto).
  - clear eval_app_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; eauto).
Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_natrec_order_sound eval_app_order_sound : mctt.

(** [eval_sub] is pointwise, so its order is the order of every component. *)
Lemma eval_sub_order_sound : forall Θ Ξ σ p p' x,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ p ↘ p' ->
    eval_exp_order Θ Ξ (σ x) p.
Proof.
  intros * H; eapply eval_exp_order_sound, eval_sub_index; eassumption.
Qed.

#[export]
Hint Resolve eval_sub_order_sound : mctt.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A variable does not recurse: the environment is total, so it is just
      looked up. *)
  Definition eval_var_impl x p (H : eval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply eval_exp_var.
  Defined.

  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_natrec_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ _ |- _ => progressive_invert H
    end.

  (** The global and parameter cases: the resolution the order was built for is
      the one computed, which fixes the body, or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gs_param _ ?lp = Some _, H2 : gs_param _ ?lp = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gs_param _ ?lp = Some _, H2 : gs_param _ ?lp = None |- _ =>
          rewrite H1 in H2; discriminate H2
      end.

  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    repeat impl_obl_tac1;
    try match goal with H : eval_exp_order _ _ (a_glob _) _ |- _ => inversion H; subst; clear H end;
    try match goal with H : eval_exp_order _ _ (a_param _) _ |- _ => inversion H; subst; clear H end;
    impl_obl_glob;
    try solve [ intuition discriminate ];
    try solve [ eapply eval_exp_glob_neut; eauto ];
    try solve [ eapply eval_exp_param; eauto ];
    try solve [ eauto ];
    try econstructor; eauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations eval_exp_impl m p (H : eval_exp_order Θ Ξ m p) : { d | ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
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
  | Π A B , p, H =>
      let (r , Hr) := eval_exp_impl A p _ in
      exist _ Πᵈ r p B _
  | λ A M , p, H => exist _ λᵈ p M _
  | M $ N   , p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      let (a, Ha) := eval_app_impl m n _ in
      exist _ a _
  | a_glob pth, p, H with inspect (gc_resolve Θ Ξ pth) := {
    | exist _ (Some (Δ, ge_def true pv A (Some M))) E =>
        let (m, Hm) := eval_exp_impl (ctx_fn Δ M) nil _ in
        exist _ m _
    | exist _ (Some (Δ, ge_def true _ A None)) E =>
        let (a, Ha) := eval_exp_impl (ctx_pi Δ A) nil _ in
        exist _ (⇑ a (d_glob pth)) _
    | exist _ (Some (Δ, ge_def false _ A B)) E =>
        let (a, Ha) := eval_exp_impl (ctx_pi Δ A) nil _ in
        exist _ (⇑ a (d_glob pth)) _
    | exist _ (Some (Δ, ge_mod _ _)) E => False_rect _ _
    | exist _ None E => False_rect _ _ }
  | a_param lp, p, H with inspect (gs_param Ξ lp) := {
    | exist _ (Some T) E =>
        let (a, Ha) := eval_exp_impl T nil _ in
        exist _ (⇑ a (d_param lp)) _
    | exist _ None E => False_rect _ _ }

  with eval_natrec_impl A MZ MS m p (H : eval_natrec_order Θ Ξ A MZ MS m p) : { d | ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
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

  with eval_app_impl m n (H : eval_app_order Θ Ξ m n) : { d | $| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | λᵈ p M        , n, H =>
      let (m, Hm) := eval_exp_impl M (p ↦ n) _ in
      exist _ m _
  | ⇑ (Πᵈ a p B) m, n, H =>
      let (b, Hb) := eval_exp_impl B (p ↦ n) _ in
      exist _ ⇑ b (m $ᵈ ⇓ a n) _.
End EvalImpl.

Extraction Inline eval_exp_impl_functional
  eval_natrec_impl_functional
  eval_app_impl_functional.

(** The definitions of [eval_*_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of eval. *)

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

Lemma eval_natrec_impl_complete : forall Θ Ξ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
    exists H H', eval_natrec_impl Θ Ξ A MZ MS m p H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall Θ Ξ m n r,
    $| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', eval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.
