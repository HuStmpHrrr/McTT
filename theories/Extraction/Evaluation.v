From Equations Require Import Equations.
From Stdlib Require Import List Lia PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import GlobalCtx.
From Mctt.Core.Semantic Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

(** The termination orders mirror the evaluation relations, relative to the
    same global context.  A transparent global recurses into its raw body
    where it is entered, which is what the [eno_delta] order records. *)

Inductive eval_exp_order (Θ : gdeps) (Ξ : gstack) : menv -> exp -> env -> Prop :=
| eeo_typ :
  `( eval_exp_order Θ Ξ κ Type@i p )
(** An environment is total, so a variable always terminates. *)
| eeo_var :
  `( eval_exp_order Θ Ξ κ #x p )
| eeo_nat :
  `( eval_exp_order Θ Ξ κ ℕ p )
| eeo_zero :
  `( eval_exp_order Θ Ξ κ zero p )
| eeo_succ :
  `( eval_exp_order Θ Ξ κ M p ->
     eval_exp_order Θ Ξ κ succ M p )
| eeo_natrec :
  `( eval_exp_order Θ Ξ κ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ m -> eval_natrec_order Θ Ξ κ A MZ MS m p) ->
     eval_exp_order Θ Ξ κ rec M return A | zero -> MZ | succ -> MS end p )
| eeo_pi :
  `( eval_exp_order Θ Ξ κ A p ->
     eval_exp_order Θ Ξ κ (Π A B) p )
| eeo_fn :
  `( eval_exp_order Θ Ξ κ (λ A M) p )
| eeo_app :
  `( eval_exp_order Θ Ξ κ M p ->
     eval_exp_order Θ Ξ κ N p ->
     (forall m n, ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ m -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ n -> eval_app_order Θ Ξ m n) ->
     eval_exp_order Θ Ξ κ (M $ N) p )
| eeo_param_closed :
  `( me_drop (lp_mod lp) κ = me_frame a args κ' ->
     eval_exp_order Θ Ξ κ (a_param lp) p )
| eeo_param_open :
  `( me_drop (lp_mod lp) κ = me_base j ->
     List.nth_error Ξ j = Some U ->
     lp_param lp < List.length (gu_params U) ->
     (forall j' U', me_drop (lp_mod lp) κ = me_base j' -> List.nth_error Ξ j' = Some U' ->
        eval_ptele_order Θ Ξ (me_base (S j')) j' (List.length (gu_params U')) (List.skipn (lp_param lp) (gu_params U'))) ->
     eval_exp_order Θ Ξ κ (a_param lp) p )
| eeo_glob_rel :
  `( eval_ent_order Θ Ξ (me_drop m κ) ip ->
     eval_exp_order Θ Ξ κ (a_glob (p_rel m ip)) p )
| eeo_glob_abs :
  `( gds_lookup Θ fp = Some U ->
     (forall U', gds_lookup Θ fp = Some U' ->
        eval_pend_order Θ Ξ (me_base 0) (p_abs fp nil) (List.length (gu_params U')) nil ip) ->
     eval_exp_order Θ Ξ κ (a_glob (p_abs fp ip)) p )

with eval_natrec_order (Θ : gdeps) (Ξ : gstack) : menv -> exp -> exp -> exp -> domain -> env -> Prop :=
| eno_zero :
  `( eval_exp_order Θ Ξ κ MZ p ->
     eval_natrec_order Θ Ξ κ A MZ MS zeroᵈ p )
| eno_succ :
  `( eval_natrec_order Θ Ξ κ A MZ MS b p ->
     (forall r, ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ r -> eval_exp_order Θ Ξ κ MS (p ↦ b ↦ r)) ->
     eval_natrec_order Θ Ξ κ A MZ MS succᵈ b p )
| eno_neut :
  `( eval_exp_order Θ Ξ κ MZ p ->
     eval_exp_order Θ Ξ κ A (p ↦ ⇑ a m) ->
     eval_natrec_order Θ Ξ κ A MZ MS ⇑ a m p )

with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order Θ Ξ κ M (p ↦ n) ->
     eval_app_order Θ Ξ λᵈ κ p M n )
| eao_neut :
  `( eval_exp_order Θ Ξ κ B (p ↦ n) ->
     eval_app_order Θ Ξ ⇑ (Πᵈ a κ p B) m n )
| eao_gfn :
  `( eval_pend_order Θ Ξ κ a c (n :: args) ip ->
     eval_app_order Θ Ξ (d_gfn κ a c args ip) n )

with eval_pend_order (Θ : gdeps) (Ξ : gstack) : menv -> path -> nat -> env -> list string -> Prop :=
| epo_wait :
  `( List.length args < c ->
     eval_pend_order Θ Ξ κ a c args ip )
| epo_enter :
  `( List.length args = c ->
     eval_ent_order Θ Ξ (me_frame a args κ) ip ->
     eval_pend_order Θ Ξ κ a c args ip )

with eval_ent_order (Θ : gdeps) (Ξ : gstack) : menv -> list string -> Prop :=
| ento_delta :
  `( frame_at Θ Ξ (me_addr κ) = Some (Δ, Φ) ->
     gm_find Φ y = Some (ge_def true pv A (Some M)) ->
     (forall Δ' Φ' pv' A' M', frame_at Θ Ξ (me_addr κ) = Some (Δ', Φ') ->
        gm_find Φ' y = Some (ge_def true pv' A' (Some M')) -> eval_exp_order Θ Ξ κ M' nil) ->
     eval_ent_order Θ Ξ κ (y :: nil) )
| ento_neut :
  `( frame_at Θ Ξ (me_addr κ) = Some (Δ, Φ) ->
     gm_find Φ y = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     (forall Δ' Φ' b' pv' A' B', frame_at Θ Ξ (me_addr κ) = Some (Δ', Φ') ->
        gm_find Φ' y = Some (ge_def b' pv' A' B') -> eval_exp_order Θ Ξ κ A' nil) ->
     eval_gne_order Θ Ξ κ (addr_depth (me_addr κ)) (d_glob (path_in (me_addr κ) y)) ->
     eval_ent_order Θ Ξ κ (y :: nil) )
| ento_mod :
  `( frame_at Θ Ξ (me_addr κ) = Some (Δ, Φ) ->
     gm_find Φ x = Some (ge_mod Δ' Φ') ->
     ip <> nil ->
     (forall Δ0 Φ0 Δ0' Φ0', frame_at Θ Ξ (me_addr κ) = Some (Δ0, Φ0) ->
        gm_find Φ0 x = Some (ge_mod Δ0' Φ0') ->
        eval_pend_order Θ Ξ κ (path_in (me_addr κ) x) (List.length Δ0') nil ip) ->
     eval_ent_order Θ Ξ κ (x :: ip) )

with eval_ptele_order (Θ : gdeps) (Ξ : gstack) : menv -> nat -> nat -> ctx -> Prop :=
| epto_nil :
  `( eval_ptele_order Θ Ξ κ j c nil )
| epto_cons :
  `( eval_ptele_order Θ Ξ κ j c Γ ->
     (forall ρ, eval_ptele Θ Ξ κ j c Γ ρ -> eval_exp_order Θ Ξ κ T ρ) ->
     eval_ptele_order Θ Ξ κ j c (T :: Γ) )

with eval_gne_order (Θ : gdeps) (Ξ : gstack) : menv -> nat -> domain_ne -> Prop :=
| egno_zero :
  `( eval_gne_order Θ Ξ κ 0 h )
| egno_succ :
  `( eval_gne_order Θ Ξ κ n h ->
     frame_at Θ Ξ a = Some (Δ, Φ) ->
     (forall Δ' Φ' h1, frame_at Θ Ξ a = Some (Δ', Φ') -> eval_gne Θ Ξ κ n h h1 -> eval_fargs_order Θ Ξ κ Δ' args h1) ->
     eval_gne_order Θ Ξ (me_frame a args κ) (S n) h )

with eval_fargs_order (Θ : gdeps) (Ξ : gstack) : menv -> ctx -> env -> domain_ne -> Prop :=
| efo_nil :
  `( eval_fargs_order Θ Ξ κ nil nil h )
| efo_cons :
  `( eval_fargs_order Θ Ξ κ Δ args h ->
     eval_exp_order Θ Ξ κ T args ->
     eval_fargs_order Θ Ξ κ (T :: Δ) (v :: args) h ).

#[local]
Hint Constructors eval_exp_order eval_natrec_order eval_app_order eval_pend_order eval_ent_order
  eval_ptele_order eval_gne_order eval_fargs_order : mctt.

Lemma eval_ptele_length : forall Θ Ξ κ j c Γ ρ, eval_ptele Θ Ξ κ j c Γ ρ -> List.length ρ = List.length Γ.
Proof. induction 1; cbn; auto. Qed.

Lemma eval_order_sound : forall Θ Ξ,
    (forall κ m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ a -> eval_exp_order Θ Ξ κ m p) /\
    (forall κ A MZ MS m p r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ r ->
       eval_natrec_order Θ Ξ κ A MZ MS m p) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n) /\
    (forall κ a c args ip r, eval_pend Θ Ξ κ a c args ip r -> eval_pend_order Θ Ξ κ a c args ip) /\
    (forall κ ip r, eval_ent Θ Ξ κ ip r -> eval_ent_order Θ Ξ κ ip) /\
    (forall κ j c Γ ρ, eval_ptele Θ Ξ κ j c Γ ρ -> eval_ptele_order Θ Ξ κ j c Γ) /\
    (forall κ n h h1, eval_gne Θ Ξ κ n h h1 -> eval_gne_order Θ Ξ κ n h) /\
    (forall κ Δ args h h1, eval_fargs Θ Ξ κ Δ args h h1 -> eval_fargs_order Θ Ξ κ Δ args h).
Proof.
  intros Θ Ξ.
  apply (eval_mut_ind Θ Ξ
           (fun κ m p a _ => eval_exp_order Θ Ξ κ m p)
           (fun κ A MZ MS m p r _ => eval_natrec_order Θ Ξ κ A MZ MS m p)
           (fun m n r _ => eval_app_order Θ Ξ m n)
           (fun κ a c args ip r _ => eval_pend_order Θ Ξ κ a c args ip)
           (fun κ ip r _ => eval_ent_order Θ Ξ κ ip)
           (fun κ j c Γ ρ _ => eval_ptele_order Θ Ξ κ j c Γ)
           (fun κ n h h1 _ => eval_gne_order Θ Ξ κ n h)
           (fun κ Δ args h h1 _ => eval_fargs_order Θ Ξ κ Δ args h));
    intros; try solve [ econstructor; intros; functional_eval_rewrite_clear; eauto ].
  all: try solve [ econstructor; try eassumption; intros;
                   repeat match goal with
                     | H1 : ?X = Some _, H2 : ?X = Some _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst
                     | H1 : ?X = me_base _, H2 : ?X = me_base _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst
                     end;
                   functional_eval_rewrite_clear; eauto ].
  - (* an open parameter *)
    eapply eeo_param_open; try eassumption.
    + match goal with H : eval_ptele _ _ _ _ _ _ _ |- _ => apply eval_ptele_length in H end.
      rewrite List.length_skipn in *; cbn in *; lia.
    + intros j' U' Hd Hn'.
      match goal with H1 : ?X = me_base _, H2 : ?X = me_base _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst end.
      match goal with H1 : ?X = Some _, H2 : ?X = Some _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst end.
      assumption.
  - econstructor; intros; try eassumption.
    match goal with H1 : eval_ptele _ _ _ _ _ _ ?ρ1, H2 : eval_ptele _ _ _ _ _ _ ?ρ2 |- _ =>
      pose proof (functional_eval_ptele _ _ _ _ _ _ H1 H2) as ->; assumption end.
  - econstructor; intros; try eassumption.
    match goal with H1 : ?X = Some _, H2 : ?X = Some _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst end.
    match goal with H1 : eval_gne _ _ _ _ _ ?h1, H2 : eval_gne _ _ _ _ _ ?h2 |- _ =>
      pose proof (functional_eval_gne _ _ _ _ _ H1 H2) as ->; assumption end.
Qed.

Lemma eval_exp_order_sound : forall Θ Ξ κ m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ a -> eval_exp_order Θ Ξ κ m p.
Proof. intros Θ Ξ; apply (eval_order_sound Θ Ξ). Qed.

Lemma eval_natrec_order_sound : forall Θ Ξ κ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ r -> eval_natrec_order Θ Ξ κ A MZ MS m p.
Proof. intros Θ Ξ; apply (eval_order_sound Θ Ξ). Qed.

Lemma eval_app_order_sound : forall Θ Ξ m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; apply (eval_order_sound Θ Ξ). Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_natrec_order_sound eval_app_order_sound : mctt.

(** [eval_sub] is pointwise, so its order is the order of every component. *)
Lemma eval_sub_order_sound : forall Θ Ξ κ σ p p' x,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ p ↘ p' ->
    eval_exp_order Θ Ξ κ (σ x) p.
Proof.
  intros * H; eapply eval_exp_order_sound, eval_sub_index; eassumption.
Qed.

#[export]
Hint Resolve eval_sub_order_sound : mctt.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Lemma pend_contra : forall (l : env) c, List.length l < c -> Nat.ltb (List.length l) c = false -> False.
Proof. intros * H1 H2; apply Nat.ltb_ge in H2; lia. Qed.

(** Inversions by [match], so that the sub-order is a structural subterm. *)
Notation app_order_gfn Θ Ξ H :=
  (match H in eval_app_order _ _ m n0 return
    match m with d_gfn κ0 a0 c0 args0 ip0 => eval_pend_order Θ Ξ κ0 a0 c0 (n0 :: args0) ip0 | _ => True end
  with
  | @eao_gfn _ _ _ _ _ _ _ _ Hp => Hp
  | _ => I
  end) (only parsing).

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_natrec_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_pend_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ent_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_ptele_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_gne_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_fargs_order _ _ _ _ _ _ |- _ => progressive_invert H
    end.

  (** Lookups the order was built for are the ones computed. *)
  #[local]
  Ltac impl_obl_lookup :=
    repeat match goal with
      | H1 : ?X = Some _, H2 : ?X = Some _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ?X = Some _, H2 : ?X = None |- _ => rewrite H1 in H2; discriminate H2
      | H1 : ?X = me_frame _ _ _, H2 : ?X = me_frame _ _ _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ?X = me_frame _ _ _, H2 : ?X = me_base _ |- _ => rewrite H1 in H2; discriminate H2
      | H1 : ?X = me_base _, H2 : ?X = me_frame _ _ _ |- _ => rewrite H1 in H2; discriminate H2
      | H1 : ?X = me_base _, H2 : ?X = me_base _ |- _ => rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
      | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
      | H : eval_ptele _ _ _ _ _ _ nil |- _ =>
          apply eval_ptele_length in H; rewrite List.length_skipn in H; cbn in H
      end.

  #[local]
  Ltac impl_obl_split :=
    match goal with
    | H : eval_exp_order _ _ _ (a_param _) _ |- _ => dependent destruction H
    | H : eval_pend_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ent_order _ _ _ (_ :: nil) |- _ => dependent destruction H
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    repeat impl_obl_tac1;
    impl_obl_lookup;
    try solve [ eauto ];
    repeat impl_obl_split;
    impl_obl_lookup;
    try solve [ intuition (discriminate || lia || congruence) ];
    try solve [ eauto ];
    try (econstructor; solve [ eauto ]);
    try econstructor; eauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations eval_exp_impl κ m p (H : eval_exp_order Θ Ξ κ m p) : { d | ⟦ m ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ d } by struct H :=
  | κ, Type@i, p, H => exist _ 𝕌@i _
  | κ, #x    , p, H => exist _ (env_var p x) _
  | κ, ℕ     , p, H => exist _ ℕᵈ _
  | κ, zero  , p, H => exist _ zeroᵈ _
  | κ, succ m, p, H =>
      let (r , Hr) := eval_exp_impl κ m p _ in
      exist _ succᵈ r _
  | κ, rec M return A | zero -> MZ | succ -> MS end, p, H =>
      let (m , Hm) := eval_exp_impl κ M p _ in
      let (r, Hr)  := eval_natrec_impl κ A MZ MS m p _ in
      exist _ r _
  | κ, Π A B , p, H =>
      let (r , Hr) := eval_exp_impl κ A p _ in
      exist _ Πᵈ r κ p B _
  | κ, λ A M , p, H => exist _ λᵈ κ p M _
  | κ, M $ N   , p, H =>
      let (m , Hm) := eval_exp_impl κ M p _ in
      let (n , Hn) := eval_exp_impl κ N p _ in
      let (a, Ha) := eval_app_impl m n _ in
      exist _ a _
  | κ, a_param lp, p, H with inspect (me_drop (lp_mod lp) κ) := {
    | exist _ (me_frame a args κ') E => exist _ (env_var args (lp_param lp)) _
    | exist _ (me_base j) E with inspect (List.nth_error Ξ j) := {
      | exist _ (Some U) E' with eval_ptele_impl (me_base (S j)) j (List.length (gu_params U)) (List.skipn (lp_param lp) (gu_params U)) _ := {
        | exist _ (v :: ρp) Hρ => exist _ v _
        | exist _ nil Hρ => False_rect _ _ }
      | exist _ None E' => False_rect _ _ } }
  | κ, a_glob (p_rel m ip), p, H =>
      let (r, Hr) := eval_ent_impl (me_drop m κ) ip _ in
      exist _ r _
  | κ, a_glob (p_abs fp ip), p, H with inspect (gds_lookup Θ fp) := {
    | exist _ (Some U) E =>
        let (r, Hr) := eval_pend_impl (me_base 0) (p_abs fp nil) (List.length (gu_params U)) nil ip _ in
        exist _ r _
    | exist _ None E => False_rect _ _ }

  with eval_natrec_impl κ A MZ MS m p (H : eval_natrec_order Θ Ξ κ A MZ MS m p) : { d | ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ d } by struct H :=
  | κ, A, MZ, MS, zeroᵈ  , p, H =>
      let (mz, Hmz) := eval_exp_impl κ MZ p _ in
      exist _ mz _
  | κ, A, MZ, MS, succᵈ m, p, H =>
      let (mr, Hmr) := eval_natrec_impl κ A MZ MS m p _ in
      let (r, Hr) := eval_exp_impl κ MS (p ↦ m ↦ mr) _ in
      exist _ r _
  | κ, A, MZ, MS, ⇑ a m , p, H =>
      let (mz, Hmz) := eval_exp_impl κ MZ p _ in
      let (mA, HmA) := eval_exp_impl κ A (p ↦ ⇑ a m) _ in
      exist _ ⇑ mA recᵈ m under κ p return A | zero -> mz | succ -> MS end _

  with eval_app_impl m n (H : eval_app_order Θ Ξ m n) : { d | $| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | λᵈ κ p M        , n, H =>
      let (m, Hm) := eval_exp_impl κ M (p ↦ n) _ in
      exist _ m _
  | ⇑ (Πᵈ a κ p B) m, n, H =>
      let (b, Hb) := eval_exp_impl κ B (p ↦ n) _ in
      exist _ ⇑ b (m $ᵈ ⇓ a n) _
  | d_gfn κ a c args ip, n, H =>
      let (r, Hr) := eval_pend_impl κ a c (n :: args) ip _ in
      exist _ r _

  with eval_pend_impl κ a c args ip (H : eval_pend_order Θ Ξ κ a c args ip) : { d | eval_pend Θ Ξ κ a c args ip d } by struct H :=
  | κ, a, c, args, ip, H with inspect (Nat.ltb (List.length args) c) := {
    | exist _ true E => exist _ (d_gfn κ a c args ip) _
    | exist _ false E =>
        let (r, Hr) := eval_ent_impl (me_frame a args κ) ip
          (match H in eval_pend_order _ _ κ0 a0 c0 args0 ip0
             return (Nat.ltb (List.length args0) c0 = false -> eval_ent_order Θ Ξ (me_frame a0 args0 κ0) ip0) with
           | @epo_wait _ _ _ _ _ _ _ Hlt => fun E0 => False_rect _ (pend_contra _ _ Hlt E0)
           | @epo_enter _ _ _ _ _ _ _ _ Hent => fun _ => Hent
           end E) in
        exist _ r _ }

  with eval_ent_impl κ ip (H : eval_ent_order Θ Ξ κ ip) : { d | eval_ent Θ Ξ κ ip d } by struct H :=
  | κ, nil, H => False_rect _ _
  | κ, y :: nil, H with inspect (frame_at Θ Ξ (me_addr κ)) := {
    | exist _ (Some (Δ, Φ)) E with inspect (gm_find Φ y) := {
      | exist _ (Some (ge_def true pv A (Some M))) E' =>
          let (r, Hr) := eval_exp_impl κ M nil _ in
          exist _ r _
      | exist _ (Some (ge_def true pv A None)) E' =>
          let (a, Ha) := eval_exp_impl κ A nil _ in
          let (m, Hm) := eval_gne_impl κ (addr_depth (me_addr κ)) (d_glob (path_in (me_addr κ) y)) _ in
          exist _ (⇑ a m) _
      | exist _ (Some (ge_def false pv A B)) E' =>
          let (a, Ha) := eval_exp_impl κ A nil _ in
          let (m, Hm) := eval_gne_impl κ (addr_depth (me_addr κ)) (d_glob (path_in (me_addr κ) y)) _ in
          exist _ (⇑ a m) _
      | exist _ (Some (ge_mod _ _)) E' => False_rect _ _
      | exist _ None E' => False_rect _ _ }
    | exist _ None E => False_rect _ _ }
  | κ, x :: (z :: ip), H with inspect (frame_at Θ Ξ (me_addr κ)) := {
    | exist _ (Some (Δ, Φ)) E with inspect (gm_find Φ x) := {
      | exist _ (Some (ge_mod Δ' Φ')) E' =>
          let (r, Hr) := eval_pend_impl κ (path_in (me_addr κ) x) (List.length Δ') nil (z :: ip) _ in
          exist _ r _
      | exist _ (Some (ge_def _ _ _ _)) E' => False_rect _ _
      | exist _ None E' => False_rect _ _ }
    | exist _ None E => False_rect _ _ }

  with eval_ptele_impl κ j c Γ (H : eval_ptele_order Θ Ξ κ j c Γ) : { ρ | eval_ptele Θ Ξ κ j c Γ ρ } by struct H :=
  | κ, j, c, nil, H => exist _ nil _
  | κ, j, c, T :: Γ, H =>
      let (ρ, Hρ) := eval_ptele_impl κ j c Γ _ in
      let (a, Ha) := eval_exp_impl κ T ρ _ in
      exist _ (⇑ a (d_param (lp_mk j (c - S (List.length Γ)))) :: ρ) _

  with eval_gne_impl κ n h (H : eval_gne_order Θ Ξ κ n h) : { h' | eval_gne Θ Ξ κ n h h' } by struct H :=
  | κ, 0, h, H => exist _ h _
  | me_base _, S n, h, H => False_rect _ _
  | me_frame a args κ, S n, h, H with inspect (frame_at Θ Ξ a) := {
    | exist _ (Some (Δ, Φ)) E =>
        let (h1, Hh1) := eval_gne_impl κ n h _ in
        let (h2, Hh2) := eval_fargs_impl κ Δ args h1 _ in
        exist _ h2 _
    | exist _ None E => False_rect _ _ }

  with eval_fargs_impl κ Δ args h (H : eval_fargs_order Θ Ξ κ Δ args h) : { h' | eval_fargs Θ Ξ κ Δ args h h' } by struct H :=
  | κ, nil, nil, h, H => exist _ h _
  | κ, T :: Δ, v :: args, h, H =>
      let (h1, Hh1) := eval_fargs_impl κ Δ args h _ in
      let (t, Ht) := eval_exp_impl κ T args _ in
      exist _ (h1 $ᵈ ⇓ t v) _
  | κ, nil, _ :: _, h, H => False_rect _ _
  | κ, _ :: _, nil, h, H => False_rect _ _.
End EvalImpl.

Extraction Inline eval_exp_impl_functional
  eval_natrec_impl_functional
  eval_app_impl_functional
  eval_pend_impl_functional
  eval_ent_impl_functional
  eval_ptele_impl_functional
  eval_gne_impl_functional
  eval_fargs_impl_functional.

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

Lemma eval_exp_impl_complete : forall Θ Ξ κ M p m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ m ->
    exists H H', eval_exp_impl Θ Ξ κ M p H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_natrec_impl_complete : forall Θ Ξ κ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ p ↘ r ->
    exists H H', eval_natrec_impl Θ Ξ κ A MZ MS m p H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall Θ Ξ m n r,
    $| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', eval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.
