(** * Experiment Z: moving VALUES along [↑ₘ n] (pushing [n] frames)

    Research prototype; not part of the development. *)
From Stdlib Require Import String.
From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import GlobalCtx ModSubst.
From Mctt.Core.Syntactic.System Require Import Transport Discharge.
From Mctt.Core.Semantic Require Import Evaluation Readback PER.
Import Domain_Notations Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The action of [↑ₘ n] on values *)

Fixpoint dpush (n : nat) (d : domain) {struct d} : domain :=
  match d with
  | d_nat => d_nat
  | d_pi a ρ B => d_pi (dpush n a) (List.map (dpush n) ρ) B[↑ₘ n]ᵐ
  | d_univ i => d_univ i
  | d_zero => d_zero
  | d_succ m => d_succ (dpush n m)
  | d_fn ρ M => d_fn (List.map (dpush n) ρ) M[↑ₘ n]ᵐ
  | d_neut a m => d_neut (dpush n a) (dnpush n m)
  end
with dnpush (n : nat) (m : domain_ne) {struct m} : domain_ne :=
  match m with
  | d_var x => d_var x
  | d_app m v => d_app (dnpush n m) (dfpush n v)
  | d_natrec ρ P mz MS m => d_natrec (List.map (dpush n) ρ) P[↑ₘ n]ᵐ (dpush n mz) MS[↑ₘ n]ᵐ (dnpush n m)
  | d_glob p => d_glob p[p_rel n nil]ᵖ
  | d_param lp => d_param (lp_mk (n + lp_mod lp) (lp_param lp))
  end
with dfpush (n : nat) (v : domain_nf) {struct v} : domain_nf :=
  match v with
  | d_dom a m => d_dom (dpush n a) (dpush n m)
  end.

Abbreviation epush n ρ := (List.map (dpush n) ρ).

Lemma env_var_push : forall n ρ x, env_var (epush n ρ) x = dpush n (env_var ρ x).
Proof. intros n ρ x; revert ρ; induction x; intros [| d ρ]; cbn; auto; apply (IHx nil). Qed.

(** [ms_q (↑ₘ n)] is [↑ₘ n] up to [ms_eq]. *)
Lemma msub_q_shift : forall (M : exp) n, M[ms_q (↑ₘ n)]ᵐ = M[↑ₘ n]ᵐ.
Proof. intros; apply exp_msub_ext, ms_q_shift. Qed.
Lemma msub_qq_shift : forall (M : exp) n, M[ms_q (ms_q (↑ₘ n))]ᵐ = M[↑ₘ n]ᵐ.
Proof. intros; apply exp_msub_ext, (ms_qn_shift 2). Qed.
Lemma msub_qn_shift : forall (M : exp) k n, M[ms_qn k (↑ₘ n)]ᵐ = M[↑ₘ n]ᵐ.
Proof. intros; apply exp_msub_ext, ms_qn_shift. Qed.

(** ** Resolution after pushing frames *)

Section Push.
  Variables (Θ : gdeps) (Ξ Ξ' : gstack) (n : nat).
  Hypothesis Hlen : length Ξ' = n.
  Hypothesis HΘ : units_scoped Θ.

  Lemma nth_push : forall m, List.nth_error (Ξ' ++ Ξ) (n + m) = List.nth_error Ξ m.
  Proof. intros; rewrite List.nth_error_app2 by lia; f_equal; lia. Qed.

  Lemma gc_resolve_push : forall p Δ b pv A B,
      gc_resolve Θ Ξ p = Some (Δ, ge_def b pv A B) ->
      gc_resolve Θ (Ξ' ++ Ξ) p[p_rel n nil]ᵖ = Some (Δ[↑ₘ n]ᵐ, ge_def b pv A[↑ₘ n]ᵐ B[↑ₘ n]ᵐ).
  Proof.
    intros [[fp | m] ip] * H.
    - (* a filed unit: closed, the shift does nothing *)
      pose proof (gc_resolve_sound _ _ _ _ _ H) as Hl.
      destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl ltac:(cbn; congruence)) as (HΔ & HA & HB).
      rewrite (ctx_msub_shift_nil _ _ _ HΔ), (exp_msub_shift_nil _ _ _ HA), (opt_msub_shift_nil _ _ _ HB).
      exact H.
    - unfold gc_resolve in *; cbn in *.
      rewrite Nat.sub_0_r, nth_push.
      destruct (List.nth_error Ξ m) as [U |]; [| discriminate ].
      unfold ge_read_rel in *.
      destruct (gm_resolve (gu_mod U) ip) as [[Δ0 [b0 pv0 A0 B0 |]] |]; try discriminate.
      injection H as <- <- <- <- <-.
      rewrite ctx_msub_shift_shift, exp_msub_shift_shift, opt_msub_shift_shift; reflexivity.
  Qed.

  Lemma params_shift_n : forall (M : exp) m,
      M[↑ₘ (S m)]ᵐ[sb_params m][↑ₘ n]ᵐ = M[↑ₘ (S (n + m))]ᵐ[sb_params (n + m)].
  Proof.
    intros; rewrite (exp_msub_sub_gen _ (sb_params m) (sb_params (n + m)) (↑ₘ n) (↑ₘ n)),
      exp_msub_shift_shift by (repeat split; intros; reflexivity).
    do 3 f_equal; lia.
  Qed.

  Lemma gs_param_push : forall lp T,
      gs_param Ξ lp = Some T ->
      gs_param (Ξ' ++ Ξ) (lp_mk (n + lp_mod lp) (lp_param lp)) = Some T[↑ₘ n]ᵐ.
  Proof.
    intros [m k] T H; unfold gs_param in *; cbn in *.
    rewrite nth_push; destruct (List.nth_error Ξ m) as [U |]; [| discriminate ].
    destruct (ctx_get (gu_params U) k) as [T0 |]; cbn in *; [| discriminate ].
    injection H as <-; rewrite params_shift_n; reflexivity.
  Qed.

  (** ** Evaluation commutes with the action *)

  Theorem eval_push :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> ⟦ M[↑ₘ n]ᵐ ⟧ Θ ⍮ Ξ' ++ Ξ ⍮ epush n ρ ↘ dpush n m) /\
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       ⟦rec dpush n m return A[↑ₘ n]ᵐ | zero -> MZ[↑ₘ n]ᵐ | succ -> MS[↑ₘ n]ᵐ end ⟧ Θ ⍮ Ξ' ++ Ξ ⍮ epush n ρ ↘ dpush n r) /\
    (forall f a r, $| f & a | Θ ⍮ Ξ ↘ r -> $| dpush n f & dpush n a | Θ ⍮ Ξ' ++ Ξ ↘ dpush n r).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => ⟦ M[↑ₘ n]ᵐ ⟧ Θ ⍮ Ξ' ++ Ξ ⍮ epush n ρ ↘ dpush n m)
             (fun A MZ MS m ρ r _ => ⟦rec dpush n m return A[↑ₘ n]ᵐ | zero -> MZ[↑ₘ n]ᵐ | succ -> MS[↑ₘ n]ᵐ end ⟧ Θ ⍮ Ξ' ++ Ξ ⍮ epush n ρ ↘ dpush n r)
             (fun f a r _ => $| dpush n f & dpush n a | Θ ⍮ Ξ' ++ Ξ ↘ dpush n r));
      intros; cbn [msubst MSub_exp exp_msub ms_glob ms_param ms_shift dpush dnpush dfpush List.map] in *;
      rewrite ?msub_q_shift, ?msub_qq_shift in *.
    all: try solve [ econstructor; eauto ].
    - apply eval_exp_var_eq; rewrite env_var_push; reflexivity.
    - (* δ *)
      pose proof (gc_resolve_push _ _ _ _ _ _ e) as He; cbn [msubst MSub_option option_map] in He.
      eapply eval_exp_glob_delta; [ exact He |].
      rewrite ctx_fn_msub, msub_qn_shift in *; assumption.
    - (* opaque *)
      pose proof (gc_resolve_push _ _ _ _ _ _ e) as He.
      eapply eval_exp_glob_neut; [ exact He | |].
      + destruct o as [-> | ->]; [ left | right ]; reflexivity.
      + rewrite ctx_pi_msub, msub_qn_shift in *; assumption.
    - (* parameter *)
      eapply eval_exp_param; [ apply gs_param_push; eassumption | assumption ].
  Qed.
End Push.

Corollary eval_push1 : forall Θ U Ξ M ρ m,
    units_scoped Θ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> ⟦ M[↑ₘ 1]ᵐ ⟧ Θ ⍮ U :: Ξ ⍮ epush 1 ρ ↘ dpush 1 m.
Proof. intros * HΘ H; exact (proj1 (eval_push Θ Ξ (U :: nil) 1 eq_refl HΘ) _ _ _ H). Qed.

(** ** Normal forms *)

Fixpoint nf_push (n : nat) (W : nf) : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_nat => nf_nat
  | nf_zero => nf_zero
  | nf_succ W => nf_succ (nf_push n W)
  | nf_pi A B => nf_pi (nf_push n A) (nf_push n B)
  | nf_fn A W => nf_fn (nf_push n A) (nf_push n W)
  | nf_neut W => nf_neut (ne_push n W)
  end
with ne_push (n : nat) (W : ne) : ne :=
  match W with
  | ne_natrec A MZ MS W => ne_natrec (nf_push n A) (nf_push n MZ) (nf_push n MS) (ne_push n W)
  | ne_app W N => ne_app (ne_push n W) (nf_push n N)
  | ne_var x => ne_var x
  | ne_param lp => ne_param (lp_mk (n + lp_mod lp) (lp_param lp))
  | ne_glob p => ne_glob p[p_rel n nil]ᵖ
  end.

Scheme nf_mut_ind := Induction for nf Sort Prop with ne_mut_ind := Induction for ne Sort Prop.
Combined Scheme nf_ne_mut_ind from nf_mut_ind, ne_mut_ind.

(** [nf_push] is [↑ₘ n] on the embedded expression. *)
Lemma nf_push_exp : forall n,
    (forall W : nf, nf_to_exp (nf_push n W) = (nf_to_exp W)[↑ₘ n]ᵐ) /\
    (forall W : ne, ne_to_exp (ne_push n W) = (ne_to_exp W)[↑ₘ n]ᵐ).
Proof.
  intros n; apply nf_ne_mut_ind; intros; cbn [nf_push ne_push nf_to_exp ne_to_exp msubst MSub_exp exp_msub ms_glob ms_param ms_shift lp_mod lp_param];
    rewrite ?msub_q_shift, ?msub_qq_shift; congruence.
Qed.

Section PushRead.
  Variables (Θ : gdeps) (Ξ Ξ' : gstack) (n : nat).
  Hypothesis Hlen : length Ξ' = n.
  Hypothesis HΘ : units_scoped Θ.

  Let Hev := eval_push Θ Ξ Ξ' n Hlen HΘ.

  Theorem read_push :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> Rnf dfpush n m in Θ ⍮ Ξ' ++ Ξ ⍮ s ↘ nf_push n W) /\
    (forall s m W, Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> Rne dnpush n m in Θ ⍮ Ξ' ++ Ξ ⍮ s ↘ ne_push n W) /\
    (forall s a W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> Rtyp dpush n a in Θ ⍮ Ξ' ++ Ξ ⍮ s ↘ nf_push n W).
  Proof.
    destruct Hev as (He & Hr & Ha).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => Rnf dfpush n m in Θ ⍮ Ξ' ++ Ξ ⍮ s ↘ nf_push n W)
             (fun s m W _ => Rne dnpush n m in Θ ⍮ Ξ' ++ Ξ ⍮ s ↘ ne_push n W)
             (fun s a W _ => Rtyp dpush n a in Θ ⍮ Ξ' ++ Ξ ⍮ s ↘ nf_push n W));
      intros; cbn [dpush dnpush dfpush nf_push ne_push List.map] in *.
    all: try solve [ econstructor; eauto ].
    - (* η *)
      econstructor; [ eassumption | apply (Ha _ _ _ e) | apply (He _ _ _ e0) | eassumption ].
    - econstructor; [ apply (He _ _ _ e) | eassumption | apply (He _ _ _ e0) | eassumption
                    | apply (He _ _ _ e1) | apply (He _ _ _ e2) | eassumption | eassumption ].
    - econstructor; [ eassumption | apply (He _ _ _ e) | eassumption ].
  Qed.
End PushRead.

(** ** Functoriality: what a Kripke-style model would need *)

Lemma path_push_add : forall a b (p : path), p[p_rel a nil]ᵖ[p_rel b nil]ᵖ = p[p_rel (b + a) nil]ᵖ.
Proof. apply path_open_shift_add. Qed.

Lemma dpush_dpush : forall a b,
    (forall d, dpush b (dpush a d) = dpush (b + a) d).
Proof.
  intros a b.
  fix IH 1 with (IHn (m : domain_ne) {struct m} : dnpush b (dnpush a m) = dnpush (b + a) m)
                (IHf (v : domain_nf) {struct v} : dfpush b (dfpush a v) = dfpush (b + a) v).
  - intros [| a0 ρ B | i | | m | ρ M | a0 m]; cbn; rewrite ?exp_msub_shift_shift; f_equal; auto.
    all: induction ρ as [| d ρ IHρ]; cbn; f_equal; auto.
  - intros [x | m v | ρ P mz MS m | p | [k j]]; cbn; rewrite ?exp_msub_shift_shift, ?path_push_add; f_equal; auto.
    + induction ρ as [| d ρ IHρ]; cbn; f_equal; auto.
    + f_equal; lia.
  - intros [a0 m]; cbn; f_equal; auto.
Qed.

(** ** The PER model along a push *)

Section PushPER.
  Variables (Θ : gdeps) (Ξ Ξ' : gstack) (n : nat).
  Hypothesis Hlen : length Ξ' = n.
  Hypothesis HΘ : units_scoped Θ.

  Abbreviation GC1 := (gc_mk Θ Ξ).
  Abbreviation GC2 := (gc_mk Θ (Ξ' ++ Ξ)).

  Let Hev := eval_push Θ Ξ Ξ' n Hlen HΘ.
  Let Hrd := read_push Θ Ξ Ξ' n Hlen HΘ.

  Lemma per_bot_push : forall m m', @per_bot GC1 m m' -> @per_bot GC2 (dnpush n m) (dnpush n m').
  Proof.
    intros * H s; destruct (H s) as (L & H1 & H2).
    exists (ne_push n L); split; apply Hrd; assumption.
  Qed.

  Lemma per_top_push : forall m m', @per_top GC1 m m' -> @per_top GC2 (dfpush n m) (dfpush n m').
  Proof.
    intros * H s; destruct (H s) as (L & H1 & H2).
    exists (nf_push n L); split; apply Hrd; assumption.
  Qed.

  Lemma per_top_typ_push : forall a a', @per_top_typ GC1 a a' -> @per_top_typ GC2 (dpush n a) (dpush n a').
  Proof.
    intros * H s; destruct (H s) as (L & H1 & H2).
    exists (nf_push n L); split; apply Hrd; assumption.
  Qed.

  Lemma per_nat_push : forall m m', @per_nat GC1 m m' -> @per_nat GC2 (dpush n m) (dpush n m').
  Proof. induction 1; cbn; constructor; auto using per_bot_push. Qed.

  Lemma per_ne_push : forall m m', @per_ne GC1 m m' -> @per_ne GC2 (dpush n m) (dpush n m').
  Proof. destruct 1; cbn; constructor; auto using per_bot_push. Qed.

  (** The transport statement. *)
  Definition transported (i : nat) (R : relation domain) (a a' : domain) : Prop :=
    exists R', @per_univ_elem GC2 i R' (dpush n a) (dpush n a') /\
          forall x y, R x y -> R' (dpush n x) (dpush n y).

  (** *** The only obstruction: arguments outside the image.

      [Dense] says every pair related at the pushed context by the relation of
      a transported type is the image of a pair related before.  Under it the
      transport goes through; [dense_fails] shows it is false as soon as
      [n > 0]. *)
  Definition Dense : Prop :=
    forall i R a a' R',
      @per_univ_elem GC1 i R a a' ->
      @per_univ_elem GC2 i R' (dpush n a) (dpush n a') ->
      forall e e', R' e e' -> exists d d', R d d' /\ e = dpush n d /\ e' = dpush n d'.

  Hypothesis HD : Dense.

  Theorem per_univ_elem_push_dense : forall i R a a',
      @per_univ_elem GC1 i R a a' -> transported i R a a'.
  Proof.
    destruct Hev as (He & Hr & Ha).
    intros i R a a' H; per_univ_elem_induction H.
    - (* universe *)
      subst j'. exists (@per_univ GC2 j); split.
      + apply (@per_univ_elem_core_univ' GC2); [ assumption | reflexivity ].
      + intros x y Hxy; apply H1 in Hxy as [R0 HR0].
        destruct (H2 _ _ _ HR0) as (R1 & HR1 & _); exists R1; exact HR1.
    - (* ℕ *)
      exists (@per_nat GC2); split.
      + cbn; basic_per_univ_elem_econstructor; reflexivity.
      + intros x y Hxy; apply per_nat_push, H; assumption.
    - (* Π *)
      destruct IHH as (in_rel' & Hin' & Hinmap).
      set (out_rel' := fun (c c' : domain) (_ : in_rel' c c') (m m' : domain) =>
                         forall R0, @rel_typ GC2 i B[↑ₘ n]ᵐ (epush n ρ ↦ c) B'[↑ₘ n]ᵐ (epush n ρ' ↦ c') R0 -> R0 m m').
      (* the codomain at an image pair *)
      assert (Hcod : forall d d' (Hd : in_rel d d'),
                 exists b b' R1, ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ d ↘ b /\ ⟦ B' ⟧ Θ ⍮ Ξ ⍮ ρ' ↦ d' ↘ b' /\
                   @per_univ_elem GC2 i R1 (dpush n b) (dpush n b') /\
                   (forall x y, out_rel d d' Hd x y -> R1 (dpush n x) (dpush n y))).
      { intros d d' Hd; destruct (H1 d d' Hd) as [b b' Hb Hb' [_ (R1 & HR1 & Hmap)]].
        exists b, b', R1; repeat split; assumption. }
      exists (fun f f' => forall c c' (Hc : in_rel' c c'), @rel_mod_app GC2 f c f' c' (out_rel' c c' Hc)).
      split.
      + cbn [dpush]. eapply (@per_univ_elem_pi' GC2); [ exact Hin' | | reflexivity ].
        intros c c' Hc.
        destruct (HD _ _ _ _ _ H Hin' _ _ Hc) as (d & d' & Hd & -> & ->).
        destruct (Hcod d d' Hd) as (b & b' & R1 & Hb & Hb' & HR1 & _).
        econstructor; [ apply (He _ _ _ Hb) | apply (He _ _ _ Hb') |].
        eapply per_univ_elem_resp_iff; [ exact HR1 |].
        intros x0 y0; split; [ intros Hxy R0 [b0 b0' Hb0 Hb0' HR0]
               | intros Hxy; apply Hxy; econstructor; [ apply (He _ _ _ Hb) | apply (He _ _ _ Hb') | exact HR1 ] ].
        cbn in Hb0, Hb0'.
        rewrite (functional_eval_exp _ _ _ _ Hb0 (He _ _ _ Hb)),
          (functional_eval_exp _ _ _ _ Hb0' (He _ _ _ Hb')) in HR0.
        apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR0); assumption.
      + intros f f' Hf c c' Hc.
        destruct (HD _ _ _ _ _ H Hin' _ _ Hc) as (d & d' & Hd & -> & ->).
        destruct (Hcod d d' Hd) as (b & b' & R1 & Hb & Hb' & HR1 & Hmap).
        destruct (proj1 (H2 f f') Hf d d' Hd) as [fa f'a' Hfa Hf'a' Hr1].
        econstructor; [ apply (Ha _ _ _ Hfa) | apply (Ha _ _ _ Hf'a') |].
        intros R0 [b0 b0' Hb0 Hb0' HR0]; cbn in Hb0, Hb0'.
        rewrite (functional_eval_exp _ _ _ _ Hb0 (He _ _ _ Hb)),
          (functional_eval_exp _ _ _ _ Hb0' (He _ _ _ Hb')) in HR0.
        apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR0), Hmap; assumption.
    - (* neutral *)
      exists (@per_ne GC2); split.
      + cbn; basic_per_univ_elem_econstructor; [ apply per_bot_push; assumption | reflexivity ].
      + intros x y Hxy; apply per_ne_push, H0; assumption.
  Qed.
End PushPER.

(** *** Density is false: the new frame's parameters are not in the image,
    not even up to the relation. *)

Lemma read_ne_push_not_new_param : forall Θ Ξ n s m k,
    n > 0 -> ~ Rne dnpush n m in Θ ⍮ Ξ ⍮ s ↘ ne_param (lp_mk 0 k).
Proof.
  intros * Hn H; destruct m; cbn in H; inversion H; subst; lia.
Qed.

Theorem new_param_not_in_image : forall Θ Ξ Ξ' n,
    n > 0 ->
    let e := d_neut d_nat (d_param (lp_mk 0 0)) in
    @per_nat (gc_mk Θ (Ξ' ++ Ξ)) e e /\
    forall d, ~ @per_nat (gc_mk Θ (Ξ' ++ Ξ)) e (dpush n d).
Proof.
  intros * Hn e; split.
  - constructor; intros s; exists (ne_param (lp_mk 0 0)); split; constructor.
  - intros d H; destruct d; cbn in H; inversion H as [| | ? ? ? ? Hb]; subst.
    destruct (Hb 0) as (L & H1 & H2); inversion H1; subst.
    eapply read_ne_push_not_new_param; [ exact Hn | exact H2 ].
Qed.

Corollary dense_fails : forall Θ Ξ Ξ' n (Hlen : length Ξ' = n),
    n > 0 -> ~ Dense Θ Ξ Ξ' n.
Proof.
  intros * Hlen Hn HD.
  assert (H1 : @per_univ_elem (gc_mk Θ Ξ) 0 (@per_nat (gc_mk Θ Ξ)) d_nat d_nat)
    by (basic_per_univ_elem_econstructor; reflexivity).
  assert (H2 : @per_univ_elem (gc_mk Θ (Ξ' ++ Ξ)) 0 (@per_nat (gc_mk Θ (Ξ' ++ Ξ))) (dpush n d_nat) (dpush n d_nat))
    by (cbn; basic_per_univ_elem_econstructor; reflexivity).
  destruct (new_param_not_in_image Θ Ξ Ξ' n Hn) as [He Hne].
  destruct (HD _ _ _ _ _ H1 H2 _ _ He) as (d & d' & _ & Hd & _).
  apply (Hne d); rewrite <- Hd; exact He.
Qed.

(** ** Close: the readback of a member applied to a parameter of function
    type is η-long, so it is not the closing of the readback.

    Frame [x] has one parameter [P : ℕ → ℕ] and an opaque member [m : ℕ].
    Inside, [⇑ ℕ (d_glob (p_rel 0 [m]))] reads back to [m].  Closing sends
    [m] to [x.m $ #0] ([ms_close]), and the only candidate value is the
    neutral [x.m] applied to the variable standing for [P] (level [0]).  Its
    readback is [x.m (λ y. #1 y)], not [x.m #0]. *)
Section CloseEta.
  Local Open Scope string_scope.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition q_xm : path := p_rel 0 ("x" :: "m" :: nil).
  Definition tyNN : domain := d_pi d_nat nil a_nat.
  Definition v_closed : domain :=
    d_neut d_nat (d_app (d_glob q_xm) (d_dom tyNN (d_neut tyNN (d_var 0)))).

  Lemma close_target : (a_glob (p_rel 0 ("m" :: nil)))[ms_close (p_rel 0 ("x" :: nil)) 1 0]ᵐ
                       = a_app (a_glob q_xm) (a_var 0).
  Proof. reflexivity. Qed.

  Lemma close_readback_eta :
    exists W, Rnf d_dom d_nat v_closed in Θ ⍮ Ξ ⍮ 1 ↘ W /\
         nf_to_exp W = a_app (a_glob q_xm) (a_fn a_nat (a_app (a_var 1) (a_var 0))).
  Proof.
    eexists; split.
    - unfold v_closed, tyNN.
      eapply read_nf_nat_neut, read_ne_app; [ apply read_ne_glob |].
      eapply read_nf_fn; [ apply read_typ_nat | eapply eval_app_neut; apply eval_exp_nat
                         | apply eval_exp_nat |].
      eapply read_nf_nat_neut, read_ne_app; [ apply read_ne_var |].
      eapply read_nf_nat_neut, read_ne_var.
    - reflexivity.
  Qed.

  Corollary close_readback_not_msub : forall W,
      Rnf d_dom d_nat v_closed in Θ ⍮ Ξ ⍮ 1 ↘ W ->
      nf_to_exp W <> (a_glob (p_rel 0 ("m" :: nil)))[ms_close (p_rel 0 ("x" :: nil)) 1 0]ᵐ.
  Proof.
    intros W HW; destruct close_readback_eta as (W' & HW' & HE).
    rewrite (functional_read_nf _ _ _ _ HW HW'), HE, close_target; discriminate.
  Qed.
End CloseEta.
