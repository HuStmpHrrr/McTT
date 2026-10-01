(** * Simulation: Evaluating a Substituted Term against the Original

    Evaluation applies no substitution, so the only bridge between a term
    [M[θ]] — which the syntactic judgments produce, e.g. a global's body after
    the module substitutions of resolution — and [M] itself, evaluated where
    [θ]'s leaves already mean what they stand for, is semantic.  [θ] is a
    simultaneous replacement of the three kinds of leaves (λ-variables, module
    parameters, globals) by binder-free terms ([tsub]); [cfg θ …] says that,
    at the two configurations, each leaf's image evaluates to something
    related to what the leaf evaluates to on the right.  Then the values are
    related by [vsim]: equal up to the syntax inside closures, which is
    related the same way ([csim]).  [vsim] is reflexive by construction.

    The main theorem ([sim_eval]) is by induction on the left evaluation; the
    right evaluation exists and its value is related.  [vsim]-related values
    read back equally ([sim_read]). *)

From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import GlobalCtx.
From Mctt.Core.Semantic Require Import Evaluation Readback.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** ** Simultaneous Replacement of Leaves *)

Record tsub : Set := ts_mk
  { ts_var : nat -> exp
  ; ts_param : lpath -> exp
  ; ts_glob : path -> exp }.

Definition ts_q (θ : tsub) : tsub :=
  ts_mk (fun x => match x with 0 => a_var 0 | S y => (ts_var θ y)[↑]ʷ end)
        (fun lp => (ts_param θ lp)[↑]ʷ)
        (fun p => (ts_glob θ p)[↑]ʷ).

Fixpoint exp_tsub (θ : tsub) (M : exp) : exp :=
  match M with
  | a_typ i => a_typ i
  | a_nat => a_nat
  | a_zero => a_zero
  | a_succ M => a_succ (exp_tsub θ M)
  | a_natrec A MZ MS M =>
      a_natrec (exp_tsub (ts_q θ) A) (exp_tsub θ MZ) (exp_tsub (ts_q (ts_q θ)) MS) (exp_tsub θ M)
  | a_pi A B => a_pi (exp_tsub θ A) (exp_tsub (ts_q θ) B)
  | a_fn A M => a_fn (exp_tsub θ A) (exp_tsub (ts_q θ) M)
  | a_app M N => a_app (exp_tsub θ M) (exp_tsub θ N)
  | a_var x => ts_var θ x
  | a_param lp => ts_param θ lp
  | a_glob p => ts_glob θ p
  end.

Definition ts_id : tsub := ts_mk a_var a_param a_glob.

Definition ts_eq (θ θ' : tsub) : Prop :=
  (forall x, ts_var θ x = ts_var θ' x) /\
  (forall lp, ts_param θ lp = ts_param θ' lp) /\
  (forall p, ts_glob θ p = ts_glob θ' p).

Lemma ts_q_eq : forall θ θ', ts_eq θ θ' -> ts_eq (ts_q θ) (ts_q θ').
Proof.
  intros * (H1 & H2 & H3); repeat split; intros; cbn; rewrite ?H1, ?H2, ?H3; try reflexivity.
  destruct x; cbn; rewrite ?H1; reflexivity.
Qed.

Lemma exp_tsub_ext : forall M θ θ', ts_eq θ θ' -> exp_tsub θ M = exp_tsub θ' M.
Proof.
  induction M; intros * H; cbn; try reflexivity;
    try solve [ destruct H as (H1 & H2 & H3); auto ];
    f_equal; eauto using ts_q_eq.
Qed.

Lemma ts_q_id : ts_eq (ts_q ts_id) ts_id.
Proof. repeat split; intros; [ destruct x |..]; reflexivity. Qed.

Lemma ts_q_eq_id : forall θ, ts_eq θ ts_id -> ts_eq (ts_q θ) ts_id.
Proof.
  intros θ (H1 & H2 & H3); repeat split; intros; cbn; rewrite ?H1, ?H2, ?H3; [ destruct x; cbn; rewrite ?H1 |..]; reflexivity.
Qed.

Lemma exp_tsub_id_gen : forall M θ, ts_eq θ ts_id -> exp_tsub θ M = M.
Proof.
  induction M; intros θ H; cbn;
    try solve [ reflexivity | destruct H as (H1 & H2 & H3); auto ];
    f_equal; eauto using ts_q_eq_id.
Qed.

Lemma ts_eq_refl : forall θ, ts_eq θ θ.
Proof. intros; repeat split; reflexivity. Qed.

Corollary exp_tsub_id : forall M, exp_tsub ts_id M = M.
Proof. intros; apply exp_tsub_id_gen, ts_eq_refl. Qed.

(** *** Binder-free terms

    What a leaf may be replaced by.  Evaluating one creates no closure, so its
    value does not depend on how its environment is represented: weakening it
    and extending the environment gives the same value. *)
Fixpoint bfree (M : exp) : Prop :=
  match M with
  | a_pi _ _ | a_fn _ _ | a_natrec _ _ _ _ => False
  | a_succ M => bfree M
  | a_app M N => bfree M /\ bfree N
  | _ => True
  end.

Lemma bfree_wk : forall M φ, bfree M -> bfree M[φ]ʷ.
Proof. induction M; intros; cbn in *; intuition. Qed.

(** *** Scoping of the right-hand term *)
Fixpoint exp_ok (n : nat) (P : lpath -> Prop) (Q : path -> Prop) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_nat | a_zero => True
  | a_succ M => exp_ok n P Q M
  | a_natrec A MZ MS M => exp_ok (S n) P Q A /\ exp_ok n P Q MZ /\ exp_ok (S (S n)) P Q MS /\ exp_ok n P Q M
  | a_pi A B | a_fn A B => exp_ok n P Q A /\ exp_ok (S n) P Q B
  | a_app M N => exp_ok n P Q M /\ exp_ok n P Q N
  | a_var x => x < n
  | a_param lp => P lp
  | a_glob p => Q p
  end.

Lemma exp_ok_mono : forall M n m P Q, n <= m -> exp_ok n P Q M -> exp_ok m P Q M.
Proof.
  induction M; intros * Hle H; cbn in *; intuition (eauto with arith; try lia).
  all: try (eapply IHM1; [| eassumption ]; lia).
  all: try (eapply IHM2; [| eassumption ]; lia).
  all: try (eapply IHM3; [| eassumption ]; lia).
Qed.

Lemma exp_ok_ex : forall M, exists n, exp_ok n (fun _ => True) (fun _ => True) M.
Proof.
  induction M; cbn.
  all: try solve [ exists 0; auto ].
  - exact IHM.
  - destruct IHM1 as [a Ha], IHM2 as [b Hb], IHM3 as [c Hc], IHM4 as [d Hd].
    exists (a + b + c + d); repeat split;
      (eapply exp_ok_mono; [| eassumption ]; lia).
  - destruct IHM1 as [a Ha], IHM2 as [b Hb].
    exists (a + b); split; (eapply exp_ok_mono; [| eassumption ]; lia).
  - destruct IHM1 as [a Ha], IHM2 as [b Hb].
    exists (a + b); split; (eapply exp_ok_mono; [| eassumption ]; lia).
  - destruct IHM1 as [a Ha], IHM2 as [b Hb].
    exists (a + b); split; (eapply exp_ok_mono; [| eassumption ]; lia).
  - match goal with |- exists _, ?y < _ => exists (S y); lia end.
Qed.

Section Sim.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  (** ** Weakening a binder-free term *)

  Lemma eval_param_env : forall κ lp ρ ρ' v,
      ⟦ a_param lp ⟧ κ ⍮ ρ ↘ v -> ⟦ a_param lp ⟧ κ ⍮ ρ' ↘ v.
  Proof. intros * H; inversion H; subst; econstructor; eassumption. Qed.

  Lemma eval_glob_env : forall κ p ρ ρ' v,
      ⟦ a_glob p ⟧ κ ⍮ ρ ↘ v -> ⟦ a_glob p ⟧ κ ⍮ ρ' ↘ v.
  Proof. intros * H; inversion H; subst; econstructor; eassumption. Qed.

  Lemma eval_bfree_shift : forall M κ ρ d v,
      bfree M ->
      ⟦ M[↑]ʷ ⟧ κ ⍮ ρ ↦ d ↘ v ->
      ⟦ M ⟧ κ ⍮ ρ ↘ v.
  Proof.
    induction M; intros * Hb H; cbn in *; try contradiction;
      try solve [ inversion H; subst; econstructor; eauto
                | eapply eval_param_env; eassumption
                | eapply eval_glob_env; eassumption ].
    - destruct Hb; inversion H; subst; econstructor; [ eapply IHM1 | eapply IHM2 | ]; eauto.
    - inversion H; subst; apply eval_exp_var_eq; reflexivity.
  Qed.

  Lemma eval_bfree_shift2 : forall M κ ρ d d' v,
      bfree M ->
      ⟦ M[↑]ʷ[↑]ʷ ⟧ κ ⍮ ρ ↦ d ↦ d' ↘ v ->
      ⟦ M ⟧ κ ⍮ ρ ↘ v.
  Proof. intros; do 2 (eapply eval_bfree_shift; eauto using bfree_wk). Qed.

  (** ** The relations *)

  Inductive vsim : domain -> domain -> Prop :=
  | vs_refl : forall d, vsim d d
  | vs_succ : forall m m', vsim m m' -> vsim (succᵈ m) (succᵈ m')
  | vs_pi : forall a a' κ ρ B κ' ρ' B',
      vsim a a' -> csim κ ρ B κ' ρ' B' -> vsim (Πᵈ a κ ρ B) (Πᵈ a' κ' ρ' B')
  | vs_fn : forall κ ρ M κ' ρ' M',
      csim κ ρ M κ' ρ' M' -> vsim (λᵈ κ ρ M) (λᵈ κ' ρ' M')
  | vs_neut : forall a a' m m',
      vsim a a' -> nsim m m' -> vsim (⇑ a m) (⇑ a' m')
  | vs_gfn : forall κ κ' a c args args' ip,
      mesim κ κ' -> envsim args args' -> vsim (d_gfn κ a c args ip) (d_gfn κ' a c args' ip)
  with nsim : domain_ne -> domain_ne -> Prop :=
  | ns_refl : forall m, nsim m m
  | ns_app : forall m m' a a' n n',
      nsim m m' -> vsim a a' -> vsim n n' -> nsim (m $ᵈ ⇓ a n) (m' $ᵈ ⇓ a' n')
  | ns_natrec : forall κ ρ A mz MS m κ' ρ' A' mz' MS' m',
      csim2 κ ρ A MS κ' ρ' A' MS' -> vsim mz mz' -> nsim m m' ->
      nsim (d_natrec κ ρ A mz MS m) (d_natrec κ' ρ' A' mz' MS' m')
  with envsim : env -> env -> Prop :=
  | es_nil : envsim nil nil
  | es_cons : forall d d' ρ ρ', vsim d d' -> envsim ρ ρ' -> envsim (d :: ρ) (d' :: ρ')
  with mesim : menv -> menv -> Prop :=
  | mes_base : forall j, mesim (me_base j) (me_base j)
  | mes_frame : forall a args args' κ κ',
      envsim args args' -> mesim κ κ' -> mesim (me_frame a args κ) (me_frame a args' κ')
  (** A closure body under one binder, and the motive and successor branch of a
      recursor, under one and two. *)
  with csim : menv -> env -> exp -> menv -> env -> exp -> Prop :=
  | cs_mk : forall θ n P Q κ ρ M κ' ρ' M',
      M = exp_tsub (ts_q θ) M' -> exp_ok (S n) P Q M' -> cfg θ n P Q κ ρ κ' ρ' ->
      csim κ ρ M κ' ρ' M'
  with csim2 : menv -> env -> exp -> exp -> menv -> env -> exp -> exp -> Prop :=
  | cs2_mk : forall θ n P Q κ ρ A MS κ' ρ' A' MS',
      A = exp_tsub (ts_q θ) A' -> MS = exp_tsub (ts_q (ts_q θ)) MS' ->
      exp_ok (S n) P Q A' -> exp_ok (S (S n)) P Q MS' -> cfg θ n P Q κ ρ κ' ρ' ->
      csim2 κ ρ A MS κ' ρ' A' MS'
  (** The leaves at [(κ, ρ)] on the left stand for those at [(κ', ρ')]: the
      variables below [n], and the parameters and globals in [P] and [Q]. *)
  with cfg : tsub -> nat -> (lpath -> Prop) -> (path -> Prop) -> menv -> env -> menv -> env -> Prop :=
  | cfg_mk : forall θ n (P : lpath -> Prop) (Q : path -> Prop) (κ : menv) (ρ : env) (κ' : menv) (ρ' : env),
      (forall x, bfree (ts_var θ x)) ->
      (forall lp, bfree (ts_param θ lp)) ->
      (forall p, bfree (ts_glob θ p)) ->
      (forall x v, x < n -> ⟦ ts_var θ x ⟧ κ ⍮ ρ ↘ v -> vsim v (ρ' x)) ->
      (forall lp v, P lp -> ⟦ ts_param θ lp ⟧ κ ⍮ ρ ↘ v ->
               exists v', ⟦ a_param lp ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v') ->
      (forall p, Q p -> gleaf θ κ ρ κ' ρ' p) ->
      cfg θ n P Q κ ρ κ' ρ'
  (** A global's image is a global resolved from a related place, or simply
      evaluates to something related. *)
  with gleaf : tsub -> menv -> env -> menv -> env -> path -> Prop :=
  | gl_struct : forall θ κ ρ κ' ρ' p p',
      ts_glob θ p = a_glob p' -> stsim κ p' κ' p -> gleaf θ κ ρ κ' ρ' p
  | gl_eval : forall θ κ ρ κ' ρ' p,
      (forall v, ⟦ ts_glob θ p ⟧ κ ⍮ ρ ↘ v -> exists v', ⟦ a_glob p ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v') ->
      gleaf θ κ ρ κ' ρ' p
  with stsim : menv -> path -> menv -> path -> Prop :=
  | st_rel : forall κ κ' m m' ip,
      mesim (me_drop m κ) (me_drop m' κ') -> stsim κ (p_rel m ip) κ' (p_rel m' ip)
  | st_abs : forall κ κ' fp ip, stsim κ (p_abs fp ip) κ' (p_abs fp ip).

  Hint Constructors vsim nsim envsim mesim csim csim2 cfg gleaf stsim : mctt.

  (** ** Basic facts *)

  Lemma envsim_refl : forall ρ, envsim ρ ρ.
  Proof. induction ρ; constructor; auto using vs_refl. Qed.

  Lemma mesim_refl : forall κ, mesim κ κ.
  Proof. induction κ; constructor; auto using envsim_refl. Qed.

  Hint Resolve envsim_refl mesim_refl : mctt.

  Lemma envsim_length : forall ρ ρ', envsim ρ ρ' -> List.length ρ = List.length ρ'.
  Proof. induction 1; cbn; auto. Qed.

  Lemma envsim_var : forall ρ ρ', envsim ρ ρ' -> forall x, vsim (ρ x) (ρ' x).
  Proof.
    induction 1; intros x; [ destruct x; apply vs_refl |].
    destruct x; cbn; auto.
  Qed.

  Lemma mesim_drop : forall κ κ', mesim κ κ' -> forall m, mesim (me_drop m κ) (me_drop m κ').
  Proof.
    induction 1; intros [| m]; cbn; auto with mctt.
  Qed.

  Lemma mesim_addr : forall κ κ', mesim κ κ' -> me_addr κ = me_addr κ'.
  Proof. destruct 1; reflexivity. Qed.

  Lemma mesim_base_inv : forall κ j, mesim (me_base j) κ -> κ = me_base j.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma mesim_frame_inv : forall a args κ κ', mesim (me_frame a args κ) κ' ->
      exists args' κ0, κ' = me_frame a args' κ0 /\ envsim args args' /\ mesim κ κ0.
  Proof. intros * H; inversion H; subst; eauto. Qed.

  (** The identity relates two related configurations. *)
  Lemma cfg_id : forall n P Q κ ρ κ' ρ',
      mesim κ κ' -> envsim ρ ρ' -> cfg ts_id n P Q κ ρ κ' ρ'.
  Proof.
    intros * Hκ Hρ; constructor; cbn; auto.
    - intros * _ H; inversion H; subst; apply envsim_var; assumption.
    - intros [m k] v _ H; inversion H; subst; cbn [lp_mod lp_param] in *.
      + pose proof (mesim_drop _ _ Hκ m) as Hd.
        match goal with Heq : me_drop _ _ = me_frame _ _ _ |- _ => rewrite Heq in Hd end.
        destruct (mesim_frame_inv _ _ _ _ Hd) as (args' & κ0 & Heq' & Ha & _).
        eexists; split; [ eapply eval_exp_param_closed; exact Heq' | apply envsim_var; assumption ].
      + pose proof (mesim_drop _ _ Hκ m) as Hd.
        match goal with Heq : me_drop _ _ = me_base _ |- _ => rewrite Heq in Hd end.
        apply mesim_base_inv in Hd.
        eexists; split; [ eapply eval_exp_param_open; eassumption | apply vs_refl ].
    - intros [[fp | m] ip] _; (eapply gl_struct; [ reflexivity |]);
        [ apply st_abs | apply st_rel, mesim_drop; assumption ].
  Qed.

  Lemma csim_refl : forall κ ρ M, csim κ ρ M κ ρ M.
  Proof.
    intros; destruct (exp_ok_ex M) as [n Hn].
    eapply (cs_mk ts_id n); [ symmetry; apply exp_tsub_id_gen, ts_q_id | | apply cfg_id; auto with mctt ].
    eapply exp_ok_mono; [| eassumption ]; lia.
  Qed.

  Lemma csim2_refl : forall κ ρ A MS, csim2 κ ρ A MS κ ρ A MS.
  Proof.
    intros; destruct (exp_ok_ex A) as [n Hn]; destruct (exp_ok_ex MS) as [m Hm].
    eapply (cs2_mk ts_id (n + m)).
    - symmetry; apply exp_tsub_id_gen, ts_q_id.
    - symmetry; apply exp_tsub_id_gen.
      pose proof (ts_q_eq _ _ ts_q_id) as (A1 & A2 & A3).
      destruct ts_q_id as (B1 & B2 & B3).
      repeat split; intros; rewrite ?A1, ?A2, ?A3, ?B1, ?B2, ?B3; reflexivity.
    - eapply exp_ok_mono; [| eassumption ]; lia.
    - eapply exp_ok_mono; [| eassumption ]; lia.
    - apply cfg_id; auto with mctt.
  Qed.

  Hint Resolve csim_refl csim2_refl : mctt.

  (** *** Inversions, the reflexive case included *)

  Lemma vsim_zero_inv : forall d, vsim zeroᵈ d -> d = zeroᵈ.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma vsim_succ_inv : forall m d, vsim (succᵈ m) d -> exists m', d = succᵈ m' /\ vsim m m'.
  Proof. intros * H; inversion H; subst; eauto using vs_refl. Qed.

  Lemma vsim_pi_inv : forall a κ ρ B d, vsim (Πᵈ a κ ρ B) d ->
      exists a' κ' ρ' B', d = Πᵈ a' κ' ρ' B' /\ vsim a a' /\ csim κ ρ B κ' ρ' B'.
  Proof. intros * H; inversion H; subst; do 4 eexists; eauto using vs_refl, csim_refl. Qed.

  Lemma vsim_fn_inv : forall κ ρ M d, vsim (λᵈ κ ρ M) d ->
      exists κ' ρ' M', d = λᵈ κ' ρ' M' /\ csim κ ρ M κ' ρ' M'.
  Proof. intros * H; inversion H; subst; do 3 eexists; eauto using csim_refl. Qed.

  Lemma vsim_neut_inv : forall a m d, vsim (⇑ a m) d ->
      exists a' m', d = ⇑ a' m' /\ vsim a a' /\ nsim m m'.
  Proof. intros * H; inversion H; subst; do 2 eexists; eauto using vs_refl, ns_refl. Qed.

  Lemma vsim_gfn_inv : forall κ a c args ip d, vsim (d_gfn κ a c args ip) d ->
      exists κ' args', d = d_gfn κ' a c args' ip /\ mesim κ κ' /\ envsim args args'.
  Proof. intros * H; inversion H; subst; do 2 eexists; eauto with mctt. Qed.

  Lemma vsim_univ_inv : forall i d, vsim 𝕌@i d -> d = 𝕌@i.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma vsim_nat_inv : forall d, vsim ℕᵈ d -> d = ℕᵈ.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma nsim_var_inv : forall x m, nsim (d_var x) m -> m = d_var x.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma nsim_glob_inv : forall p m, nsim (d_glob p) m -> m = d_glob p.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma nsim_param_inv : forall lp m, nsim (d_param lp) m -> m = d_param lp.
  Proof. intros * H; inversion H; reflexivity. Qed.

  Lemma nsim_app_inv : forall m a n d, nsim (m $ᵈ ⇓ a n) d ->
      exists m' a' n', d = m' $ᵈ ⇓ a' n' /\ nsim m m' /\ vsim a a' /\ vsim n n'.
  Proof. intros * H; inversion H; subst; do 3 eexists; eauto using vs_refl, ns_refl. Qed.

  Lemma nsim_natrec_inv : forall κ ρ A mz MS m d, nsim (d_natrec κ ρ A mz MS m) d ->
      exists κ' ρ' A' mz' MS' m', d = d_natrec κ' ρ' A' mz' MS' m' /\
        csim2 κ ρ A MS κ' ρ' A' MS' /\ vsim mz mz' /\ nsim m m'.
  Proof. intros * H; inversion H; subst; do 6 eexists; eauto using vs_refl, ns_refl, csim2_refl. Qed.

  Lemma envsim_cons_inv : forall d ρ ρ', envsim (d :: ρ) ρ' ->
      exists d' ρ0, ρ' = d' :: ρ0 /\ vsim d d' /\ envsim ρ ρ0.
  Proof. intros * H; inversion H; subst; eauto. Qed.

  (** *** Going under a binder *)

  Lemma cfg_q : forall θ n P Q κ ρ κ' ρ' d d',
      cfg θ n P Q κ ρ κ' ρ' -> vsim d d' ->
      cfg (ts_q θ) (S n) P Q κ (ρ ↦ d) κ' (ρ' ↦ d').
  Proof.
    intros * H Hd; inversion H as [? ? ? ? ? ? ? ? Hbv Hbp Hbg Hv Hp Hg]; subst.
    constructor; cbn.
    - intros [| x]; cbn; auto using bfree_wk.
    - auto using bfree_wk.
    - auto using bfree_wk.
    - intros [| x] v Hx Hev; cbn in *.
      + inversion Hev; subst; exact Hd.
      + apply Hv; [ lia | eapply eval_bfree_shift; eauto ].
    - intros * HP Hev.
      destruct (Hp _ _ HP (eval_bfree_shift _ _ _ _ _ (Hbp _) Hev)) as (v' & Hev' & Hs).
      eauto using eval_param_env.
    - intros p HQ; destruct (Hg _ HQ) as [? ? ? ? ? ? p' Heq Hst | ? ? ? ? ? ? Hev].
      + eapply gl_struct; [ cbn; rewrite Heq; reflexivity | exact Hst ].
      + apply gl_eval; intros v Hv'.
        destruct (Hev _ (eval_bfree_shift _ _ _ _ _ (Hbg _) Hv')) as (v' & Hev' & Hs).
        eauto using eval_glob_env.
  Qed.

  (** ** Leaves *)

  Lemma leaf_var : forall θ n P Q κ ρ κ' ρ' x v,
      cfg θ n P Q κ ρ κ' ρ' -> x < n -> ⟦ ts_var θ x ⟧ κ ⍮ ρ ↘ v ->
      exists v', ⟦ #x ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v'.
  Proof. intros * H Hx Hev; inversion H; subst; eexists; split; [ apply eval_exp_var | eauto ]. Qed.

  Lemma leaf_param : forall θ n P Q κ ρ κ' ρ' lp v,
      cfg θ n P Q κ ρ κ' ρ' -> P lp -> ⟦ ts_param θ lp ⟧ κ ⍮ ρ ↘ v ->
      exists v', ⟦ a_param lp ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v'.
  Proof. intros * H HP Hev; inversion H; subst; eauto. Qed.

  Lemma leaf_glob : forall θ n P Q κ ρ κ' ρ' p v,
      cfg θ n P Q κ ρ κ' ρ' -> Q p -> ⟦ ts_glob θ p ⟧ κ ⍮ ρ ↘ v ->
      (forall p', ts_glob θ p = a_glob p' -> stsim κ p' κ' p ->
             exists v', ⟦ a_glob p ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v') ->
      exists v', ⟦ a_glob p ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v'.
  Proof.
    intros * H HQ Hev Hs; inversion H as [? ? ? ? ? ? ? ? _ _ _ _ _ Hg]; subst.
    destruct (Hg _ HQ); eauto.
  Qed.

  (** ** The simulation *)

  Definition sim_exp_stmt κ N ρ v :=
    forall θ n P Q M κ' ρ',
      N = exp_tsub θ M -> exp_ok n P Q M -> cfg θ n P Q κ ρ κ' ρ' ->
      exists v', ⟦ M ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v'.

  Definition sim_natrec_stmt κ A MZ MS m ρ r :=
    forall θ n P Q A' MZ' MS' κ' ρ' m',
      A = exp_tsub (ts_q θ) A' -> MZ = exp_tsub θ MZ' -> MS = exp_tsub (ts_q (ts_q θ)) MS' ->
      exp_ok (S n) P Q A' -> exp_ok n P Q MZ' -> exp_ok (S (S n)) P Q MS' ->
      cfg θ n P Q κ ρ κ' ρ' -> vsim m m' ->
      exists r', eval_natrec Θ Ξ κ' A' MZ' MS' m' ρ' r' /\ vsim r r'.

  (** A leaf whose image is not a global resolved structurally. *)
  Ltac sim_leaf :=
    match goal with
    | Heq : ?N = ts_var ?θ ?x, Hok : ?x < _, Hc : cfg ?θ _ _ _ _ _ _ _ |- _ =>
        eapply leaf_var; [ exact Hc | exact Hok | rewrite <- Heq; econstructor; eassumption ]
    | Heq : ?N = ts_param ?θ ?lp, Hc : cfg ?θ _ _ _ _ _ _ _ |- _ =>
        eapply leaf_param; [ exact Hc | eassumption | rewrite <- Heq; econstructor; eassumption ]
    | Heq : ?N = ts_glob ?θ ?p, Hc : cfg ?θ _ _ _ _ _ _ _ |- _ =>
        eapply leaf_glob; [ exact Hc | eassumption | rewrite <- Heq; econstructor; eassumption
                          | intros ? Hp' ?; rewrite <- Heq in Hp'; discriminate Hp' ]
    end.

  Ltac intro_to_eq := repeat lazymatch goal with |- _ = _ -> _ => fail | _ => intro end.

  Ltac intro_to_sim := repeat lazymatch goal with |- vsim _ _ -> _ => fail | |- mesim _ _ -> _ => fail | _ => intro end.

  Ltac sim_intro :=
    repeat lazymatch goal with |- sim_exp_stmt _ _ _ _ => fail | _ => intro end;
    unfold sim_exp_stmt; intros θ_ k_ P_ Q_ M0 κ0 ρ0 Heq Hok Hc; destruct M0; cbn [exp_tsub exp_ok] in Heq, Hok;
    try discriminate; try sim_leaf.

  Theorem sim_eval :
    (forall κ N ρ v, ⟦ N ⟧ κ ⍮ ρ ↘ v -> sim_exp_stmt κ N ρ v) /\
    (forall κ A MZ MS m ρ r, eval_natrec Θ Ξ κ A MZ MS m ρ r -> sim_natrec_stmt κ A MZ MS m ρ r) /\
    (forall f d r, eval_app Θ Ξ f d r ->
       forall f' d', vsim f f' -> vsim d d' -> exists r', eval_app Θ Ξ f' d' r' /\ vsim r r') /\
    (forall κ a c args ip r, eval_pend Θ Ξ κ a c args ip r ->
       forall κ' args', mesim κ κ' -> envsim args args' ->
       exists r', eval_pend Θ Ξ κ' a c args' ip r' /\ vsim r r') /\
    (forall κ ip r, eval_ent Θ Ξ κ ip r ->
       forall κ', mesim κ κ' -> exists r', eval_ent Θ Ξ κ' ip r' /\ vsim r r') /\
    (forall κ j c Γ ρ, eval_ptele Θ Ξ κ j c Γ ρ ->
       forall κ', mesim κ κ' -> exists ρ', eval_ptele Θ Ξ κ' j c Γ ρ' /\ envsim ρ ρ') /\
    (forall κ k h h1, eval_gne Θ Ξ κ k h h1 ->
       forall κ' h', mesim κ κ' -> nsim h h' -> exists h1', eval_gne Θ Ξ κ' k h' h1' /\ nsim h1 h1') /\
    (forall κ Δ args h h1, eval_fargs Θ Ξ κ Δ args h h1 ->
       forall κ' args' h', mesim κ κ' -> envsim args args' -> nsim h h' ->
       exists h1', eval_fargs Θ Ξ κ' Δ args' h' h1' /\ nsim h1 h1').
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun κ N ρ v _ => sim_exp_stmt κ N ρ v)
             (fun κ A MZ MS m ρ r _ => sim_natrec_stmt κ A MZ MS m ρ r)
             (fun f d r _ => forall f' d', vsim f f' -> vsim d d' ->
                exists r', eval_app Θ Ξ f' d' r' /\ vsim r r')
             (fun κ a c args ip r _ => forall κ' args', mesim κ κ' -> envsim args args' ->
                exists r', eval_pend Θ Ξ κ' a c args' ip r' /\ vsim r r')
             (fun κ ip r _ => forall κ', mesim κ κ' -> exists r', eval_ent Θ Ξ κ' ip r' /\ vsim r r')
             (fun κ j c Γ ρ _ => forall κ', mesim κ κ' ->
                exists ρ', eval_ptele Θ Ξ κ' j c Γ ρ' /\ envsim ρ ρ')
             (fun κ k h h1 _ => forall κ' h', mesim κ κ' -> nsim h h' ->
                exists h1', eval_gne Θ Ξ κ' k h' h1' /\ nsim h1 h1')
             (fun κ Δ args h h1 _ => forall κ' args' h', mesim κ κ' -> envsim args args' -> nsim h h' ->
                exists h1', eval_fargs Θ Ξ κ' Δ args' h' h1' /\ nsim h1 h1'));
      unfold sim_natrec_stmt.
    (* typ, var, nat, zero *)
    1-4: sim_intro; (try (injection Heq as; subst); eexists; split; [ solve [ constructor ] | apply vs_refl ]).
    (* succ *)
    - sim_intro; injection Heq as ->.
      destruct (H _ _ _ _ _ _ _ eq_refl Hok Hc) as (v' & Hv' & Hs).
      eexists; split; [ econstructor; eassumption | auto with mctt ].
    (* natrec *)
    - sim_intro; injection Heq as -> -> -> ->; destruct Hok as (HA & HZ & HS & HM).
      destruct (H _ _ _ _ _ _ _ eq_refl HM Hc) as (m' & Hm' & Hs).
      destruct (H0 _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl HA HZ HS Hc Hs) as (r' & Hr' & Hs').
      eexists; split; [ econstructor; eassumption | exact Hs' ].
    (* pi *)
    - sim_intro; injection Heq as -> ->; destruct Hok as (HA & HB).
      destruct (H _ _ _ _ _ _ _ eq_refl HA Hc) as (a' & Ha' & Hs).
      eexists; split; [ econstructor; eassumption | eauto with mctt ].
    (* fn *)
    - sim_intro; injection Heq as -> ->; destruct Hok as (HA & HB).
      eexists; split; [ econstructor | eauto with mctt ].
    (* app *)
    - sim_intro; injection Heq as -> ->; destruct Hok as (HM & HN).
      destruct (H _ _ _ _ _ _ _ eq_refl HM Hc) as (m' & Hm' & Hs1).
      destruct (H0 _ _ _ _ _ _ _ eq_refl HN Hc) as (n' & Hn' & Hs2).
      destruct (H1 _ _ Hs1 Hs2) as (r' & Hr' & Hs).
      eexists; split; [ econstructor; eassumption | exact Hs ].
    (* parameters: leaves only *)
    - sim_intro.
    - sim_intro.
    (* a relative global *)
    - sim_intro.
      inversion Hc as [? ? ? ? ? ? ? ? _ _ _ _ _ Hg]; subst.
      destruct (Hg _ Hok) as [? ? ? ? ? ? p' Heqp Hst | ? ? ? ? ? ? Hev].
      + rewrite <- Heq in Heqp; injection Heqp as <-.
        inversion Hst; subst.
        destruct (H _ ltac:(eassumption)) as (r' & Hr' & Hs).
        eexists; split; [ econstructor; eassumption | exact Hs ].
      + apply Hev; rewrite <- Heq; econstructor; eassumption.
    (* an absolute global *)
    - sim_intro.
      inversion Hc as [? ? ? ? ? ? ? ? _ _ _ _ _ Hg]; subst.
      destruct (Hg _ Hok) as [? ? ? ? ? ? p' Heqp Hst | ? ? ? ? ? ? Hev].
      + rewrite <- Heq in Heqp; injection Heqp as <-.
        inversion Hst; subst.
        destruct (H _ _ ltac:(apply mesim_refl) es_nil) as (r' & Hr' & Hs).
        eexists; split; [ econstructor; eassumption | exact Hs ].
      + apply Hev; rewrite <- Heq; econstructor; eassumption.
    (* natrec: zero *)
    - intro_to_eq; intros -> -> -> HA HZ HS Hc Hm.
      apply vsim_zero_inv in Hm as ->.
      destruct (H _ _ _ _ _ _ _ eq_refl HZ Hc) as (mz' & Hmz' & Hs).
      eexists; split; [ econstructor; eassumption | exact Hs ].
    (* natrec: succ *)
    - intro_to_eq; intros -> -> -> HA HZ HS Hc Hm.
      destruct (vsim_succ_inv _ _ Hm) as (b' & -> & Hb).
      destruct (H _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl HA HZ HS Hc Hb) as (r' & Hr' & Hr).
      destruct (H0 _ _ _ _ _ _ _ eq_refl HS (cfg_q _ _ _ _ _ _ _ _ _ _ (cfg_q _ _ _ _ _ _ _ _ _ _ Hc Hb) Hr))
        as (ms' & Hms' & Hs).
      eexists; split; [ econstructor; eassumption | exact Hs ].
    (* natrec: neutral *)
    - intro_to_eq; intros -> -> -> HA HZ HS Hc Hm.
      destruct (vsim_neut_inv _ _ _ Hm) as (b' & m2 & -> & Hb & Hmm).
      destruct (H _ _ _ _ _ _ _ eq_refl HZ Hc) as (mz' & Hmz' & Hs1).
      destruct (H0 _ _ _ _ _ _ _ eq_refl HA (cfg_q _ _ _ _ _ _ _ _ _ _ Hc Hm)) as (a' & Ha' & Hs2).
      eexists; split; [ econstructor; eassumption |].
      apply vs_neut; [ exact Hs2 |].
      apply ns_natrec; [ econstructor; eauto | exact Hs1 | exact Hmm ].
    (* app: closure *)
    - intro_to_sim; intros Hf Hd.
      destruct (vsim_fn_inv _ _ _ _ Hf) as (κ' & ρ' & M' & -> & Hcs).
      inversion Hcs as [θ k P Q ? ? ? ? ? ? -> Hok Hc]; subst.
      destruct (H _ _ _ _ _ _ _ eq_refl Hok (cfg_q _ _ _ _ _ _ _ _ _ _ Hc Hd)) as (m' & Hm' & Hs).
      eexists; split; [ econstructor; eassumption | exact Hs ].
    (* app: neutral *)
    - intro_to_sim; intros Hf Hd.
      destruct (vsim_neut_inv _ _ _ Hf) as (A' & m' & -> & HA & Hm).
      destruct (vsim_pi_inv _ _ _ _ _ HA) as (a' & κ' & ρ' & B' & -> & Ha & Hcs).
      inversion Hcs as [θ k P Q ? ? ? ? ? ? -> Hok Hc]; subst.
      destruct (H _ _ _ _ _ _ _ eq_refl Hok (cfg_q _ _ _ _ _ _ _ _ _ _ Hc Hd)) as (b' & Hb' & Hs).
      eexists; split; [ econstructor; eassumption | auto with mctt ].
    (* app: a pending global *)
    - intro_to_sim; intros Hf Hd.
      destruct (vsim_gfn_inv _ _ _ _ _ _ Hf) as (κ' & args' & -> & Hκ & Ha).
      destruct (H _ _ Hκ (es_cons _ _ _ _ Hd Ha)) as (r' & Hr' & Hs).
      eexists; split; [ econstructor; eassumption | exact Hs ].
    (* pend: wait *)
    - intro_to_sim; intros Hκ Ha; eexists; split; [ apply eval_pend_wait; rewrite <- (envsim_length _ _ Ha); assumption |].
      auto with mctt.
    (* pend: enter *)
    - intro_to_sim; intros Hκ Ha.
      destruct (H _ (mes_frame _ _ _ _ _ Ha Hκ)) as (r' & Hr' & Hs).
      eexists; split; [ apply eval_pend_enter; [ rewrite <- (envsim_length _ _ Ha); assumption | exact Hr' ] | exact Hs ].
    (* ent: δ *)
    - intro_to_sim; intros Hκ.
      destruct (exp_ok_ex M) as [n Hn].
      destruct (H _ n _ _ _ _ _ (eq_sym (exp_tsub_id M)) Hn (cfg_id _ _ _ _ _ _ _ Hκ es_nil)) as (r' & Hr' & Hs).
      eexists; split; [ eapply eval_ent_delta; [ rewrite <- (mesim_addr _ _ Hκ); eassumption | eassumption | exact Hr' ] | exact Hs ].
    (* ent: neutral *)
    - intro_to_sim; intros Hκ.
      destruct (exp_ok_ex A) as [n Hn].
      destruct (H _ n _ _ _ _ _ (eq_sym (exp_tsub_id A)) Hn (cfg_id _ _ _ _ _ _ _ Hκ es_nil)) as (a' & Ha' & Hs).
      destruct (H0 _ _ Hκ (ns_refl _)) as (m' & Hm' & Hsm).
      rewrite (mesim_addr _ _ Hκ) in *.
      eexists; split; [ eapply eval_ent_neut; eassumption | auto with mctt ].
    (* ent: a nested module *)
    - intro_to_sim; intros Hκ.
      destruct (H _ _ Hκ es_nil) as (r' & Hr' & Hs).
      rewrite (mesim_addr _ _ Hκ) in *.
      eexists; split; [ eapply eval_ent_mod; eassumption | exact Hs ].
    (* ptele *)
    - intro_to_sim; intros Hκ; eexists; split; constructor.
    - intro_to_sim; intros Hκ.
      destruct (H _ Hκ) as (ρ' & Hρ' & Hs).
      destruct (exp_ok_ex T) as [n Hn].
      destruct (H0 _ n _ _ _ _ _ (eq_sym (exp_tsub_id T)) Hn (cfg_id _ _ _ _ _ _ _ Hκ Hs)) as (a' & Ha' & Hsa).
      eexists; split; [ econstructor; eassumption | auto with mctt ].
    (* gne *)
    - intro_to_sim; intros Hκ Hh; eexists; split; [ constructor | exact Hh ].
    - intro_to_sim; intros Hκ Hh.
      destruct (mesim_frame_inv _ _ _ _ Hκ) as (args' & κ0 & -> & Ha & Hκ0).
      destruct (H _ _ Hκ0 Hh) as (h1' & Hh1' & Hs1).
      destruct (H0 _ _ _ Hκ0 Ha Hs1) as (h2' & Hh2' & Hs2).
      eexists; split; [ econstructor; eassumption | exact Hs2 ].
    (* fargs *)
    - intro_to_sim; intros Hκ Ha Hh; inversion Ha; subst; eexists; split; [ constructor | exact Hh ].
    - intro_to_sim; intros Hκ Ha Hh.
      destruct (envsim_cons_inv _ _ _ Ha) as (v' & args0 & -> & Hv & Ha0).
      destruct (H _ _ _ Hκ Ha0 Hh) as (h1' & Hh1' & Hs1).
      destruct (exp_ok_ex T) as [n Hn].
      destruct (H0 _ n _ _ _ _ _ (eq_sym (exp_tsub_id T)) Hn (cfg_id _ _ _ _ _ _ _ Hκ Ha0)) as (t' & Ht' & Hst).
      eexists; split; [ econstructor; eassumption | auto with mctt ].
  Qed.

  Corollary sim_eval_exp : forall θ n P Q M κ ρ κ' ρ' v,
      ⟦ exp_tsub θ M ⟧ κ ⍮ ρ ↘ v -> exp_ok n P Q M -> cfg θ n P Q κ ρ κ' ρ' ->
      exists v', ⟦ M ⟧ κ' ⍮ ρ' ↘ v' /\ vsim v v'.
  Proof. intros * H; exact (proj1 sim_eval _ _ _ _ H _ _ _ _ _ _ _ eq_refl). Qed.

  Corollary sim_eval_app : forall f d r f' d',
      eval_app Θ Ξ f d r -> vsim f f' -> vsim d d' -> exists r', eval_app Θ Ξ f' d' r' /\ vsim r r'.
  Proof. intros * H; eapply (proj1 (proj2 (proj2 sim_eval))); eassumption. Qed.

  (** A closure applied to related arguments. *)
  Corollary sim_eval_csim : forall κ ρ B κ' ρ' B' c c' b,
      csim κ ρ B κ' ρ' B' -> vsim c c' ->
      ⟦ B ⟧ κ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ B' ⟧ κ' ⍮ ρ' ↦ c' ↘ b' /\ vsim b b'.
  Proof.
    intros * Hcs Hc Hb; inversion Hcs as [θ k P Q ? ? ? ? ? ? -> Hok Hcf]; subst.
    eapply sim_eval_exp; eauto using cfg_q.
  Qed.

  Corollary sim_eval_csim2_A : forall κ ρ A MS κ' ρ' A' MS' c c' b,
      csim2 κ ρ A MS κ' ρ' A' MS' -> vsim c c' ->
      ⟦ A ⟧ κ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ A' ⟧ κ' ⍮ ρ' ↦ c' ↘ b' /\ vsim b b'.
  Proof.
    intros * Hcs Hc Hb; inversion Hcs as [θ k P Q ? ? ? ? ? ? ? ? -> -> HA HS Hcf]; subst.
    eapply sim_eval_exp; eauto using cfg_q.
  Qed.

  Corollary sim_eval_csim2_MS : forall κ ρ A MS κ' ρ' A' MS' c c' d d' b,
      csim2 κ ρ A MS κ' ρ' A' MS' -> vsim c c' -> vsim d d' ->
      ⟦ MS ⟧ κ ⍮ ρ ↦ c ↦ d ↘ b ->
      exists b', ⟦ MS' ⟧ κ' ⍮ ρ' ↦ c' ↦ d' ↘ b' /\ vsim b b'.
  Proof.
    intros * Hcs Hc Hd Hb; inversion Hcs as [θ k P Q ? ? ? ? ? ? ? ? -> -> HA HS Hcf]; subst.
    eapply sim_eval_exp; eauto using cfg_q.
  Qed.

  (** ** Readback *)

  Theorem sim_read :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall a v a' v', m = ⇓ a v -> vsim a a' -> vsim v v' -> Rnf ⇓ a' v' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s m W, Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> forall m', nsim m m' -> Rne m' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s a W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> forall a', vsim a a' -> Rtyp a' in Θ ⍮ Ξ ⍮ s ↘ W).
  Proof.
    apply read_mut_ind; intros;
      repeat match goal with
        | H : ⇓ _ _ = ⇓ _ _ |- _ => injection H as <- <-
        | H : vsim 𝕌@_ _ |- _ => apply vsim_univ_inv in H as ->
        | H : vsim ℕᵈ _ |- _ => apply vsim_nat_inv in H as ->
        | H : vsim zeroᵈ _ |- _ => apply vsim_zero_inv in H as ->
        | H : vsim (succᵈ _) _ |- _ =>
            let m' := fresh "m'" in destruct (vsim_succ_inv _ _ H) as (m' & -> & ?); clear H
        | H : vsim (⇑ _ _) _ |- _ =>
            let a' := fresh "a'" in let m' := fresh "m'" in
            destruct (vsim_neut_inv _ _ _ H) as (a' & m' & -> & ? & ?); clear H
        | H : vsim (Πᵈ _ _ _ _) _ |- _ =>
            let a' := fresh "a'" in let κ' := fresh "κ'" in let ρ' := fresh "ρ'" in let B' := fresh "B'" in
            destruct (vsim_pi_inv _ _ _ _ _ H) as (a' & κ' & ρ' & B' & -> & ? & ?); clear H
        | H : nsim (d_var _) _ |- _ => apply nsim_var_inv in H as ->
        | H : nsim (d_glob _) _ |- _ => apply nsim_glob_inv in H as ->
        | H : nsim (d_param _) _ |- _ => apply nsim_param_inv in H as ->
        | H : nsim (_ $ᵈ ?n) _ |- _ => is_var n; destruct n
        | H : nsim (_ $ᵈ _) _ |- _ =>
            let m' := fresh "m'" in let a' := fresh "a'" in let n' := fresh "n'" in
            destruct (nsim_app_inv _ _ _ _ H) as (m' & a' & n' & -> & ? & ? & ?); clear H
        | H : nsim (d_natrec _ _ _ _ _ _) _ |- _ =>
            destruct (nsim_natrec_inv _ _ _ _ _ _ _ H) as (? & ? & ? & ? & ? & ? & -> & ? & ? & ?); clear H
        end.
    all: try solve [ constructor; eauto using vs_refl ].
    (* a function, at a Π type: η *)
    - match goal with
      | Ha : vsim ?a ?a', Hcs : csim ?κ ?ρ ?B ?κ' ?ρ' ?B',
        Happ : $| ?m & ⇑! ?a ?s | Θ ⍮ Ξ ↘ ?m0, HB : ⟦ ?B ⟧ ?κ ⍮ ?ρ ↦ ⇑! ?a ?s ↘ ?b,
        Hm : vsim ?m ?m2 |- _ =>
          assert (Hx : vsim (⇑! a s) (⇑! a' s)) by (apply vs_neut; [ exact Ha | apply ns_refl ]);
          destruct (sim_eval_app _ _ _ _ _ Happ Hm Hx) as (m2' & Hm2 & Hs2);
          destruct (sim_eval_csim _ _ _ _ _ _ _ _ _ Hcs Hx HB) as (b' & Hb' & Hsb)
      end.
      econstructor; eauto.
    (* the neutral of an eliminator *)
    - match goal with
      | Hcs : csim2 ?κ ?ρ ?B ?MS ?κ' ?ρ' ?B' ?MS',
        Hb : ⟦ ?B ⟧ ?κ ⍮ ?ρ ↦ ⇑! ℕᵈ ?s ↘ ?b,
        Hz : ⟦ ?B ⟧ ?κ ⍮ ?ρ ↦ zeroᵈ ↘ ?bz,
        Hsu : ⟦ ?B ⟧ ?κ ⍮ ?ρ ↦ succᵈ (⇑! ℕᵈ ?s) ↘ ?bs,
        Hms : ⟦ ?MS ⟧ ?κ ⍮ ?ρ ↦ ⇑! ℕᵈ ?s ↦ ⇑! ?b (S ?s) ↘ ?ms |- _ =>
          assert (Hx : vsim (⇑! ℕᵈ s) (⇑! ℕᵈ s)) by apply vs_refl;
          destruct (sim_eval_csim2_A _ _ _ _ _ _ _ _ _ _ _ Hcs Hx Hb) as (b' & Hb' & Hsb);
          destruct (sim_eval_csim2_A _ _ _ _ _ _ _ _ _ _ _ Hcs (vs_refl _) Hz) as (bz' & Hbz' & Hsbz);
          destruct (sim_eval_csim2_A _ _ _ _ _ _ _ _ _ _ _ Hcs (vs_refl _) Hsu) as (bs' & Hbs' & Hsbs);
          assert (Hy : vsim (⇑! b (S s)) (⇑! b' (S s))) by (apply vs_neut; [ exact Hsb | apply ns_refl ]);
          destruct (sim_eval_csim2_MS _ _ _ _ _ _ _ _ _ _ _ _ _ Hcs Hx Hy Hms) as (ms' & Hms' & Hsms)
      end.
      econstructor; eauto.
    (* a Π type *)
    - match goal with
      | Ha : vsim ?a ?a', Hcs : csim ?κ ?ρ ?B ?κ' ?ρ' ?B',
        HB : ⟦ ?B ⟧ ?κ ⍮ ?ρ ↦ ⇑! ?a ?s ↘ ?b |- _ =>
          assert (Hx : vsim (⇑! a s) (⇑! a' s)) by (apply vs_neut; [ exact Ha | apply ns_refl ]);
          destruct (sim_eval_csim _ _ _ _ _ _ _ _ _ Hcs Hx HB) as (b' & Hb' & Hsb)
      end.
      econstructor; eauto.
  Qed.

  Corollary sim_read_nf : forall s a v W a' v',
      Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ W -> vsim a a' -> vsim v v' -> Rnf ⇓ a' v' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; eapply (proj1 sim_read); eauto. Qed.

  Corollary sim_read_ne : forall s m W m',
      Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> nsim m m' -> Rne m' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; eapply (proj1 (proj2 sim_read)); eauto. Qed.

  Corollary sim_read_typ : forall s a W a',
      Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> vsim a a' -> Rtyp a' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; eapply (proj2 (proj2 sim_read)); eauto. Qed.
End Sim.

#[export] Hint Constructors vsim nsim envsim mesim csim csim2 cfg gleaf stsim : mctt.
#[export] Hint Resolve envsim_refl mesim_refl csim_refl csim2_refl : mctt.
