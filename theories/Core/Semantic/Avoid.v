(** * NbE Invents No Variables

    Normalizing a weakened term in the extended context never mentions the
    new variable: if [M[↑]] is normalized in [Γ ▹ A], its normal form is
    fresh at [#0] ([nbe_wk_fresh]).  Evaluation builds no variable, so a
    value can only mention a variable its environment holds; and readback
    introduces only variables above the ones in scope.

    The invariant is [dav v b d]: the value [d] mentions no de Bruijn level
    [v], and only levels below [b].  It cannot be stated on environments
    alone: the environment of the extended context holds the new variable,
    at index [0], and so does every closure built in it.  What makes the
    value fresh is that the weakened term never *reads* that index.  So a
    closure records one position [K] of its environment that may be bad,
    together with the freshness of its body at that position, shifted by the
    closure's binders.  [K = None] is a closure whose environment avoids [v]
    everywhere.

    The proof is structural, in the pattern of [Core.Semantic.Transparency]
    ([dclean]); readback is where the level arithmetic happens: a variable at
    level [x] reads back at length [n] as the index [n - x - 1], which is not
    [n - v - 1] when [x <> v] and both are below [n]. *)
From Stdlib Require Import Arith Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Core.Syntactic Require Import Fresh Members.
Import Domain_Notations Syntax_Notations Wk_Notations.

Create HintDb avoid.

(** ** Freshness at an Optional Position *)

Definition oshift (j : nat) (K : option nat) : option nat := option_map (Nat.add j) K.

Lemma oshift_oshift : forall i j K, oshift i (oshift j K) = oshift (i + j) K.
Proof. intros i j []; cbn; [ f_equal; lia | reflexivity ]. Qed.

Lemma oshift_zero : forall K, oshift 0 K = K.
Proof. intros []; reflexivity. Qed.

Definition ofresh (K : option nat) (M : exp) : Prop :=
  match K with None => True | Some k => exp_fresh k M end.
Definition omfresh (K : option nat) (H : modexp) : Prop :=
  match K with None => True | Some k => modexp_fresh k H end.
Definition oufresh (K : option nat) (U : gunit) : Prop :=
  match K with None => True | Some k => gunit_fresh k U end.
Definition ogfresh (K : option nat) (Φ : gmod) : Prop :=
  match K with None => True | Some k => gmod_fresh k Φ end.

(** ** The Invariant *)

Section Avoid.
  Variables (v b : nat).

  Inductive dav : domain -> Prop :=
  | dav_nat : dav ℕᵈ
  | dav_pi : forall a (ρ : env) B K,
      dav a ->
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) B ->
      dav (Πᵈ a ρ B)
  | dav_univ : forall i, dav 𝕌ω@i
  | dav_suniv : forall l, dav l -> dav 𝕌@l
  | dav_level : forall n, dav (Levelᵈ@n)
  | dav_lvl : forall c xs, dav_la xs -> dav (lvᵈ c xs)
  | dav_zero : dav zeroᵈ
  | dav_succ : forall m, dav m -> dav (succᵈ m)
  | dav_True : dav ⊤ᵈ
  | dav_true : dav ⋆ᵈ
  | dav_False : dav ⊥ᵈ
  | dav_fn : forall (ρ : env) M K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) M ->
      dav (λᵈ ρ M)
  | dav_neut : forall a m, dav a -> dav_ne m -> dav (⇑ a m)
  | dav_member : forall h ch, dmav h -> dav (d_member h ch)
  with dav_ne : domain_ne -> Prop :=
  | dav_var : forall x, x <> v -> x < b -> dav_ne (#ᵈ x)
  | dav_app : forall m n, dav_ne m -> dav_nf n -> dav_ne (m $ᵈ n)
  | dav_natrec : forall (ρ : env) A mz MS m K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) A ->
      dav mz ->
      ofresh (oshift 2 K) MS ->
      dav_ne m ->
      dav_ne (recᵈ m under ρ return A | zero -> mz | succ -> MS end)
  | dav_exfalso : forall (ρ : env) A m K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) A ->
      dav_ne m ->
      dav_ne (efqᵈ m under ρ return A)
  | dav_glob : forall p, dav_ne (d_glob p)
  with dav_nf : domain_nf -> Prop :=
  | dav_dom : forall a m, dav a -> dav m -> dav_nf (⇓ a m)
  with dmav : dmod -> Prop :=
  | dmav_global : forall p args, (forall a, In a args -> dav a) -> dmav (dm_global p args)
  | dmav_local : forall (ρ : env) U args K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      oufresh K U ->
      (forall a, In a args -> dav a) ->
      dmav (dm_local ρ U args)
  | dmav_member : forall h ch, dmav h -> dmav (dm_member h ch)
  with dav_la : list (nat * nat * domain_ne) -> Prop :=
  | dav_la_nil : dav_la nil
  | dav_la_cons : forall k n m xs, dav_ne m -> dav_la xs -> dav_la ((k, n, m) :: xs)
  with deav : dentry -> Prop :=
  | deav_term : forall d, dav d -> deav (de_term d)
  | deav_mod : forall h, dmav h -> deav (de_mod h).

  Definition env_av (K : option nat) (ρ : env) : Prop :=
    forall x, K <> Some x -> deav (env_entry ρ x).
End Avoid.

Scheme dav_mind := Induction for dav Sort Prop
  with dav_ne_mind := Induction for dav_ne Sort Prop
  with dav_nf_mind := Induction for dav_nf Sort Prop
  with dmav_mind := Induction for dmav Sort Prop
  with dav_la_mind := Induction for dav_la Sort Prop
  with deav_mind := Induction for deav Sort Prop.
Combined Scheme dav_mut_ind from dav_mind, dav_ne_mind, dav_nf_mind, dmav_mind, dav_la_mind, deav_mind.

#[local] Hint Constructors dav dav_ne dav_nf dmav dav_la deav : mctt.

(** The bound only grows. *)
Lemma dav_mono : forall v b,
    (forall d, dav v b d -> forall b', b <= b' -> dav v b' d) /\
    (forall m, dav_ne v b m -> forall b', b <= b' -> dav_ne v b' m) /\
    (forall n, dav_nf v b n -> forall b', b <= b' -> dav_nf v b' n) /\
    (forall h, dmav v b h -> forall b', b <= b' -> dmav v b' h) /\
    (forall xs, dav_la v b xs -> forall b', b <= b' -> dav_la v b' xs) /\
    (forall e, deav v b e -> forall b', b <= b' -> deav v b' e).
Proof.
  intros v b.
  apply (dav_mut_ind v b
           (fun d _ => forall b', b <= b' -> dav v b' d)
           (fun m _ => forall b', b <= b' -> dav_ne v b' m)
           (fun n _ => forall b', b <= b' -> dav_nf v b' n)
           (fun h _ => forall b', b <= b' -> dmav v b' h)
           (fun xs _ => forall b', b <= b' -> dav_la v b' xs)
           (fun e _ => forall b', b <= b' -> deav v b' e));
    intros; econstructor; eauto; lia.
Qed.

Lemma env_av_mono : forall v b b' K ρ, b <= b' -> env_av v b K ρ -> env_av v b' K ρ.
Proof. intros * Hb H x Hx; eapply (proj2 (proj2 (proj2 (proj2 (proj2 (dav_mono v b)))))); eauto. Qed.

(** ** Environments *)
Section Env.
  Variables (v b : nat).

  Lemma env_av_nil : forall K, env_av v b K nil.
  Proof. intros K x _; induction x; cbn; [ repeat constructor | assumption ]. Qed.

  Lemma env_av_none : forall K ρ, env_av v b None ρ -> env_av v b K ρ.
  Proof. intros * H x _; apply H; discriminate. Qed.

  Lemma env_av_cons : forall K e ρ, env_av v b K ρ -> deav v b e -> env_av v b (oshift 1 K) (e :: ρ).
  Proof.
    intros * Hρ He [| x] Hx; cbn; [ exact He |].
    apply Hρ; intros ->; apply Hx; reflexivity.
  Qed.

  (** The excluded entry: the head of the environment may be anything. *)
  Lemma env_av_cons_bad : forall e ρ, env_av v b None ρ -> env_av v b (Some 0) (e :: ρ).
  Proof.
    intros * Hρ [| x] Hx; cbn; [ contradiction Hx; reflexivity |].
    apply Hρ; discriminate.
  Qed.

  Lemma env_av_args : forall args K ρ,
      env_av v b K ρ -> (forall a, In a args -> dav v b a) ->
      env_av v b (oshift (List.length args) K) (env_args ρ args).
  Proof.
    induction args as [| a args IH]; intros * Hρ Ha; cbn; [ rewrite oshift_zero; exact Hρ |].
    replace (S (List.length args)) with (List.length args + 1) by lia.
    rewrite <- oshift_oshift.
    apply IH; [ apply env_av_cons; [ exact Hρ | constructor; apply Ha; left; reflexivity ]
              | intros; apply Ha; right; assumption ].
  Qed.

  Lemma env_av_var : forall K ρ x, env_av v b K ρ -> K <> Some x -> dav v b (ρ x).
  Proof.
    intros * H Hx; unfold env_var; destruct (H x Hx); [ assumption | repeat constructor ].
  Qed.

  Lemma env_av_mod : forall K ρ x, env_av v b K ρ -> K <> Some x -> dmav v b (env_mod ρ x).
  Proof.
    intros * H Hx; unfold env_mod; destruct (H x Hx); [| assumption ].
    constructor; intros ? [].
  Qed.

  (** The atoms of a level value avoid [v] when the value does. *)
  Lemma dav_la_view : forall d, dav v b d -> dav_la v b (dlvl_atoms d).
  Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

  Lemma dav_la_suc : forall xs, dav_la v b xs -> dav_la v b (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
  Proof. induction 1; cbn; repeat constructor; assumption. Qed.

  Lemma dav_la_app : forall xs ys, dav_la v b xs -> dav_la v b ys -> dav_la v b (xs ++ ys).
  Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

  Lemma dav_lvl_suc : forall d, dav v b d -> dav v b (dlvl_suc d).
  Proof. intros; unfold dlvl_suc; constructor; apply dav_la_suc, dav_la_view; assumption. Qed.

  Lemma dav_lvl_max : forall d e, dav v b d -> dav v b e -> dav v b (dlvl_max d e).
  Proof. intros; unfold dlvl_max; constructor; apply dav_la_app; apply dav_la_view; assumption. Qed.

  Lemma dmav_local_nil : forall K ρ U, env_av v b K ρ -> oufresh K U -> dmav v b (dm_local ρ U nil).
  Proof. intros * Hρ HU; econstructor; [ exact Hρ | exact HU | intros ? [] ]. Qed.

  Lemma dmav_global_nil : forall p, dmav v b (dm_global p nil).
  Proof. intros; constructor; intros ? []. Qed.

  Lemma dav_args_snoc : forall (args : list domain) n,
      (forall a, In a args -> dav v b a) -> dav v b n -> forall a, In a (args ++ n :: nil) -> dav v b a.
  Proof. intros * H Hn a Ha; apply in_app_or in Ha as [Ha | [<- | []]]; auto. Qed.
End Env.

(** ** Freshness Through the Module Syntax *)

Lemma modexp_spine_fresh : forall H k R args pre,
    modexp_spine H = (R, args, pre) ->
    modexp_fresh k H ->
    modexp_fresh k R /\ Forall (exp_fresh k) args.
Proof.
  induction H; intros * Hs Hf; cbn in Hs, Hf;
    try (inversion Hs; subst; split; [ assumption | constructor ]).
  - destruct (modexp_spine H) as [[R0 args0] pre0] eqn:E; inversion Hs; subst.
    exact (IHmodexp _ _ _ _ eq_refl Hf).
  - destruct (modexp_spine H) as [[R0 args0] pre0] eqn:E; inversion Hs; subst.
    destruct Hf as [HH HN].
    destruct (IHmodexp _ _ _ _ eq_refl HH) as [HR Ha].
    split; [ assumption | apply Forall_app; split; [ assumption | constructor; [ assumption | constructor ] ] ].
Qed.

Lemma prefix_upto_fresh : forall Φ x Φ0 k,
    gm_prefix_upto Φ x = Some Φ0 ->
    gmod_fresh k Φ ->
    gmod_fresh k Φ0.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hp Hf; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb x y); [ inversion Hp; subst; exact Hf |].
    cbn in Hf; destruct Hf; eapply IH; eassumption.
  - cbn in Hf; destruct Hf; eapply IH; eassumption.
Qed.

Lemma ofresh_prefix_upto : forall Φ x Φ0 K,
    gm_prefix_upto Φ x = Some Φ0 -> ogfresh K Φ -> ogfresh K Φ0.
Proof. intros * Hp; destruct K; cbn; [ eapply prefix_upto_fresh; eassumption | auto ]. Qed.

(** The parts of a fresh compound, each at the position its binders shift
    to.  Stated at an optional position, so that one lemma serves both the
    environment with a bad position and the one without. *)
Section OFresh.
  Variable K : option nat.

  Lemma ofresh_univ : forall M, ofresh K Type⟨M⟩ -> ofresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma ofresh_succl : forall M, ofresh K (succl M) -> ofresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma ofresh_maxl_l : forall M N, ofresh K (maxl M N) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_maxl_r : forall M N, ofresh K (maxl M N) -> ofresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_succ : forall M, ofresh K (succ M) -> ofresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma ofresh_natrec_A : forall A MZ MS M, ofresh K (rec M return A | zero -> MZ | succ -> MS end) -> ofresh (oshift 1 K) A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_natrec_Z : forall A MZ MS M, ofresh K (rec M return A | zero -> MZ | succ -> MS end) -> ofresh K MZ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_natrec_S : forall A MZ MS M, ofresh K (rec M return A | zero -> MZ | succ -> MS end) -> ofresh (oshift 2 K) MS.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_natrec_M : forall A MZ MS M, ofresh K (rec M return A | zero -> MZ | succ -> MS end) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_exfalso_A : forall A M, ofresh K (efq M return A) -> ofresh (oshift 1 K) A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_exfalso_M : forall A M, ofresh K (efq M return A) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_pi_A : forall A B, ofresh K (Π A B) -> ofresh K A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_pi_B : forall A B, ofresh K (Π A B) -> ofresh (oshift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_fn_M : forall A M, ofresh K (λ A M) -> ofresh (oshift 1 K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_app_l : forall M N, ofresh K (M $ N) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_app_r : forall M N, ofresh K (M $ N) -> ofresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_let_M : forall oA M B, ofresh K (a_let (b_def oA M) B) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_let_B : forall bd B, ofresh K (a_let bd B) -> ofresh (oshift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_letmod_U : forall U B, ofresh K (a_let (b_mod U) B) -> oufresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_mem : forall H x, ofresh K (a_mem H x) -> omfresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_var : forall x, ofresh K #x -> K <> Some x.
  Proof. destruct K; cbn; congruence. Qed.

  Lemma omfresh_var : forall x, omfresh K (me_var x) -> K <> Some x.
  Proof. destruct K; cbn; congruence. Qed.
  Lemma omfresh_lit : forall U, omfresh K (me_lit U) -> oufresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_mem : forall H y, omfresh K (me_mem H y) -> omfresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_app_l : forall H N, omfresh K (me_app H N) -> omfresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_app_r : forall H N, omfresh K (me_app H N) -> ofresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_spine : forall H R args pre,
      modexp_spine H = (R, args, pre) -> omfresh K H -> omfresh K R /\ Forall (ofresh K) args.
  Proof.
    destruct K as [k |]; cbn; intros * Hs Hf.
    - destruct (modexp_spine_fresh _ _ _ _ _ Hs Hf); split; assumption.
    - split; [ exact I | apply Forall_forall; intros; exact I ].
  Qed.

  Lemma oufresh_body : forall Δ Φ, oufresh K (gu_body Δ Φ) -> ogfresh (oshift (List.length Δ) K) Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma oufresh_alias : forall Δ E, oufresh K (gu_mk Δ (md_alias E)) -> omfresh (oshift (List.length Δ) K) E.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_def_prefix : forall Φ y b pv A M,
      ogfresh K (gm_ext Φ y (ge_def b pv A (Some M))) -> ogfresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_def_body : forall Φ y b pv A M,
      ogfresh K (gm_ext Φ y (ge_def b pv A (Some M))) -> ofresh (oshift (gm_binders Φ) K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_mod_prefix : forall Φ y pm U,
      ogfresh K (gm_ext Φ y (ge_mod pm U)) -> ogfresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_mod_unit : forall Φ y pm U,
      ogfresh K (gm_ext Φ y (ge_mod pm U)) -> oufresh (oshift (gm_binders Φ) K) U.
  Proof. destruct K; cbn; tauto. Qed.
End OFresh.

#[local] Hint Resolve ofresh_univ ofresh_succl ofresh_maxl_l ofresh_maxl_r ofresh_succ
  ofresh_natrec_A ofresh_natrec_Z ofresh_natrec_S ofresh_natrec_M ofresh_exfalso_A ofresh_exfalso_M
  ofresh_pi_A ofresh_pi_B ofresh_fn_M ofresh_app_l ofresh_app_r ofresh_let_M ofresh_let_B
  ofresh_letmod_U ofresh_mem ofresh_var omfresh_var omfresh_lit omfresh_mem omfresh_app_l omfresh_app_r
  oufresh_body oufresh_alias ogfresh_def_prefix ogfresh_def_body ogfresh_mod_prefix ogfresh_mod_unit : avoid.

(** ** Evaluation Builds No Variable *)

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack) (v b : nat).

  #[local] Hint Resolve env_av_nil env_av_cons env_av_var env_av_mod dav_args_snoc env_av_args
    dmav_local_nil dmav_global_nil : mctt.
  #[local] Hint Extern 1 (dav _ _ (dlvl_lit _)) => repeat constructor : mctt.
  #[local] Hint Extern 1 (dav _ _ (dlvl_suc _)) => apply dav_lvl_suc : mctt.
  #[local] Hint Extern 1 (dav _ _ (dlvl_max _ _)) => apply dav_lvl_max : mctt.

  (** The entry an extension adds, given the invariant of its value. *)
  Ltac deav_of d :=
    first [ apply deav_term; solve [ eassumption | eauto 3 with mctt avoid ]
          | apply deav_mod; solve [ eassumption | eauto 3 with mctt avoid ] ].

  (** Forward reasoning: instantiate each induction hypothesis at the
      position the environment it is about has its bad entry at, and
      discharge its premises. *)
  Ltac av_fwd :=
    repeat match goal with
    | H : forall x, ?K <> Some x -> deav ?v ?b (env_entry ?ρ x) |- _ => change (env_av v b K ρ) in H
    | H : Forall _ (_ :: _) |- _ => inversion_clear H
    | H : In _ (_ :: _) |- _ => destruct H as [<- | H]
    | H : In _ nil |- _ => destruct H
    | H : forall a, In a (?x :: ?l) -> ?P |- _ =>
        let H1 := fresh "H" in let H2 := fresh "H" in
        assert (H1 : forall a, a = x -> P) by (intros a Ha; apply H; left; symmetry; exact Ha);
        assert (H2 : forall a, In a l -> P) by (intros a Ha; apply H; right; exact Ha);
        specialize (H1 x eq_refl); clear H
    | Hs : modexp_spine ?H = _, Hf : ofresh ?K (a_mem ?H _) |- _ =>
        apply ofresh_mem in Hf; destruct (omfresh_spine _ _ _ _ _ Hs Hf); clear Hs
    | IH : forall K0, env_av ?v ?b K0 nil -> _ |- _ => specialize (IH None (env_av_nil _ _ None) I)
    | IH : forall K0, env_av ?v ?b K0 ?ρ -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ => specialize (IH K Hρ)
    | IH : forall K0, env_av ?v ?b K0 (extend_env (extend_env ?ρ ?d1) ?d2) -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in let E2 := fresh "E" in
        assert (E1 : deav v b (de_term d1)) by deav_of d1;
        assert (E2 : deav v b (de_term d2)) by deav_of d2;
        specialize (IH (oshift 1 (oshift 1 K)) (env_av_cons _ _ _ _ _ (env_av_cons _ _ _ _ _ Hρ E1) E2));
        rewrite oshift_oshift in IH; cbn [Nat.add] in IH
    | IH : forall K0, env_av ?v ?b K0 (extend_env ?ρ ?d) -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : deav v b (de_term d)) by deav_of d;
        specialize (IH (oshift 1 K) (env_av_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_av ?v ?b K0 (extend_env_mod ?ρ ?h) -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : deav v b (de_mod h)) by deav_of h;
        specialize (IH (oshift 1 K) (env_av_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_av ?v ?b K0 (env_args ?ρ ?args) -> _, Hρ : env_av ?v ?b ?K ?ρ,
      Ha : forall a, In a ?args -> dav ?v ?b a |- _ =>
        specialize (IH (oshift (List.length args) K) (env_av_args _ _ _ _ _ Hρ Ha));
        repeat match goal with Hl : List.length args = List.length ?D |- _ => rewrite Hl in IH end
    | IH : ?P -> ?Q |- _ =>
        let HP := fresh "HP" in assert (HP : P) by (solve [ eassumption | eauto 3 with mctt avoid ]); specialize (IH HP)
    end.

  Lemma eval_av :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall K, env_av v b K ρ -> ofresh K M -> dav v b m) /\
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       forall K, env_av v b K ρ -> dav v b m -> ofresh (oshift 1 K) A -> ofresh K MZ ->
            ofresh (oshift 2 K) MS -> dav v b r) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dav v b m -> dav v b n -> dav v b r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms ->
       forall K, env_av v b K ρ -> Forall (ofresh K) Ms -> forall a, In a ms -> dav v b a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r ->
       dav v b m -> (forall a, In a args -> dav v b a) -> dav v b r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall K, env_av v b K ρ -> omfresh K H -> dmav v b h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmav v b h -> dav v b n -> dmav v b r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmav v b h -> dav v b r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmav v b h -> dmav v b r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmav v b h -> dav v b r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmav v b h -> dmav v b r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
       forall K, env_av v b K ρ -> ogfresh K Φ -> env_av v b (oshift (gm_binders Φ) K) ρ').
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => forall K, env_av v b K ρ -> ofresh K M -> dav v b m)
             (fun A MZ MS m ρ r _ => forall K, env_av v b K ρ -> dav v b m -> ofresh (oshift 1 K) A ->
                                     ofresh K MZ -> ofresh (oshift 2 K) MS -> dav v b r)
             (fun m n r _ => dav v b m -> dav v b n -> dav v b r)
             (fun Ms ρ ms _ => forall K, env_av v b K ρ -> Forall (ofresh K) Ms ->
                                forall a, In a ms -> dav v b a)
             (fun m args r _ => dav v b m -> (forall a, In a args -> dav v b a) -> dav v b r)
             (fun H ρ h _ => forall K, env_av v b K ρ -> omfresh K H -> dmav v b h)
             (fun h n r _ => dmav v b h -> dav v b n -> dmav v b r)
             (fun h x r _ => dmav v b h -> dav v b r)
             (fun h y r _ => dmav v b h -> dmav v b r)
             (fun h ch r _ => dmav v b h -> dav v b r)
             (fun h ch r _ => dmav v b h -> dmav v b r)
             (fun ρ Φ ρ' _ => forall K, env_av v b K ρ -> ogfresh K Φ ->
                               env_av v b (oshift (gm_binders Φ) K) ρ'));
      intros.
    all: repeat match goal with
           | H : dav _ _ (_ _) |- _ => inversion_clear H
           | H : dmav _ _ (_ _ _) |- _ => inversion_clear H
           | H : dmav _ _ (_ _ _ _) |- _ => inversion_clear H
           end.
    all: av_fwd.
    all: try solve [ eauto 4 with mctt avoid ].
    (** What is left: the closures the rules build, and the module bodies,
        whose freshness is at the position their parameters and entries
        shift it to. *)
    - (* [efq] on a neutral *)
      apply dav_neut; [ assumption |]. inversion H; subst.
      eapply dav_exfalso with (K := K); eassumption.
    - (* a definition of a saturated body *)
      assert (HΦ : ogfresh (oshift (List.length Δ) K) (gm_ext Φ' x (ge_def b0 pv A (Some M))))
        by (eapply ofresh_prefix_upto; [ exact e0 | apply oufresh_body; exact H3 ]).
      specialize (H (ogfresh_def_prefix _ _ _ _ _ _ _ HΦ)).
      eapply H0; [ exact H | exact (ogfresh_def_body _ _ _ _ _ _ _ HΦ) ].
    - (* an alias submodule of a global module: a closure over the empty environment *)
      apply H. apply (dmav_local v b nil U args None); [ apply env_av_nil | exact I | exact H1 ].
    - (* a submodule of a saturated body *)
      assert (HΦ : ogfresh (oshift (List.length Δ) K) (gm_ext Φ' y (ge_mod pm Uy)))
        by (eapply ofresh_prefix_upto; [ exact e0 | apply oufresh_body; exact H2 ]).
      specialize (H (ogfresh_mod_prefix _ _ _ _ _ HΦ)).
      eapply dmav_local_nil; [ exact H | exact (ogfresh_mod_unit _ _ _ _ _ HΦ) ].
    - (* the empty body *)
      cbn [gm_binders]; rewrite oshift_zero; exact H.
    - (* a definition entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- oshift_oshift.
      apply env_av_cons; [ exact H | constructor; exact H0 ].
    - (* a submodule entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- oshift_oshift.
      apply env_av_cons;
        [ exact H | constructor; eapply dmav_local_nil; [ exact H | exact (ogfresh_mod_unit _ _ _ _ _ H1) ] ].
  Qed.
End Eval.

(** A closure, evaluated at one or two more entries. *)
Lemma eval_clo_av : forall Θ Ξ v b K (ρ : env) B c d,
    env_av v b K ρ -> ofresh (oshift 1 K) B -> dav v b c ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> dav v b d.
Proof.
  intros * Hρ HB Hc Hd.
  eapply (proj1 (eval_av Θ Ξ v b)); [ exact Hd | apply env_av_cons; [ exact Hρ | constructor; exact Hc ] | exact HB ].
Qed.

Lemma eval_clo2_av : forall Θ Ξ v b K (ρ : env) B c1 c2 d,
    env_av v b K ρ -> ofresh (oshift 2 K) B -> dav v b c1 -> dav v b c2 ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> dav v b d.
Proof.
  intros * Hρ HB Hc1 Hc2 Hd.
  eapply (proj1 (eval_av Θ Ξ v b) _ _ _ Hd (oshift 1 (oshift 1 K))).
  - apply env_av_cons; [ apply env_av_cons; [ exact Hρ | constructor; exact Hc1 ] | constructor; exact Hc2 ].
  - rewrite oshift_oshift; exact HB.
Qed.

Lemma app_av : forall Θ Ξ v b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dav v b m -> dav v b n -> dav v b r.
Proof. intros * H; exact (proj1 (proj2 (proj2 (eval_av Θ Ξ v b))) _ _ _ H). Qed.

Lemma dav_mono' : forall v b b' d, b <= b' -> dav v b d -> dav v b' d.
Proof. intros; eapply (proj1 (dav_mono v b)); eassumption. Qed.

Lemma dav_ne_mono' : forall v b b' d, b <= b' -> dav_ne v b d -> dav_ne v b' d.
Proof. intros; eapply (proj1 (proj2 (dav_mono v b))); eassumption. Qed.

(** ** Readback Introduces Only Variables Above the Ones in Scope *)

Lemma la_fresh_all : forall k xs, la_fresh k xs <-> la_all (ne_fresh k) xs.
Proof. intros k xs; induction xs as [| j s a r IH]; cbn; [ tauto | rewrite IH; tauto ]. Qed.

Lemma la_fresh_canon : forall k c xs, la_fresh k xs -> la_fresh k (snd (lvl_canon (c, xs))).
Proof. intros * H; apply la_fresh_all, la_all_canon, la_fresh_all; assumption. Qed.

Section Read.
  Variables (Θ : gdeps) (Ξ : gstack) (v : nat).

  (** A neutral variable at the readback length, at a bound past it. *)
  Lemma dav_fresh_var : forall b s a, v < s -> b <= s -> dav v b a -> dav v (S s) (⇑! a s).
  Proof.
    intros * Hv Hb Ha; constructor; [ eapply (proj1 (dav_mono v b)); [ exact Ha | lia ] | constructor; lia ].
  Qed.

  (** The invariant of a value built during readback: by its constructor, by
      monotonicity, or by the evaluation it came from. *)
  Ltac dav_tac v :=
    first [ eassumption
          | solve [ constructor ]
          | match goal with H : dav v ?b0 ?d |- dav v ?n ?d => eapply (dav_mono' v b0 n d); [ lia | exact H ] end
          | match goal with |- dav v _ (d_neut _ (d_var _)) => constructor; [ dav_tac v | constructor; lia ] end
          | match goal with |- dav v _ (d_succ _) => constructor; dav_tac v end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env (extend_env ?ρ ?c1) ?c2 ↘ ?d,
              Hρ : forall x, ?K <> Some x -> deav v ?b0 (env_entry ?ρ x) |- dav v ?n ?d =>
                eapply (eval_clo2_av _ _ v n K ρ B c1 c2 d);
                  [ eapply env_av_mono; [| exact Hρ ]; lia | assumption | dav_tac v | dav_tac v | exact e ]
            end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env ?ρ ?c ↘ ?d,
              Hρ : forall x, ?K <> Some x -> deav v ?b0 (env_entry ?ρ x) |- dav v ?n ?d =>
                eapply (eval_clo_av _ _ v n K ρ B c d);
                  [ eapply env_av_mono; [| exact Hρ ]; lia | assumption | dav_tac v | exact e ]
            end
          | match goal with
            | e : $| ?m & ?c | _ ⍮ _ ↘ ?d |- dav v ?n ?d =>
                eapply (app_av _ _ v n m c d); [ exact e | dav_tac v | dav_tac v ]
            end ].

  Lemma read_av :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall b, v < s -> b <= s -> dav_nf v b m -> nf_fresh (s - v - 1) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall b, v < s -> b <= s -> dav_ne v b m -> ne_fresh (s - v - 1) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall b, v < s -> b <= s -> dav v b a -> nf_fresh (s - v - 1) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall b, v < s -> b <= s -> dav_la v b xs -> la_fresh (s - v - 1) ys).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall b, v < s -> b <= s -> dav_nf v b m -> nf_fresh (s - v - 1) W)
             (fun s m M _ => forall b, v < s -> b <= s -> dav_ne v b m -> ne_fresh (s - v - 1) M)
             (fun s a A _ => forall b, v < s -> b <= s -> dav v b a -> nf_fresh (s - v - 1) A)
             (fun s xs ys _ => forall b, v < s -> b <= s -> dav_la v b xs -> la_fresh (s - v - 1) ys));
      intros;
      repeat match goal with
        | H : dav_nf _ _ (_ _ _) |- _ => inversion_clear H
        | H : dav_la _ _ (_ :: _) |- _ => inversion_clear H
        end.
    all: repeat match goal with
      | H : dav _ _ (d_neut _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_lvl _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_succ _) |- _ => inversion_clear H
      | H : dav _ _ (d_suniv _) |- _ => inversion_clear H
      | H : dav _ _ (d_pi _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_app _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_var _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_natrec _ _ _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_exfalso _ _ _) |- _ => inversion_clear H
      | H : dav_nf _ _ (_ _ _) |- _ => inversion_clear H
      end.
    all: cbn [nf_fresh ne_fresh la_fresh nf_lvl_of nf_univ_of fst snd]; repeat split.
    all: try exact I.
    all: try lia.
    all: try solve [ eauto 3 with mctt ].
    all: try solve [ apply la_fresh_canon; eauto 3 with mctt ].
    (** Under a binder: the closure is evaluated at a neutral at the readback
        length, which is above the bound, and read back one step further. *)
    all: repeat match goal with
      | |- context [ S (S (?s - v - 1)) ] => replace (S (S (s - v - 1))) with (S (S s) - v - 1) by lia
      | |- context [ S (?s - v - 1) ] => replace (S (s - v - 1)) with (S s - v - 1) by lia
      end.
    all: match goal with H : forall b1, _ -> b1 <= ?n -> _ -> ?C |- ?C => apply (H n); [ lia | lia |] end.
    all: repeat constructor.
    all: dav_tac v.
  Qed.
End Read.

(** ** The Initial Environment, and the Corollary *)

(** The initial environment of a context mentions only the levels below its
    length. *)
Lemma initial_env_av : forall Θ Ξ Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    forall v b, List.length Γ <= v -> List.length Γ <= b -> env_av v b None ρ.
Proof.
  induction 1; intros v' b' Hv Hb; cbn [List.length] in *.
  - apply env_av_nil.
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor; constructor;
      [ eapply (proj1 (eval_av Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ]
      | constructor; lia ].
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor; eapply (proj1 (eval_av Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ].
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor; eapply dmav_local_nil; [ apply IHinitial_env; lia | exact I ].
Qed.

(** The environment of [Γ ▹ A] avoids the new variable everywhere except at
    its own position. *)
Lemma initial_env_wk_av : forall Θ Ξ Γ A ρ,
    initial_env Θ Ξ (Γ ▹ A) ρ ->
    env_av (List.length Γ) (S (List.length Γ)) (Some 0) ρ.
Proof.
  intros * Hρ; inversion_clear Hρ.
  apply env_av_cons_bad; eapply initial_env_av; [ eassumption | lia | lia ].
Qed.

(** NbE invents no variables: a weakened term, normalized in the extended
    context at its weakened type, has a normal form fresh at the new
    variable. *)
Theorem nbe_wk_fresh : forall Θ Ξ Γ A M T W,
    nbe Θ Ξ (Γ ▹ A) M[↑]ʷ T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * Hn; inversion_clear Hn as [? ? ? ? ? ? ? Hρ].
  pose proof (initial_env_wk_av _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (read_av Θ Ξ (List.length Γ))); [ eassumption | cbn; lia | cbn; reflexivity |].
  constructor; eapply (proj1 (eval_av Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.

(** The same for the normal form of a weakened type. *)
Theorem nbe_ty_wk_fresh : forall Θ Ξ Γ A T W,
    nbe_ty Θ Ξ (Γ ▹ A) T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * Hn; inversion_clear Hn as [? ? ? ? ? Hρ].
  pose proof (initial_env_wk_av _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (proj2 (proj2 (read_av Θ Ξ (List.length Γ))))); [ eassumption | cbn; lia | cbn; reflexivity |].
  eapply (proj1 (eval_av Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.
