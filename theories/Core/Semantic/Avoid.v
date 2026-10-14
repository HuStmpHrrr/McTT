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
From Mctt.Core.Syntactic Require Import Fresh Members Inductives.
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

(** The components of a shape, each under the domains before it. *)
Fixpoint ptfresh (K : option nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => ofresh K B /\ ptfresh (oshift 1 K) t
  | pt_self _ Ps | pt_aux _ Ps => Forall (ofresh K) Ps
  end.

Lemma ptfresh_none : forall t, ptfresh None t.
Proof.
  induction t as [? Ps | ? Ps | B t IH]; cbn; [ apply Forall_forall; intros; exact I.. | split; [ exact I | exact IH ] ].
Qed.

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
  | dav_indty : forall p args, (forall a, In a args -> dav a) -> dav (d_ind p args)
  | dav_con : forall p c args, (forall a, In a args -> dav a) -> dav (d_con p c args)
  (** The recursive result of a function shape: the eliminator's closure,
      as [dav_elim], and the argument. *)
  | dav_ihfn : forall (ρ : env) nm A Bs t f K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift nm K) A ->
      (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
      dav f ->
      dav (d_ihfn ρ nm A Bs t f)
  (** The families of a function shape: the shape's rest is fresh under the
      domain the family binds; the motive, under the shape's parameters and
      the argument. *)
  | dav_shfam : forall p ups (ρ : env) t K,
      (forall a, In a ups -> dav a) ->
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ptfresh (oshift 1 K) t ->
      dav (d_shfam p ups ρ t)
  | dav_ihfam : forall (ρm : env) A (ρ : env) t f Km K,
      (forall x, Km <> Some x -> deav (env_entry ρm x)) ->
      ofresh (oshift (S (List.length (ptyp_ps t))) Km) A ->
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ptfresh (oshift 1 K) t ->
      dav f ->
      dav (d_ihfam ρm A ρ t f)
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
  (** A stuck eliminator: the motive is fresh under its binders, and so is
      each branch under its own. *)
  | dav_elim : forall (ρ : env) nm A Bs p args m K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift nm K) A ->
      (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
      (forall a, In a args -> dav a) ->
      dav_ne m ->
      dav_ne (d_elim ρ nm A Bs p args m)
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

  (** An environment that avoids [v] everywhere, extended. *)
  Lemma env_av_cons_none : forall ρ d, env_av v b None ρ -> dav v b d -> env_av v b None (ρ ↦ d).
  Proof. intros; change (@None nat) with (oshift 1 None); apply env_av_cons; [ assumption | constructor; assumption ]. Qed.

  Lemma env_av_args_none : forall args ρ,
      env_av v b None ρ -> (forall a, In a args -> dav v b a) -> env_av v b None (env_args ρ args).
  Proof. intros; change (@None nat) with (oshift (List.length args) None); apply env_av_args; assumption. Qed.

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
  Lemma ofresh_elim_A : forall p nm A Bs M, ofresh K (a_elim p nm A Bs M) -> ofresh (oshift nm K) A.
  Proof. destruct K; cbn; [ intros p nm A Bs M H; apply (proj1 (exp_fresh_elim _ p nm A Bs M)) in H; tauto | auto ]. Qed.
  Lemma ofresh_elim_B : forall p nm A Bs M, ofresh K (a_elim p nm A Bs M) ->
                                          forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B.
  Proof.
    destruct K; cbn; [| auto ].
    intros p nm A Bs M H; apply (proj1 (exp_fresh_elim _ p nm A Bs M)) in H as (_ & _ & H & _).
    intros * Hin; exact (proj1 (Forall_forall _ _) H _ Hin).
  Qed.
  Lemma ofresh_elim_M : forall p nm A Bs M, ofresh K (a_elim p nm A Bs M) -> ofresh K M.
  Proof. destruct K; cbn; [ intros p nm A Bs M H; apply (proj1 (exp_fresh_elim _ p nm A Bs M)) in H; tauto | auto ]. Qed.
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
(** Freshness does not read the name of an eliminator, so it is taken from
    the hypothesis rather than left to unification. *)
#[local] Hint Extern 1 (ofresh _ _) =>
  match goal with
  | H : ofresh ?K (a_elim ?p ?nm ?A ?Bs ?M) |- ofresh (oshift ?nm ?K) ?A => exact (ofresh_elim_A K p nm A Bs M H)
  | H : ofresh ?K (a_elim ?p ?nm ?A ?Bs ?M) |- ofresh ?K ?M => exact (ofresh_elim_M K p nm A Bs M H)
  end : avoid.

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
       forall K, env_av v b K ρ -> ogfresh K Φ -> env_av v b (oshift (gm_binders Φ) K) ρ') /\
    (forall ρ nm A Bs m r, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       forall K, env_av v b K ρ -> ofresh (oshift nm K) A ->
            (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) -> dav v b m -> dav v b r) /\
    (forall ρ nm A Bs gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       forall K, env_av v b K ρ -> ofresh (oshift nm K) A ->
            (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
            (forall a, In a vs -> dav v b a) -> forall a, In a ihs -> dav v b a) /\
    (forall ρ nm A Bs t m r, eval_ih Θ Ξ ρ nm A Bs t m r ->
       forall K, env_av v b K ρ -> ofresh (oshift nm K) A ->
            (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) -> dav v b m -> dav v b r) /\
    (forall p ups ρ t a, eval_shty Θ Ξ p ups ρ t a ->
       forall K, env_av v b K ρ -> ptfresh K t -> (forall u, In u ups -> dav v b u) -> dav v b a) /\
    (forall ρm A ρ t m a, eval_ihty Θ Ξ ρm A ρ t m a ->
       forall Km, env_av v b Km ρm -> ofresh (oshift (S (List.length (ptyp_ps t))) Km) A ->
       forall K, env_av v b K ρ -> ptfresh K t -> dav v b m -> dav v b a).
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
                               env_av v b (oshift (gm_binders Φ) K) ρ')
             (fun ρ nm A Bs m r _ => forall K, env_av v b K ρ -> ofresh (oshift nm K) A ->
                                    (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
                                    dav v b m -> dav v b r)
             (fun ρ nm A Bs gs vs ihs _ => forall K, env_av v b K ρ -> ofresh (oshift nm K) A ->
                                         (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
                                         (forall a, In a vs -> dav v b a) -> forall a, In a ihs -> dav v b a)
             (fun ρ nm A Bs t m r _ => forall K, env_av v b K ρ -> ofresh (oshift nm K) A ->
                                     (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) -> dav v b m -> dav v b r)
             (fun p ups ρ t a _ => forall K, env_av v b K ρ -> ptfresh K t -> (forall u, In u ups -> dav v b u) -> dav v b a)
             (fun ρm A ρ t m a _ => forall Km, env_av v b Km ρm -> ofresh (oshift (S (List.length (ptyp_ps t))) Km) A ->
                                   forall K, env_av v b K ρ -> ptfresh K t -> dav v b m -> dav v b a));
      intros; cbn [ptfresh ptyp_ps] in *.
    all: repeat match goal with
           | H : dav _ _ (_ _) |- _ => inversion_clear H
           | H : dmav _ _ (_ _ _) |- _ => inversion_clear H
           | H : dmav _ _ (_ _ _ _) |- _ => inversion_clear H
           end.
    all: av_fwd.
    (** Inductive types.  The values are lists, of which evaluation takes
        segments; a branch and the motive are evaluated in an environment
        extended by as many values as they bind. *)
    all: try solve [ lazymatch goal with |- dav _ _ (d_ind _ _) => idtac | |- dav _ _ (d_con _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    all: try solve [ match goal with
      | Hf : ofresh ?K (a_elim _ _ _ _ _), IH : _ -> _ -> dav _ _ ?r |- dav _ _ ?r =>
          apply IH; [ eapply ofresh_elim_B; exact Hf | assumption ]
      end ].
    all: try solve [ match goal with
      | e : brs_lookup ?Bs ?c = Some (?n, ?B), Hl : List.length ?vs = (ind_np ?D + List.length ?gs)%nat,
        Hn : ?n = _, Hih : ⟦ihs _ of ?gs under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?ihs,
        IHi : (forall x1, In x1 (skipn _ _) -> dav _ _ x1) -> forall x2, In x2 ?ihs -> dav _ _ x2,
        HB : forall c0 n0 B0, In (c0, n0, B0) ?Bs -> ofresh (oshift n0 ?K) B0,
        Hρ : env_av _ _ ?K ?ρ,
        IHB : forall K0, env_av _ _ K0 (env_args ?ρ ?L) -> ofresh K0 ?B -> dav _ _ ?r |- dav _ _ ?r =>
          let Hi := fresh "Hi" in
          pose proof (IHi ltac:(all_in_with assumption)) as Hi;
          destruct (eval_ihs_length _ _ _ _ _ _ _ Hih) as [_ Hni];
          apply (IHB (oshift (List.length L) K));
            [ apply env_av_args; [ exact Hρ | all_in_with assumption ]
            | rewrite (ind_branch_args_length _ _ _ _ Hl), Hni, <- Hn; exact (HB _ _ _ (brs_lookup_in _ _ _ _ e)) ]
      end ].
    all: try solve [ match goal with
      | Hl : List.length ?as' = ind_np ?D, Hn : ?nm = S (ind_nn ?D), HA : ofresh (oshift ?nm ?K) ?A,
        Hρ : env_av _ _ ?K ?ρ,
        IHA : forall K0, env_av _ _ K0 (env_args ?ρ ?L) -> ofresh K0 ?A -> dav _ _ ?a
        |- dav _ _ (⇑ ?a (d_elim _ _ _ _ _ _ _)) =>
          constructor;
            [ apply (IHA (oshift (List.length L) K));
                [ apply env_av_args; [ exact Hρ | all_in_with ltac:(constructor; [ constructor; assumption | assumption ]) ]
                | rewrite (ind_motive_args_length _ _ _ Hl), <- Hn; exact HA ]
            | eapply dav_elim; eassumption ]
      end ].
    (* the recursive results *)
    all: try solve [ match goal with
      | IH : (forall x1, In x1 ?vs -> dav _ _ x1) -> forall x2, In x2 ?ihs -> dav _ _ x2,
        Hv : forall x3, In x3 (_ :: ?vs) -> dav _ _ x3, Ha : In ?d ?ihs |- dav _ _ ?d =>
          exact (IH (all_in_tail _ _ _ Hv) _ Ha)
      end ].
    all: try solve [ eauto 4 with mctt avoid ].
    (** The types of a function shape's argument and recursive result: a
        [Π] over the family, in an environment that holds only the family. *)
    all: try solve [ lazymatch goal with |- dav _ _ (Πᵈ _ (_ ↦ d_shfam _ _ _ _) _) => idtac end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      eapply dav_pi with (K := None); [ eauto | | exact I ];
      apply env_av_cons_none; [ apply env_av_nil | eapply dav_shfam; eassumption ] ].
    all: try solve [ lazymatch goal with |- dav _ _ (Πᵈ _ (_ ↦ d_ihfam _ _ _ _ _) _) => idtac end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      eapply dav_pi with (K := None); [ eauto | | exact I ];
      apply env_av_cons_none; [ apply env_av_nil | eapply dav_ihfam; eassumption ] ].
    (** The type of the recursive result at a shape's leaf: the motive at
        the leaf's parameters and the argument. *)
    all: try solve [ match goal with
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs, IH : forall K0, env_av _ _ K0 (env_args ?ρm (?bs ++ ?v0 :: nil)) -> ofresh K0 ?A -> _,
        Hm : env_av _ _ ?Km ?ρm, HA : ofresh (oshift (S (List.length ?Ps)) ?Km) ?A |- _ =>
          let Hlb := fresh "Hlb" in
          assert (Hlb : List.length bs = List.length Ps) by (clear - e; induction e; cbn; congruence);
          apply (IH (oshift (List.length (bs ++ v0 :: nil)) Km));
            [ apply env_av_args; [ exact Hm | apply dav_args_snoc; assumption ]
            | rewrite List.length_app, Hlb; cbn [List.length]; replace (List.length Ps + 1) with (S (List.length Ps)) by lia; exact HA ]
      end ].
    (** What is left: the closures the rules build, and the module bodies,
        whose freshness is at the position their parameters and entries
        shift it to. *)
    - (* [efq] on a neutral *)
      apply dav_neut; [ assumption |]. inversion H; subst.
      eapply dav_exfalso with (K := K); eassumption.
    - (* the module of an inductive type, a member of a global module: the
         type former, applied to the module's arguments *)
      apply H; [ constructor; all_in_with assumption | exact H1 ].
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

Lemma shty_av : forall Θ Ξ v b p ups ρ t a K, eval_shty Θ Ξ p ups ρ t a ->
    env_av v b K ρ -> ptfresh K t -> (forall u, In u ups -> dav v b u) -> dav v b a.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
  exact (Hs _ _ _ _ _ H K).
Qed.

Lemma ihty_av : forall Θ Ξ v b ρm A ρ t m a Km K, eval_ihty Θ Ξ ρm A ρ t m a ->
    env_av v b Km ρm -> ofresh (oshift (S (List.length (ptyp_ps t))) Km) A ->
    env_av v b K ρ -> ptfresh K t -> dav v b m -> dav v b a.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy).
  intros; eapply Hy; eassumption.
Qed.

(** The shapes of a constructor's recursive arguments end at [nn]
    parameters, argument by argument. *)
Lemma plen_forall : forall (gs : list carg) (nn : nat), cargs_plen nn gs ->
    Forall (fun g => match g with ca_rec t => List.length (ptyp_ps t) = nn | ca_arg _ => True end) gs.
Proof.
  unfold cargs_plen; induction gs as [| g gs IH]; intros nn H; constructor.
  - destruct g as [A | t]; [ exact I | exact (H nil t gs eq_refl) ].
  - apply IH; intros gs1 t gs2 E; apply (H (g :: gs1) t gs2); rewrite E; reflexivity.
Qed.

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

  (** The fresh variables of the telescopes of a declaration are above the
      readback length, and below the length past them.  The types of the
      telescopes are closed, so their environments avoid [v] everywhere. *)
  Lemma fresh_tele_av : forall ρ T s vs, fresh_tele Θ Ξ ρ T s vs ->
      forall b, v < s -> b <= s -> env_av v b None ρ -> forall a, In a vs -> dav v (s + List.length T) a.
  Proof.
    induction 1; intros b0 Hv Hb Hρ; [ apply all_in_nil |].
    assert (Ha : dav v b0 a) by (eapply (proj1 (eval_av Θ Ξ v b0)); [ eassumption | exact Hρ | exact I ]).
    cbn [List.length]; replace (s + S (List.length T)) with (S s + List.length T) by lia.
    apply all_in_cons.
    - eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia.
    - apply (IHfresh_tele (S s)); [ lia | lia |].
      change (@None nat) with (oshift 1 None).
      apply env_av_cons; [ eapply env_av_mono; [| exact Hρ ]; lia | constructor; apply (dav_fresh_var b0); assumption ].
  Qed.

  Lemma fresh_cargs_av : forall p ups ρ gs s vs, fresh_cargs Θ Ξ p ups ρ gs s vs ->
      forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a ups -> dav v b a) ->
      forall a, In a vs -> dav v (s + List.length gs) a.
  Proof.
    induction 1; intros b0 Hv Hb Hρ Hu.
    - apply all_in_nil.
    - assert (Ha : dav v b0 a) by (eapply (proj1 (eval_av Θ Ξ v b0)); [ eassumption | exact Hρ | exact I ]).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      apply all_in_cons; [ eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia |].
      apply (IHfresh_cargs (S s)); [ lia | lia | | intros; eapply dav_mono'; [| apply Hu; eassumption ]; lia ].
      change (@None nat) with (oshift 1 None).
      apply env_av_cons; [ eapply env_av_mono; [| exact Hρ ]; lia | constructor; apply (dav_fresh_var b0); assumption ].
    - assert (Ha : dav v b0 a) by (eapply shty_av; [ eassumption | exact Hρ | apply ptfresh_none | exact Hu ]).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      apply all_in_cons; [ eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia |].
      apply (IHfresh_cargs b0); [ lia | lia | exact Hρ | exact Hu ].
  Qed.

  (** The recursive results are at the motive's instance at the recursive
      argument and its parameters: as many as the motive binds, when each
      recursive argument has as many parameters as the type has non-uniform
      ones. *)
  Lemma fresh_ihs_av : forall ρ A ρa gs vs s ihs, fresh_ihs Θ Ξ ρ A ρa gs vs s ihs ->
      forall nn b K, v < s -> b <= s -> env_av v b K ρ -> ofresh (oshift (S nn) K) A -> env_av v b None ρa ->
      List.Forall (fun g => match g with ca_rec t => List.length (ptyp_ps t) = nn | ca_arg _ => True end) gs ->
      (forall a, In a vs -> dav v b a) ->
      forall a, In a ihs -> dav v (s + cargs_nrec gs) a.
  Proof.
    induction 1; intros nn b0 K Hv Hb Hρ HA Hρa Hl Hvs.
    - apply all_in_nil.
    - inversion_clear Hl as [| ? ? _ Hl2].
      apply (IHfresh_ihs nn b0 K); try assumption.
      + apply env_av_cons_none; [ exact Hρa | exact (all_in_head _ _ _ Hvs) ].
      + exact (all_in_tail _ _ _ Hvs).
    - inversion_clear Hl as [| ? ? Hl1 Hl2]; cbn beta iota in Hl1.
      assert (Ha : dav v b0 a)
        by (eapply ihty_av; [ eassumption | exact Hρ | rewrite Hl1; exact HA | exact Hρa | apply ptfresh_none
                            | exact (all_in_head _ _ _ Hvs) ]).
      cbn [cargs_nrec]; replace (s + S (cargs_nrec gs)) with (S s + cargs_nrec gs) by lia.
      apply all_in_cons.
      + eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia.
      + apply (IHfresh_ihs nn b0 K); try assumption; try lia.
        exact (all_in_tail _ _ _ Hvs).
  Qed.

  Lemma nfs_fresh_app : forall k Ms Ns, nfs_fresh k Ms -> nfs_fresh k Ns -> nfs_fresh k (nfs_app Ms Ns).
  Proof. induction Ms; cbn; intuition. Qed.

  Lemma read_av :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall b, v < s -> b <= s -> dav_nf v b m -> nf_fresh (s - v - 1) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall b, v < s -> b <= s -> dav_ne v b m -> ne_fresh (s - v - 1) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall b, v < s -> b <= s -> dav v b a -> nf_fresh (s - v - 1) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall b, v < s -> b <= s -> dav_la v b xs -> la_fresh (s - v - 1) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a vs -> dav v b a) ->
       nfs_fresh (s - v - 1) Ms) /\
    (forall s p ups ρ gs vs Ms, read_cargs Θ Ξ s p ups ρ gs vs Ms ->
       forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a ups -> dav v b a) ->
       (forall a, In a vs -> dav v b a) -> nfs_fresh (s - v - 1) Ms) /\
    (forall s ρ A p D ups cs Bs Bs', read_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
       forall b K, v < s -> b <= s -> env_av v b K ρ -> ofresh (oshift (S (ind_nn D)) K) A ->
       (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
       (forall a, In a ups -> dav v b a) -> nbrs_fresh (s - v - 1) Bs').
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall b, v < s -> b <= s -> dav_nf v b m -> nf_fresh (s - v - 1) W)
             (fun s m M _ => forall b, v < s -> b <= s -> dav_ne v b m -> ne_fresh (s - v - 1) M)
             (fun s a A _ => forall b, v < s -> b <= s -> dav v b a -> nf_fresh (s - v - 1) A)
             (fun s xs ys _ => forall b, v < s -> b <= s -> dav_la v b xs -> la_fresh (s - v - 1) ys)
             (fun s ρ T vs Ms _ => forall b, v < s -> b <= s -> env_av v b None ρ ->
                                  (forall a, In a vs -> dav v b a) -> nfs_fresh (s - v - 1) Ms)
             (fun s p ups ρ gs vs Ms _ => forall b, v < s -> b <= s -> env_av v b None ρ ->
                                        (forall a, In a ups -> dav v b a) ->
                                        (forall a, In a vs -> dav v b a) -> nfs_fresh (s - v - 1) Ms)
             (fun s ρ A p D ups cs Bs Bs' _ => forall b K, v < s -> b <= s -> env_av v b K ρ ->
                                             ofresh (oshift (S (ind_nn D)) K) A ->
                                             (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
                                             (forall a, In a ups -> dav v b a) -> nbrs_fresh (s - v - 1) Bs'));
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
      | H : dav _ _ (d_ind _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_con _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_app _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_var _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_natrec _ _ _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_exfalso _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_elim _ _ _ _ _ _ _) |- _ => inversion_clear H
      | H : dav_nf _ _ (_ _ _) |- _ => inversion_clear H
      end.
    all: cbn [nf_fresh ne_fresh la_fresh nfs_fresh nbrs_fresh nf_lvl_of nf_univ_of fst snd]; repeat split.
    all: try exact I.
    all: try lia.
    all: try solve [ eauto 3 with mctt ].
    all: try solve [ apply la_fresh_canon; eauto 3 with mctt ].
    (** Inductive types.  The parameters and the arguments of a constructor,
        and the parameters of a type, are read back at their types, which
        are closed. *)
    all: try solve [ match goal with
      | IH1 : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None nil -> _ -> nfs_fresh _ ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None (env_args nil ?as') -> _ -> _ -> nfs_fresh _ ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> dav v ?b a |- nfs_fresh _ (nfs_app ?Ps ?Args) =>
          apply nfs_fresh_app;
            [ apply (IH1 b); [ lia | lia | apply env_av_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_av_args_none; [ apply env_av_nil | assumption ]
                             | all_in_with assumption | all_in_with assumption ] ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None nil -> _ -> nfs_fresh _ ?Ps,
        Hb : ?b <= ?s |- nfs_fresh _ ?Ps =>
          apply (IH b); [ lia | lia | apply env_av_nil | assumption ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> dav_nf v b0 (⇓ ?a ?v0) -> nf_fresh _ ?V |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | constructor;
            [ eapply (proj1 (eval_av Θ Ξ v b)); [ exact e | exact Hρ | exact I ] | exact (all_in_head _ _ _ Hv) ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None (?ρ ↦ ?v0) -> _ |- nfs_fresh _ _ =>
          apply (IH b); try lia;
            [ apply env_av_cons_none; [ exact Hρ | exact (all_in_head _ _ _ Hv) ] |..]; all_in_with assumption
      end ].
    all: try solve [ match goal with
      | e : eval_shty _ _ ?p ?ups ?ρ ?t ?a, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> dav v ?b x,
        Hv : forall x, In x (?v0 :: _) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> dav_nf v b0 (⇓ ?a ?v0) -> nf_fresh _ ?V |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | constructor;
            [ eapply shty_av; [ exact e | exact Hρ | apply ptfresh_none | exact Hu ] | exact (all_in_head _ _ _ Hv) ] ]
      end ].
    all: try solve [ match goal with
      | Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (_ :: ?vs) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None ?ρ -> _ -> (forall x, In x ?vs -> _) -> nfs_fresh _ ?W
        |- nfs_fresh _ ?W =>
          apply (IH b); [ lia | lia | exact Hρ | assumption | exact (all_in_tail _ _ _ Hv) ]
      end ].
    (** A stuck eliminator: its motive under the fresh non-uniform
        parameters and scrutinee, which are above the readback length. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil (firstn (ind_nu ?D) ?as')) _ ?s ?ns,
        e2 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?a,
        IH : forall b0, _ -> _ -> dav v b0 ?a -> nf_fresh _ ?A',
        Hb : ?b <= ?s, Hρ : forall x, ?K <> Some x -> deav v ?b (env_entry ?ρ x),
        Hn : ?nm = S (ind_nn ?D), HA : ofresh (oshift ?nm ?K) ?A,
        Has : forall x, In x ?as' -> dav v ?b x |- nf_fresh (?nm + _) ?A' =>
          let Hlen := fresh "Hlen" in let Hns := fresh "Hns" in
          pose proof (fresh_tele_length _ _ _ _ f) as Hlen; rewrite ind_nn_tele_length in Hlen;
          assert (Hns : forall x, In x ns -> dav v (s + ind_nn D) x)
            by (rewrite <- (ind_nn_tele_length D); eapply (fresh_tele_av _ _ _ _ f b);
                [ lia | lia | apply env_av_args_none; [ apply env_av_nil | all_in_with assumption ] ]);
          replace (nm + (s - v - 1)) with (S (s + ind_nn D) - v - 1) by lia;
          apply (IH (S (s + ind_nn D))); [ lia | lia |];
          eapply (proj1 (eval_av Θ Ξ v (S (s + ind_nn D))));
            [ exact e2 | apply env_av_args; [ eapply env_av_mono; [| exact Hρ ]; lia |] |];
            [ apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; lia |];
              apply all_in_cons; [| apply all_in_nil ];
              apply (dav_fresh_var (s + ind_nn D)); [ lia | lia |];
              constructor; apply all_in_app;
                [ apply all_in_firstn; intros; eapply dav_mono'; [| apply Has; eassumption ]; lia | exact Hns ]
            | rewrite length_app, Hlen; cbn [List.length]; replace (ind_nn D + 1) with nm by lia; exact HA ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0, v < ?s -> b0 <= ?s -> env_av v b0 K0 ?ρ -> ofresh (oshift (S (ind_nn ?D)) K0) ?A -> _ -> _ ->
             nbrs_fresh _ ?W,
        Hb : ?b <= ?s, Hρ : forall x, ?K <> Some x -> deav v ?b (env_entry ?ρ x),
        Hn : ?nm = S (ind_nn ?D), HA : ofresh (oshift ?nm ?K) ?A,
        HB : forall c0 n0 B0, In (c0, n0, B0) _ -> ofresh (oshift n0 ?K) B0 |- nbrs_fresh _ ?W =>
          apply (IH b K); [ lia | lia | exact Hρ | rewrite <- Hn; exact HA | exact HB | all_in_with assumption ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results, as many as it binds. *)
    all: try solve [ match goal with
      | e : ?n = (ind_nn ?D + List.length ?gs + cargs_nrec ?gs)%nat,
        f : fresh_tele _ _ (env_args nil ?ups) _ ?s ?ns,
        f0 : fresh_cargs _ _ _ _ _ ?gs _ ?vs,
        Hpl : cargs_plen (ind_nn ?D) ?gs,
        f2 : fresh_ihs _ _ ?ρ ?A _ ?gs ?vs _ ?ihs,
        e0 : ⟦ ?B ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ ?vs ++ ?ihs) ↘ ?bv,
        e1 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?t,
        IH : forall b0, _ -> _ -> dav_nf v b0 (⇓ ?t ?bv) -> nf_fresh _ ?B',
        Hb : ?b <= ?s, Hρ : env_av v ?b ?K ?ρ, HA : ofresh (oshift (S (ind_nn ?D)) ?K) ?A,
        HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> ofresh (oshift n0 ?K) B0,
        Hu : forall x, In x ?ups -> dav v ?b x |- nf_fresh (?n + _) ?B' =>
          let Hl1 := fresh "Hl" in let Hl2 := fresh "Hl" in let Hl3 := fresh "Hl" in
          let Hns := fresh "Hns" in let Hvs := fresh "Hvs" in let Hρa := fresh "Hρa" in let Hihs := fresh "Hihs" in
          pose proof (fresh_tele_length _ _ _ _ f) as Hl1; rewrite ind_nn_tele_length in Hl1;
          pose proof (fresh_cargs_length _ _ _ _ _ _ f0) as Hl2;
          pose proof (fresh_ihs_length _ _ _ _ _ _ _ f2) as Hl3;
          assert (Hns : forall x, In x ns -> dav v (s + ind_nn D) x)
            by (rewrite <- (ind_nn_tele_length D); eapply (fresh_tele_av _ _ _ _ f b);
                [ lia | lia | apply env_av_args_none; [ apply env_av_nil | assumption ] ]);
          assert (Hρa : env_av v (s + ind_nn D) None (env_args nil (ups ++ ns)))
            by (apply env_av_args_none; [ apply env_av_nil | apply all_in_app; [ intros; eapply dav_mono'; [| apply Hu; eassumption ]; lia | exact Hns ] ]);
          pose proof (fresh_cargs_av _ _ _ _ _ _ f0 (s + ind_nn D) ltac:(lia) ltac:(lia) Hρa
                        ltac:(intros; eapply dav_mono'; [| apply Hu; eassumption ]; lia)) as Hvs;
          pose proof (fresh_ihs_av _ _ _ _ _ _ _ f2 (ind_nn D) (s + ind_nn D + List.length gs) K
                        ltac:(lia) ltac:(lia) ltac:(eapply env_av_mono; [| exact Hρ ]; lia) HA
                        ltac:(eapply env_av_mono; [| exact Hρa ]; lia) (plen_forall _ _ Hpl) Hvs) as Hihs;
          replace (n + (s - v - 1)) with (s + n - v - 1) by lia;
          apply (IH (s + n)); [ lia | lia |];
          constructor;
            [ eapply (proj1 (eval_av Θ Ξ v (s + n))); [ exact e1 | apply env_av_args; [ eapply env_av_mono; [| exact Hρ ]; lia |] |];
                [ apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; lia |];
                  apply all_in_cons; [| apply all_in_nil ];
                  constructor; apply all_in_app; [ intros; eapply dav_mono'; [| apply Hu; eassumption ]; lia |];
                  apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; lia
                                    | intros; eapply dav_mono'; [| apply Hvs; eassumption ]; lia ]
                | rewrite length_app, Hl1; cbn [List.length]; replace (ind_nn D + 1) with (S (ind_nn D)) by lia; exact HA ]
            | eapply (proj1 (eval_av Θ Ξ v (s + n))); [ exact e0 | apply env_av_args; [ eapply env_av_mono; [| exact Hρ ]; lia |] |];
                [ apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; lia |];
                  apply all_in_app; [ intros; eapply dav_mono'; [| apply Hvs; eassumption ]; lia
                                    | intros; eapply dav_mono'; [| apply Hihs; eassumption ]; lia ]
                | rewrite !length_app, Hl1, Hl2, Hl3, Nat.add_assoc, <- e; exact (HB _ _ _ (or_introl eq_refl)) ] ]
      end ].
    all: try solve [ match goal with
      | IH : context [ nbrs_fresh _ ?W ], HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> _ |- nbrs_fresh _ ?W =>
          eapply IH;
            [ lia | | eassumption | eassumption | intros c1 n1 B1 Hin; exact (HB c1 n1 B1 (or_intror Hin)) | eassumption ];
          lia
      end ].
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
