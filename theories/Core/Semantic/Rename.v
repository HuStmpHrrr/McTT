(** * Renaming the Levels of Values: Readback Commutes with Weakening

    A value names variables by de Bruijn *level* ([d_var x]); readback at
    length [s] turns the level [x] into the index [s - x - 1].  So the same
    value read back at [s] and at [S s] gives two normal forms that differ by
    the weakening [↑] — provided the value only mentions levels below [s]
    ([read_shift]).  This is the step "readback at [|Γ| + 1] is the weakening
    of readback at [|Γ|]" of the semantic proof that NbE commutes with
    weakening ([Core.NbEWeakening]).

    The two readbacks do not run in lockstep on the *same* value: under a
    binder, readback at [s] applies the closure to the fresh level [s], and
    readback at [S s] to the fresh level [S s].  So the statement is
    generalised to a renaming [f] of levels, applied to values by [drn f]:

    - evaluation is equivariant under every [f] ([eval_rn]): it never looks
      at a level, it only carries them;
    - readback of [drn f d] at [s'] is the readback of [d] at [s], renamed by
      a weakening [φ] that sends the index of [x] at [s] to the index of
      [f x] at [s'] ([read_rn]).  For the canonical form of a level this
      needs [φ] to preserve the order of indices
      ([Core.Syntactic.NfRename.lvl_canon_wk]).

    [read_shift] is the instance [f x = x] below [s] and [f x = S x] from
    [s] on: it fixes the initial environment of a context of length [s], and
    so every value evaluated in it.

    That readback only meets levels below [s] is the invariant [dav] of
    [Core.Semantic.Avoid], at every excluded level [v ≥ s] ([dbd]). *)
From Stdlib Require Import Arith Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE Avoid.
From Mctt.Core.Syntactic Require Import Fresh Members NfRename.
Import Domain_Notations Syntax_Notations Wk_Notations.

(** ** The Renaming *)

Section Rename.
  Variable f : nat -> nat.

  Fixpoint drn (d : domain) : domain :=
    match d with
    | d_nat => d_nat
    | d_pi a ρ B => d_pi (drn a) (List.map dern ρ) B
    | d_univ i => d_univ i
    | d_suniv l => d_suniv (drn l)
    | d_level n => d_level n
    | d_lvl c xs => d_lvl c (List.map (fun ka => match ka with (k, n, m) => (k, n, drn_ne m) end) xs)
    | d_zero => d_zero
    | d_succ m => d_succ (drn m)
    | d_True => d_True
    | d_true => d_true
    | d_False => d_False
    | d_fn ρ M => d_fn (List.map dern ρ) M
    | d_neut a m => d_neut (drn a) (drn_ne m)
    | d_member h ch => d_member (dmrn h) ch
    end
  with drn_ne (m : domain_ne) : domain_ne :=
    match m with
    | d_var x => d_var (f x)
    | d_app m n => d_app (drn_ne m) (drn_nf n)
    | d_natrec ρ A mz MS m => d_natrec (List.map dern ρ) A (drn mz) MS (drn_ne m)
    | d_exfalso ρ A m => d_exfalso (List.map dern ρ) A (drn_ne m)
    | d_glob p => d_glob p
    end
  with drn_nf (n : domain_nf) : domain_nf :=
    match n with
    | d_dom a m => d_dom (drn a) (drn m)
    end
  with dmrn (h : dmod) : dmod :=
    match h with
    | dm_global p args => dm_global p (List.map drn args)
    | dm_local ρ U args => dm_local (List.map dern ρ) U (List.map drn args)
    | dm_member h ch => dm_member (dmrn h) ch
    end
  with dern (e : dentry) : dentry :=
    match e with
    | de_term d => de_term (drn d)
    | de_mod h => de_mod (dmrn h)
    end.

  Definition ern (ρ : env) : env := List.map dern ρ.
  Definition larn (xs : list (nat * nat * domain_ne)) : list (nat * nat * domain_ne) :=
    List.map (fun ka => match ka with (k, n, m) => (k, n, drn_ne m) end) xs.

  Lemma drn_lvl : forall c xs, drn (d_lvl c xs) = d_lvl c (larn xs).
  Proof. reflexivity. Qed.

  Lemma ern_cons : forall e ρ, ern (e :: ρ) = dern e :: ern ρ.
  Proof. reflexivity. Qed.

  Lemma ern_nil : ern nil = nil.
  Proof. reflexivity. Qed.

  Lemma env_entry_rn : forall ρ x, env_entry (ern ρ) x = dern (env_entry ρ x).
  Proof.
    intros; rewrite !env_entry_nth; unfold ern.
    change (de_term d_zero) with (dern (de_term d_zero)) at 1.
    apply List.map_nth.
  Qed.

  Lemma env_var_rn : forall ρ x, env_var (ern ρ) x = drn (env_var ρ x).
  Proof. intros; unfold env_var; rewrite env_entry_rn; destruct (env_entry ρ x); reflexivity. Qed.

  Lemma env_mod_rn : forall ρ x, env_mod (ern ρ) x = dmrn (env_mod ρ x).
  Proof. intros; unfold env_mod; rewrite env_entry_rn; destruct (env_entry ρ x); reflexivity. Qed.

  Lemma env_args_rn : forall args ρ, ern (env_args ρ args) = env_args (ern ρ) (List.map drn args).
  Proof. induction args; intros; cbn; [ reflexivity | apply IHargs ]. Qed.

  Lemma dsort_rn : forall d, dsort (drn d) = dsort d.
  Proof. destruct d; reflexivity. Qed.

  Lemma dlvl_view_rn : forall d, dlvl_view (drn d) = (fst (dlvl_view d), larn (snd (dlvl_view d))).
  Proof. destruct d; cbn; try reflexivity; rewrite dsort_rn; reflexivity. Qed.

  Lemma dlvl_suc_rn : forall d, drn (dlvl_suc d) = dlvl_suc (drn d).
  Proof.
    intros; unfold dlvl_suc, dlvl_cst, dlvl_atoms; rewrite dlvl_view_rn, drn_lvl; cbn [fst snd]; f_equal.
    unfold larn; rewrite !List.map_map; apply List.map_ext; intros [[] ?]; reflexivity.
  Qed.

  Lemma dlvl_max_rn : forall d e, drn (dlvl_max d e) = dlvl_max (drn d) (drn e).
  Proof.
    intros; unfold dlvl_max, dlvl_cst, dlvl_atoms; rewrite !dlvl_view_rn, drn_lvl; cbn [fst snd]; f_equal.
    unfold larn; apply List.map_app.
  Qed.

  Lemma length_ern : forall ρ, List.length (ern ρ) = List.length ρ.
  Proof. intros; apply List.length_map. Qed.
End Rename.

(** ** Evaluation Is Equivariant *)

Create Rewrite HintDb rn.

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack) (f : nat -> nat).

  #[local] Hint Rewrite env_var_rn env_mod_rn env_args_rn dlvl_suc_rn dlvl_max_rn
    List.map_app List.length_map : rn.

  Lemma eval_rn :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f m) /\
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       ⟦rec drn f m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f r) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| drn f m & drn f n | Θ ⍮ Ξ ↘ drn f r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ern f ρ ↘ List.map (drn f) ms) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> $*| drn f m & List.map (drn f) args | Θ ⍮ Ξ ↘ drn f r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ern f ρ ↘ dmrn f h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> $ᵐ| dmrn f h & drn f n | Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmrn f h ·ₜ x Θ ⍮ Ξ ↘ drn f r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmrn f h ·ₘ y Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmrn f h ·ₜ* ch Θ ⍮ Ξ ↘ drn f r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmrn f h ·ₘ* ch Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ern f ρ ↘ ern f ρ').
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => ⟦ M ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f m)
             (fun A MZ MS m ρ r _ => ⟦rec drn f m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f r)
             (fun m n r _ => $| drn f m & drn f n | Θ ⍮ Ξ ↘ drn f r)
             (fun Ms ρ ms _ => ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ern f ρ ↘ List.map (drn f) ms)
             (fun m args r _ => $*| drn f m & List.map (drn f) args | Θ ⍮ Ξ ↘ drn f r)
             (fun H ρ h _ => ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ern f ρ ↘ dmrn f h)
             (fun h n r _ => $ᵐ| dmrn f h & drn f n | Θ ⍮ Ξ ↘ dmrn f r)
             (fun h x r _ => dmrn f h ·ₜ x Θ ⍮ Ξ ↘ drn f r)
             (fun h y r _ => dmrn f h ·ₘ y Θ ⍮ Ξ ↘ dmrn f r)
             (fun h ch r _ => dmrn f h ·ₜ* ch Θ ⍮ Ξ ↘ drn f r)
             (fun h ch r _ => dmrn f h ·ₘ* ch Θ ⍮ Ξ ↘ dmrn f r)
             (fun ρ Φ ρ' _ => ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ern f ρ ↘ ern f ρ'));
      intros; cbn [drn drn_ne drn_nf dmrn dern List.map] in *;
      repeat change (List.map (dern f) ?ρ) with (ern f ρ) in *;
      autorewrite with rn in *; cbn [List.map] in *;
      try solve [ econstructor; autorewrite with rn; eauto ].
    - (* a variable *) rewrite <- env_var_rn; apply eval_exp_var.
    - (* a module slot *) rewrite <- env_mod_rn; apply eval_me_var.
  Qed.
End Eval.

(** ** Values that Mention Only the Levels Below [b]

    [dav v b d] of [Core.Semantic.Avoid] bounds the levels of [d] by [b] and
    excludes [v]; at every [v ≥ b] the exclusion is vacuous, and a closure
    evaluated at a level [≥ b] stays within the bound. *)
Definition dbd (b : nat) (d : domain) : Prop := forall v, b <= v -> dav v b d.
Definition dbd_ne (b : nat) (m : domain_ne) : Prop := forall v, b <= v -> dav_ne v b m.
Definition dbd_nf (b : nat) (n : domain_nf) : Prop := forall v, b <= v -> dav_nf v b n.
Definition dbd_la (b : nat) (xs : list (nat * nat * domain_ne)) : Prop := forall v, b <= v -> dav_la v b xs.

Section Bound.
  Variables (Θ : gdeps) (Ξ : gstack).

  Ltac dbd_inv := unfold dbd, dbd_ne, dbd_nf, dbd_la in *; intros * H; repeat split; intros v Hv;
    repeat match goal with H : forall v, _ <= v -> _ |- _ => specialize (H v ltac:(lia)) end;
    repeat match goal with
      | H : dav _ _ (_ _) |- _ => inversion_clear H
      | H : dav _ _ (_ _ _) |- _ => inversion_clear H
      | H : dav _ _ (_ _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (_ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (_ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (_ _ _ _ _) |- _ => inversion_clear H
      | H : dav_nf _ _ (_ _ _) |- _ => inversion_clear H
      | H : dav_la _ _ (_ :: _) |- _ => inversion_clear H
      end;
    try lia; try assumption.

  Lemma dbd_nf_inv : forall b a m, dbd_nf b (⇓ a m) -> dbd b a /\ dbd b m.
  Proof. dbd_inv. Qed.
  Lemma dbd_neut_inv : forall b a m, dbd b (⇑ a m) -> dbd b a /\ dbd_ne b m.
  Proof. dbd_inv. Qed.
  Lemma dbd_suniv_inv : forall b l, dbd b 𝕌@l -> dbd b l.
  Proof. dbd_inv. Qed.
  Lemma dbd_succ_inv : forall b m, dbd b (succᵈ m) -> dbd b m.
  Proof. dbd_inv. Qed.
  Lemma dbd_lvl_inv : forall b c xs, dbd b (lvᵈ c xs) -> dbd_la b xs.
  Proof. dbd_inv. Qed.
  Lemma dbd_la_inv : forall b k n m xs, dbd_la b ((k, n, m) :: xs) -> dbd_ne b m /\ dbd_la b xs.
  Proof. dbd_inv. Qed.
  Lemma dbd_app_inv : forall b m n, dbd_ne b (m $ᵈ n) -> dbd_ne b m /\ dbd_nf b n.
  Proof. dbd_inv. Qed.
  Lemma dbd_var_inv : forall b x, dbd_ne b (#ᵈ x) -> x < b.
  Proof. intros * H; specialize (H b (le_n _)); inversion H; assumption. Qed.

  Lemma dbd_mono : forall b b' d, b <= b' -> dbd b d -> dbd b' d.
  Proof. intros * Hb H v Hv; eapply dav_mono'; [| apply H ]; lia. Qed.

  Lemma dbd_fresh : forall b s a, s < b -> dbd s a -> dbd b (⇑! a s).
  Proof.
    intros * Hs Ha v Hv; constructor; [ eapply dav_mono'; [| apply Ha ]; lia | constructor; lia ].
  Qed.

  Lemma dbd_nat : forall b, dbd b ℕᵈ.
  Proof. intros b v Hv; constructor. Qed.
  Lemma dbd_bot : forall b, dbd b ⊥ᵈ.
  Proof. intros b v Hv; constructor. Qed.
  Lemma dbd_zero : forall b, dbd b zeroᵈ.
  Proof. intros b v Hv; constructor. Qed.
  Lemma dbd_level : forall b n, dbd b (Levelᵈ@n).
  Proof. intros b v Hv; constructor. Qed.

  Lemma dbd_succ : forall b m, dbd b m -> dbd b (succᵈ m).
  Proof. intros * H v Hv; constructor; apply H, Hv. Qed.

  Lemma dbd_nf_dom : forall b a m, dbd b a -> dbd b m -> dbd_nf b (⇓ a m).
  Proof. intros * Ha Hm v Hv; constructor; auto. Qed.

  Lemma dbd_app : forall b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dbd b m -> dbd b n -> dbd b r.
  Proof. intros * Hr Hm Hn v Hv; eapply app_av; eauto. Qed.

  (** A closure of a bounded value, evaluated at bounded arguments, at any
      larger bound. *)
  Definition dbd_clo (b : nat) (ρ : env) (B : exp) : Prop :=
    forall b' c d, b <= b' -> dbd b' c -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> dbd b' d.
  Definition dbd_clo2 (b : nat) (ρ : env) (B : exp) : Prop :=
    forall b' c1 c2 d, b <= b' -> dbd b' c1 -> dbd b' c2 -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> dbd b' d.

  Lemma dbd_pi_inv : forall b a ρ B, dbd b (Πᵈ a ρ B) -> dbd b a /\ dbd_clo b ρ B.
  Proof.
    intros * H; split; [ intros v Hv; specialize (H v Hv); inversion H; assumption |].
    intros b' c d Hb Hc Hd v Hv.
    specialize (H v ltac:(lia)); inversion_clear H.
    eapply eval_clo_av; [ eapply env_av_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.

  Lemma dbd_natrec_inv : forall b ρ A mz MS m,
      dbd_ne b (recᵈ m under ρ return A | zero -> mz | succ -> MS end) ->
      dbd b mz /\ dbd_ne b m /\ dbd_clo b ρ A /\ dbd_clo2 b ρ MS.
  Proof.
    intros * H; repeat split;
      try (intros v Hv; specialize (H v Hv); inversion H; assumption).
    - intros b' c d Hb Hc Hd v Hv.
      specialize (H v ltac:(lia)); inversion_clear H.
      eapply eval_clo_av; [ eapply env_av_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
    - intros b' c1 c2 d Hb Hc1 Hc2 Hd v Hv.
      specialize (H v ltac:(lia)); inversion_clear H.
      eapply eval_clo2_av;
        [ eapply env_av_mono; [| eassumption ]; lia | eassumption | apply Hc1; lia | apply Hc2; lia | exact Hd ].
  Qed.

  Lemma dbd_exfalso_inv : forall b ρ A m,
      dbd_ne b (efqᵈ m under ρ return A) -> dbd_ne b m /\ dbd_clo b ρ A.
  Proof.
    intros * H; split; [ intros v Hv; specialize (H v Hv); inversion H; assumption |].
    intros b' c d Hb Hc Hd v Hv.
    specialize (H v ltac:(lia)); inversion_clear H.
    eapply eval_clo_av; [ eapply env_av_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.
End Bound.

(** The bound of a value built during readback: by its constructor, by
    monotonicity, or by the evaluation it came from. *)
Ltac dbd_solve :=
  first [ eassumption
        | apply dbd_nf_dom; dbd_solve
        | apply dbd_succ; dbd_solve
        | apply dbd_fresh; [ lia | dbd_solve ]
        | apply dbd_nat | apply dbd_bot | apply dbd_zero | apply dbd_level
        | match goal with
          | Hc : dbd_clo _ _ ?b ?ρ ?B, e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↦ ?c ↘ ?d |- dbd ?b' ?d =>
              apply (Hc b' c d); [ lia | dbd_solve | exact e ]
          | Hc : dbd_clo2 _ _ ?b ?ρ ?B, e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↦ ?c1 ↦ ?c2 ↘ ?d |- dbd ?b' ?d =>
              apply (Hc b' c1 c2 d); [ lia | dbd_solve | dbd_solve | exact e ]
          | e : $| ?m & ?n | ?T ⍮ ?X ↘ ?r |- dbd ?b ?r => apply (dbd_app T X b m n r e); dbd_solve
          | H : dbd ?b0 ?d |- dbd ?b ?d => apply (dbd_mono b0 b d); [ lia | exact H ]
          end ].

(** ** Readback Is Equivariant

    [rn_ok f s s' φ]: reading back at [s] and at [s'], the renaming [f] of
    levels and the weakening [φ] of indices agree on the levels below [s];
    from [s] on, [f] is the shift by [s' - s], so the fresh levels of the two
    readbacks correspond. *)
Definition rn_ok (f : nat -> nat) (s s' : nat) (φ : wk) : Prop :=
  s <= s' /\
  (forall x, s <= x -> f x = x + (s' - s)) /\
  (forall x, x < s -> f x < s') /\
  (forall x, x < s -> φ (s - x - 1) = s' - f x - 1) /\
  wk_mono φ.

Lemma rn_ok_fresh : forall f s s' φ, rn_ok f s s' φ -> f s = s'.
Proof. intros * (? & Hf & _); rewrite Hf; lia. Qed.

Lemma rn_ok_q : forall f s s' φ, rn_ok f s s' φ -> rn_ok f (S s) (S s') (wk_q φ).
Proof.
  intros * (Hs & Hf & Hlt & Hφ & Hm); repeat split.
  - lia.
  - intros x Hx; rewrite (Hf x); lia.
  - intros x Hx; destruct (Nat.eq_dec x s) as [-> |]; [ rewrite (Hf s); lia | specialize (Hlt x ltac:(lia)); lia ].
  - intros x Hx; destruct (Nat.eq_dec x s) as [-> |].
    + rewrite (Hf s) by lia; replace (S s - s - 1) with 0 by lia; cbn [wk_q]; lia.
    + replace (S s - x - 1) with (S (s - x - 1)) by lia; cbn [wk_q].
      rewrite Hφ by lia; specialize (Hlt x ltac:(lia)); lia.
  - apply wk_mono_q, Hm.
Qed.

Section Read.
  Variables (Θ : gdeps) (Ξ : gstack) (f : nat -> nat).

  Lemma eval_clo_rn : forall B ρ c d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↦ drn f c ↘ drn f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma eval_clo2_rn : forall B ρ c1 c2 d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↦ drn f c1 ↦ drn f c2 ↘ drn f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma app_rn : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| drn f m & drn f n | Θ ⍮ Ξ ↘ drn f r.
  Proof. intros * H; exact (proj1 (proj2 (proj2 (eval_rn Θ Ξ f))) _ _ _ H). Qed.

  Lemma read_rn :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall s' φ, rn_ok f s s' φ -> dbd_nf s m -> Rnf drn_nf f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall s' φ, rn_ok f s s' φ -> dbd_ne s m -> Rne drn_ne f m in Θ ⍮ Ξ ⍮ s' ↘ ne_wk φ M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall s' φ, rn_ok f s s' φ -> dbd s a -> Rtyp drn f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall s' φ, rn_ok f s s' φ -> dbd_la s xs -> Rla larn f xs in Θ ⍮ Ξ ⍮ s' ↘ la_wk φ ys).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall s' φ, rn_ok f s s' φ -> dbd_nf s m -> Rnf drn_nf f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W)
             (fun s m M _ => forall s' φ, rn_ok f s s' φ -> dbd_ne s m -> Rne drn_ne f m in Θ ⍮ Ξ ⍮ s' ↘ ne_wk φ M)
             (fun s a A _ => forall s' φ, rn_ok f s s' φ -> dbd s a -> Rtyp drn f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A)
             (fun s xs ys _ => forall s' φ, rn_ok f s s' φ -> dbd_la s xs -> Rla larn f xs in Θ ⍮ Ξ ⍮ s' ↘ la_wk φ ys));
      intros; cbn [drn drn_ne drn_nf dmrn dern nf_wk ne_wk la_wk larn List.map] in *.
    (** The bounds of the parts. *)
    all: repeat match goal with
      | H : dbd_nf _ (d_dom _ _) |- _ => apply dbd_nf_inv in H as [? ?]
      | H : dbd _ (d_neut _ _) |- _ => apply dbd_neut_inv in H as [? ?]
      | H : dbd _ (d_suniv _) |- _ => apply dbd_suniv_inv in H
      | H : dbd _ (d_succ _) |- _ => apply dbd_succ_inv in H
      | H : dbd _ (d_lvl _ _) |- _ => apply dbd_lvl_inv in H
      | H : dbd _ (d_pi _ _ _) |- _ => apply (dbd_pi_inv Θ Ξ) in H as [? ?]
      | H : dbd_la _ ((_, _) :: _) |- _ => apply dbd_la_inv in H as [? ?]
      | H : dbd_ne _ (d_app _ _) |- _ => apply dbd_app_inv in H as [? ?]
      | H : dbd_ne _ (d_natrec _ _ _ _ _) |- _ => apply (dbd_natrec_inv Θ Ξ) in H as (? & ? & ? & ?)
      | H : dbd_ne _ (d_exfalso _ _ _) |- _ => apply (dbd_exfalso_inv Θ Ξ) in H as [? ?]
      end.
    (** The fresh levels correspond, under one binder and under two. *)
    all: match goal with Hok : rn_ok f ?s ?s' ?φ |- _ =>
           pose proof (rn_ok_fresh _ _ _ _ Hok) as Hf0;
           pose proof (rn_ok_fresh _ _ _ _ (rn_ok_q _ _ _ _ Hok)) as Hf1;
           pose proof (rn_ok_q _ _ _ _ Hok) as Hok1; pose proof (rn_ok_q _ _ _ _ Hok1) as Hok2
         end.
    (** The evaluations of the renamed closures. *)
    all: on_all_hyp: fun H => match type of H with
      | ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↦ _ ↦ _ ↘ _ =>
          let H' := fresh "Er" in pose proof (eval_clo2_rn _ _ _ _ _ H) as H'; cbn [drn drn_ne] in H'
      | ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↦ _ ↘ _ =>
          let H' := fresh "Er" in pose proof (eval_clo_rn _ _ _ _ H) as H'; cbn [drn drn_ne] in H'
      | $| _ & _ | _ ⍮ _ ↘ _ =>
          let H' := fresh "Er" in pose proof (app_rn _ _ _ H) as H'; cbn [drn drn_ne] in H'
      | _ => idtac
      end.
    all: rewrite ?Hf0, ?Hf1 in *.
    all: repeat change (List.map (dern f) ?ρ) with (ern f ρ).
    all: cbn [larn] in *.
    (** A level: the renaming commutes with its canonical form. *)
    all: try match goal with
         | Hok : rn_ok f _ _ ?φ |- read_nf _ _ _ _ (nf_wk _ (nf_lvl_of (lvl_canon _))) =>
             rewrite nf_lvl_of_wk, <- lvl_canon_wk by (destruct Hok as (_ & _ & _ & _ & ?); assumption);
             unfold lvl_wk; cbn [fst snd]
         end.
    (** A variable: the index of [x] at [s] is renamed to that of [f x] at [s']. *)
    all: try match goal with
         | Hok : rn_ok f ?s _ _, Hx : dbd_ne _ (d_var ?x) |- read_ne _ _ _ (d_var _) _ =>
             let Hφ := fresh "Hφ" in
             destruct Hok as (_ & _ & _ & Hφ & _); rewrite Hφ by (eapply dbd_var_inv; exact Hx)
         end.
    (** A small universe: the same through [nf_univ_of]. *)
    all: try match goal with |- read_typ _ _ _ (d_suniv _) _ => rewrite nf_univ_of_wk end.
    (** A neutral level: its sort is that of its type, which the renaming
        keeps. *)
    all: try match goal with |- context [dsort ?a] => rewrite <- (dsort_rn f a) end.
    all: econstructor.
    all: try rewrite <- nf_lvl_of_wk.
    all: try eassumption.
    all: match goal with
         | IH : _ |- _ => solve [ eapply IH; [ eassumption | dbd_solve ] ]
         end.
  Qed.

  Corollary read_nf_rn : forall s s' φ m W,
      rn_ok f s s' φ -> dbd_nf s m ->
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> Rnf drn_nf f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W.
  Proof. intros * ? ? H; eapply (proj1 read_rn); eassumption. Qed.

  Corollary read_typ_rn : forall s s' φ a A,
      rn_ok f s s' φ -> dbd s a ->
      Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> Rtyp drn f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A.
  Proof. intros * ? ? H; eapply (proj1 (proj2 (proj2 read_rn))); eassumption. Qed.
End Read.

(** ** Readback Shift

    The renaming that makes room for one more variable at level [s]: the
    levels below [s] stay, the others move up by one.  It fixes the initial
    environment of a context of length [s] and every value evaluated in it,
    and it corresponds to [↑] on indices.  So the value of a term of [Γ]
    reads back at [|Γ| + 1] as the weakening of what it reads back as at
    [|Γ|]. *)
Definition lvl_shift_above (s : nat) : nat -> nat := fun x => if x <? s then x else S x.

Lemma rn_ok_shift : forall s, rn_ok (lvl_shift_above s) s (S s) wk_shift.
Proof.
  intros s; unfold lvl_shift_above; repeat split.
  - lia.
  - intros x Hx; destruct (Nat.ltb_spec x s); lia.
  - intros x Hx; destruct (Nat.ltb_spec x s); lia.
  - intros x Hx; destruct (Nat.ltb_spec x s); cbn [wk_shift]; lia.
  - apply wk_mono_shift.
Qed.

(** A renaming that fixes the levels of a context fixes its initial
    environment. *)
Lemma initial_env_rn : forall Θ Ξ Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    forall f, (forall x, x < List.length Γ -> f x = x) -> ern f ρ = ρ.
Proof.
  induction 1; intros f Hf; cbn [List.length] in Hf; [ reflexivity | | |].
  all: assert (Hρ : ern f ρ = ρ) by (apply IHinitial_env; intros; apply Hf; lia).
  - pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H0) as Ha; rewrite Hρ in Ha.
    assert (drn f a = a) as Ea by (eapply functional_eval_exp; eassumption).
    cbn [extend_env ern List.map dern drn drn_ne]; fold (ern f ρ).
    rewrite Hρ, Ea, Hf by lia; reflexivity.
  - pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H0) as Hm; rewrite Hρ in Hm.
    assert (drn f m = m) as Em by (eapply functional_eval_exp; eassumption).
    cbn [extend_env ern List.map dern]; fold (ern f ρ).
    rewrite Hρ, Em; reflexivity.
  - cbn [extend_env_mod ern List.map dern dmrn]; fold (ern f ρ); rewrite Hρ; reflexivity.
Qed.

Corollary eval_initial_rn : forall Θ Ξ Γ ρ M m,
    initial_env Θ Ξ Γ ρ -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    forall f, (forall x, x < List.length Γ -> f x = x) -> drn f m = m.
Proof.
  intros * Hρ Hm f Hf.
  pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ Hm) as Hm'.
  rewrite (initial_env_rn _ _ _ _ Hρ f Hf) in Hm'.
  eapply functional_eval_exp; eassumption.
Qed.

(** A value of the initial environment mentions only the levels of the
    context. *)
Lemma eval_initial_dbd : forall Θ Ξ Γ ρ M m,
    initial_env Θ Ξ Γ ρ -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> dbd (List.length Γ) m.
Proof.
  intros * Hρ Hm v Hv.
  apply (proj1 (eval_av Θ Ξ v (List.length Γ)) _ _ _ Hm None); [| exact I ].
  eapply initial_env_av; [ exact Hρ | exact Hv | reflexivity ].
Qed.

Lemma lvl_shift_above_lt : forall s x, x < s -> lvl_shift_above s x = x.
Proof. intros; unfold lvl_shift_above; destruct (Nat.ltb_spec x s); lia. Qed.

(** Readback shift: a value of [Γ] reads back one variable further out as
    the weakening of its normal form. *)
Theorem read_shift : forall Θ Ξ Γ ρ A M a m W,
    initial_env Θ Ξ Γ ρ ->
    ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    Rnf ⇓ a m in Θ ⍮ Ξ ⍮ List.length Γ ↘ W ->
    Rnf ⇓ a m in Θ ⍮ Ξ ⍮ S (List.length Γ) ↘ nf_wk ↑ W.
Proof.
  intros * Hρ Ha Hm HW.
  pose proof (read_nf_rn Θ Ξ (lvl_shift_above (List.length Γ)) _ _ _ _ _ (rn_ok_shift _)
                (dbd_nf_dom _ _ _ (eval_initial_dbd _ _ _ _ _ _ Hρ Ha) (eval_initial_dbd _ _ _ _ _ _ Hρ Hm)) HW)
    as HW'.
  cbn [drn_nf] in HW'.
  rewrite (eval_initial_rn _ _ _ _ _ _ Hρ Ha _ (lvl_shift_above_lt _)),
    (eval_initial_rn _ _ _ _ _ _ Hρ Hm _ (lvl_shift_above_lt _)) in HW'.
  exact HW'.
Qed.

Theorem read_typ_shift : forall Θ Ξ Γ ρ A a W,
    initial_env Θ Ξ Γ ρ ->
    ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    Rtyp a in Θ ⍮ Ξ ⍮ List.length Γ ↘ W ->
    Rtyp a in Θ ⍮ Ξ ⍮ S (List.length Γ) ↘ nf_wk ↑ W.
Proof.
  intros * Hρ Ha HW.
  pose proof (read_typ_rn Θ Ξ (lvl_shift_above (List.length Γ)) _ _ _ _ _ (rn_ok_shift _)
                (eval_initial_dbd _ _ _ _ _ _ Hρ Ha) HW) as HW'.
  rewrite (eval_initial_rn _ _ _ _ _ _ Hρ Ha _ (lvl_shift_above_lt _)) in HW'.
  exact HW'.
Qed.
