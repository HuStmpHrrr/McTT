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
From Mctt.Core.Syntactic Require Import Fresh Members NfRename Inductives.
Import Domain_Notations Syntax_Notations Wk_Notations.

(** ** The Renaming *)

Section Rename.
  Variable f : nat -> nat.

  Fixpoint drn (d : domain) : domain :=
    match d with
    | d_pi a ρ B => d_pi (drn a) (List.map dern ρ) B
    | d_univ i => d_univ i
    | d_suniv l => d_suniv (drn l)
    | d_level n => d_level n
    | d_lvl c xs => d_lvl c (List.map (fun ka => match ka with (k, n, m) => (k, n, drn_ne m) end) xs)
    | d_True => d_True
    | d_true => d_true
    | d_False => d_False
    | d_fn ρ M => d_fn (List.map dern ρ) M
    | d_neut a m => d_neut (drn a) (drn_ne m)
    | d_member h ch => d_member (dmrn h) ch
    | d_ind p args => d_ind p (List.map drn args)
    | d_con p c args => d_con p c (List.map drn args)
    | d_ihfn ρ nm A Bs t g => d_ihfn (List.map dern ρ) nm A Bs t (drn g)
    | d_shfam p ups ρ t => d_shfam p (List.map drn ups) (List.map dern ρ) t
    | d_ihfam ρm A ρ t g => d_ihfam (List.map dern ρm) A (List.map dern ρ) t (drn g)
    end
  with drn_ne (m : domain_ne) : domain_ne :=
    match m with
    | d_var x => d_var (f x)
    | d_app m n => d_app (drn_ne m) (drn_nf n)
    | d_exfalso ρ A m => d_exfalso (List.map dern ρ) A (drn_ne m)
    | d_elim ρ nm A Bs p args m => d_elim (List.map dern ρ) nm A Bs p (List.map drn args) (drn_ne m)
    | d_glob p => d_glob p
    end
  with drn_nf (n : domain_nf) : domain_nf :=
    match n with
    | d_dom a m => d_dom (drn a) (drn m)
    end
  with dmrn (h : dmod) : dmod :=
    match h with
    | dm_global p args => dm_global p (List.map drn args)
    | dm_local Δ D ρ => dm_local Δ D (List.map dern ρ)
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
    change (de_term d_true) with (dern (de_term d_true)) at 1.
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
    List.map_app List.length_map List.firstn_map List.skipn_map : rn.

  Lemma kpad_rn : forall n ρ, ern f (kpad n ρ) = kpad n (ern f ρ).
  Proof. intros; unfold kpad, ern; rewrite List.map_app; f_equal; induction n; cbn; f_equal; assumption. Qed.

  Lemma kbentry_rn : forall ρ E, dern f (kbentry ρ E) = kbentry (ern f ρ) E.
  Proof. intros ρ [? ? ? ? | ? [] | ? ? ? ? | ? ? ? ?]; reflexivity. Qed.

  Lemma kgens_env_rn : forall gs ρ k, ern f (kgens_env ρ k gs) = kgens_env (ern f ρ) k gs.
  Proof.
    induction gs as [| g gs IH]; intros; cbn [kgens_env]; [ reflexivity |].
    rewrite IH; f_equal; destruct g; reflexivity.
  Qed.

  (** Kinds read no level. *)
  Lemma kind_rn :
    (forall h ch k, dkind Θ Ξ h ch k -> dkind Θ Ξ (dmrn f h) ch k) /\
    (forall ρ U ch k, ukind Θ Ξ ρ U ch k -> ukind Θ Ξ (ern f ρ) U ch k) /\
    (forall ρ H ch k, skind Θ Ξ ρ H ch k -> skind Θ Ξ (ern f ρ) H ch k) /\
    (forall ρ Φ ρ', kenv Θ Ξ ρ Φ ρ' -> kenv Θ Ξ (ern f ρ) Φ (ern f ρ')) /\
    (forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> kbody Θ Ξ (ern f ρ) Φ Φx) /\
    (forall ρ H its gs, kgens Θ Ξ ρ H its gs -> kgens Θ Ξ (ern f ρ) H its gs).
  Proof.
    apply kind_mut_ind; intros; cbn [dmrn ern List.map dern drn] in *;
      repeat change (List.map (dern f) ?ρ) with (ern f ρ) in *;
      rewrite ?kpad_rn in *; try rewrite <- kpad_rn in *;
      try solve [ econstructor; eauto ].
    all: try solve [ rewrite kgens_env_rn; econstructor; eauto ].
    all: try solve [ rewrite kbentry_rn; econstructor; eauto ].
    all: try solve [ econstructor; [ eassumption | rewrite <- kpad_rn; eassumption | eassumption ] ].
    all: try solve [ econstructor; rewrite <- kpad_rn; eassumption ].
    all: try solve [ econstructor; rewrite env_mod_rn; eassumption ].
    all: try solve [ eapply uk_item_mod; [ eassumption | rewrite <- kpad_rn; eassumption | eassumption | eassumption ] ].
  Qed.

  Lemma eval_rn :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| drn f m & drn f n | Θ ⍮ Ξ ↘ drn f r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ern f ρ ↘ List.map (drn f) ms) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> $*| drn f m & List.map (drn f) args | Θ ⍮ Ξ ↘ drn f r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ern f ρ ↘ dmrn f h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ern f ρ ↘ dmrn f h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> $ᵐ| dmrn f h & drn f n | Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> $ᵐ*| dmrn f h & List.map (drn f) ns | Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmrn f h ·ₜ x Θ ⍮ Ξ ↘ drn f r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmrn f h ·ₘ y Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmrn f h ·ₜ* ch Θ ⍮ Ξ ↘ drn f r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmrn f h ·ₘ* ch Θ ⍮ Ξ ↘ dmrn f r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ern f ρ ↘ ern f ρ') /\
    (forall ρ nm A Bs m r, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       ⟦elim drn f m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f r) /\
    (forall ρ nm A Bs gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       ⟦ihs List.map (drn f) vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ List.map (drn f) ihs) /\
    (forall ρ nm A Bs t m r, eval_ih Θ Ξ ρ nm A Bs t m r -> eval_ih Θ Ξ (ern f ρ) nm A Bs t (drn f m) (drn f r)) /\
    (forall p ups ρ t a, eval_shty Θ Ξ p ups ρ t a -> eval_shty Θ Ξ p (List.map (drn f) ups) (ern f ρ) t (drn f a)) /\
    (forall ρm A ρ t m a, eval_ihty Θ Ξ ρm A ρ t m a -> eval_ihty Θ Ξ (ern f ρm) A (ern f ρ) t (drn f m) (drn f a)).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => ⟦ M ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f m)
             (fun m n r _ => $| drn f m & drn f n | Θ ⍮ Ξ ↘ drn f r)
             (fun Ms ρ ms _ => ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ern f ρ ↘ List.map (drn f) ms)
             (fun m args r _ => $*| drn f m & List.map (drn f) args | Θ ⍮ Ξ ↘ drn f r)
             (fun H ρ h _ => ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ern f ρ ↘ dmrn f h)
             (fun Δ D ρ h _ => ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ern f ρ ↘ dmrn f h)
             (fun h n r _ => $ᵐ| dmrn f h & drn f n | Θ ⍮ Ξ ↘ dmrn f r)
             (fun h ns r _ => $ᵐ*| dmrn f h & List.map (drn f) ns | Θ ⍮ Ξ ↘ dmrn f r)
             (fun h x r _ => dmrn f h ·ₜ x Θ ⍮ Ξ ↘ drn f r)
             (fun h y r _ => dmrn f h ·ₘ y Θ ⍮ Ξ ↘ dmrn f r)
             (fun h ch r _ => dmrn f h ·ₜ* ch Θ ⍮ Ξ ↘ drn f r)
             (fun h ch r _ => dmrn f h ·ₘ* ch Θ ⍮ Ξ ↘ dmrn f r)
             (fun ρ Φ ρ' _ => ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ern f ρ ↘ ern f ρ')
             (fun ρ nm A Bs m r _ => ⟦elim drn f m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ drn f r)
             (fun ρ nm A Bs gs vs ihs _ =>
                ⟦ihs List.map (drn f) vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↘ List.map (drn f) ihs)
             (fun ρ nm A Bs t m r _ => eval_ih Θ Ξ (ern f ρ) nm A Bs t (drn f m) (drn f r))
             (fun p ups ρ t a _ => eval_shty Θ Ξ p (List.map (drn f) ups) (ern f ρ) t (drn f a))
             (fun ρm A ρ t m a _ => eval_ihty Θ Ξ (ern f ρm) A (ern f ρ) t (drn f m) (drn f a)));
      intros; cbn [drn drn_ne drn_nf dmrn dern List.map extend_env] in *;
      repeat change (List.map (dern f) ?ρ) with (ern f ρ) in *;
      autorewrite with rn in *; cbn [List.map] in *;
      try solve [ econstructor; autorewrite with rn; eauto ].
    all: try solve [ econstructor; [ apply kind_rn; eassumption | eassumption | eauto | eauto ] ].
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

  Lemma dbd_bot : forall b, dbd b ⊥ᵈ.
  Proof. intros b v Hv; constructor. Qed.
  Lemma dbd_level : forall b n, dbd b (Levelᵈ@n).
  Proof. intros b v Hv; constructor. Qed.

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

  Lemma dbd_exfalso_inv : forall b ρ A m,
      dbd_ne b (efqᵈ m under ρ return A) -> dbd_ne b m /\ dbd_clo b ρ A.
  Proof.
    intros * H; split; [ intros v Hv; specialize (H v Hv); inversion H; assumption |].
    intros b' c d Hb Hc Hd v Hv.
    specialize (H v ltac:(lia)); inversion_clear H.
    eapply eval_clo_av; [ eapply env_av_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.

  (** ** Inductive Types

      An environment of bounded values, and a closure under [n] binders. *)
  Definition env_dbd (b : nat) (ρ : env) : Prop := forall v, b <= v -> env_av v b None ρ.

  Definition dbd_clon (b : nat) (ρ : env) (B : exp) (n : nat) : Prop :=
    forall b' cs d, b <= b' -> List.length cs = n -> (forall c, In c cs -> dbd b' c) ->
               ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ cs ↘ d -> dbd b' d.

  (** A closure under [n] binders whose environment avoids the excluded
      level at every position its body reads, as the invariant states it. *)
  Definition dbd_eclo (b : nat) (ρ : env) (B : exp) (n : nat) : Prop :=
    forall v, b <= v -> exists K, env_av v b K ρ /\ ofresh (oshift n K) B.

  Lemma dbd_eclo_clon : forall b ρ B n, dbd_eclo b ρ B n -> dbd_clon b ρ B n.
  Proof.
    intros * H b' cs d Hb Hl Hc Hd v Hv; destruct (H v ltac:(lia)) as (K & HK & HB).
    eapply (proj1 (eval_av Θ Ξ v b'));
      [ exact Hd | apply env_av_args; [ eapply env_av_mono; [| exact HK ]; lia | intros; apply Hc; [ assumption | lia ] ] |].
    rewrite Hl; exact HB.
  Qed.

  Lemma env_dbd_nil : forall b, env_dbd b nil.
  Proof. intros b v _; apply env_av_nil. Qed.

  Lemma env_dbd_args : forall b ρ args, env_dbd b ρ -> (forall a, In a args -> dbd b a) -> env_dbd b (env_args ρ args).
  Proof. intros * Hρ Ha v Hv; apply env_av_args_none; [ apply Hρ, Hv | intros; apply Ha; assumption ]. Qed.

  Lemma env_dbd_cons : forall b ρ d, env_dbd b ρ -> dbd b d -> env_dbd b (ρ ↦ d).
  Proof. intros * Hρ Hd v Hv; apply env_av_cons_none; [ apply Hρ, Hv | apply Hd, Hv ]. Qed.

  Lemma env_dbd_mono : forall b b' ρ, b <= b' -> env_dbd b ρ -> env_dbd b' ρ.
  Proof. intros * Hb Hρ v Hv; eapply env_av_mono; [| apply Hρ ]; lia. Qed.

  Lemma eval_dbd : forall M ρ a b, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> env_dbd b ρ -> dbd b a.
  Proof. intros * H Hρ v Hv; eapply (proj1 (eval_av Θ Ξ v b)); [ exact H | apply Hρ, Hv | exact I ]. Qed.

  Lemma dbd_indty : forall b p args, (forall a, In a args -> dbd b a) -> dbd b (d_ind p args).
  Proof. intros * Ha v Hv; constructor; intros; apply Ha; assumption. Qed.

  Lemma dbd_con : forall b p c args, (forall a, In a args -> dbd b a) -> dbd b (d_con p c args).
  Proof. intros * Ha v Hv; constructor; intros; apply Ha; assumption. Qed.

  Lemma dbd_indty_inv : forall b p args, dbd b (d_ind p args) -> forall a, In a args -> dbd b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  Lemma dbd_con_inv : forall b p c args, dbd b (d_con p c args) -> forall a, In a args -> dbd b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  Lemma dbd_elim_inv : forall b ρ nm A Bs p args m,
      dbd_ne b (d_elim ρ nm A Bs p args m) ->
      dbd_ne b m /\ (forall a, In a args -> dbd b a) /\ dbd_eclo b ρ A nm /\
      (forall c n B, In (c, n, B) Bs -> dbd_clon b ρ B n).
  Proof.
    intros * H; repeat split.
    - intros v Hv; specialize (H v Hv); inversion H; assumption.
    - intros a Ha v Hv; specialize (H v Hv); inversion H; auto.
    - intros v Hv; specialize (H v Hv); inversion_clear H; eexists; split; eassumption.
    - intros c n B Hin b' cs d Hb Hl Hc Hd v Hv; specialize (H v ltac:(lia)); inversion_clear H.
      eapply (proj1 (eval_av Θ Ξ v b')); [ exact Hd | apply env_av_args; [ eapply env_av_mono; [| eassumption ]; lia | intros; apply Hc; [ assumption | lia ] ] |].
      rewrite Hl; eauto.
  Qed.

  (** The fresh variables of the telescopes of a declaration are above the
      readback length, and below the length past them. *)
  Lemma fresh_tele_dbd : forall ρ T s ns, fresh_tele Θ Ξ ρ T s ns -> env_dbd s ρ ->
      forall a, In a ns -> dbd (s + List.length T) a.
  Proof.
    induction 1; intros Hρ; [ intros ? [] |].
    assert (Ha : dbd s a) by (eapply eval_dbd; eassumption).
    cbn [List.length]; replace (s + S (List.length T)) with (S s + List.length T) by lia.
    intros d [<- | Hd].
    - apply dbd_fresh; [ lia | exact Ha ].
    - apply IHfresh_tele; [| exact Hd ]. apply env_dbd_cons; [ eapply env_dbd_mono; [| exact Hρ ]; lia | apply dbd_fresh; [ lia | exact Ha ] ].
  Qed.

  Lemma shty_dbd : forall p ups ρ t a b, eval_shty Θ Ξ p ups ρ t a ->
      env_dbd b ρ -> (forall u, In u ups -> dbd b u) -> dbd b a.
  Proof.
    intros * H Hρ Hu v Hv; eapply shty_av; [ exact H | apply Hρ, Hv | apply ptfresh_none | intros; apply Hu; assumption ].
  Qed.

  Lemma fresh_cargs_dbd : forall p ups ρ gs s vs, fresh_cargs Θ Ξ p ups ρ gs s vs ->
      env_dbd s ρ -> (forall a, In a ups -> dbd s a) ->
      forall a, In a vs -> dbd (s + List.length gs) a.
  Proof.
    induction 1; intros Hρ Hu.
    - intros ? [].
    - assert (Ha : dbd s a) by (eapply eval_dbd; eassumption).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      intros d [<- | Hd]; [ apply dbd_fresh; [ lia | exact Ha ] |].
      apply IHfresh_cargs;
        [ apply env_dbd_cons; [ eapply env_dbd_mono; [| exact Hρ ]; lia | apply dbd_fresh; [ lia | exact Ha ] ]
        | intros; eapply dbd_mono; [| apply Hu; eassumption ]; lia | exact Hd ].
    - assert (Ha : dbd s a) by (eapply shty_dbd; eassumption).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      intros d [<- | Hd]; [ apply dbd_fresh; [ lia | exact Ha ] |].
      apply IHfresh_cargs;
        [ eapply env_dbd_mono; [| exact Hρ ]; lia | intros; eapply dbd_mono; [| apply Hu; eassumption ]; lia | exact Hd ].
  Qed.

  Lemma fresh_ihs_dbd : forall ρ A ρa gs vs s ihs, fresh_ihs Θ Ξ ρ A ρa gs vs s ihs ->
      forall nn b, b <= s -> dbd_eclo b ρ A (S nn) -> env_dbd s ρa ->
      Forall (fun g => match g with ca_rec t => List.length (ptyp_ps t) = nn | ca_arg _ => True end) gs ->
      (forall a, In a vs -> dbd s a) ->
      forall a, In a ihs -> dbd (s + cargs_nrec gs) a.
  Proof.
    induction 1; intros nn b0 Hb HA Hρa Hl Hvs.
    - intros ? [].
    - inversion_clear Hl as [| ? ? _ Hl2].
      apply (IHfresh_ihs nn b0); auto.
      + apply env_dbd_cons; [ exact Hρa | apply Hvs; left; reflexivity ].
      + intros; apply Hvs; right; assumption.
    - inversion_clear Hl as [| ? ? Hl1 Hl2]; cbn beta iota in Hl1.
      assert (Ha : dbd s a).
      { intros w Hw; destruct (HA w ltac:(lia)) as (K & HK & HfA).
        eapply ihty_av; [ exact H | eapply env_av_mono; [| exact HK ]; lia | rewrite Hl1; exact HfA
                        | apply Hρa, Hw | apply ptfresh_none | apply Hvs; [ left; reflexivity | exact Hw ] ]. }
      cbn [cargs_nrec]; replace (s + S (cargs_nrec gs)) with (S s + cargs_nrec gs) by lia.
      intros d [<- | Hd].
      + apply dbd_fresh; [ lia | exact Ha ].
      + eapply (IHfresh_ihs nn b0); try eassumption; try lia.
        * eapply env_dbd_mono; [| exact Hρa ]; lia.
        * intros; eapply dbd_mono; [| apply Hvs; right; eassumption ]; lia.
  Qed.
End Bound.

(** The bound of a value built during readback: by its constructor, by
    monotonicity, or by the evaluation it came from. *)
Ltac dbd_solve :=
  first [ eassumption
        | apply dbd_nf_dom; dbd_solve
        | apply dbd_fresh; [ lia | dbd_solve ]
        | apply dbd_bot | apply dbd_level
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

Lemma rn_ok_qn : forall n f s s' φ, rn_ok f s s' φ -> rn_ok f (n + s) (n + s') (wk_qn n φ).
Proof. induction n; intros * H; cbn; [ exact H | apply rn_ok_q; auto ]. Qed.

Lemma nfs_wk_app : forall φ Ms Ns, nfs_wk φ (nfs_app Ms Ns) = nfs_app (nfs_wk φ Ms) (nfs_wk φ Ns).
Proof. induction Ms; intros; cbn; congruence. Qed.

Section Read.
  Variables (Θ : gdeps) (Ξ : gstack) (f : nat -> nat).

  Lemma eval_clo_rn : forall B ρ c d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↦ drn f c ↘ drn f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma eval_clo2_rn : forall B ρ c1 c2 d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ern f ρ ↦ drn f c1 ↦ drn f c2 ↘ drn f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma app_rn : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| drn f m & drn f n | Θ ⍮ Ξ ↘ drn f r.
  Proof. intros * H; exact (proj1 (proj2 (eval_rn Θ Ξ f)) _ _ _ H). Qed.

  Lemma eval_args_rn : forall B ρ args d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ args ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args (ern f ρ) (List.map (drn f) args) ↘ drn f d.
  Proof. intros * H; rewrite <- env_args_rn; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  (** The fresh variables of the telescopes of a declaration, renamed: from
      the readback length on, [f] is the shift to the other length. *)
  Lemma fresh_tele_rn : forall ρ T s ns, fresh_tele Θ Ξ ρ T s ns ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      fresh_tele Θ Ξ (ern f ρ) T s' (List.map (drn f) ns).
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor |].
    cbn [drn drn_ne]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
    constructor; [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ H) |].
    pose proof (IHfresh_tele (S s') ltac:(intros; rewrite Hf by lia; lia) ltac:(lia)) as IH.
    cbn [ern List.map dern drn drn_ne extend_env] in IH; rewrite (Hf s) in IH by lia.
    replace (s + (s' - s)) with s' in IH by lia; exact IH.
  Qed.

  Lemma shty_rn : forall p ups ρ t a,
      eval_shty Θ Ξ p ups ρ t a -> eval_shty Θ Ξ p (List.map (drn f) ups) (ern f ρ) t (drn f a).
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
    exact (Hs _ _ _ _ _ H).
  Qed.

  Lemma ihty_rn : forall ρm A ρ t m a,
      eval_ihty Θ Ξ ρm A ρ t m a -> eval_ihty Θ Ξ (ern f ρm) A (ern f ρ) t (drn f m) (drn f a).
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy).
    exact (Hy _ _ _ _ _ _ H).
  Qed.

  Lemma fresh_cargs_rn : forall p ups ρ gs s vs, fresh_cargs Θ Ξ p ups ρ gs s vs ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      fresh_cargs Θ Ξ p (List.map (drn f) ups) (ern f ρ) gs s' (List.map (drn f) vs).
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor | |].
    - cbn [drn drn_ne]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ H) |].
      pose proof (IHfresh_cargs (S s') ltac:(intros; rewrite Hf by lia; lia) ltac:(lia)) as IH.
      cbn [ern List.map dern drn drn_ne extend_env] in IH; rewrite (Hf s) in IH by lia.
      replace (s + (s' - s)) with s' in IH by lia; exact IH.
    - cbn [drn drn_ne]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; [ exact (shty_rn _ _ _ _ _ H) |].
      apply (IHfresh_cargs (S s')); [ intros; rewrite Hf by lia; lia | lia ].
  Qed.

  Lemma fresh_ihs_rn : forall ρ A ρa gs vs s ihs, fresh_ihs Θ Ξ ρ A ρa gs vs s ihs ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      fresh_ihs Θ Ξ (ern f ρ) A (ern f ρa) gs (List.map (drn f) vs) s' (List.map (drn f) ihs).
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor | |].
    - constructor; pose proof (IHfresh_ihs s' Hf Hs) as IH.
      cbn [ern List.map dern extend_env] in IH |- *; exact IH.
    - cbn [drn drn_ne]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; [ exact (ihty_rn _ _ _ _ _ _ H) |].
      apply (IHfresh_ihs (S s')); [ intros; rewrite Hf by lia; lia | lia ].
  Qed.

  Lemma read_rn :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall s' φ, rn_ok f s s' φ -> dbd_nf s m -> Rnf drn_nf f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall s' φ, rn_ok f s s' φ -> dbd_ne s m -> Rne drn_ne f m in Θ ⍮ Ξ ⍮ s' ↘ ne_wk φ M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall s' φ, rn_ok f s s' φ -> dbd s a -> Rtyp drn f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall s' φ, rn_ok f s s' φ -> dbd_la s xs -> Rla larn f xs in Θ ⍮ Ξ ⍮ s' ↘ la_wk φ ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall s' φ, rn_ok f s s' φ -> env_dbd s ρ -> (forall a, In a vs -> dbd s a) ->
       Rps List.map (drn f) vs at T in Θ ⍮ Ξ ⍮ ern f ρ ⍮ s' ↘ nfs_wk φ Ms) /\
    (forall s p ups ρ gs vs Ms, read_cargs Θ Ξ s p ups ρ gs vs Ms ->
       forall s' φ, rn_ok f s s' φ -> (forall a, In a ups -> dbd s a) -> env_dbd s ρ ->
       (forall a, In a vs -> dbd s a) ->
       read_cargs Θ Ξ s' p (List.map (drn f) ups) (ern f ρ) gs (List.map (drn f) vs) (nfs_wk φ Ms)) /\
    (forall s ρ A p D ups cs Bs Bs', read_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
       forall s' φ, rn_ok f s s' φ -> dbd_eclo s ρ A (S (ind_nn D)) ->
       (forall c n B, In (c, n, B) Bs -> dbd_clon Θ Ξ s ρ B n) -> (forall a, In a ups -> dbd s a) ->
       read_brs Θ Ξ s' (ern f ρ) A p D (List.map (drn f) ups) cs Bs (nbrs_wk φ Bs')).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall s' φ, rn_ok f s s' φ -> dbd_nf s m -> Rnf drn_nf f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W)
             (fun s m M _ => forall s' φ, rn_ok f s s' φ -> dbd_ne s m -> Rne drn_ne f m in Θ ⍮ Ξ ⍮ s' ↘ ne_wk φ M)
             (fun s a A _ => forall s' φ, rn_ok f s s' φ -> dbd s a -> Rtyp drn f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A)
             (fun s xs ys _ => forall s' φ, rn_ok f s s' φ -> dbd_la s xs -> Rla larn f xs in Θ ⍮ Ξ ⍮ s' ↘ la_wk φ ys)
             (fun s ρ T vs Ms _ => forall s' φ, rn_ok f s s' φ -> env_dbd s ρ -> (forall a, In a vs -> dbd s a) ->
                Rps List.map (drn f) vs at T in Θ ⍮ Ξ ⍮ ern f ρ ⍮ s' ↘ nfs_wk φ Ms)
             (fun s p ups ρ gs vs Ms _ => forall s' φ, rn_ok f s s' φ -> (forall a, In a ups -> dbd s a) ->
                env_dbd s ρ -> (forall a, In a vs -> dbd s a) ->
                read_cargs Θ Ξ s' p (List.map (drn f) ups) (ern f ρ) gs (List.map (drn f) vs) (nfs_wk φ Ms))
             (fun s ρ A p D ups cs Bs Bs' _ => forall s' φ, rn_ok f s s' φ -> dbd_eclo s ρ A (S (ind_nn D)) ->
                (forall c n B, In (c, n, B) Bs -> dbd_clon Θ Ξ s ρ B n) -> (forall a, In a ups -> dbd s a) ->
                read_brs Θ Ξ s' (ern f ρ) A p D (List.map (drn f) ups) cs Bs (nbrs_wk φ Bs')));
      intros; cbn [drn drn_ne drn_nf dmrn dern nf_wk ne_wk la_wk larn nfs_wk nbrs_wk List.map] in *.
    (** The bounds of the parts. *)
    all: repeat match goal with
      | H : dbd_nf _ (d_dom _ _) |- _ => apply dbd_nf_inv in H as [? ?]
      | H : dbd _ (d_neut _ _) |- _ => apply dbd_neut_inv in H as [? ?]
      | H : dbd _ (d_suniv _) |- _ => apply dbd_suniv_inv in H
      | H : dbd _ (d_lvl _ _) |- _ => apply dbd_lvl_inv in H
      | H : dbd _ (d_pi _ _ _) |- _ => apply (dbd_pi_inv Θ Ξ) in H as [? ?]
      | H : dbd_la _ ((_, _) :: _) |- _ => apply dbd_la_inv in H as [? ?]
      | H : dbd_ne _ (d_app _ _) |- _ => apply dbd_app_inv in H as [? ?]
      | H : dbd_ne _ (d_exfalso _ _ _) |- _ => apply (dbd_exfalso_inv Θ Ξ) in H as [? ?]
      | H : dbd _ (d_ind _ _) |- _ => pose proof (dbd_indty_inv _ _ _ H); clear H
      | H : dbd _ (d_con _ _ _) |- _ => pose proof (dbd_con_inv _ _ _ _ H); clear H
      | H : dbd_ne _ (d_elim _ _ _ _ _ _ _) |- _ => apply (dbd_elim_inv Θ Ξ) in H as (? & ? & ? & ?)
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
    (** Inductive types.  A constructor at its type: the parameters and the
        arguments, renamed, at their renamed types. *)
    all: try solve [ lazymatch goal with |- read_nf _ _ _ _ (nf_con _ _ _) =>
      rewrite nfs_wk_app;
      econstructor; try eassumption;
      [ rewrite List.length_map; assumption
      | rewrite List.length_map; assumption
      | exact (H s' φ H1 (env_dbd_nil _) H4)
      | rewrite List.firstn_map, List.skipn_map;
        change (env_args nil (List.map (drn f) as')) with (env_args (ern f nil) (List.map (drn f) as'));
        rewrite <- env_args_rn;
        apply H0; [ exact H1 | all_in_with assumption | apply env_dbd_args; [ apply env_dbd_nil | exact H4 ]
                  | all_in_with assumption ] ] end ].
    (** A stuck eliminator: its fresh variables, renamed, are the fresh
        variables at the other length; the motive is read one binder
        further than its non-uniform parameters. *)
    all: try solve [ lazymatch goal with |- read_ne _ _ _ (d_elim _ _ _ _ _ _ _) _ =>
      pose proof H2 as (Hss & Hfx & _);
      pose proof (fresh_tele_length _ _ _ _ f0) as Hlen; rewrite ind_nn_tele_length in Hlen;
      assert (Hns : forall x, In x ns -> dbd (s + ind_nn D) x)
        by (rewrite <- (ind_nn_tele_length D); eapply (fresh_tele_dbd Θ Ξ);
            [ exact f0 | apply env_dbd_args; [ apply env_dbd_nil | all_in_with assumption ] ]);
      assert (Hfn : f (s + ind_nn D) = s' + ind_nn D) by (rewrite Hfx; lia);
      pose proof (fresh_tele_rn _ _ _ _ f0 s' Hfx Hss) as Hns';
      rewrite env_args_rn, <- List.firstn_map in Hns'; cbn [ern List.map] in Hns';
      pose proof (eval_args_rn _ _ _ _ e2) as Ha';
      rewrite List.map_app in Ha'; cbn [List.map drn drn_ne] in Ha'; rewrite Hfn, List.map_app, <- List.firstn_map in Ha';
      assert (HaD : dbd (S (s + ind_nn D)) a)
        by (eapply (dbd_eclo_clon Θ Ξ _ _ _ _ H5); [ lia | | | exact e2 ]; [ rewrite length_app, Hlen; cbn; lia |];
            apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia |];
            apply all_in_cons; [| apply all_in_nil ];
            apply dbd_fresh; [ lia |]; apply dbd_indty; apply all_in_app;
              [ apply all_in_firstn; intros; eapply dbd_mono; [| apply H4; eassumption ]; lia | exact Hns ]);
      subst nm;
      econstructor; try eassumption; try reflexivity;
      [ rewrite List.length_map; assumption
      | replace (S (s' + ind_nn D)) with (S (ind_nn D) + s') by lia;
        apply H; [ replace (S (s + ind_nn D)) with (S (ind_nn D) + s) by lia; apply rn_ok_qn, H2 | exact HaD ]
      | rewrite List.firstn_map; apply H0; [ exact H2 | exact H5 | exact H6 | all_in_with assumption ]
      | apply H1; assumption ] end ].
    (** An inductive type at its parameters. *)
    all: try solve [ lazymatch goal with |- read_typ _ _ _ (d_ind _ _) _ =>
      econstructor; try eassumption; [ rewrite List.length_map; assumption | exact (H s' φ H0 (env_dbd_nil _) H2) ] end ].
    (** A parameter or an argument at its type, and the rest in the
        environment extended by it. *)
    all: try solve [ lazymatch goal with |- read_ps _ _ _ _ (_ :: _) _ _ =>
      econstructor;
      [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ e)
      | apply H; [ exact H1 | apply dbd_nf_dom; [ eapply eval_dbd; eassumption | apply (all_in_head _ _ _ H3) ] ]
      | apply H0; [ exact H1 | apply env_dbd_cons; [ assumption | apply (all_in_head _ _ _ H3) ] | exact (all_in_tail _ _ _ H3) ] ] end ].
    all: try solve [ lazymatch goal with |- read_cargs _ _ _ _ _ _ (ca_arg _ :: _) _ _ =>
      econstructor;
      [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ e)
      | apply H; [ exact H1 | apply dbd_nf_dom; [ eapply eval_dbd; eassumption | apply (all_in_head _ _ _ H4) ] ]
      | apply H0; [ exact H1 | exact H2 | apply env_dbd_cons; [ assumption | apply (all_in_head _ _ _ H4) ]
                  | exact (all_in_tail _ _ _ H4) ] ] end ].
    all: try solve [ lazymatch goal with |- read_cargs _ _ _ _ _ _ (ca_rec _ :: _) _ _ =>
      econstructor;
      [ exact (shty_rn _ _ _ _ _ e)
      | apply H; [ exact H1 | apply dbd_nf_dom; [ eapply shty_dbd; eassumption | apply (all_in_head _ _ _ H4) ] ]
      | apply H0; [ exact H1 | exact H2 | exact H3 | exact (all_in_tail _ _ _ H4) ] ] end ].
    (** A branch: under its fresh variables, renamed, as many as it binds. *)
    all: try solve [ lazymatch goal with |- read_brs _ _ _ _ _ _ _ _ (_ :: _) _ _ =>
      pose proof H1 as (Hss & Hfx & _);
      match goal with Hp : cargs_plen _ _ |- _ => rename Hp into Hpl end;
      match goal with Fa : fresh_cargs _ _ _ _ _ _ _ _ |- _ => rename Fa into Fc end;
      match goal with Fi : fresh_ihs _ _ _ _ _ _ _ _ _ |- _ => rename Fi into Fi' end;
      pose proof (fresh_tele_length _ _ _ _ f0) as Hl1; rewrite ind_nn_tele_length in Hl1;
      pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Hl2;
      pose proof (fresh_ihs_length _ _ _ _ _ _ _ Fi') as Hl3;
      assert (Hns : forall x, In x ns -> dbd (s + ind_nn D) x)
        by (rewrite <- (ind_nn_tele_length D); eapply (fresh_tele_dbd Θ Ξ);
            [ exact f0 | apply env_dbd_args; [ apply env_dbd_nil | exact H4 ] ]);
      assert (Hρa : env_dbd (s + ind_nn D) (env_args nil (ups ++ ns)))
        by (apply env_dbd_args; [ apply env_dbd_nil | apply all_in_app; [ intros; eapply dbd_mono; [| apply H4; eassumption ]; lia | exact Hns ] ]);
      pose proof (fresh_cargs_dbd Θ Ξ _ _ _ _ _ _ Fc Hρa
                    ltac:(intros; eapply dbd_mono; [| apply H4; eassumption ]; lia)) as Hvs;
      pose proof (fresh_ihs_dbd Θ Ξ _ _ _ _ _ _ _ Fi' (ind_nn D) s ltac:(lia) H2
                    ltac:(eapply env_dbd_mono; [| exact Hρa ]; lia) (plen_forall _ _ Hpl) Hvs) as Hihs;
      pose proof (fresh_tele_rn _ _ _ _ f0 s' Hfx Hss) as Hns';
      rewrite env_args_rn in Hns'; cbn [ern List.map] in Hns';
      pose proof (fresh_cargs_rn _ _ _ _ _ _ Fc (s' + ind_nn D) ltac:(intros; rewrite Hfx by lia; lia) ltac:(lia)) as Hvs';
      rewrite env_args_rn, List.map_app in Hvs'; cbn [ern List.map] in Hvs';
      pose proof (fresh_ihs_rn _ _ _ _ _ _ _ Fi' (s' + ind_nn D + List.length gs)
                    ltac:(intros; rewrite Hfx by lia; lia) ltac:(lia)) as Hihs';
      rewrite env_args_rn, List.map_app in Hihs'; cbn [ern List.map] in Hihs';
      pose proof (eval_args_rn _ _ _ _ e0) as Hb'; rewrite !List.map_app in Hb';
      pose proof (eval_args_rn _ _ _ _ e1) as Ht'; rewrite List.map_app in Ht'; cbn [List.map drn] in Ht';
      rewrite !List.map_app in Ht';
      econstructor; try eassumption;
      [ replace (s' + n) with (n + s') by lia;
        apply H; [ replace (s + n) with (n + s) by lia; apply rn_ok_qn, H1 |];
        apply dbd_nf_dom;
        [ eapply (dbd_eclo_clon Θ Ξ _ _ _ _ H2); [ lia | | | exact e1 ]; [ rewrite length_app, Hl1; cbn; lia |];
          apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia |];
          apply all_in_cons; [| apply all_in_nil ];
          apply dbd_con, all_in_app; [ intros; eapply dbd_mono; [| apply H4; eassumption ]; lia |];
          apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia
                            | intros; eapply dbd_mono; [| apply Hvs; eassumption ]; lia ]
        | eapply (H3 c n B (or_introl eq_refl)); [ lia | | | exact e0 ]; [ rewrite !length_app, Hl1, Hl2, Hl3; lia |];
          apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia |];
          apply all_in_app; [ intros; eapply dbd_mono; [| apply Hvs; eassumption ]; lia
                            | intros; eapply dbd_mono; [| apply Hihs; eassumption ]; lia ] ]
      | apply H0; [ exact H1 | exact H2 | intros c0 n0 B0 Hin; exact (H3 c0 n0 B0 (or_intror Hin)) | exact H4 ] ] end ].
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
  - pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (eval_rn Θ Ξ f))))) _ _ _ H0) as Hh; rewrite Hρ in Hh.
    assert (dmrn f h = h) as Eh by (eapply functional_eval_modexp; eassumption).
    cbn [extend_env_mod ern List.map dern]; fold (ern f ρ); rewrite Hρ, Eh; reflexivity.
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
