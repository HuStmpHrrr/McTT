(** * Renaming the Levels of Values: Readback Commutes with Weakening

    A value names variables by de Bruijn *level* ([d_var x]); readback at
    length [s] turns the level [x] into the index [s - x - 1].  So the same
    value read back at [s] and at [S s] gives two normal forms that differ by
    the weakening [↑] — provided the value only mentions levels below [s]
    ([read_shift]).  This is the step "readback at [|Γ| + 1] is the weakening
    of readback at [|Γ|]" of the semantic proof that NbE commutes with
    weakening ([Core.Consequences.NormalFormWeakening]).

    The two readbacks do not run in lockstep on the *same* value: under a
    binder, readback at [s] applies the closure to the fresh level [s], and
    readback at [S s] to the fresh level [S s].  So the statement is
    generalised to a renaming [f] of levels, applied to values by [domain_rename f]:

    - evaluation is equivariant under every [f] ([eval_rn]): it never looks
      at a level, it only carries them;
    - readback of [domain_rename f d] at [s'] is the readback of [d] at [s], renamed by
      a weakening [φ] that sends the index of [x] at [s] to the index of
      [f x] at [s'] ([read_rn]).  For the canonical form of a level this
      needs [φ] to preserve the order of indices
      ([Core.Syntactic.NfRename.lvl_canon_wk]).

    [read_shift] is the instance [f x = x] below [s] and [f x = S x] from
    [s] on: it fixes the initial environment of a context of length [s], and
    so every value evaluated in it.

    That readback only meets levels below [s] is the invariant [domain_avoids] of
    [Core.Semantic.Avoid], at every excluded level [v ≥ s] ([dbd]). *)
From Stdlib Require Import Arith Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE Avoid.
From Mctt.Core.Syntactic Require Import Fresh Members NfRename.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
Import Domain_Notations Syntax_Notations Wk_Notations.

(** ** The Renaming *)

Section Rename.
  Variable f : nat -> nat.

  (** A value with every de Bruijn level renamed by [f], closures'
      environments included; mutually, for the other sorts of values. *)
  Fixpoint domain_rename (d : domain) : domain :=
    match d with
    | d_pi a ρ B => d_pi (domain_rename a) (List.map dentry_rename ρ) B
    | d_univ i => d_univ i
    | d_suniv l => d_suniv (domain_rename l)
    | d_level n => d_level n
    | d_lvl c xs => d_lvl c (List.map (fun ka => match ka with (k, n, m) => (k, n, domain_ne_rename m) end) xs)
    | d_True => d_True
    | d_true => d_true
    | d_False => d_False
    | d_fn ρ M => d_fn (List.map dentry_rename ρ) M
    | d_neut a m => d_neut (domain_rename a) (domain_ne_rename m)
    | d_member h ch => d_member (dmod_rename h) ch
    | d_ind p k args => d_ind p k (List.map domain_rename args)
    | d_con p k c args => d_con p k c (List.map domain_rename args)
    | d_ihfn ρ Bks p ups t i g => d_ihfn (List.map dentry_rename ρ) Bks p (List.map domain_rename ups) t i (domain_rename g)
    | d_shfam p ups ρ t => d_shfam p (List.map domain_rename ups) (List.map dentry_rename ρ) t
    | d_ihfam ρm As p ups ρ t i g => d_ihfam (List.map dentry_rename ρm) As p (List.map domain_rename ups) (List.map dentry_rename ρ) t i (domain_rename g)
    | d_record p args => d_record p (List.map domain_rename args)
    | d_tuple vs => d_tuple (List.map (fun ga => match ga with (g, a) => (g, domain_rename a) end) vs)
    end
  with domain_ne_rename (m : domain_ne) : domain_ne :=
    match m with
    | d_var x => d_var (f x)
    | d_app m n => d_app (domain_ne_rename m) (domain_nf_rename n)
    | d_exfalso ρ A m => d_exfalso (List.map dentry_rename ρ) A (domain_ne_rename m)
    | d_elim ρ Bks p ups j args m =>
        d_elim (List.map dentry_rename ρ) Bks p (List.map domain_rename ups) j (List.map domain_rename args) (domain_ne_rename m)
    | d_glob p => d_glob p
    | d_proj g m => d_proj g (domain_ne_rename m)
    end
  with domain_nf_rename (n : domain_nf) : domain_nf :=
    match n with
    | d_dom a m => d_dom (domain_rename a) (domain_rename m)
    end
  with dmod_rename (h : dmod) : dmod :=
    match h with
    | dm_global p args => dm_global p (List.map domain_rename args)
    | dm_local Δ D ρ => dm_local Δ D (List.map dentry_rename ρ)
    | dm_member h ch => dm_member (dmod_rename h) ch
    end
  with dentry_rename (e : dentry) : dentry :=
    match e with
    | de_term d => de_term (domain_rename d)
    | de_mod h => de_mod (dmod_rename h)
    | de_dm d h => de_dm (domain_rename d) (dmod_rename h)
    end.

  Definition env_rename (ρ : env) : env := List.map dentry_rename ρ.
  Definition level_atoms_rename (xs : list (nat * nat * domain_ne)) : list (nat * nat * domain_ne) :=
    List.map (fun ka => match ka with (k, n, m) => (k, n, domain_ne_rename m) end) xs.

  Lemma domain_rename_lvl : forall c xs, domain_rename (d_lvl c xs) = d_lvl c (level_atoms_rename xs).
  Proof. reflexivity. Qed.

  Lemma env_rename_cons : forall e ρ, env_rename (e :: ρ) = dentry_rename e :: env_rename ρ.
  Proof. reflexivity. Qed.

  Lemma env_rename_nil : env_rename nil = nil.
  Proof. reflexivity. Qed.

  Lemma env_entry_rn : forall ρ x, env_entry (env_rename ρ) x = dentry_rename (env_entry ρ x).
  Proof.
    intros; rewrite !env_entry_nth; unfold env_rename.
    change (de_term d_true) with (dentry_rename (de_term d_true)) at 1.
    apply List.map_nth.
  Qed.

  Lemma env_var_rn : forall ρ x, env_var (env_rename ρ) x = domain_rename (env_var ρ x).
  Proof. intros; unfold env_var; rewrite env_entry_rn; destruct (env_entry ρ x); reflexivity. Qed.

  Lemma env_mod_rn : forall ρ x, env_mod (env_rename ρ) x = dmod_rename (env_mod ρ x).
  Proof. intros; unfold env_mod; rewrite env_entry_rn; destruct (env_entry ρ x); reflexivity. Qed.

  Lemma env_args_rn : forall args ρ, env_rename (env_args ρ args) = env_args (env_rename ρ) (List.map domain_rename args).
  Proof. induction args; intros; cbn; [ reflexivity | apply IHargs ]. Qed.

  Lemma dsort_rn : forall d, dsort (domain_rename d) = dsort d.
  Proof. destruct d; reflexivity. Qed.

  Lemma dlvl_view_rn : forall d, dlvl_view (domain_rename d) = (fst (dlvl_view d), level_atoms_rename (snd (dlvl_view d))).
  Proof. destruct d; cbn; try reflexivity; rewrite dsort_rn; reflexivity. Qed.

  Lemma dlvl_suc_rn : forall d, domain_rename (dlvl_suc d) = dlvl_suc (domain_rename d).
  Proof.
    intros; unfold dlvl_suc, dlvl_cst, dlvl_atoms; rewrite dlvl_view_rn, domain_rename_lvl; cbn [fst snd]; f_equal.
    unfold level_atoms_rename; rewrite !List.map_map; apply List.map_ext; intros [[] ?]; reflexivity.
  Qed.

  Lemma dlvl_max_rn : forall d e, domain_rename (dlvl_max d e) = dlvl_max (domain_rename d) (domain_rename e).
  Proof.
    intros; unfold dlvl_max, dlvl_cst, dlvl_atoms; rewrite !dlvl_view_rn, domain_rename_lvl; cbn [fst snd]; f_equal.
    unfold level_atoms_rename; apply List.map_app.
  Qed.

  Lemma length_env_rename : forall ρ, List.length (env_rename ρ) = List.length ρ.
  Proof. intros; apply List.length_map. Qed.

  (** The fields of a renamed tuple: each value renamed. *)
  Lemma tuple_rn : forall (vs : list (string * domain)),
      List.map (fun ga => match ga with (g, a) => (g, domain_rename a) end) vs = List.map (fun p => (fst p, domain_rename (snd p))) vs.
  Proof. intros; apply List.map_ext; intros []; reflexivity. Qed.

  (** The group of an eliminator is read off the head of a value, which the
      renaming keeps. *)
  Lemma elim_grp_of_rn : forall oq m, elim_grp_of oq (domain_rename m) = elim_grp_of oq m.
  Proof.
    intros [p |] m; [ reflexivity |].
    destruct m; try reflexivity.
    match goal with |- elim_grp_of _ (domain_rename (d_neut ?a _)) = _ => destruct a; reflexivity end.
  Qed.
End Rename.

(** ** Evaluation Is Equivariant *)

Create Rewrite HintDb rn.

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack) (f : nat -> nat).

  #[local] Hint Rewrite env_var_rn env_mod_rn env_args_rn dlvl_suc_rn dlvl_max_rn
    List.map_app List.length_map List.firstn_map List.skipn_map : rn.

  Lemma kpad_rn : forall n ρ, env_rename f (kpad n ρ) = kpad n (env_rename f ρ).
  Proof. intros; unfold kpad, env_rename; rewrite List.map_app; f_equal; induction n; cbn; f_equal; assumption. Qed.

  Lemma kbentry_rn : forall ρ E, dentry_rename f (kbentry ρ E) = kbentry (env_rename f ρ) E.
  Proof. intros ρ [? ? ? ? | ? [] | ? ? ? ? ? | ? ? ? [] | ? ? ? ?]; reflexivity. Qed.

  Lemma kgens_env_rn : forall gs ρ k, env_rename f (kgens_env ρ k gs) = kgens_env (env_rename f ρ) k gs.
  Proof.
    induction gs as [| g gs IH]; intros; cbn [kgens_env]; [ reflexivity |].
    rewrite IH; f_equal; destruct g; reflexivity.
  Qed.

  (** Kinds read no level. *)
  Lemma kind_rn :
    (forall h ch k, dkind Θ Ξ h ch k -> dkind Θ Ξ (dmod_rename f h) ch k) /\
    (forall ρ U ch k, ukind Θ Ξ ρ U ch k -> ukind Θ Ξ (env_rename f ρ) U ch k) /\
    (forall ρ H ch k, skind Θ Ξ ρ H ch k -> skind Θ Ξ (env_rename f ρ) H ch k) /\
    (forall ρ Φ ρ', kenv Θ Ξ ρ Φ ρ' -> kenv Θ Ξ (env_rename f ρ) Φ (env_rename f ρ')) /\
    (forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> kbody Θ Ξ (env_rename f ρ) Φ Φx) /\
    (forall ρ H its gs, kgens Θ Ξ ρ H its gs -> kgens Θ Ξ (env_rename f ρ) H its gs).
  Proof.
    apply kind_mut_ind; intros; cbn [dmod_rename env_rename List.map dentry_rename domain_rename] in *;
      repeat change (List.map (dentry_rename f) ?ρ) with (env_rename f ρ) in *;
      rewrite ?kpad_rn in *; try rewrite <- kpad_rn in *;
      try solve [ econstructor; eauto ].
    all: try solve [ rewrite kgens_env_rn; econstructor; eauto ].
    all: try solve [ rewrite kbentry_rn; econstructor; eauto ].
    all: try solve [ econstructor; [ eassumption | rewrite <- kpad_rn; eassumption | eassumption ] ].
    all: try solve [ econstructor; rewrite <- kpad_rn; eassumption ].
    all: try solve [ econstructor; rewrite env_mod_rn; eassumption ].
    all: try solve [ eapply ukind_item_mod; [ eassumption | rewrite <- kpad_rn; eassumption | eassumption | eassumption ] ].
    all: try solve [ eapply ukind_item_dm; [ eassumption | rewrite <- kpad_rn; eassumption | eassumption | eassumption ] ].
    all: try solve [ eapply ukind_dm_step; [ eassumption | eassumption | rewrite <- kpad_rn; eassumption | eassumption ] ].
  Qed.

  Lemma eval_rn :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| domain_rename f m & domain_rename f n | Θ ⍮ Ξ ↘ domain_rename f r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) ms) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> $*| domain_rename f m & List.map (domain_rename f) args | Θ ⍮ Ξ ↘ domain_rename f r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ dmod_rename f h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ dmod_rename f h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> $ᵐ| dmod_rename f h & domain_rename f n | Θ ⍮ Ξ ↘ dmod_rename f r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> $ᵐ*| dmod_rename f h & List.map (domain_rename f) ns | Θ ⍮ Ξ ↘ dmod_rename f r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmod_rename f h ·ₜ x Θ ⍮ Ξ ↘ domain_rename f r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmod_rename f h ·ₘ y Θ ⍮ Ξ ↘ dmod_rename f r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmod_rename f h ·ₜ* ch Θ ⍮ Ξ ↘ domain_rename f r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmod_rename f h ·ₘ* ch Θ ⍮ Ξ ↘ dmod_rename f r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ env_rename f ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       ⟦elim domain_rename f m at j of p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       ⟦ihs List.map (domain_rename f) vs of gs under p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) ihs) /\
    (forall ρ p ups Bks t m rs, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
       ⟦ih domain_rename f m of t under p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) rs) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
       ⟦mref j of p (List.map (domain_rename f) ups) ⟧ Θ ⍮ Ξ ↘ (fst (fst r), snd (fst r), List.map (domain_rename f) (snd r))) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> ⟦shty t of p (List.map (domain_rename f) ups) ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f a) /\
    (forall p ups ρm As ρ t m as', ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
       ⟦ihty domain_rename f m of t at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) as') /\
    (forall g m r, eval_proj Θ Ξ g m r -> eval_proj Θ Ξ g (domain_rename f m) (domain_rename f r)) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs ->
       eval_nflds Θ Ξ (List.map (domain_rename f) ns) (domain_ne_rename f m) fl (List.map (domain_rename f) pre) (List.map (domain_rename f) rs)) /\
    (forall fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> ⟦projs fl of domain_rename f m ⟧ Θ ⍮ Ξ ↘ List.map (domain_rename f) ws) /\
    (forall p ups ρm As ρ gs vs as', ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
       ⟦ihtys List.map (domain_rename f) vs of gs at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) as').
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => ⟦ M ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f m)
             (fun m n r _ => $| domain_rename f m & domain_rename f n | Θ ⍮ Ξ ↘ domain_rename f r)
             (fun Ms ρ ms _ => ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) ms)
             (fun m args r _ => $*| domain_rename f m & List.map (domain_rename f) args | Θ ⍮ Ξ ↘ domain_rename f r)
             (fun H ρ h _ => ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ dmod_rename f h)
             (fun Δ D ρ h _ => ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ dmod_rename f h)
             (fun h n r _ => $ᵐ| dmod_rename f h & domain_rename f n | Θ ⍮ Ξ ↘ dmod_rename f r)
             (fun h ns r _ => $ᵐ*| dmod_rename f h & List.map (domain_rename f) ns | Θ ⍮ Ξ ↘ dmod_rename f r)
             (fun h x r _ => dmod_rename f h ·ₜ x Θ ⍮ Ξ ↘ domain_rename f r)
             (fun h y r _ => dmod_rename f h ·ₘ y Θ ⍮ Ξ ↘ dmod_rename f r)
             (fun h ch r _ => dmod_rename f h ·ₜ* ch Θ ⍮ Ξ ↘ domain_rename f r)
             (fun h ch r _ => dmod_rename f h ·ₘ* ch Θ ⍮ Ξ ↘ dmod_rename f r)
             (fun ρ Φ ρ' _ => ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ env_rename f ρ')
             (fun ρ p ups Bks j m r _ => ⟦elim domain_rename f m at j of p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f r)
             (fun ρ p ups Bks gs vs ihs _ =>
                ⟦ihs List.map (domain_rename f) vs of gs under p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) ihs)
             (fun ρ p ups Bks t m rs _ => ⟦ih domain_rename f m of t under p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) rs)
             (fun p ups j r _ => ⟦mref j of p (List.map (domain_rename f) ups) ⟧ Θ ⍮ Ξ ↘ (fst (fst r), snd (fst r), List.map (domain_rename f) (snd r)))
             (fun p ups ρ t a _ => ⟦shty t of p (List.map (domain_rename f) ups) ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f a)
             (fun p ups ρm As ρ t m as' _ =>
                ⟦ihty domain_rename f m of t at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) as')
             (fun g m r _ => eval_proj Θ Ξ g (domain_rename f m) (domain_rename f r))
             (fun ns m fl pre rs _ =>
                eval_nflds Θ Ξ (List.map (domain_rename f) ns) (domain_ne_rename f m) fl (List.map (domain_rename f) pre) (List.map (domain_rename f) rs))
             (fun fl m ws _ => ⟦projs fl of domain_rename f m ⟧ Θ ⍮ Ξ ↘ List.map (domain_rename f) ws)
             (fun p ups ρm As ρ gs vs as' _ =>
                ⟦ihtys List.map (domain_rename f) vs of gs at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ
                  ↘ List.map (domain_rename f) as'));
      intros; cbn [domain_rename domain_ne_rename domain_nf_rename dmod_rename dentry_rename List.map extend_env fst snd] in *;
      rewrite ?tuple_rn in *;
      repeat change (List.map (dentry_rename f) ?ρ) with (env_rename f ρ) in *;
      autorewrite with rn in *; cbn [List.map] in *;
      try solve [ econstructor; autorewrite with rn; eauto ].
    all: try solve [ econstructor; [ eassumption | rewrite elim_grp_of_rn; eassumption | eassumption ] ].
    all: try solve [ econstructor; [ eassumption | eassumption | rewrite elim_grp_of_rn; eassumption | eassumption ] ].
    all: try solve [ econstructor; [ apply kind_rn; eassumption | eassumption | eauto | eauto ] ].
    all: try solve [ econstructor; [ apply kind_rn; eassumption | eassumption | eassumption | eauto | eauto ] ].
    (* records: a tuple's fields, a field of a tuple, a neutral projection *)
    all: try solve [ rewrite <- combine_map_r; constructor; assumption ].
    all: try solve [ constructor; rewrite field_lookup_map;
                     match goal with H : field_lookup _ _ = Some _ |- _ => rewrite H end; reflexivity ].
    all: try solve [ econstructor; [ eassumption | eassumption | eassumption |];
                     rewrite List.nth_error_map; match goal with H : List.nth_error _ _ = Some _ |- _ => rewrite H end;
                     reflexivity ].
    (* a record view's constructor at its last argument: the tuple of its
       fields *)
    all: try solve [ lazymatch goal with |- $| d_con _ _ _ _ & _ | _ ⍮ _ ↘ d_tuple _ => idtac end;
                     rewrite <- combine_map_r, <- List.skipn_map, List.map_app; cbn [List.map];
                     eapply eval_app_con_rview_full; [ eassumption | eassumption | eassumption | rewrite List.length_map; assumption ] ].
    (* the [i]-th recursive result of a function shape, and its family *)
    all: try solve [ first [ eapply eval_app_ihfn | eapply eval_app_ihfam ];
                     [ eassumption | eassumption
                     | rewrite List.nth_error_map; match goal with H : List.nth_error _ _ = Some _ |- _ => rewrite H end; reflexivity ] ].
    (* at a function shape: one per leaf path of the rest *)
    all: try solve [ rewrite List.map_map; cbn [domain_rename List.map dentry_rename]; repeat change (List.map (dentry_rename f) ?ρ) with (env_rename f ρ);
                     first [ eapply eval_ih_pi; eassumption | eapply eval_ihty_pi; eassumption ] ].
    - (* a variable *) rewrite <- env_var_rn; apply eval_exp_var.
    - (* a module slot *) rewrite <- env_mod_rn; apply eval_me_var.
  Qed.
End Eval.

(** ** Values that Mention Only the Levels Below [b]

    [domain_avoids v b d] of [Core.Semantic.Avoid] bounds the levels of [d] by [b] and
    excludes [v]; at every [v ≥ b] the exclusion is vacuous, and a closure
    evaluated at a level [≥ b] stays within the bound.  The bound, like
    [domain_avoids], is relative to a global context; the section runs to the end of
    readback equivariance ([read_rn]), whose statement is phrased in it. *)
Section Bound.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition dbd (b : nat) (d : domain) : Prop := forall v, b <= v -> domain_avoids Θ Ξ v b d.
  Definition dbd_ne (b : nat) (m : domain_ne) : Prop := forall v, b <= v -> domain_ne_avoids Θ Ξ v b m.
  Definition dbd_nf (b : nat) (n : domain_nf) : Prop := forall v, b <= v -> domain_nf_avoids Θ Ξ v b n.
  Definition dbd_la (b : nat) (xs : list (nat * nat * domain_ne)) : Prop := forall v, b <= v -> level_atoms_avoid Θ Ξ v b xs.

  Ltac dbd_inv := unfold dbd, dbd_ne, dbd_nf, dbd_la in *; intros * H; repeat split; intros v Hv;
    repeat match goal with H : forall v, _ <= v -> _ |- _ => specialize (H v ltac:(lia)) end;
    repeat match goal with
      | H : domain_avoids _ _ _ _ (_ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ _ _ (_ _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ _ _ (_ _ _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ _ _ (_ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ _ _ (_ _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ _ _ (_ _ _ _ _) |- _ => inversion_clear H
      | H : domain_nf_avoids _ _ _ _ (_ _ _) |- _ => inversion_clear H
      | H : level_atoms_avoid _ _ _ _ (_ :: _) |- _ => inversion_clear H
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
  Proof. intros * Hb H v Hv; eapply domain_avoids_mono'; [| apply H ]; lia. Qed.

  Lemma dbd_fresh : forall b s a, s < b -> dbd s a -> dbd b (⇑! a s).
  Proof.
    intros * Hs Ha v Hv; constructor; [ eapply domain_avoids_mono'; [| apply Ha ]; lia | constructor; lia ].
  Qed.

  Lemma dbd_bot : forall b, dbd b ⊥ᵈ.
  Proof. intros b v Hv; constructor. Qed.
  Lemma dbd_level : forall b n, dbd b (Levelᵈ@n).
  Proof. intros b v Hv; constructor. Qed.

  Lemma dbd_nf_dom : forall b a m, dbd b a -> dbd b m -> dbd_nf b (⇓ a m).
  Proof. intros * Ha Hm v Hv; constructor; auto. Qed.

  Lemma dbd_app : forall b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dbd b m -> dbd b n -> dbd b r.
  Proof. intros * Hr Hm Hn v Hv; eapply app_avoids; eauto. Qed.

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
    eapply eval_clo_avoids; [ eapply env_avoids_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.

  Lemma dbd_exfalso_inv : forall b ρ A m,
      dbd_ne b (efqᵈ m under ρ return A) -> dbd_ne b m /\ dbd_clo b ρ A.
  Proof.
    intros * H; split; [ intros v Hv; specialize (H v Hv); inversion H; assumption |].
    intros b' c d Hb Hc Hd v Hv.
    specialize (H v ltac:(lia)); inversion_clear H.
    eapply eval_clo_avoids; [ eapply env_avoids_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.

  (** ** Inductive Types

      An environment of bounded values, and a closure under [n] binders. *)
  Definition env_dbd (b : nat) (ρ : env) : Prop := forall v, b <= v -> env_avoids Θ Ξ v b None ρ.

  Definition dbd_clon (b : nat) (ρ : env) (B : exp) (n : nat) : Prop :=
    forall b' cs d, b <= b' -> List.length cs = n -> (forall c, In c cs -> dbd b' c) ->
               ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ cs ↘ d -> dbd b' d.

  (** A closure under [n] binders whose environment avoids the excluded
      level at every position its body reads, as the invariant states it. *)
  Definition dbd_eclo (b : nat) (ρ : env) (B : exp) (n : nat) : Prop :=
    forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\ optional_exp_fresh (optional_shift n K) B.

  Lemma dbd_eclo_clon : forall b ρ B n, dbd_eclo b ρ B n -> dbd_clon b ρ B n.
  Proof.
    intros * H b' cs d Hb Hl Hc Hd v Hv; destruct (H v ltac:(lia)) as (K & HK & HB).
    eapply (proj1 (eval_avoids Θ Ξ v b'));
      [ exact Hd | apply env_avoids_args; [ eapply env_avoids_mono; [| exact HK ]; lia | intros; apply Hc; [ assumption | lia ] ] |].
    rewrite Hl; exact HB.
  Qed.

  Lemma env_dbd_nil : forall b, env_dbd b nil.
  Proof. intros b v _; apply env_avoids_nil. Qed.

  Lemma env_dbd_args : forall b ρ args, env_dbd b ρ -> (forall a, In a args -> dbd b a) -> env_dbd b (env_args ρ args).
  Proof. intros * Hρ Ha v Hv; apply env_avoids_args_none; [ apply Hρ, Hv | intros; apply Ha; assumption ]. Qed.

  Lemma env_dbd_cons : forall b ρ d, env_dbd b ρ -> dbd b d -> env_dbd b (ρ ↦ d).
  Proof. intros * Hρ Hd v Hv; apply env_avoids_cons_none; [ apply Hρ, Hv | apply Hd, Hv ]. Qed.

  Lemma env_dbd_mono : forall b b' ρ, b <= b' -> env_dbd b ρ -> env_dbd b' ρ.
  Proof. intros * Hb Hρ v Hv; eapply env_avoids_mono; [| apply Hρ ]; lia. Qed.

  Lemma eval_dbd : forall M ρ a b, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> env_dbd b ρ -> dbd b a.
  Proof. intros * H Hρ v Hv; eapply (proj1 (eval_avoids Θ Ξ v b)); [ exact H | apply Hρ, Hv | exact I ]. Qed.

  Lemma dbd_indty : forall b p k args, (forall a, In a args -> dbd b a) -> dbd b (d_ind p k args).
  Proof. intros * Ha v Hv; constructor; intros; apply Ha; assumption. Qed.

  Lemma dbd_con : forall b p k c args, (forall a, In a args -> dbd b a) -> dbd b (d_con p k c args).
  Proof. intros * Ha v Hv; constructor; intros; apply Ha; assumption. Qed.

  Lemma dbd_indty_inv : forall b p k args, dbd b (d_ind p k args) -> forall a, In a args -> dbd b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  Lemma dbd_con_inv : forall b p k c args, dbd b (d_con p k c args) -> forall a, In a args -> dbd b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  (** Records: the arguments of a type former, the neutral a field is
      projected from, and a field of a bounded value. *)
  Lemma dbd_record_inv : forall b p args, dbd b (d_record p args) -> forall a, In a args -> dbd b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  Lemma dbd_proj_inv : forall b g m, dbd_ne b (d_proj g m) -> dbd_ne b m.
  Proof. intros * H v Hv; specialize (H v Hv); inversion H; assumption. Qed.

  Lemma dbd_proj : forall b g m r, eval_proj Θ Ξ g m r -> dbd b m -> dbd b r.
  Proof. intros * H Hm v Hv; exact (proj_avoids _ _ _ _ _ _ _ H (Hm v Hv)). Qed.

  (** The fields along a record view's path of a bounded value. *)
  Lemma projs_dbd : forall b fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> dbd b m -> forall a, In a ws -> dbd b a.
  Proof. intros * H Hm a Ha v Hv; exact (projs_avoids _ _ _ _ _ _ _ H (Hm v Hv) a Ha). Qed.

  (** The blocks of an eliminator, closures in an environment that avoids
      the excluded level at every position they read. *)
  Definition dbd_blocks (b : nat) (ρ : env) (Bks : list eblock) : Prop :=
    forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\ blocks_optional_exp_fresh K Bks.

  Lemma dbd_blocks_motive : forall b ρ Bks bk, dbd_blocks b ρ Bks -> In bk Bks -> dbd_eclo b ρ (eb_motive bk) (eb_nm bk).
  Proof.
    intros * H Hin v Hv; destruct (H v Hv) as (K & HK & HB); exists K; split; [ exact HK | exact (proj1 (HB _ Hin)) ].
  Qed.

  Lemma dbd_blocks_branch : forall b ρ Bks bk, dbd_blocks b ρ Bks -> In bk Bks ->
      forall c n B, In (c, n, B) (eb_brs bk) -> dbd_clon b ρ B n.
  Proof.
    intros * H Hin c n B HB b' cs d Hb Hl Hc Hd v Hv; destruct (H v ltac:(lia)) as (K & HK & HBk).
    eapply (proj1 (eval_avoids Θ Ξ v b')); [ exact Hd | apply env_avoids_args; [ eapply env_avoids_mono; [| exact HK ]; lia | intros; apply Hc; [ assumption | lia ] ] |].
    rewrite Hl; exact (proj2 (HBk _ Hin) _ _ _ HB).
  Qed.

  Lemma dbd_blocks_mono : forall b b' ρ Bks, b <= b' -> dbd_blocks b ρ Bks -> dbd_blocks b' ρ Bks.
  Proof.
    intros * Hb H v Hv; destruct (H v ltac:(lia)) as (K & HK & HB); exists K; split; [ eapply env_avoids_mono; [| exact HK ]; lia | exact HB ].
  Qed.

  Lemma mref_dbd : forall p ups j r b, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
      (forall u, In u ups -> dbd b u) -> forall a, In a (snd r) -> dbd b a.
  Proof. intros * H Hu a Ha v Hv; eapply mref_avoids; [ exact H | intros; apply Hu; assumption | exact Ha ]. Qed.

  Lemma dbd_elim_inv : forall b ρ Bks p ups j args m,
      dbd_ne b (d_elim ρ Bks p ups j args m) ->
      dbd_ne b m /\ (forall a, In a args -> dbd b a) /\ dbd_blocks b ρ Bks /\
      (forall a, In a ups -> dbd b a).
  Proof.
    intros * H; repeat split.
    - intros v Hv; specialize (H v Hv); inversion H; assumption.
    - intros a Ha v Hv; specialize (H v Hv); inversion H; auto.
    - intros v Hv; specialize (H v Hv); inversion_clear H; eexists; split; eassumption.
    - intros a Ha v Hv; specialize (H v Hv); inversion_clear H; eauto.
  Qed.

  (** The uniform parameters an eliminator carries, bounded. *)
  Definition ups_dbd (b : nat) (ups : list domain) : Prop := forall a, In a ups -> dbd b a.

  Lemma ups_dbd_avoids : forall b ups, ups_dbd b ups -> forall v, b <= v -> ups_avoids Θ Ξ v b ups.
  Proof. intros * H v Hv a Ha; exact (H a Ha v Hv). Qed.

  Lemma ups_dbd_mono : forall b b' ups, b <= b' -> ups_dbd b ups -> ups_dbd b' ups.
  Proof. intros * Hb H a Ha; exact (dbd_mono _ _ _ Hb (H a Ha)). Qed.

  (** The fresh variables of the telescopes of a declaration are above the
      readback length, and below the length past them. *)
  Lemma fresh_tele_dbd : forall ρ T s ns, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ns -> env_dbd s ρ ->
      forall a, In a ns -> dbd (s + List.length T) a.
  Proof.
    induction 1; intros Hρ; [ intros ? [] |].
    assert (Ha : dbd s a) by (eapply eval_dbd; eassumption).
    cbn [List.length]; replace (s + S (List.length T)) with (S s + List.length T) by lia.
    intros d [<- | Hd].
    - apply dbd_fresh; [ lia | exact Ha ].
    - apply IHfresh_tele; [| exact Hd ]. apply env_dbd_cons; [ eapply env_dbd_mono; [| exact Hρ ]; lia | apply dbd_fresh; [ lia | exact Ha ] ].
  Qed.

  Lemma shty_dbd : forall p ups ρ t a b, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      env_dbd b ρ -> (forall u, In u ups -> dbd b u) -> dbd b a.
  Proof.
    intros * H Hρ Hu v Hv; eapply shty_avoids; [ exact H | apply Hρ, Hv | apply optional_ptyp_fresh_none | intros; apply Hu; assumption ].
  Qed.

  Lemma fresh_cargs_dbd : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
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

  (** The fresh variables along the leaf paths of the container's: one
      above the other, from [s] on. *)
  Lemma fresh_leaf_vars_dbd : forall bs as' s vs, fresh_leaf_vars bs as' s vs ->
      (forall a, In a as' -> dbd s a) -> forall a, In a vs -> dbd (s + List.length vs) a.
  Proof.
    induction 1; intros Ha; [ apply all_in_nil | | ].
    - cbn [List.length]; replace (s + S (List.length vs)) with (S s + List.length vs) by lia.
      apply all_in_cons; [ apply dbd_fresh; [ lia | exact (all_in_head _ _ _ Ha) ] |].
      apply IHfresh_leaf_vars; intros; eapply dbd_mono; [| apply Ha; right; eassumption ]; lia.
    - apply IHfresh_leaf_vars; exact (all_in_tail _ _ _ Ha).
  Qed.

  (** The recursive results of a branch, fresh variables above the
      readback length [s], as many as there are; their types are the
      motives [As] in [ρ], which avoid the excluded level wherever the
      recursive arguments' shapes end ([ends_fresh]). *)
  Lemma fresh_ihs_dbd : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall b, b <= s -> env_dbd s ρa -> ups_dbd s ups ->
      (forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\
                              forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh Θ Ξ p K As t) ->
      (forall a, In a vs -> dbd s a) ->
      forall a, In a ihs -> dbd (s + List.length ihs) a.
  Proof.
    induction 1; intros b0 Hb Hρa Hu Hl Hvs.
    - apply all_in_nil.
    - apply (IHfresh_ihs b0); try assumption.
      + apply env_dbd_cons; [ exact Hρa | exact (all_in_head _ _ _ Hvs) ].
      + intros w Hw; destruct (Hl w Hw) as (K & HK & HK'); exists K; split; [ exact HK |].
        intros gs1 t gs2 E; apply (HK' (ca_arg T :: gs1) t gs2); rewrite E; reflexivity.
      + exact (all_in_tail _ _ _ Hvs).
    - assert (Has : forall a, In a as' -> dbd s a).
      { intros a Ha w Hw; destruct (Hl w ltac:(lia)) as (K & HK & HK').
        eapply ihty_avoids; [ eassumption | eapply env_avoids_mono; [| exact HK ]; lia | exact (HK' nil t gs eq_refl)
                        | exact (ups_dbd_avoids _ _ Hu _ Hw) | exact (Hρa w Hw) | apply optional_ptyp_fresh_none
                        | exact (all_in_head _ _ _ Hvs w Hw) | exact Ha ]. }
      match goal with Hf : fresh_leaf_vars _ _ _ _ |- _ => pose proof (fresh_leaf_vars_dbd _ _ _ _ Hf Has) as Hfl end.
      rewrite List.length_app; apply all_in_app.
      + intros a Ha; eapply dbd_mono; [| exact (Hfl a Ha) ]; lia.
      + assert (Hr : forall a, In a ihs -> dbd (List.length ihs1 + s + List.length ihs) a).
        { apply (IHfresh_ihs b0);
            [ lia | eapply env_dbd_mono; [| exact Hρa ]; lia | eapply ups_dbd_mono; [| exact Hu ]; lia
            | | intros; eapply dbd_mono; [| apply Hvs; right; eassumption ]; lia ].
          intros w Hw; destruct (Hl w Hw) as (K & HK & HK'); exists K; split; [ exact HK |].
          intros gs1 t0 gs2 E; apply (HK' (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity. }
        intros a Ha; eapply dbd_mono; [| exact (Hr a Ha) ]; lia.
    - apply (IHfresh_ihs b0); try assumption.
      + intros w Hw; destruct (Hl w Hw) as (K & HK & HK'); exists K; split; [ exact HK |].
        intros gs1 t0 gs2 E; apply (HK' (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity.
      + exact (all_in_tail _ _ _ Hvs).
  Qed.

  (** The motives at the recursive arguments of the eliminator's group, from
      the blocks: their shapes end where the motives avoid the excluded
      level. *)
  Lemma ihs_motives_dbd : forall p D Bks b ρ gs, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
      cargs_plen D gs -> blocks_nm_at D None Bks -> dbd_blocks b ρ Bks ->
      forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\
                              forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh Θ Ξ p K (blocks_motives Bks) t.
  Proof.
    intros * HD Har Hpl Hnm HB v Hv; destruct (HB v Hv) as (K & HK & HBk); exists K; split; [ exact HK |].
    exact (cargs_ends_fresh _ _ _ _ _ _ _ HD Har Hnm HBk Hpl).
  Qed.

  (** The recursive results a branch is read under. *)
  Lemma wrap_ihs_eval_dbd : forall ρ p ups Bks Dc gs' gs vs ihs r b,
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
      dbd_blocks b ρ Bks -> ups_dbd b ups -> (forall a, In a vs -> dbd b a) -> (forall a, In a ihs -> dbd b a) ->
      forall a, In a r -> dbd b a.
  Proof.
    intros * H HB Ho Hv Hi a Ha w Hw; destruct (HB w Hw) as (K & HK & HBk).
    eapply wrap_ihs_eval_avoids; [ exact H | exact HK | exact HBk | exact (ups_dbd_avoids _ _ Ho _ Hw)
                             | intros; apply Hv; assumption | intros; apply Hi; assumption | exact Ha ].
  Qed.

(** The bound of a value built during readback: by its constructor, by
    monotonicity, or by the evaluation it came from. *)
Ltac dbd_solve :=
  first [ eassumption
        | apply dbd_nf_dom; dbd_solve
        | apply dbd_fresh; [ lia | dbd_solve ]
        | apply dbd_bot | apply dbd_level
        | match goal with
          | Hc : dbd_clo ?b ?ρ ?B, e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↦ ?c ↘ ?d |- dbd ?b' ?d =>
              apply (Hc b' c d); [ lia | dbd_solve | exact e ]
          | Hc : dbd_clo2 ?b ?ρ ?B, e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↦ ?c1 ↦ ?c2 ↘ ?d |- dbd ?b' ?d =>
              apply (Hc b' c1 c2 d); [ lia | dbd_solve | dbd_solve | exact e ]
          | e : $| ?m & ?n | _ ⍮ _ ↘ ?r |- dbd ?b ?r => apply (dbd_app b m n r e); dbd_solve
          | H : dbd ?b0 ?d |- dbd ?b ?d => apply (dbd_mono b0 b d); [ lia | exact H ]
          end ].

(** ** Readback Is Equivariant

    [rn_ok f s s' φ]: reading back at [s] and at [s'], the renaming [f] of
    levels and the weakening [φ] of indices agree on the levels below [s];
    from [s] on, [f] is the shift by [s' - s], so the fresh levels of the two
    readbacks correspond. *)
Record rn_ok (f : nat -> nat) (s s' : nat) (φ : wk) : Prop := mk_rn_ok
  { rn_le : s <= s'
  ; rn_above : forall x, s <= x -> f x = x + (s' - s)
  ; rn_below : forall x, x < s -> f x < s'
  ; rn_index : forall x, x < s -> φ (s - x - 1) = s' - f x - 1
  ; rn_mono : wk_mono φ }.

Lemma rn_ok_fresh : forall f s s' φ, rn_ok f s s' φ -> f s = s'.
Proof. intros * [? Hf _ _ _]; rewrite Hf; lia. Qed.

Lemma rn_ok_q : forall f s s' φ, rn_ok f s s' φ -> rn_ok f (S s) (S s') (wk_q φ).
Proof.
  intros * [Hs Hf Hlt Hφ Hm]; constructor.
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

  Variable (f : nat -> nat).

  Lemma eval_clo_rn : forall B ρ c d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↦ domain_rename f c ↘ domain_rename f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma eval_clo2_rn : forall B ρ c1 c2 d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↦ domain_rename f c1 ↦ domain_rename f c2 ↘ domain_rename f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma app_rn : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| domain_rename f m & domain_rename f n | Θ ⍮ Ξ ↘ domain_rename f r.
  Proof. intros * H; exact (proj1 (proj2 (eval_rn Θ Ξ f)) _ _ _ H). Qed.

  Lemma eval_args_rn : forall B ρ args d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ args ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args (env_rename f ρ) (List.map (domain_rename f) args) ↘ domain_rename f d.
  Proof. intros * H; rewrite <- env_args_rn; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  (** The fresh variables of the telescopes of a declaration, renamed: from
      the readback length on, [f] is the shift to the other length. *)
  Lemma fresh_tele_rn : forall ρ T s ns, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ns ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      Ftele T in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (domain_rename f) ns.
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor |].
    cbn [domain_rename domain_ne_rename]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
    constructor; [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ H) |].
    pose proof (IHfresh_tele (S s') ltac:(intros; rewrite Hf by lia; lia) ltac:(lia)) as IH.
    cbn [env_rename List.map dentry_rename domain_rename domain_ne_rename extend_env] in IH; rewrite (Hf s) in IH by lia.
    replace (s + (s' - s)) with s' in IH by lia; exact IH.
  Qed.

  Lemma shty_rn : forall p ups ρ t a,
      ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> ⟦shty t of p (List.map (domain_rename f) ups) ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ domain_rename f a.
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
    exact (Hs _ _ _ _ _ H).
  Qed.

  Lemma ihty_rn : forall p ups ρm As ρ t m as',
      ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
      ⟦ihty domain_rename f m of t at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) as'.
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy & _).
    exact (Hy _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma proj_rn : forall g m r, eval_proj Θ Ξ g m r -> eval_proj Θ Ξ g (domain_rename f m) (domain_rename f r).
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
    exact (Hp _ _ _ H).
  Qed.

  (** The fields along a record view's path, renamed. *)
  Lemma projs_rn : forall fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> ⟦projs fl of domain_rename f m ⟧ Θ ⍮ Ξ ↘ List.map (domain_rename f) ws.
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _).
    exact (Hpj _ _ _ H).
  Qed.

  Lemma ih_rn : forall ρ p ups Bks t m rs,
      ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
      ⟦ih domain_rename f m of t under p (List.map (domain_rename f) ups) Bks ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) rs.
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _).
    exact (Hi _ _ _ _ _ _ _ H).
  Qed.

  Lemma mref_rn : forall p ups j hd k pre,
      ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (hd, k, pre) -> ⟦mref j of p (List.map (domain_rename f) ups) ⟧ Θ ⍮ Ξ ↘ (hd, k, List.map (domain_rename f) pre).
  Proof.
    intros * H; destruct (eval_rn Θ Ξ f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
    exact (Hm _ _ _ _ H).
  Qed.

  (** Picking the recursive results along the leaf paths commutes with
      renaming. *)
  Lemma wrap_leaf_vals_rn : forall bs rs ihs ihs' out, wrap_leaf_vals bs rs ihs ihs' out ->
      wrap_leaf_vals bs (List.map (domain_rename f) rs) (List.map (domain_rename f) ihs) (List.map (domain_rename f) ihs') (List.map (domain_rename f) out).
  Proof. induction 1; cbn [List.map]; constructor; assumption. Qed.

  Lemma wrap_ihs_eval_rn : forall ρ p ups Bks Dc gs' gs vs ihs r,
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
      ⟦wihs (List.map (domain_rename f) vs) of gs' gs of Dc with (List.map (domain_rename f) ihs) under p (List.map (domain_rename f) ups) Bks ⟧
        Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) r.
  Proof.
    induction 1; cbn [List.map]; rewrite ?List.map_app;
      econstructor; eauto using ih_rn, wrap_leaf_vals_rn.
  Qed.

  Lemma fresh_cargs_rn : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      Fcargs gs of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (domain_rename f) vs.
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor | |].
    - cbn [domain_rename domain_ne_rename]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ H) |].
      pose proof (IHfresh_cargs (S s') ltac:(intros; rewrite Hf by lia; lia) ltac:(lia)) as IH.
      cbn [env_rename List.map dentry_rename domain_rename domain_ne_rename extend_env] in IH; rewrite (Hf s) in IH by lia.
      replace (s + (s' - s)) with s' in IH by lia; exact IH.
    - cbn [domain_rename domain_ne_rename]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; [ exact (shty_rn _ _ _ _ _ H) |].
      apply (IHfresh_cargs (S s')); [ intros; rewrite Hf by lia; lia | lia ].
  Qed.

  (** The fresh variables along the leaf paths, renamed. *)
  Lemma fresh_leaf_vars_rn : forall bs as' s vs, fresh_leaf_vars bs as' s vs ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      fresh_leaf_vars bs (List.map (domain_rename f) as') s' (List.map (domain_rename f) vs).
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor | |].
    - cbn [domain_rename domain_ne_rename]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; apply (IHfresh_leaf_vars (S s')); [ intros; rewrite Hf by lia; lia | lia ].
    - constructor; exact (IHfresh_leaf_vars s' Hf Hs).
  Qed.

  Lemma fresh_ihs_rn : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall s', (forall x, s <= x -> f x = x + (s' - s)) -> s <= s' ->
      Fihs List.map (domain_rename f) vs at gs' gs of Dc under (env_rename f ρ) As at p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρa ⍮ s'
        ↘ List.map (domain_rename f) ihs.
  Proof.
    induction 1; intros s' Hf Hs; cbn [List.map]; [ constructor | | |].
    - constructor; pose proof (IHfresh_ihs s' Hf Hs) as IH.
      cbn [env_rename List.map dentry_rename extend_env] in IH |- *; exact IH.
    - rewrite List.map_app; econstructor;
        [ eassumption | exact (ihty_rn _ _ _ _ _ _ _ _ H0) | exact (fresh_leaf_vars_rn _ _ _ _ H1 s' Hf Hs) |].
      rewrite List.length_map; apply (IHfresh_ihs (List.length ihs1 + s')); [ intros; rewrite Hf by lia; lia | lia ].
    - apply fresh_ihs_nest; exact (IHfresh_ihs s' Hf Hs).
  Qed.

  Lemma read_rn :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall s' φ, rn_ok f s s' φ -> dbd_nf s m -> Rnf domain_nf_rename f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall s' φ, rn_ok f s s' φ -> dbd_ne s m -> Rne domain_ne_rename f m in Θ ⍮ Ξ ⍮ s' ↘ ne_wk φ M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall s' φ, rn_ok f s s' φ -> dbd s a -> Rtyp domain_rename f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall s' φ, rn_ok f s s' φ -> dbd_la s xs -> Rla level_atoms_rename f xs in Θ ⍮ Ξ ⍮ s' ↘ List.map (map_level_atom (ne_wk φ)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall s' φ, rn_ok f s s' φ -> env_dbd s ρ -> (forall a, In a vs -> dbd s a) ->
       Rps List.map (domain_rename f) vs at T in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (nf_wk φ) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall s' φ, rn_ok f s s' φ -> (forall a, In a ups -> dbd s a) -> env_dbd s ρ ->
       (forall a, In a vs -> dbd s a) ->
       Rcargs List.map (domain_rename f) vs at gs of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (nf_wk φ) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       forall s' φ, rn_ok f s s' φ -> (forall a, In a ups -> dbd s a) -> env_dbd s ρ -> dbd s x ->
       Rsh domain_rename f x at t of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ nf_wk φ X) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       forall s' φ, rn_ok f s s' φ -> dbd_blocks s ρ Bks ->
       (forall D, ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks) ->
       (forall D, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D) -> (forall a, In a ups -> dbd s a) ->
       Rblks i Ms of Dc from p (List.map (domain_rename f) ups) Bks sel in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (map_normal_block (fun n => nf_wk (wk_qn n φ))) NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall s' φ, rn_ok f s s' φ -> dbd_blocks s ρ Bks ->
       (forall D, ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks) ->
       (forall D, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D) -> im_nn Mv = im_nn Mi ->
       dbd_eclo s ρ A (S (im_nn Mi)) ->
       (forall c n B, In (c, n, B) Bs -> dbd_clon s ρ B n) -> (forall a, In a ups -> dbd s a) ->
       (forall a, In a (snd r) -> dbd s a) ->
       Rbrs Bs at cs of Mi (fst (fst r), snd (fst r), List.map (domain_rename f) (snd r)) of Dc from p (List.map (domain_rename f) ups)
         Bks Mv A in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (map_normal_branch (fun n => nf_wk (wk_qn n φ))) Bs') /\
    (forall s ρ fl d Fs, Rflds d at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       forall s' φ, rn_ok f s s' φ -> env_dbd s ρ -> dbd s d ->
       Rflds domain_rename f d at fl in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (nf_wk φ) Fs).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall s' φ, rn_ok f s s' φ -> dbd_nf s m -> Rnf domain_nf_rename f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W)
             (fun s m M _ => forall s' φ, rn_ok f s s' φ -> dbd_ne s m -> Rne domain_ne_rename f m in Θ ⍮ Ξ ⍮ s' ↘ ne_wk φ M)
             (fun s a A _ => forall s' φ, rn_ok f s s' φ -> dbd s a -> Rtyp domain_rename f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A)
             (fun s xs ys _ => forall s' φ, rn_ok f s s' φ -> dbd_la s xs -> Rla level_atoms_rename f xs in Θ ⍮ Ξ ⍮ s' ↘ List.map (map_level_atom (ne_wk φ)) ys)
             (fun s ρ T vs Ms _ => forall s' φ, rn_ok f s s' φ -> env_dbd s ρ -> (forall a, In a vs -> dbd s a) ->
                Rps List.map (domain_rename f) vs at T in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (nf_wk φ) Ms)
             (fun s p ups ρ gs vs Ms _ => forall s' φ, rn_ok f s s' φ -> (forall a, In a ups -> dbd s a) ->
                env_dbd s ρ -> (forall a, In a vs -> dbd s a) ->
                Rcargs List.map (domain_rename f) vs at gs of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (nf_wk φ) Ms)
             (fun s p ups ρ t x X _ => forall s' φ, rn_ok f s s' φ -> (forall a, In a ups -> dbd s a) ->
                env_dbd s ρ -> dbd s x ->
                Rsh domain_rename f x at t of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ nf_wk φ X)
             (fun s ρ p ups Bks Dc sel i Ms NBks _ => forall s' φ, rn_ok f s s' φ -> dbd_blocks s ρ Bks ->
                (forall D, ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks) ->
                (forall D, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D) -> (forall a, In a ups -> dbd s a) ->
                Rblks i Ms of Dc from p (List.map (domain_rename f) ups) Bks sel in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (map_normal_block (fun n => nf_wk (wk_qn n φ))) NBks)
             (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ => forall s' φ, rn_ok f s s' φ -> dbd_blocks s ρ Bks ->
                (forall D, ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks) ->
                (forall D, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D) -> im_nn Mv = im_nn Mi ->
                dbd_eclo s ρ A (S (im_nn Mi)) ->
                (forall c n B, In (c, n, B) Bs -> dbd_clon s ρ B n) -> (forall a, In a ups -> dbd s a) ->
                (forall a, In a (snd r) -> dbd s a) ->
                Rbrs Bs at cs of Mi (fst (fst r), snd (fst r), List.map (domain_rename f) (snd r)) of Dc from p (List.map (domain_rename f) ups)
                  Bks Mv A in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (map_normal_branch (fun n => nf_wk (wk_qn n φ))) Bs')
             (fun s ρ fl d Fs _ => forall s' φ, rn_ok f s s' φ -> env_dbd s ρ -> dbd s d ->
                Rflds domain_rename f d at fl in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ List.map (nf_wk φ) Fs));
      intros; cbn [domain_rename domain_ne_rename domain_nf_rename dmod_rename dentry_rename nf_wk ne_wk level_atoms_rename List.map fst snd] in *;
      unfold map_level_atom, map_normal_block, map_normal_branch in *;
      cbn [atom_offset atom_sort atom_level block_arity block_motive block_branches
           branch_constructor branch_arity branch_body] in *.
    (** The bounds of the parts. *)
    all: repeat match goal with
      | H : dbd_nf _ (d_dom _ _) |- _ => apply dbd_nf_inv in H as [? ?]
      | H : dbd _ (d_neut _ _) |- _ => apply dbd_neut_inv in H as [? ?]
      | H : dbd _ (d_suniv _) |- _ => apply dbd_suniv_inv in H
      | H : dbd _ (d_lvl _ _) |- _ => apply dbd_lvl_inv in H
      | H : dbd _ (d_pi _ _ _) |- _ => apply dbd_pi_inv in H as [? ?]
      | H : dbd_la _ ((_, _) :: _) |- _ => apply dbd_la_inv in H as [? ?]
      | H : dbd_ne _ (d_app _ _) |- _ => apply dbd_app_inv in H as [? ?]
      | H : dbd_ne _ (d_exfalso _ _ _) |- _ => apply dbd_exfalso_inv in H as [? ?]
      | H : dbd _ (d_ind _ _ _) |- _ => pose proof (dbd_indty_inv _ _ _ _ H); clear H
      | H : dbd _ (d_con _ _ _ _) |- _ => pose proof (dbd_con_inv _ _ _ _ _ H); clear H
      | H : dbd_ne _ (d_elim _ _ _ _ _ _ _) |- _ => apply dbd_elim_inv in H as (? & ? & ? & ?)
      | H : dbd _ (d_record _ _) |- _ => pose proof (dbd_record_inv _ _ _ H); clear H
      | H : dbd_ne _ (d_proj _ _) |- _ => apply dbd_proj_inv in H
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
          let H' := fresh "Er" in pose proof (eval_clo2_rn _ _ _ _ _ H) as H'; cbn [domain_rename domain_ne_rename] in H'
      | ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↦ _ ↘ _ =>
          let H' := fresh "Er" in pose proof (eval_clo_rn _ _ _ _ H) as H'; cbn [domain_rename domain_ne_rename] in H'
      | $| _ & _ | _ ⍮ _ ↘ _ =>
          let H' := fresh "Er" in pose proof (app_rn _ _ _ H) as H'; cbn [domain_rename domain_ne_rename] in H'
      | _ => idtac
      end.
    all: rewrite ?Hf0, ?Hf1 in *.
    all: repeat change (List.map (dentry_rename f) ?ρ) with (env_rename f ρ).
    all: cbn [level_atoms_rename] in *.
    (** A level: the renaming commutes with its canonical form. *)
    all: try match goal with
         | Hok : rn_ok f _ _ ?φ |- read_nf _ _ _ _ (nf_wk _ (nf_lvl_of (lvl_canon _))) =>
             rewrite nf_lvl_of_wk, <- lvl_canon_wk by exact (rn_mono _ _ _ _ Hok);
             unfold lvl_wk; cbn [fst snd]
         end.
    (** A variable: the index of [x] at [s] is renamed to that of [f x] at [s']. *)
    all: try match goal with
         | Hok : rn_ok f ?s _ _, Hx : dbd_ne _ (d_var ?x) |- read_ne _ _ _ (d_var _) _ =>
             let Hφ := fresh "Hφ" in
             pose proof (rn_index _ _ _ _ Hok) as Hφ; rewrite Hφ by (eapply dbd_var_inv; exact Hx)
         end.
    (** A small universe: the same through [nf_univ_of]. *)
    all: try match goal with |- read_typ _ _ _ (d_suniv _) _ => rewrite nf_univ_of_wk end.
    (** A neutral level: its sort is that of its type, which the renaming
        keeps. *)
    all: try match goal with |- context [dsort ?a] => rewrite <- (dsort_rn f a) end.
    (** Inductive types.  A constructor at its type: the parameters and the
        arguments, renamed, at their renamed types. *)
    all: try solve [ lazymatch goal with |- read_nf _ _ _ _ (nf_con _ _ _ _) =>
      match goal with
      | Hl : ind_lookup _ _ ?p = Some ?D, Hk : ind_member ?D ?k = Some ?Mk, Hh : im_head ?Mk = mh_decl _,
        Hc : ind_con ?Mk ?c = Some ?gs,
        Hla : List.length ?as' = im_np _ _, Hlv : List.length ?vs = _,
        IH1 : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        IH2 : forall s0 φ0, rn_ok f ?s s0 φ0 -> _ -> env_dbd ?s (env_args nil ?as') -> _ -> read_cargs _ _ s0 _ _ _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Has : forall a, In a ?as' -> dbd ?s a, Hvs : forall a, In a ?vs -> dbd ?s a |- _ =>
          rewrite List.map_app;
          eapply read_nf_con; [ exact Hl | exact Hk | exact Hh | exact Hc | rewrite List.length_map; exact Hla
                              | rewrite List.length_map; exact Hlv | exact (IH1 s' φ Hok (env_dbd_nil _) Has) | ];
          rewrite List.firstn_map, List.skipn_map;
          change (env_args nil (List.map (domain_rename f) as')) with (env_args (env_rename f nil) (List.map (domain_rename f) as'));
          rewrite <- env_args_rn;
          apply IH2; [ exact Hok | all_in_with assumption | apply env_dbd_args; [ apply env_dbd_nil | exact Has ]
                     | all_in_with assumption ]
      end end ].
    (** A constructor at a view: as at a declared member, the arguments
        after the container's parameters. *)
    all: try solve [ lazymatch goal with |- read_nf _ _ _ _ (nf_con _ _ _ _) =>
      match goal with
      | Hl : ind_lookup _ _ ?p = Some ?D, Hk : ind_member ?D ?j = Some ?Mj, Hh : im_head ?Mj = mh_view _ _ _ _,
        Hc : ind_con ?Mj ?c = Some ?gs,
        Hla : List.length ?as' = im_np _ _, Hlv : List.length ?vs = _,
        IH1 : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        IH2 : forall s0 φ0, rn_ok f ?s s0 φ0 -> _ -> env_dbd ?s (env_args nil ?as') -> _ -> read_cargs _ _ s0 _ _ _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Has : forall a, In a ?as' -> dbd ?s a, Hvs : forall a, In a ?vs -> dbd ?s a |- _ =>
          rewrite List.map_app;
          eapply read_nf_con_view; [ exact Hl | exact Hk | exact Hh | exact Hc
                                   | rewrite List.length_map; exact Hla
                                   | rewrite List.length_map; exact Hlv | exact (IH1 s' φ Hok (env_dbd_nil _) Has) | ];
          rewrite List.firstn_map, List.skipn_map;
          change (env_args nil (List.map (domain_rename f) as')) with (env_args (env_rename f nil) (List.map (domain_rename f) as'));
          rewrite <- env_args_rn;
          apply IH2; [ exact Hok | all_in_with assumption | apply env_dbd_args; [ apply env_dbd_nil | exact Has ]
                     | all_in_with assumption ]
      end end ].
    (** A value at a record view: the uniform parameters, then the fields
        along its path at the constructor's arguments, renamed. *)
    all: try solve [ lazymatch goal with |- read_nf _ _ _ (d_dom (d_ind _ _ _) _) (nf_con _ _ _ _) =>
      match goal with
      | Hl : ind_lookup _ _ ?p = Some ?D, Hk : ind_member ?D ?j = Some ?Mj, Hh : im_head ?Mj = mh_record _ _ _,
        Hc : im_cons ?Mj = (?c, ?gs) :: nil, Hla : List.length ?as' = ind_nu _,
        Hw : eval_projs _ _ _ ?v ?ws,
        IH1 : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        IH2 : forall s0 φ0, rn_ok f ?s s0 φ0 -> _ -> env_dbd ?s (env_args nil ?as') -> _ -> read_cargs _ _ s0 _ _ _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Has : forall a, In a ?as' -> dbd ?s a, Hv : dbd ?s ?v |- _ =>
          rewrite List.map_app;
          eapply read_nf_rview; [ exact Hl | exact Hk | exact Hh | exact Hc | rewrite List.length_map; exact Hla
                                | exact (projs_rn _ _ _ Hw) | exact (IH1 s' φ Hok (env_dbd_nil _) Has) | ];
          change (env_args nil (List.map (domain_rename f) as')) with (env_args (env_rename f nil) (List.map (domain_rename f) as'));
          rewrite <- env_args_rn;
          apply IH2; [ exact Hok | exact Has | apply env_dbd_args; [ apply env_dbd_nil | exact Has ]
                     | exact (projs_dbd _ _ _ _ Hw Hv) ]
      end end ].
    (** A stuck eliminator: the blocks of the group read, renamed, at the
        renamed uniform parameters. *)
    all: try solve [ lazymatch goal with |- read_ne _ _ _ (d_elim _ _ _ _ _ _ _) _ =>
      match goal with
      | Hl : ind_lookup _ _ ?p = Some ?D, Hj : ind_member ?D ?j = Some ?Mj, Hr : im_ref ?p ?j ?Mj = (?pc, ?k),
        Hl' : ind_lookup _ _ ?pc = Some ?Dq, Hk : ind_member ?Dq ?k = Some ?Mk, Hlen : List.length ?as' = im_np _ _,
        Hnm : blocks_nm_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hm : eval_mref _ _ ?p ?ups ?j (?pc, ?k, ?pre),
        IHp : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        IHb : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_blocks ?s ?ρ ?Bks -> _ -> _ -> _ -> read_blocks _ _ s0 _ _ _ _ _ _ _ _ _,
        IHm : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_ne ?s ?m -> read_ne _ _ s0 _ _,
        Hok : rn_ok f ?s ?s' ?φ, HBd : dbd_blocks ?s ?ρ ?Bks, Hmd : dbd_ne ?s ?m,
        Hu : forall a, In a ?ups -> dbd ?s a |- _ =>
          eapply read_ne_elim; [ exact Hl | exact Hj | exact Hr | exact Hl' | exact Hk
                               | rewrite List.length_map; exact Hlen | exact Hnm | exact Har
                               | exact (mref_rn _ _ _ _ _ _ Hm)
                               | exact (IHp s' φ Hok (env_dbd_nil _) (mref_dbd _ _ _ _ _ Hm Hu))
                               | apply (IHb s' φ Hok HBd); [ | | exact Hu ]
                               | apply IHm; [ exact Hok | exact Hmd ] ];
          intros D0 HD0; rewrite Hl in HD0; injection HD0 as <-; assumption
      end end ].
    (** A block: the motive, renamed, read one binder further than its
        non-uniform parameters; the branches; the blocks after it. *)
    all: try solve [ lazymatch goal with |- read_blocks _ _ _ _ _ _ _ _ _ _ (_ :: _) _ =>
      match goal with
      | Hl : ind_lookup _ _ ?p = Some ?D, Hv : ind_member ?D (elim_src ?sel ?i) = Some ?Mv,
        Hb : List.nth_error ?Bks (elim_src ?sel ?i) = Some ?bk, Hnmb : eb_nm ?bk = S (im_nn ?Mi),
        Hm : eval_mref _ _ ?p ?X (elim_src ?sel ?i) (?hd, ?k, ?pre),
        f0 : fresh_tele _ _ (env_args nil ?X) _ ?s ?ns,
        e2 : ⟦ eb_motive ?bk ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?a,
        IHA : forall s0 φ0, rn_ok f (S (?s + im_nn ?Mi)) s0 φ0 -> dbd _ ?a -> read_typ _ _ s0 _ _,
        IHB : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_blocks ?s ?ρ ?Bks -> _ -> _ -> _ -> dbd_eclo ?s ?ρ (eb_motive ?bk) _ ->
              _ -> _ -> _ -> read_brs _ _ s0 _ _ _ _ _ _ _ _ _ _ _ _,
        IHK : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_blocks ?s ?ρ ?Bks -> _ -> _ -> _ -> read_blocks _ _ s0 _ _ _ _ _ _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, HBd : dbd_blocks ?s ?ρ ?Bks,
        Hnm : forall D0, ind_lookup _ _ ?p = Some D0 -> blocks_nm_at _ _ _,
        Har : forall D0, ind_lookup _ _ ?p = Some D0 -> rview_leaf_arity _,
        HX : forall a, In a ?X -> dbd ?s a |- _ =>
          let Hss := fresh "Hss" in let Hfx := fresh "Hfx" in
          let Hlen := fresh "Hlen" in let Hns := fresh "Hns" in let Hp := fresh "Hp" in let Hfn := fresh "Hfn" in
          let Hin := fresh "Hin" in let Hnn := fresh "Hnn" in
          pose proof Hok as [Hss Hfx _ _ _];
          pose proof (List.nth_error_In _ _ Hb) as Hin;
          assert (Hnn : im_nn Mv = im_nn Mi) by (pose proof (Hnm _ Hl _ _ _ Hv Hb) as Hx; congruence);
          pose proof (fresh_tele_length _ _ _ _ f0) as Hlen; rewrite List.length_rev in Hlen;
          change (List.length (im_nparams Mv)) with (im_nn Mv) in Hlen; rewrite Hnn in Hlen;
          assert (Hns : forall x, In x ns -> dbd (s + im_nn Mi) x)
            by (let H' := fresh in
                pose proof (fresh_tele_dbd _ _ _ _ f0 ltac:(apply env_dbd_args; [ apply env_dbd_nil | exact HX ])) as H';
                rewrite List.length_rev in H'; change (List.length (im_nparams Mv)) with (im_nn Mv) in H';
                rewrite Hnn in H'; exact H');
          pose proof (mref_dbd _ _ _ _ _ Hm HX) as Hp; cbn [snd] in Hp;
          assert (Hfn : f (s + im_nn Mi) = s' + im_nn Mi) by (rewrite Hfx; lia);
          eapply read_blocks_cons;
          [ exact Hl | exact Hv | exact Hb | exact Hnmb | exact (mref_rn _ _ _ _ _ _ Hm)
          | let H' := fresh in pose proof (fresh_tele_rn _ _ _ _ f0 s' Hfx Hss) as H'; rewrite env_args_rn in H';
            cbn [env_rename List.map] in H'; exact H'
          | let H' := fresh in pose proof (eval_args_rn _ _ _ _ e2) as H'; rewrite List.map_app in H';
            cbn [List.map domain_rename domain_ne_rename] in H'; rewrite Hfn, List.map_app in H'; exact H'
          | replace (S (s' + im_nn Mi)) with (S (im_nn Mi) + s') by lia; apply IHA;
            [ replace (S (s + im_nn Mi)) with (S (im_nn Mi) + s) by lia; apply rn_ok_qn, Hok |];
            eapply (dbd_eclo_clon _ _ _ _ (dbd_blocks_motive _ _ _ _ HBd Hin)); [ lia | | | exact e2 ];
              [ rewrite length_app, Hlen, Hnmb; cbn; lia |];
              apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia |];
              apply all_in_cons; [| apply all_in_nil ];
              apply dbd_fresh; [ lia |]; apply dbd_indty; apply all_in_app;
                [ intros; eapply dbd_mono; [| apply Hp; eassumption ]; lia | exact Hns ]
          | apply IHB; [ exact Hok | exact HBd | exact Hnm | exact Har | exact Hnn
                       | rewrite <- Hnmb; exact (dbd_blocks_motive _ _ _ _ HBd Hin)
                       | exact (dbd_blocks_branch _ _ _ _ HBd Hin) | exact HX | exact Hp ]
          | apply IHK; [ exact Hok | exact HBd | exact Hnm | exact Har | exact HX ] ]
      end end ].
    (** An inductive type at its parameters. *)
    all: try solve [ lazymatch goal with |- read_typ _ _ _ (d_ind _ _ _) _ =>
      match goal with
      | IH : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Has : forall a, In a ?as' -> dbd ?s a |- _ =>
          econstructor; try eassumption; [ rewrite List.length_map; assumption | exact (IH s' φ Hok (env_dbd_nil _) Has) ]
      end end ].
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
      [ apply H; [ exact H1 | exact H2 | exact H3 | apply (all_in_head _ _ _ H4) ]
      | apply H0; [ exact H1 | exact H2 | exact H3 | exact (all_in_tail _ _ _ H4) ] ] end ].
    (** A branch: under its fresh variables, renamed, as many as it binds. *)
    all: lazymatch goal with |- read_brs _ _ _ _ _ _ _ _ _ _ _ _ (_ :: _) _ _ =>
      lazymatch goal with
      | Hc : ind_con ?Mv ?c = Some ?gs, Hl : ind_lookup _ _ ?p = Some ?D,
        Hn0 : ?n0 = (im_nn ?Mi + _ + cargs_nrec ?D ?gs)%nat, Hn : ?n = (im_nn ?Mi + _ + cargs_nrec ?Dc ?gs')%nat,
        Hcnt : cargs_nin ?D ?Dc ?gs' ?gs = cargs_nrec ?Dc ?gs', Hpl : cargs_plen ?D ?gs,
        f0 : fresh_tele _ _ (env_args nil ?X) _ ?s ?ns, Fc : fresh_cargs _ _ _ _ _ ?gs _ ?vs,
        Fi : fresh_ihs _ _ ?ρ _ _ _ ?Dc _ ?gs' ?gs ?vs _ ?ihs, Fw : wrap_ihs_eval _ _ ?ρ _ _ _ ?Dc ?gs' ?gs ?vs ?ihs ?wihs,
        e0 : ⟦ ?B ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ ?vs ++ ?wihs) ↘ ?bv,
        e1 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?t,
        IHB : forall s0 φ0, rn_ok f (?s + ?n) s0 φ0 -> dbd_nf _ (⇓ ?t ?bv) -> read_nf _ _ s0 _ _,
        IHR : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_blocks ?s ?ρ ?Bks -> _ -> _ -> _ -> _ -> _ -> _ -> _ ->
              read_brs _ _ s0 _ _ _ _ _ _ _ _ _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, HBd : dbd_blocks ?s ?ρ ?Bks,
        Hnm : forall D0, ind_lookup _ _ ?p = Some D0 -> blocks_nm_at _ _ _,
        Har : forall D0, ind_lookup _ _ ?p = Some D0 -> rview_leaf_arity _, Hnn : im_nn ?Mv = im_nn ?Mi,
        HAd : dbd_eclo ?s ?ρ ?A _, HBs : forall c0 n1 B0, In (c0, n1, B0) _ -> dbd_clon ?s ?ρ B0 n1,
        HX : forall a, In a ?X -> dbd ?s a, Hp : forall a, In a ?pre -> dbd ?s a |- _ =>
          let Hss := fresh "Hss" in let Hfx := fresh "Hfx" in let Hnm' := fresh "Hnm" in let Har' := fresh "Har" in
          let Hl1 := fresh "Hl" in let Hl2 := fresh "Hl" in let Hl3 := fresh "Hl" in let Hl4 := fresh "Hl" in
          let Hl5 := fresh "Hl" in
          let Hns := fresh "Hns" in let Hρa := fresh "Hρa" in let Hvs := fresh "Hvs" in let Hihs := fresh "Hihs" in
          let Hw := fresh "Hw" in let Hgl := fresh "Hgl" in
          pose proof Hok as [Hss Hfx _ _ _];
          pose proof (Hnm _ Hl) as Hnm'; pose proof (Har _ Hl) as Har';
          pose proof (fresh_tele_length _ _ _ _ f0) as Hl1; rewrite List.length_rev in Hl1;
          change (List.length (im_nparams Mv)) with (im_nn Mv) in Hl1; rewrite Hnn in Hl1;
          pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Hl2;
          destruct (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ _ _ Hl
                      (leaves_coherent_of_order _ (rview_leaf_order _ Har')) Fw) as [Hl3 Hl4];
          pose proof (fresh_ihs_length _ _ _ _ _ _ _ _ _ _ _ _ Hl Fi) as Hl5; rewrite Hcnt in Hl5;
          assert (Hgl : List.length gs = List.length gs') by congruence;
          assert (Hns : forall x, In x ns -> dbd (s + im_nn Mi) x)
            by (let H' := fresh in
                pose proof (fresh_tele_dbd _ _ _ _ f0 ltac:(apply env_dbd_args; [ apply env_dbd_nil | exact HX ])) as H';
                rewrite List.length_rev in H'; change (List.length (im_nparams Mv)) with (im_nn Mv) in H';
                rewrite Hnn in H'; exact H');
          assert (Hρa : env_dbd (s + im_nn Mi) (env_args nil (X ++ ns)))
            by (apply env_dbd_args; [ apply env_dbd_nil | apply all_in_app; [ intros; eapply dbd_mono; [| apply HX; eassumption ]; lia | exact Hns ] ]);
          pose proof (fresh_cargs_dbd _ _ _ _ _ _ Fc Hρa
                        ltac:(intros; eapply dbd_mono; [| apply HX; eassumption ]; lia)) as Hvs;
          rewrite Hgl in Hvs;
          pose proof (fresh_ihs_dbd _ _ _ _ _ _ _ _ _ _ _ Fi s ltac:(lia)
                        ltac:(eapply env_dbd_mono; [| exact Hρa ]; lia)
                        ltac:(intros ? ?; eapply dbd_mono; [| apply HX; eassumption ]; lia)
                        (ihs_motives_dbd _ _ _ _ _ _ Hl Har' Hpl Hnm' HBd) Hvs) as Hihs;
          rewrite Hl5 in Hihs;
          assert (Hw : forall x, In x wihs -> dbd (s + n) x)
            by (eapply wrap_ihs_eval_dbd; [ exact Fw | eapply dbd_blocks_mono; [| exact HBd ]; lia
                                                  | eapply ups_dbd_mono; [| exact HX ]; lia
                                                  | intros; eapply dbd_mono; [| apply Hvs; eassumption ]; lia
                                                  | intros; eapply dbd_mono; [| apply Hihs; eassumption ]; lia ]);
          eapply read_brs_cons;
          [ exact Hc | exact Hl | exact Hn0 | exact Hn | exact Hcnt | exact Hpl
          | let H' := fresh in pose proof (fresh_tele_rn _ _ _ _ f0 s' Hfx Hss) as H'; rewrite env_args_rn in H';
            cbn [env_rename List.map] in H'; exact H'
          | let H' := fresh in
            pose proof (fresh_cargs_rn _ _ _ _ _ _ Fc (s' + im_nn Mi) ltac:(intros; rewrite Hfx by lia; lia) ltac:(lia)) as H';
            rewrite env_args_rn, List.map_app in H'; cbn [env_rename List.map] in H'; exact H'
          | let H' := fresh in
            pose proof (fresh_ihs_rn _ _ _ _ _ _ _ _ _ _ _ Fi (s' + im_nn Mi + List.length gs')
                          ltac:(intros; rewrite Hfx by lia; lia) ltac:(lia)) as H';
            rewrite env_args_rn, List.map_app in H'; cbn [env_rename List.map] in H'; exact H'
          | exact (wrap_ihs_eval_rn _ _ _ _ _ _ _ _ _ _ Fw)
          | let H' := fresh in pose proof (eval_args_rn _ _ _ _ e0) as H'; rewrite !List.map_app in H'; exact H'
          | let H' := fresh in pose proof (eval_args_rn _ _ _ _ e1) as H'; rewrite List.map_app in H';
            cbn [List.map domain_rename] in H'; rewrite !List.map_app in H'; exact H'
          | replace (s' + n) with (n + s') by lia;
            apply IHB; [ replace (s + n) with (n + s) by lia; apply rn_ok_qn, Hok |];
            apply dbd_nf_dom;
            [ eapply (dbd_eclo_clon _ _ _ _ HAd); [ lia | | | exact e1 ]; [ rewrite length_app, Hl1; cbn; lia |];
              apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia |];
              apply all_in_cons; [| apply all_in_nil ];
              apply dbd_con, all_in_app; [ intros; eapply dbd_mono; [| apply Hp; eassumption ]; lia |];
              apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia
                                | intros; eapply dbd_mono; [| apply Hvs; eassumption ]; lia ]
            | eapply (HBs c n0 B (or_introl eq_refl)); [ lia | | | exact e0 ]; [ rewrite !length_app, Hl1, Hl2, Hgl, Hl3; lia |];
              apply all_in_app; [ intros; eapply dbd_mono; [| apply Hns; eassumption ]; lia |];
              apply all_in_app; [ intros; eapply dbd_mono; [| apply Hvs; eassumption ]; lia | exact Hw ] ]
          | apply IHR; [ exact Hok | exact HBd | exact Hnm | exact Har | exact Hnn | exact HAd
                       | intros ? ? ? Hin; exact (HBs _ _ _ (or_intror Hin)) | exact HX | exact Hp ] ]
      end | _ => idtac end.
    (** A recursive argument at the end of its shape: the member at the
        renamed parameters. *)
    all: try solve [ lazymatch goal with |- read_shape _ _ _ _ _ _ (pt_self _ _) _ _ =>
      match goal with
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?ρ ↘ ?bs, IH : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_nf ?s _ -> read_nf _ _ s0 _ _,
        Hok : rn_ok f ?s ?s' ?φ, Hρ : env_dbd ?s ?ρ |- _ =>
          econstructor; [ exact (proj1 (proj2 (proj2 (eval_rn Θ Ξ f))) _ _ _ e) |];
          rewrite <- List.map_app; apply (IH s' φ Hok); apply dbd_nf_dom; [| assumption ];
          apply dbd_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha]; [ auto |];
          intros w Hw;
          exact (proj1 (proj2 (proj2 (eval_avoids Θ Ξ w s))) _ _ _ e None (Hρ w Hw) (proj2 (List.Forall_forall _ _) (fun _ _ => I)) _ Ha)
      end end ].
    (** A recursive argument of a function shape: under the renamed fresh
        variable of its domain. *)
    all: try solve [ lazymatch goal with |- read_shape _ _ _ _ _ _ (pt_pi _ _) _ _ =>
      match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b, e0 : $| ?x & ⇑! ?b ?s | _ ⍮ _ ↘ ?r, Er : $| domain_rename f ?x & _ | _ ⍮ _ ↘ domain_rename f ?r,
        IHA : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd ?s ?b -> read_typ _ _ s0 _ _,
        IHV : forall s0 φ0, rn_ok f (S ?s) s0 φ0 -> _ -> env_dbd (S ?s) (?ρ ↦ _) -> dbd (S ?s) ?r -> _,
        Hok : rn_ok f ?s ?s' ?φ, Hok1 : rn_ok f (S ?s) (S ?s') _, Hf0 : f ?s = ?s',
        Hρ : env_dbd ?s ?ρ, Hu : forall a, In a ?ups -> dbd ?s a, Hx : dbd ?s ?x |- _ =>
          let Hbd := fresh "Hbd" in
          assert (Hbd : dbd s b) by (eapply eval_dbd; eassumption);
          econstructor; [ exact (proj1 (eval_rn Θ Ξ f) _ _ _ e) | exact (IHA s' φ Hok Hbd) | exact Er |];
          change (env_rename f (ρ ↦ ⇑! b s)) with (env_rename f ρ ↦ domain_rename f (⇑! b s)) in IHV; cbn [domain_rename domain_ne_rename] in IHV; rewrite Hf0 in IHV;
          apply (IHV (S s') (wk_q φ) Hok1);
          [ intros; eapply dbd_mono; [| apply Hu; eassumption ]; lia
          | apply env_dbd_cons; [ eapply env_dbd_mono; [| exact Hρ ]; lia | apply dbd_fresh; [ lia | exact Hbd ] ]
          | eapply dbd_app; [ exact e0 | eapply dbd_mono; [| exact Hx ]; lia | apply dbd_fresh; [ lia | exact Hbd ] ] ]
      end end ].
    (** Records: a tuple at its record type, the parameters and the fields
        renamed; a record type at its parameters; a field, projected and
        read at its renamed type, then the rest with it. *)
    all: try solve [ lazymatch goal with |- read_nf _ _ _ (d_dom (d_record _ _) _) _ =>
      match goal with
      | IHp : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        IHf : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s (env_args nil ?ns) -> _ -> read_fields _ _ s0 _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Hns : forall a, In a ?ns -> dbd ?s a |- _ =>
          econstructor; [ eassumption | rewrite List.length_map; eassumption
                        | exact (IHp s' φ Hok (env_dbd_nil _) Hns) |];
          change (env_args nil (List.map (domain_rename f) ns)) with (env_args (env_rename f nil) (List.map (domain_rename f) ns));
          rewrite <- env_args_rn;
          apply IHf; [ exact Hok | apply env_dbd_args; [ apply env_dbd_nil | exact Hns ] | assumption ]
      end end ].
    all: try solve [ lazymatch goal with |- read_typ _ _ _ (d_record _ _) _ =>
      match goal with
      | IHp : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s nil -> _ -> read_ps _ _ s0 _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Hns : forall a, In a ?ns -> dbd ?s a |- _ =>
          econstructor; [ eassumption | rewrite List.length_map; eassumption | exact (IHp s' φ Hok (env_dbd_nil _) Hns) ]
      end end ].
    all: try solve [ lazymatch goal with |- read_fields _ _ _ _ (_ :: _) _ _ =>
      match goal with
      | e : eval_proj _ _ _ ?d ?r, e0 : ⟦ ?T ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?t,
        IHF : forall s0 φ0, rn_ok f ?s s0 φ0 -> dbd_nf ?s _ -> read_nf _ _ s0 _ _,
        IHR : forall s0 φ0, rn_ok f ?s s0 φ0 -> env_dbd ?s (?ρ ↦ ?r) -> _ -> read_fields _ _ s0 _ _ _ _,
        Hok : rn_ok f ?s ?s' ?φ, Hρ : env_dbd ?s ?ρ, Hd : dbd ?s ?d |- _ =>
          let Hr := fresh "Hr" in
          assert (Hr : dbd s r) by exact (dbd_proj _ _ _ _ e Hd);
          econstructor; [ exact (proj_rn _ _ _ e) | exact (proj1 (eval_rn Θ Ξ f) _ _ _ e0)
                        | apply (IHF s' φ Hok); apply dbd_nf_dom; [ eapply eval_dbd; eassumption | exact Hr ]
                        | apply (IHR s' φ Hok); [ apply env_dbd_cons; assumption | exact Hd ] ]
      end end ].
    all: econstructor.
    all: try rewrite <- nf_lvl_of_wk.
    all: try eassumption.
    all: match goal with
         | IH : _ |- _ => solve [ eapply IH; [ eassumption | dbd_solve ] ]
         end.
  Qed.

  Corollary read_nf_rn : forall s s' φ m W,
      rn_ok f s s' φ -> dbd_nf s m ->
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> Rnf domain_nf_rename f m in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ W.
  Proof. intros * ? ? H; eapply (proj1 read_rn); eassumption. Qed.

  Corollary read_typ_rn : forall s s' φ a A,
      rn_ok f s s' φ -> dbd s a ->
      Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> Rtyp domain_rename f a in Θ ⍮ Ξ ⍮ s' ↘ nf_wk φ A.
  Proof. intros * ? ? H; eapply (proj1 (proj2 (proj2 read_rn))); eassumption. Qed.
End Bound.

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
  intros s; unfold lvl_shift_above; constructor.
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
    forall f, (forall x, x < List.length Γ -> f x = x) -> env_rename f ρ = ρ.
Proof.
  induction 1; intros f Hf; cbn [List.length] in Hf; [ reflexivity | | | |].
  all: assert (Hρ : env_rename f ρ = ρ) by (apply IHinitial_env; intros; apply Hf; lia).
  - pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H0) as Ha; rewrite Hρ in Ha.
    assert (domain_rename f a = a) as Ea by (eapply functional_eval_exp; eassumption).
    cbn [extend_env env_rename List.map dentry_rename domain_rename domain_ne_rename]; fold (env_rename f ρ).
    rewrite Hρ, Ea, Hf by lia; reflexivity.
  - pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H0) as Hm; rewrite Hρ in Hm.
    assert (domain_rename f m = m) as Em by (eapply functional_eval_exp; eassumption).
    cbn [extend_env env_rename List.map dentry_rename]; fold (env_rename f ρ).
    rewrite Hρ, Em; reflexivity.
  - pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (eval_rn Θ Ξ f))))) _ _ _ H0) as Hh; rewrite Hρ in Hh.
    assert (dmod_rename f h = h) as Eh by (eapply functional_eval_modexp; eassumption).
    cbn [extend_env_mod env_rename List.map dentry_rename]; fold (env_rename f ρ); rewrite Hρ, Eh; reflexivity.
  - pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H0) as Hm; rewrite Hρ in Hm.
    assert (domain_rename f m = m) as Em by (eapply functional_eval_exp; eassumption).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (eval_rn Θ Ξ f))))) _ _ _ H1) as Hh; rewrite Hρ in Hh.
    assert (dmod_rename f h = h) as Eh by (eapply functional_eval_modexp; eassumption).
    cbn [extend_env_dm env_rename List.map dentry_rename]; fold (env_rename f ρ); rewrite Hρ, Em, Eh; reflexivity.
Qed.

Corollary eval_initial_rn : forall Θ Ξ Γ ρ M m,
    initial_env Θ Ξ Γ ρ -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    forall f, (forall x, x < List.length Γ -> f x = x) -> domain_rename f m = m.
Proof.
  intros * Hρ Hm f Hf.
  pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ Hm) as Hm'.
  rewrite (initial_env_rn _ _ _ _ Hρ f Hf) in Hm'.
  eapply functional_eval_exp; eassumption.
Qed.

(** A value of the initial environment mentions only the levels of the
    context. *)
Lemma eval_initial_dbd : forall Θ Ξ Γ ρ M m,
    initial_env Θ Ξ Γ ρ -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> dbd Θ Ξ (List.length Γ) m.
Proof.
  intros * Hρ Hm v Hv.
  apply (proj1 (eval_avoids Θ Ξ v (List.length Γ)) _ _ _ Hm None); [| exact I ].
  eapply initial_env_avoids; [ exact Hρ | exact Hv | reflexivity ].
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
                (dbd_nf_dom _ _ _ _ _ (eval_initial_dbd _ _ _ _ _ _ Hρ Ha) (eval_initial_dbd _ _ _ _ _ _ Hρ Hm)) HW)
    as HW'.
  cbn [domain_nf_rename] in HW'.
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
