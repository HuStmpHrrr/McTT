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
    [Core.Semantic.Avoid], at every excluded level [v ≥ s] ([domain_bounded]). *)
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
    | d_pi κd κc a ρ B => d_pi κd κc (domain_rename a) (List.map dentry_rename ρ) B
    | d_univ i => d_univ i
    | d_suniv l => d_suniv (domain_rename l)
    | d_level n => d_level n
    | d_level_sort => d_level_sort
    | d_lvl c xs => d_lvl c (List.map (fun ka => match ka with (k, n, m) => (k, n, domain_ne_rename m) end) xs)
    | d_prop => d_prop
    | d_True => d_True
    | d_proof M ρ => d_proof M (List.map dentry_rename ρ)
    | d_False => d_False
    | d_and a ρ Q => d_and (domain_rename a) (List.map dentry_rename ρ) Q
    | d_fn a ρ M => d_fn (domain_rename a) (List.map dentry_rename ρ) M
    | d_neut a m => d_neut (domain_rename a) (domain_ne_rename m)
    | d_member h ch => d_member (dmod_rename h) ch
    | d_ind p k args => d_ind p k (List.map domain_rename args)
    | d_con p k c args => d_con p k c (List.map domain_rename args)
    | d_ihfn ρ Bks p ups t i g => d_ihfn (List.map dentry_rename ρ) Bks p (List.map domain_rename ups) t i (domain_rename g)
    | d_shfam p ups ρ B t => d_shfam p (List.map domain_rename ups) (List.map dentry_rename ρ) B t
    | d_ihfam ρm As p ups ρ B t i g =>
        d_ihfam (List.map dentry_rename ρm) As p (List.map domain_rename ups) (List.map dentry_rename ρ) B t i (domain_rename g)
    | d_record p args => d_record p (List.map domain_rename args)
    | d_tuple vs => d_tuple (List.map (fun ga => match ga with (g, a) => (g, domain_rename a) end) vs)
    end
  with domain_ne_rename (m : domain_ne) : domain_ne :=
    match m with
    | d_var x => d_var (f x)
    | d_app m n => d_app (domain_ne_rename m) (domain_nf_rename n)
    | d_absurd c p => d_absurd (domain_rename c) (domain_rename p)
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
    | de_term d t => de_term (domain_rename d) (entry_type_rename t)
    | de_mod h U => de_mod (dmod_rename h) U
    | de_dm d t h U => de_dm (domain_rename d) (entry_type_rename t) (dmod_rename h) U
    end
  (** The type an entry is stored at: its values renamed, its syntax
      kept *)
  with entry_type_rename (t : entry_type) : entry_type :=
    match t with
    | entry_type_value a => entry_type_value (domain_rename a)
    | entry_type_closure A ρ => entry_type_closure A (List.map dentry_rename ρ)
    | entry_type_shape p ups ρ t => entry_type_shape p (List.map domain_rename ups) (List.map dentry_rename ρ) t
    | entry_type_induction_hypothesis ρm As p ups ρ t v i =>
        entry_type_induction_hypothesis (List.map dentry_rename ρm) As p (List.map domain_rename ups) (List.map dentry_rename ρ) t
          (domain_rename v) i
    | entry_type_none => entry_type_none
    end.

  Definition env_rename (ρ : env) : env := List.map dentry_rename ρ.
  Definition level_atoms_rename (xs : list (nat * nat * domain_ne)) : list (nat * nat * domain_ne) :=
    List.map (fun ka => match ka with (k, n, m) => (k, n, domain_ne_rename m) end) xs.

  Lemma domain_rename_lvl : forall c xs, domain_rename (d_lvl c xs) = d_lvl c (level_atoms_rename xs).
  Proof. reflexivity. Qed.

  Lemma level_atoms_rename_nil : level_atoms_rename nil = nil.
  Proof. reflexivity. Qed.

  Lemma level_atoms_rename_cons : forall k n m xs,
      level_atoms_rename ((k, n, m) :: xs) = (k, n, domain_ne_rename m) :: level_atoms_rename xs.
  Proof. reflexivity. Qed.

  Lemma env_rename_cons : forall e ρ, env_rename (e :: ρ) = dentry_rename e :: env_rename ρ.
  Proof. reflexivity. Qed.

  Lemma env_rename_extend_env : forall ρ c t, env_rename (ρ ↦ c ⦂ t) = env_rename ρ ↦ domain_rename c ⦂ entry_type_rename t.
  Proof. reflexivity. Qed.

  Lemma env_rename_nil : env_rename nil = nil.
  Proof. reflexivity. Qed.

  Lemma env_entry_rn : forall ρ x, env_entry (env_rename ρ) x = dentry_rename (env_entry ρ x).
  Proof.
    intros; rewrite !env_entry_nth; unfold env_rename.
    change absent_entry with (dentry_rename absent_entry) at 1.
    apply List.map_nth.
  Qed.

  Lemma env_var_rn : forall ρ x, env_var (env_rename ρ) x = domain_rename (env_var ρ x).
  Proof. intros; unfold env_var; rewrite env_entry_rn; destruct (env_entry ρ x); reflexivity. Qed.

  Lemma env_mod_rn : forall ρ x, env_mod (env_rename ρ) x = dmod_rename (env_mod ρ x).
  Proof. intros; unfold env_mod; rewrite env_entry_rn; destruct (env_entry ρ x); reflexivity. Qed.

  (** A typed entry renamed: its value and its type. *)
  Definition typed_rename (vt : (domain * entry_type)%type) : (domain * entry_type)%type :=
    (domain_rename (fst vt), entry_type_rename (snd vt)).

  Lemma env_extend_typed_rn : forall vts ρ,
      env_rename (env_extend_typed ρ vts) = env_extend_typed (env_rename ρ) (List.map typed_rename vts).
  Proof. induction vts; intros; cbn; [ reflexivity | apply IHvts ]. Qed.

  (** The builders of typed entries commute with the renaming. *)
  Lemma tele_head_type_rn : forall ρ T, entry_type_rename (tele_head_type ρ T) = tele_head_type (env_rename ρ) T.
  Proof. intros ρ [| [] T]; reflexivity. Qed.

  Lemma tele_entries_rn : forall vs ρ T,
      List.map typed_rename (tele_entries ρ T vs) = tele_entries (env_rename ρ) T (List.map domain_rename vs).
  Proof.
    induction vs as [| v vs IH]; intros; cbn; [ reflexivity |].
    unfold typed_rename at 1; cbn [fst snd]; rewrite tele_head_type_rn; f_equal.
    rewrite IH; cbn; rewrite tele_head_type_rn; reflexivity.
  Qed.

  Lemma env_tele_rn : forall ρ T vs, env_rename (env_tele ρ T vs) = env_tele (env_rename ρ) T (List.map domain_rename vs).
  Proof. intros; unfold env_tele; rewrite env_extend_typed_rn, tele_entries_rn; reflexivity. Qed.

  Lemma decl_env_rn : forall D ups, env_rename (decl_env D ups) = decl_env D (List.map domain_rename ups).
  Proof. intros; unfold decl_env; apply env_tele_rn. Qed.

  Lemma cargs_entries_rn : forall p ups vs ρ gs,
      List.map typed_rename (cargs_entries p ups ρ gs vs)
      = cargs_entries p (List.map domain_rename ups) (env_rename ρ) gs (List.map domain_rename vs).
  Proof.
    intros p ups; induction vs as [| v vs IH]; intros ρ [| [r A | t] gs]; cbn; try reflexivity;
      f_equal; rewrite ?IH; reflexivity.
  Qed.

  Lemma ihs_types_rn : forall D p ups ρm As gs vs ρ,
      List.map entry_type_rename (ihs_types D p ups ρm As ρ gs vs)
      = ihs_types D p (List.map domain_rename ups) (env_rename ρm) As (env_rename ρ) gs (List.map domain_rename vs).
  Proof.
    intros D p ups ρm As; induction gs as [| [r A | t] gs IH]; intros [| v vs] ρ; cbn; try reflexivity.
    - apply (IH vs (ρ ↦ v ⦂ entry_type_closure A ρ)).
    - rewrite List.map_app, List.map_map, IH; f_equal.
  Qed.

  Lemma pair_values_with_types_rn : forall vs ts,
      List.map typed_rename (pair_values_with_types vs ts)
      = pair_values_with_types (List.map domain_rename vs) (List.map entry_type_rename ts).
  Proof. induction vs as [| v vs IH]; intros [| t ts]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.

  Lemma branch_entries_rn : forall D Mj p ups As ρm gs ns vs ihs,
      List.map typed_rename (branch_entries D Mj p ups As ρm gs ns vs ihs)
      = branch_entries D Mj p (List.map domain_rename ups) As (env_rename ρm) gs
          (List.map domain_rename ns) (List.map domain_rename vs) (List.map domain_rename ihs).
  Proof.
    intros; unfold branch_entries; cbv zeta.
    rewrite !List.map_app, tele_entries_rn, decl_env_rn, cargs_entries_rn, pair_values_with_types_rn, ihs_types_rn,
      env_extend_typed_rn, tele_entries_rn, decl_env_rn; reflexivity.
  Qed.

  Lemma motive_entries_rn : forall D Mk ups ns a m,
      List.map typed_rename (motive_entries D Mk ups ns a m)
      = motive_entries D Mk (List.map domain_rename ups) (List.map domain_rename ns) (domain_rename a) (domain_rename m).
  Proof. intros; unfold motive_entries; rewrite List.map_app, tele_entries_rn, decl_env_rn; reflexivity. Qed.


  Lemma global_proof_env_rn : forall p T args,
      env_rename (global_proof_env p T args) = global_proof_env p T (List.map domain_rename args).
  Proof. intros; unfold global_proof_env; cbn; rewrite env_tele_rn, List.length_map; reflexivity. Qed.

  Lemma kinds_pads_rn : forall n ρ, env_rename (kinds_pads n ρ) = kinds_pads n (env_rename ρ).
  Proof. intros; unfold kinds_pads, env_rename; rewrite List.map_app; f_equal; induction n; cbn; f_equal; assumption. Qed.

  Lemma domain_level_sort_rn : forall d, domain_level_sort (domain_rename d) = domain_level_sort d.
  Proof. destruct d; reflexivity. Qed.

  Lemma domain_level_view_rn : forall d, domain_level_view (domain_rename d) = (fst (domain_level_view d), level_atoms_rename (snd (domain_level_view d))).
  Proof. destruct d; cbn; try reflexivity; rewrite domain_level_sort_rn; reflexivity. Qed.

  Lemma domain_level_suc_rn : forall d, domain_rename (domain_level_suc d) = domain_level_suc (domain_rename d).
  Proof.
    intros; unfold domain_level_suc, domain_level_const, domain_level_atoms; rewrite domain_level_view_rn, domain_rename_lvl; cbn [fst snd]; f_equal.
    unfold level_atoms_rename; rewrite !List.map_map; apply List.map_ext; intros [[] ?]; reflexivity.
  Qed.

  Lemma domain_level_max_rn : forall d e, domain_rename (domain_level_max d e) = domain_level_max (domain_rename d) (domain_rename e).
  Proof.
    intros; unfold domain_level_max, domain_level_const, domain_level_atoms; rewrite !domain_level_view_rn, domain_rename_lvl; cbn [fst snd]; f_equal.
    unfold level_atoms_rename; apply List.map_app.
  Qed.

  Lemma length_env_rename : forall ρ, List.length (env_rename ρ) = List.length ρ.
  Proof. intros; apply List.length_map. Qed.

  (** The fields of a renamed tuple: each value renamed. *)
  Lemma tuple_rn : forall (vs : list (string * domain)),
      List.map (fun ga => match ga with (g, a) => (g, domain_rename a) end) vs = List.map (fun p => (fst p, domain_rename (snd p))) vs.
  Proof. intros; apply List.map_ext; intros []; reflexivity. Qed.

  (** The kind of a type value is read off its head, which the renaming
      keeps. *)
  Lemma domain_kind_rn : forall d, domain_kind (domain_rename d) = domain_kind d.
  Proof. intros []; try reflexivity; match goal with |- context [ d_neut ?a _ ] => destruct a; reflexivity end. Qed.

  (** A neutral's kind is its type's head's, whatever the neutral. *)
  Lemma domain_kind_neut_rn : forall a m m', domain_kind (d_neut (domain_rename a) m) = domain_kind (d_neut a m').
  Proof. intros []; reflexivity. Qed.

  (** The kind of the next parameter of a module value is read off its
      telescope and its number of arguments, which the renaming keeps. *)
  Lemma dmod_param_kind_rn : forall Θ Ξ h, dmod_param_kind Θ Ξ (dmod_rename h) = dmod_param_kind Θ Ξ h.
  Proof. intros Θ Ξ h; induction h; cbn [dmod_rename dmod_param_kind]; rewrite ?List.length_map; congruence. Qed.

  (** So is the kind of a function's next argument. *)
  Lemma arg_kind_rn : forall Θ Ξ m, arg_kind Θ Ξ (domain_rename m) = arg_kind Θ Ξ m.
  Proof.
    intros; destruct m; cbn [domain_rename]; unfold arg_kind; rewrite ?domain_kind_rn, ?List.length_map, ?dmod_param_kind_rn; try reflexivity.
    (* a neutral, at the type its head reads *)
    match goal with |- match domain_rename ?m with _ => _ end = _ => destruct m end;
      cbn [domain_rename]; rewrite ?domain_kind_rn; reflexivity.
  Qed.
End Rename.

(** ** Evaluation Is Equivariant *)

Create Rewrite HintDb rn.

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack) (f : nat -> nat).

  #[local] Hint Rewrite env_var_rn env_mod_rn env_extend_typed_rn env_tele_rn domain_level_suc_rn domain_level_max_rn
    domain_kind_rn arg_kind_rn List.map_app List.length_map List.firstn_map List.skipn_map : rn.

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
    (forall m ρ fl rs, eval_neutral_fields Θ Ξ m ρ fl rs ->
       eval_neutral_fields Θ Ξ (domain_ne_rename f m) (env_rename f ρ) fl (List.map (domain_rename f) rs)) /\
    (forall fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> ⟦projs fl of domain_rename f m ⟧ Θ ⍮ Ξ ↘ List.map (domain_rename f) ws) /\
    (forall p ups ρm As ρ gs vs as', ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
       ⟦ihtys List.map (domain_rename f) vs of gs at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↘ List.map (domain_rename f) as') /\
    (forall rs Ms ρ vs, eval_field_vals Θ Ξ rs Ms ρ vs -> eval_field_vals Θ Ξ rs Ms (env_rename f ρ) (List.map (domain_rename f) vs)) /\
    (forall g Ms ρ r, eval_app_args Θ Ξ g Ms ρ r -> eval_app_args Θ Ξ (domain_rename f g) Ms (env_rename f ρ) (domain_rename f r)).
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
             (fun m ρ fl rs _ => eval_neutral_fields Θ Ξ (domain_ne_rename f m) (env_rename f ρ) fl (List.map (domain_rename f) rs))
             (fun fl m ws _ => ⟦projs fl of domain_rename f m ⟧ Θ ⍮ Ξ ↘ List.map (domain_rename f) ws)
             (fun p ups ρm As ρ gs vs as' _ =>
                ⟦ihtys List.map (domain_rename f) vs of gs at p (List.map (domain_rename f) ups) under (env_rename f ρm) As ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ
                  ↘ List.map (domain_rename f) as')
             (fun rs Ms ρ vs _ => eval_field_vals Θ Ξ rs Ms (env_rename f ρ) (List.map (domain_rename f) vs))
             (fun g Ms ρ r _ => eval_app_args Θ Ξ (domain_rename f g) Ms (env_rename f ρ) (domain_rename f r)));
      intros; cbn [domain_rename domain_ne_rename domain_nf_rename dmod_rename dentry_rename List.map extend_env fst snd] in *;
      rewrite ?tuple_rn in *;
      repeat change (List.map (dentry_rename f) ?ρ) with (env_rename f ρ) in *;
      autorewrite with rn in *; cbn [List.map] in *;
      try solve [ econstructor; autorewrite with rn; eauto ].
    (* the typed entries a branch, a motive or a kept member proof is
       evaluated or kept over: their builders commute with the renaming *)
    all: rewrite ?branch_entries_rn, ?motive_entries_rn, ?decl_env_rn, ?global_proof_env_rn,
           ?List.skipn_map, ?List.firstn_map in *.
    all: try solve [ econstructor; eauto; rewrite ?List.length_map; eauto ].
    all: try solve [ econstructor; eauto; rewrite ?List.skipn_map, ?List.firstn_map; eauto ].
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
    (* the cases the kind directs: the kind read off a value, which the
       renaming keeps *)
    all: cbn [env_rename List.map dentry_rename domain_rename] in *.
    all: try solve [ eapply eval_exp_app; [ eassumption | rewrite arg_kind_rn; eassumption | eassumption | eassumption ] ].
    all: try solve [ eapply eval_exp_app_proof; [ eassumption | rewrite arg_kind_rn; eassumption | eassumption ] ].
    all: try solve [ eapply eval_exp_let; [ eassumption | rewrite domain_kind_rn; eassumption | eassumption | eassumption ] ].
    all: try solve [ eapply eval_exp_let_proof; [ eassumption | rewrite domain_kind_rn; eassumption | eassumption ] ].
    all: try solve [ eapply eval_body_env_def; eassumption ].
    all: try solve [ eapply eval_body_env_def_proof; eassumption ].
    all: try solve [ rewrite <- combine_map_r; eapply eval_exp_tuple; eassumption ].
    (* a member of a saturated global module: saturation counts arguments,
       which the renaming keeps *)
    all: try (match goal with Hs : module_saturated ?Θ ?Ξ ?p ?args |- context [ dm_global ?p (map ?g ?args) ] =>
                assert (module_saturated Θ Ξ p (map g args)) by (intros ? ? Hl; rewrite List.length_map; exact (Hs _ _ Hl)) end;
              first [ eapply eval_sel_global; eassumption | eapply eval_sel_global_neut; eassumption
                    | eapply eval_sel_global_proof; eassumption | eapply eval_sel_global_ind; eassumption
                    | eapply eval_sel_global_record; eassumption ]).
    (* a variable and a module slot: their entries renamed *)
    all: try solve [ rewrite <- env_var_rn; apply eval_exp_var ].
    all: try solve [ rewrite <- env_mod_rn; apply eval_me_var ].
    (* a constructor of a view given its last uniform parameter *)
    all: try solve [ rewrite List.map_app in *; cbn [List.map] in *; econstructor; eauto; rewrite ?List.length_map; eauto ].
    (* an eliminator on a neutral: its motive's environment at the renamed
       parameters *)
    all: try solve [ lazymatch goal with |- ⟦elim ⇑ _ _ at _ of _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ => idtac end;
                     rewrite ?List.map_app, <- ?List.skipn_map in *; econstructor; eauto; rewrite List.length_map; assumption ].
    (* the family of a recursive argument at its member *)
    all: try solve [ match goal with H : context [ List.map (typed_rename _) (tele_entries _ _ _) ] |- _ =>
                       rewrite tele_entries_rn, decl_env_rn in H; cbn [typed_rename fst snd entry_type_rename] in H end;
                     econstructor; eauto ].
    (* an eliminator on a constructor: its branch's entries at the renamed
       arguments *)
    all: eapply eval_elim_con; try eassumption; rewrite ?List.length_map, ?List.skipn_map, ?List.firstn_map, ?List.skipn_map; eassumption.
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

  Definition domain_bounded (b : nat) (d : domain) : Prop := forall v, b <= v -> domain_avoids Θ Ξ v b d.
  Definition domain_ne_bounded (b : nat) (m : domain_ne) : Prop := forall v, b <= v -> domain_ne_avoids Θ Ξ v b m.
  Definition domain_nf_bounded (b : nat) (n : domain_nf) : Prop := forall v, b <= v -> domain_nf_avoids Θ Ξ v b n.
  Definition level_atoms_bounded (b : nat) (xs : list (nat * nat * domain_ne)) : Prop := forall v, b <= v -> level_atoms_avoid Θ Ξ v b xs.

  Ltac domain_bounded_inv := unfold domain_bounded, domain_ne_bounded, domain_nf_bounded, level_atoms_bounded in *; intros * H; repeat split; intros v Hv;
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

  Lemma domain_nf_bounded_inv : forall b a m, domain_nf_bounded b (⇓ a m) -> domain_bounded b a /\ domain_bounded b m.
  Proof. domain_bounded_inv. Qed.
  Lemma domain_bounded_neut_inv : forall b a m, domain_bounded b (⇑ a m) -> domain_bounded b a /\ domain_ne_bounded b m.
  Proof. domain_bounded_inv. Qed.
  Lemma domain_bounded_suniv_inv : forall b l, domain_bounded b 𝕌@l -> domain_bounded b l.
  Proof. domain_bounded_inv. Qed.
  Lemma domain_bounded_lvl_inv : forall b c xs, domain_bounded b (lvᵈ c xs) -> level_atoms_bounded b xs.
  Proof. domain_bounded_inv. Qed.
  Lemma level_atoms_bounded_inv : forall b k n m xs, level_atoms_bounded b ((k, n, m) :: xs) -> domain_ne_bounded b m /\ level_atoms_bounded b xs.
  Proof. domain_bounded_inv. Qed.
  Lemma domain_bounded_app_inv : forall b m n, domain_ne_bounded b (m $ᵈ n) -> domain_ne_bounded b m /\ domain_nf_bounded b n.
  Proof. domain_bounded_inv. Qed.
  Lemma domain_bounded_var_inv : forall b x, domain_ne_bounded b (#ᵈ x) -> x < b.
  Proof. intros * H; specialize (H b (le_n _)); inversion H; assumption. Qed.

  Lemma domain_bounded_mono : forall b b' d, b <= b' -> domain_bounded b d -> domain_bounded b' d.
  Proof. intros * Hb H v Hv; eapply domain_avoids_mono'; [| apply H ]; lia. Qed.

  Lemma domain_bounded_fresh : forall b s a, s < b -> domain_bounded s a -> domain_bounded b (⇑! a s).
  Proof.
    intros * Hs Ha v Hv; constructor; [ eapply domain_avoids_mono'; [| apply Ha ]; lia | constructor; lia ].
  Qed.

  Lemma domain_bounded_bot : forall b, domain_bounded b ⊥ᵈ.
  Proof. intros b v Hv; constructor. Qed.
  Lemma domain_bounded_level : forall b n, domain_bounded b (Levelᵈ@n).
  Proof. intros b v Hv; constructor. Qed.

  Lemma domain_nf_bounded_dom : forall b a m, domain_bounded b a -> domain_bounded b m -> domain_nf_bounded b (⇓ a m).
  Proof. intros * Ha Hm v Hv; constructor; auto. Qed.

  Lemma domain_bounded_app : forall b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> domain_bounded b m -> domain_bounded b n -> domain_bounded b r.
  Proof. intros * Hr Hm Hn v Hv; eapply app_avoids; eauto. Qed.

  (** A closure of a bounded value, evaluated at a bounded argument at any
      type, at any larger bound. *)
  Definition domain_bounded_clo (b : nat) (ρ : env) (B : exp) : Prop :=
    forall b' c t d, b <= b' -> domain_bounded b' c -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ⦂ t ↘ d -> domain_bounded b' d.

  Lemma domain_bounded_pi_inv : forall b κd κc a ρ B, domain_bounded b (d_pi κd κc a ρ B) -> domain_bounded b a /\ domain_bounded_clo b ρ B.
  Proof.
    intros * H; split; [ intros v Hv; specialize (H v Hv); inversion H; assumption |].
    intros b' c t d Hb Hc Hd v Hv.
    specialize (H v ltac:(lia)); inversion_clear H.
    eapply eval_clo_avoids; [ eapply env_avoids_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.

  (** The same for a [Σₚ]. *)
  Lemma domain_bounded_and_inv : forall b a ρ Q, domain_bounded b (Σₚᵈ a ρ Q) -> domain_bounded b a /\ domain_bounded_clo b ρ Q.
  Proof.
    intros * H; split; [ intros v Hv; specialize (H v Hv); inversion H; assumption |].
    intros b' c t d Hb Hc Hd v Hv.
    specialize (H v ltac:(lia)); inversion_clear H.
    eapply eval_clo_avoids; [ eapply env_avoids_mono; [| eassumption ]; lia | eassumption | apply Hc; lia | exact Hd ].
  Qed.

  (** Ex falso: its type. *)
  Lemma domain_bounded_absurd_inv : forall b c p, domain_ne_bounded b (d_absurd c p) -> domain_bounded b c.
  Proof. intros * H v Hv; specialize (H v Hv); inversion H; assumption. Qed.

  (** ** Inductive Types

      An environment of bounded values, and a closure under [n] binders,
      evaluated at bounded values at any types. *)
  Definition env_domain_bounded (b : nat) (ρ : env) : Prop := forall v, b <= v -> env_avoids Θ Ξ v b None ρ.

  Definition domain_bounded_clon (b : nat) (ρ : env) (B : exp) (n : nat) : Prop :=
    forall b' vts d, b <= b' -> List.length vts = n -> (forall c, In c (List.map fst vts) -> domain_bounded b' c) ->
               ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ vts ↘ d -> domain_bounded b' d.

  (** A closure under [n] binders whose environment avoids the excluded
      level at every position its body reads, as the invariant states it. *)
  Definition domain_bounded_eclo (b : nat) (ρ : env) (B : exp) (n : nat) : Prop :=
    forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\ optional_exp_fresh (optional_shift n K) B.

  Lemma domain_bounded_eclo_clon : forall b ρ B n, domain_bounded_eclo b ρ B n -> domain_bounded_clon b ρ B n.
  Proof.
    intros * H b' vts d Hb Hl Hc Hd v Hv; destruct (H v ltac:(lia)) as (K & HK & HB).
    eapply (proj1 (eval_avoids Θ Ξ v b'));
      [ exact Hd | apply env_avoids_extend_typed; [ eapply env_avoids_mono; [| exact HK ]; lia | intros; apply Hc; [ assumption | lia ] ] |].
    rewrite Hl; exact HB.
  Qed.

  Lemma env_domain_bounded_nil : forall b, env_domain_bounded b nil.
  Proof. intros b v _; apply env_avoids_nil. Qed.

  Lemma env_domain_bounded_extend_typed : forall b ρ vts, env_domain_bounded b ρ -> (forall a, In a (List.map fst vts) -> domain_bounded b a) ->
      env_domain_bounded b (env_extend_typed ρ vts).
  Proof. intros * Hρ Ha v Hv; apply env_avoids_extend_typed_none; [ apply Hρ, Hv | intros; apply Ha; assumption ]. Qed.

  Lemma env_domain_bounded_tele : forall b ρ T vs, env_domain_bounded b ρ -> (forall a, In a vs -> domain_bounded b a) ->
      env_domain_bounded b (env_tele ρ T vs).
  Proof. intros * Hρ Ha v Hv; apply env_avoids_env_tele_none; [ apply Hρ, Hv | intros; apply Ha; assumption ]. Qed.

  Lemma env_domain_bounded_decl_env : forall b D ups, (forall a, In a ups -> domain_bounded b a) -> env_domain_bounded b (decl_env D ups).
  Proof. intros * Ha v Hv; apply env_avoids_decl_env; intros; apply Ha; assumption. Qed.

  Lemma env_domain_bounded_cons : forall b ρ d t, env_domain_bounded b ρ -> domain_bounded b d -> env_domain_bounded b (ρ ↦ d ⦂ t).
  Proof. intros * Hρ Hd v Hv; apply env_avoids_cons_none; [ apply Hρ, Hv | apply Hd, Hv ]. Qed.

  Lemma env_domain_bounded_mono : forall b b' ρ, b <= b' -> env_domain_bounded b ρ -> env_domain_bounded b' ρ.
  Proof. intros * Hb Hρ v Hv; eapply env_avoids_mono; [| apply Hρ ]; lia. Qed.

  Lemma eval_domain_bounded : forall M ρ a b, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> env_domain_bounded b ρ -> domain_bounded b a.
  Proof. intros * H Hρ v Hv; eapply (proj1 (eval_avoids Θ Ξ v b)); [ exact H | apply Hρ, Hv | exact I ]. Qed.

  (** The values of a list of terms. *)
  Lemma eval_exps_domain_bounded : forall Ms ρ bs b, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs -> env_domain_bounded b ρ ->
      forall a, In a bs -> domain_bounded b a.
  Proof.
    intros * H Hρ a Ha v Hv.
    exact (proj1 (proj2 (proj2 (eval_avoids Θ Ξ v b))) _ _ _ H None (Hρ v Hv) (proj2 (List.Forall_forall _ _) (fun _ _ => I)) _ Ha).
  Qed.

  Lemma domain_bounded_indty : forall b p k args, (forall a, In a args -> domain_bounded b a) -> domain_bounded b (d_ind p k args).
  Proof. intros * Ha v Hv; constructor; intros; apply Ha; assumption. Qed.

  Lemma domain_bounded_con : forall b p k c args, (forall a, In a args -> domain_bounded b a) -> domain_bounded b (d_con p k c args).
  Proof. intros * Ha v Hv; constructor; intros; apply Ha; assumption. Qed.

  Lemma domain_bounded_indty_inv : forall b p k args, domain_bounded b (d_ind p k args) -> forall a, In a args -> domain_bounded b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  Lemma domain_bounded_con_inv : forall b p k c args, domain_bounded b (d_con p k c args) -> forall a, In a args -> domain_bounded b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  (** Records: the arguments of a type former, the neutral a field is
      projected from, and a field of a bounded value. *)
  Lemma domain_bounded_record_inv : forall b p args, domain_bounded b (d_record p args) -> forall a, In a args -> domain_bounded b a.
  Proof. intros * H a Ha v Hv; specialize (H v Hv); inversion H; auto. Qed.

  Lemma domain_bounded_proj_inv : forall b g m, domain_ne_bounded b (d_proj g m) -> domain_ne_bounded b m.
  Proof. intros * H v Hv; specialize (H v Hv); inversion H; assumption. Qed.

  Lemma domain_bounded_proj : forall b g m r, eval_proj Θ Ξ g m r -> domain_bounded b m -> domain_bounded b r.
  Proof. intros * H Hm v Hv; exact (proj_avoids _ _ _ _ _ _ _ H (Hm v Hv)). Qed.

  (** The fields along a record view's path of a bounded value. *)
  Lemma projs_domain_bounded : forall b fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> domain_bounded b m -> forall a, In a ws -> domain_bounded b a.
  Proof. intros * H Hm a Ha v Hv; exact (projs_avoids _ _ _ _ _ _ _ H (Hm v Hv) a Ha). Qed.

  (** The blocks of an eliminator, closures in an environment that avoids
      the excluded level at every position they read. *)
  Definition domain_bounded_blocks (b : nat) (ρ : env) (Bks : list eblock) : Prop :=
    forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\ blocks_optional_exp_fresh K Bks.

  Lemma domain_bounded_blocks_motive : forall b ρ Bks bk, domain_bounded_blocks b ρ Bks -> In bk Bks -> domain_bounded_eclo b ρ (eb_motive bk) (eb_binder_count bk).
  Proof.
    intros * H Hin v Hv; destruct (H v Hv) as (K & HK & HB); exists K; split; [ exact HK | exact (proj1 (HB _ Hin)) ].
  Qed.

  Lemma domain_bounded_blocks_branch : forall b ρ Bks bk, domain_bounded_blocks b ρ Bks -> In bk Bks ->
      forall c n B, In (c, n, B) (eb_brs bk) -> domain_bounded_clon b ρ B n.
  Proof.
    intros * H Hin c n B HB b' vts d Hb Hl Hc Hd v Hv; destruct (H v ltac:(lia)) as (K & HK & HBk).
    eapply (proj1 (eval_avoids Θ Ξ v b')); [ exact Hd | apply env_avoids_extend_typed; [ eapply env_avoids_mono; [| exact HK ]; lia | intros; apply Hc; [ assumption | lia ] ] |].
    rewrite Hl; exact (proj2 (HBk _ Hin) _ _ _ HB).
  Qed.

  Lemma domain_bounded_blocks_mono : forall b b' ρ Bks, b <= b' -> domain_bounded_blocks b ρ Bks -> domain_bounded_blocks b' ρ Bks.
  Proof.
    intros * Hb H v Hv; destruct (H v ltac:(lia)) as (K & HK & HB); exists K; split; [ eapply env_avoids_mono; [| exact HK ]; lia | exact HB ].
  Qed.

  Lemma mref_domain_bounded : forall p ups j r b, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
      (forall u, In u ups -> domain_bounded b u) -> forall a, In a (snd r) -> domain_bounded b a.
  Proof. intros * H Hu a Ha v Hv; eapply mref_avoids; [ exact H | intros; apply Hu; assumption | exact Ha ]. Qed.

  Lemma domain_bounded_elim_inv : forall b ρ Bks p ups j args m,
      domain_ne_bounded b (d_elim ρ Bks p ups j args m) ->
      domain_ne_bounded b m /\ (forall a, In a args -> domain_bounded b a) /\ domain_bounded_blocks b ρ Bks /\
      (forall a, In a ups -> domain_bounded b a).
  Proof.
    intros * H; repeat split.
    - intros v Hv; specialize (H v Hv); inversion H; assumption.
    - intros a Ha v Hv; specialize (H v Hv); inversion H; auto.
    - intros v Hv; specialize (H v Hv); inversion_clear H; eexists; split; eassumption.
    - intros a Ha v Hv; specialize (H v Hv); inversion_clear H; eauto.
  Qed.

  (** The uniform parameters an eliminator carries, bounded. *)
  Definition ups_domain_bounded (b : nat) (ups : list domain) : Prop := forall a, In a ups -> domain_bounded b a.

  Lemma ups_domain_bounded_avoids : forall b ups, ups_domain_bounded b ups -> forall v, b <= v -> ups_avoids Θ Ξ v b ups.
  Proof. intros * H v Hv a Ha; exact (H a Ha v Hv). Qed.

  Lemma ups_domain_bounded_mono : forall b b' ups, b <= b' -> ups_domain_bounded b ups -> ups_domain_bounded b' ups.
  Proof. intros * Hb H a Ha; exact (domain_bounded_mono _ _ _ Hb (H a Ha)). Qed.

  (** The fresh variables of the telescopes of a declaration are above the
      readback length, and below the length past them. *)
  Lemma fresh_tele_domain_bounded : forall ρ T s ns, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ns -> env_domain_bounded s ρ ->
      forall a, In a ns -> domain_bounded (s + List.length T) a.
  Proof.
    induction 1; intros Hρ; [ intros ? [] |].
    assert (Ha : domain_bounded s a) by (eapply eval_domain_bounded; eassumption).
    cbn [List.length]; replace (s + S (List.length T)) with (S s + List.length T) by lia.
    intros d [<- | Hd].
    - apply domain_bounded_fresh; [ lia | exact Ha ].
    - apply IHfresh_tele; [| exact Hd ]. apply env_domain_bounded_cons; [ eapply env_domain_bounded_mono; [| exact Hρ ]; lia | apply domain_bounded_fresh; [ lia | exact Ha ] ].
  Qed.

  Lemma shape_type_domain_bounded : forall p ups ρ t a b, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      env_domain_bounded b ρ -> (forall u, In u ups -> domain_bounded b u) -> domain_bounded b a.
  Proof.
    intros * H Hρ Hu v Hv; eapply shape_type_avoids; [ exact H | apply Hρ, Hv | apply optional_ptyp_fresh_none | intros; apply Hu; assumption ].
  Qed.

  Lemma fresh_cargs_domain_bounded : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      env_domain_bounded s ρ -> (forall a, In a ups -> domain_bounded s a) ->
      forall a, In a vs -> domain_bounded (s + List.length gs) a.
  Proof.
    induction 1; intros Hρ Hu.
    - intros ? [].
    - assert (Ha : domain_bounded s a) by (eapply eval_domain_bounded; eassumption).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      intros d [<- | Hd]; [ apply domain_bounded_fresh; [ lia | exact Ha ] |].
      apply IHfresh_cargs;
        [ apply env_domain_bounded_cons; [ eapply env_domain_bounded_mono; [| exact Hρ ]; lia | apply domain_bounded_fresh; [ lia | exact Ha ] ]
        | intros; eapply domain_bounded_mono; [| apply Hu; eassumption ]; lia | exact Hd ].
    - assert (Ha : domain_bounded s a) by (eapply shape_type_domain_bounded; eassumption).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      intros d [<- | Hd]; [ apply domain_bounded_fresh; [ lia | exact Ha ] |].
      apply IHfresh_cargs;
        [ eapply env_domain_bounded_mono; [| exact Hρ ]; lia | intros; eapply domain_bounded_mono; [| apply Hu; eassumption ]; lia | exact Hd ].
  Qed.

  (** The fresh variables along the leaf paths of the container's: one
      above the other, from [s] on. *)
  Lemma fresh_leaf_vars_domain_bounded : forall bs as' s vs, fresh_leaf_vars bs as' s vs ->
      (forall a, In a as' -> domain_bounded s a) -> forall a, In a vs -> domain_bounded (s + List.length vs) a.
  Proof.
    induction 1; intros Ha; [ apply all_in_nil | | ].
    - cbn [List.length]; replace (s + S (List.length vs)) with (S s + List.length vs) by lia.
      apply all_in_cons; [ apply domain_bounded_fresh; [ lia | exact (all_in_head _ _ _ Ha) ] |].
      apply IHfresh_leaf_vars; intros; eapply domain_bounded_mono; [| apply Ha; right; eassumption ]; lia.
    - apply IHfresh_leaf_vars; exact (all_in_tail _ _ _ Ha).
  Qed.

  (** The recursive results of a branch, fresh variables above the
      readback length [s], as many as there are; their types are the
      motives [As] in [ρ], which avoid the excluded level wherever the
      recursive arguments' shapes end ([ends_fresh]). *)
  Lemma fresh_ihs_domain_bounded : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall b, b <= s -> env_domain_bounded s ρa -> ups_domain_bounded s ups ->
      (forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\
                              forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh Θ Ξ p K As t) ->
      (forall a, In a vs -> domain_bounded s a) ->
      forall a, In a ihs -> domain_bounded (s + List.length ihs) a.
  Proof.
    induction 1; intros b0 Hb Hρa Hu Hl Hvs.
    - apply all_in_nil.
    - apply (IHfresh_ihs b0); try assumption.
      + apply env_domain_bounded_cons; [ exact Hρa | exact (all_in_head _ _ _ Hvs) ].
      + intros w Hw; destruct (Hl w Hw) as (K & HK & HK'); exists K; split; [ exact HK |].
        intros gs1 t gs2 E; eapply (HK' (ca_arg _ _ :: gs1) t gs2); rewrite E; reflexivity.
      + exact (all_in_tail _ _ _ Hvs).
    - assert (Has : forall a, In a as' -> domain_bounded s a).
      { intros a Ha w Hw; destruct (Hl w ltac:(lia)) as (K & HK & HK').
        eapply ihty_avoids; [ eassumption | eapply env_avoids_mono; [| exact HK ]; lia | exact (HK' nil t gs eq_refl)
                        | exact (ups_domain_bounded_avoids _ _ Hu _ Hw) | exact (Hρa w Hw) | apply optional_ptyp_fresh_none
                        | exact (all_in_head _ _ _ Hvs w Hw) | exact Ha ]. }
      match goal with Hf : fresh_leaf_vars _ _ _ _ |- _ => pose proof (fresh_leaf_vars_domain_bounded _ _ _ _ Hf Has) as Hfl end.
      rewrite List.length_app; apply all_in_app.
      + intros a Ha; eapply domain_bounded_mono; [| exact (Hfl a Ha) ]; lia.
      + assert (Hr : forall a, In a ihs -> domain_bounded (List.length ihs1 + s + List.length ihs) a).
        { apply (IHfresh_ihs b0);
            [ lia | eapply env_domain_bounded_mono; [| exact Hρa ]; lia | eapply ups_domain_bounded_mono; [| exact Hu ]; lia
            | | intros; eapply domain_bounded_mono; [| apply Hvs; right; eassumption ]; lia ].
          intros w Hw; destruct (Hl w Hw) as (K & HK & HK'); exists K; split; [ exact HK |].
          intros gs1 t0 gs2 E; apply (HK' (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity. }
        intros a Ha; eapply domain_bounded_mono; [| exact (Hr a Ha) ]; lia.
    - apply (IHfresh_ihs b0); try assumption.
      + intros w Hw; destruct (Hl w Hw) as (K & HK & HK'); exists K; split; [ exact HK |].
        intros gs1 t0 gs2 E; apply (HK' (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity.
      + exact (all_in_tail _ _ _ Hvs).
  Qed.

  (** The motives at the recursive arguments of the eliminator's group, from
      the blocks: their shapes end where the motives avoid the excluded
      level. *)
  Lemma ihs_motives_domain_bounded : forall p D Bks b ρ gs, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
      cargs_params_length D gs -> blocks_binder_count_at D None Bks -> domain_bounded_blocks b ρ Bks ->
      forall v, b <= v -> exists K, env_avoids Θ Ξ v b K ρ /\
                              forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh Θ Ξ p K (blocks_motives Bks) t.
  Proof.
    intros * HD Har Hpl Hnm HB v Hv; destruct (HB v Hv) as (K & HK & HBk); exists K; split; [ exact HK |].
    exact (cargs_ends_fresh _ _ _ _ _ _ _ HD Har Hnm HBk Hpl).
  Qed.

  (** The recursive results a branch is read under. *)
  Lemma wrap_ihs_eval_domain_bounded : forall ρ p ups Bks Dc gs' gs vs ihs r b,
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
      domain_bounded_blocks b ρ Bks -> ups_domain_bounded b ups -> (forall a, In a vs -> domain_bounded b a) -> (forall a, In a ihs -> domain_bounded b a) ->
      forall a, In a r -> domain_bounded b a.
  Proof.
    intros * H HB Ho Hv Hi a Ha w Hw; destruct (HB w Hw) as (K & HK & HBk).
    eapply wrap_ihs_eval_avoids; [ exact H | exact HK | exact HBk | exact (ups_domain_bounded_avoids _ _ Ho _ Hw)
                             | intros; apply Hv; assumption | intros; apply Hi; assumption | exact Ha ].
  Qed.

  (** The motive of a block of a stuck eliminator read back, at the fresh
      non-uniform parameters and scrutinee past the readback length. *)
  Lemma motive_domain_bounded : forall ρ A D Mv ups pre hd k Mi s ns a b,
      Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns -> im_nn Mv = im_nn Mi ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns))
                                     (⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mi))) ↘ a ->
      b <= s -> domain_bounded_eclo b ρ A (S (im_nn Mi)) ->
      ups_domain_bounded s ups -> (forall x, In x pre -> domain_bounded s x) ->
      domain_bounded (S (s + im_nn Mi)) a.
  Proof.
    intros * F Hnn e Hb HA Hu Hp.
    pose proof (fresh_tele_length _ _ _ _ F) as Hl; rewrite List.length_rev in Hl.
    change (List.length (im_nparams Mv)) with (im_nn Mv) in Hl; rewrite Hnn in Hl.
    pose proof (fresh_tele_domain_bounded _ _ _ _ F (env_domain_bounded_decl_env _ _ _ Hu)) as Hns.
    rewrite List.length_rev in Hns; change (List.length (im_nparams Mv)) with (im_nn Mv) in Hns; rewrite Hnn in Hns.
    eapply (domain_bounded_eclo_clon _ _ _ _ HA); [ lia | | | exact e ].
    - rewrite <- (List.length_map fst); unfold motive_entries; rewrite List.map_app, tele_entries_values, List.length_app, Hl.
      cbn; lia.
    - unfold motive_entries; rewrite List.map_app, tele_entries_values; cbn [List.map fst].
      apply all_in_app; [ intros; eapply domain_bounded_mono; [| apply Hns; eassumption ]; lia |].
      apply all_in_cons; [| apply all_in_nil ].
      apply domain_bounded_fresh; [ lia |]; apply domain_bounded_indty, all_in_app;
        [ intros; eapply domain_bounded_mono; [| apply Hp; eassumption ]; lia | exact Hns ].
  Qed.

  (** A branch of a block of a stuck eliminator read back, and the motive's
      instance it is read at, under the fresh variables of the group read,
      as many as the branch binds. *)
  Lemma branch_domain_bounded : forall ρ p ups Bks Dc A B pre hd k c Mi Mv D gs' gs s n0 ns vs ihs wihs bv t,
      Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
      Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮
        (s + im_nn Mi + List.length gs') ↘ ihs ->
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs) ↘ bv ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) (d_con hd k c (pre ++ ns ++ vs))) ↘ t ->
      ind_lookup Θ Ξ p = Some D ->
      n0 = (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat -> im_nn Mv = im_nn Mi ->
      cargs_container_count D Dc gs' gs = cargs_nrec Dc gs' ->
      cargs_params_length D gs -> blocks_binder_count_at D None Bks -> rview_leaf_arity D ->
      domain_bounded_blocks s ρ Bks -> ups_domain_bounded s ups ->
      domain_bounded_eclo s ρ A (S (im_nn Mi)) -> domain_bounded_clon s ρ B n0 ->
      (forall x, In x pre -> domain_bounded s x) ->
      domain_bounded (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) t /\
      domain_bounded (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) bv.
  Proof.
    intros * F F0 F2 Fw e0 e1 HD Hn0 Hnn Hcnt Hpl Hnm Har HBd Hu HA HB Hp.
    set (n := (im_nn Mi + List.length gs' + cargs_nrec Dc gs')%nat).
    pose proof (fresh_tele_length _ _ _ _ F) as Hl1; rewrite List.length_rev in Hl1.
    change (List.length (im_nparams Mv)) with (im_nn Mv) in Hl1; rewrite Hnn in Hl1.
    pose proof (fresh_cargs_length _ _ _ _ _ _ F0) as Hl2.
    destruct (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ _ _ HD (leaves_coherent_of_order _ (rview_leaf_order _ Har)) Fw)
      as [Hl3 Hl4].
    pose proof (fresh_ihs_length _ _ _ _ _ _ _ _ _ _ _ _ HD F2) as Hl5; rewrite Hcnt in Hl5.
    assert (Hgl : List.length gs = List.length gs') by congruence.
    pose proof (fresh_tele_domain_bounded _ _ _ _ F (env_domain_bounded_decl_env _ _ _ Hu)) as Hns.
    rewrite List.length_rev in Hns; change (List.length (im_nparams Mv)) with (im_nn Mv) in Hns; rewrite Hnn in Hns.
    assert (Hρa : env_domain_bounded (s + im_nn Mi) (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns)).
    { apply env_domain_bounded_tele; [ eapply env_domain_bounded_mono; [| exact (env_domain_bounded_decl_env _ _ _ Hu) ]; lia | exact Hns ]. }
    pose proof (fresh_cargs_domain_bounded _ _ _ _ _ _ F0 Hρa
                  ltac:(intros; eapply domain_bounded_mono; [| apply Hu; eassumption ]; lia)) as Hvs.
    rewrite Hgl in Hvs.
    pose proof (fresh_ihs_domain_bounded _ _ _ _ _ _ _ _ _ _ _ F2 s ltac:(lia)
                  ltac:(eapply env_domain_bounded_mono; [| exact Hρa ]; lia)
                  ltac:(intros ? ?; eapply domain_bounded_mono; [| apply Hu; eassumption ]; lia)
                  (ihs_motives_domain_bounded _ _ _ _ _ _ HD Har Hpl Hnm HBd) Hvs) as Hihs.
    rewrite Hl5 in Hihs.
    assert (Hw : forall x, In x wihs -> domain_bounded (s + n) x).
    { eapply wrap_ihs_eval_domain_bounded; [ exact Fw | eapply domain_bounded_blocks_mono; [| exact HBd ]; unfold n; lia
                                          | eapply ups_domain_bounded_mono; [| exact Hu ]; unfold n; lia
                                          | intros; eapply domain_bounded_mono; [| apply Hvs; eassumption ]; unfold n; lia
                                          | intros; eapply domain_bounded_mono; [| apply Hihs; eassumption ]; unfold n; lia ]. }
    split.
    - eapply (domain_bounded_eclo_clon _ _ _ _ HA); [ unfold n; lia | | | exact e1 ].
      + rewrite <- (List.length_map fst); unfold motive_entries; rewrite List.map_app, tele_entries_values, List.length_app, Hl1.
        cbn; lia.
      + unfold motive_entries; rewrite List.map_app, tele_entries_values; cbn [List.map fst].
        apply all_in_app; [ intros; eapply domain_bounded_mono; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_cons; [| apply all_in_nil ].
        apply domain_bounded_con, all_in_app; [ intros; eapply domain_bounded_mono; [| apply Hp; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply domain_bounded_mono; [| apply Hns; eassumption ]; unfold n; lia
                          | intros; eapply domain_bounded_mono; [| apply Hvs; eassumption ]; unfold n; lia ].
    - eapply HB; [ unfold n; lia | | | exact e0 ].
      + rewrite <- (List.length_map fst); unfold branch_entries; cbv zeta.
        rewrite !List.map_app, tele_entries_values, cargs_entries_values, pair_values_with_types_values.
        rewrite !List.length_app, Hl1, Hl2, Hgl, Hl3; lia.
      + unfold branch_entries; cbv zeta; rewrite !List.map_app, tele_entries_values, cargs_entries_values, pair_values_with_types_values.
        apply all_in_app; [ intros; eapply domain_bounded_mono; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply domain_bounded_mono; [| apply Hvs; eassumption ]; unfold n; lia | exact Hw ].
  Qed.

(** The bound of a value built during readback: by its constructor, by
    monotonicity, or by the evaluation it came from. *)
Ltac domain_bounded_solve :=
  first [ eassumption
        | apply domain_nf_bounded_dom; domain_bounded_solve
        | apply domain_bounded_fresh; [ lia | domain_bounded_solve ]
        | apply domain_bounded_bot | apply domain_bounded_level
        | match goal with
          | Hc : domain_bounded_clo ?b ?ρ ?B, e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↦ ?c ⦂ ?t ↘ ?d |- domain_bounded ?b' ?d =>
              apply (Hc b' c t d); [ lia | domain_bounded_solve | exact e ]
          | e : $| ?m & ?n | _ ⍮ _ ↘ ?r |- domain_bounded ?b ?r => apply (domain_bounded_app b m n r e); domain_bounded_solve
          | H : domain_bounded ?b0 ?d |- domain_bounded ?b ?d => apply (domain_bounded_mono b0 b d); [ lia | exact H ]
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

(** The same, at lengths given up to arithmetic. *)
Lemma rn_ok_add : forall n f s s' φ a b, rn_ok f s s' φ -> a = n + s -> b = n + s' -> rn_ok f a b (wk_qn n φ).
Proof. intros * H -> ->; apply rn_ok_qn, H. Qed.

  Variable (f : nat -> nat).

  Lemma eval_clo_rn : forall B ρ c t d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ⦂ t ↘ d -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_rename f ρ ↦ domain_rename f c ⦂ entry_type_rename f t ↘ domain_rename f d.
  Proof. intros * H; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

  Lemma app_rn : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> $| domain_rename f m & domain_rename f n | Θ ⍮ Ξ ↘ domain_rename f r.
  Proof. intros * H; exact (proj1 (proj2 (eval_rn Θ Ξ f)) _ _ _ H). Qed.

  Lemma eval_extend_typed_rn : forall B ρ vts d,
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ vts ↘ d ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed (env_rename f ρ) (List.map (typed_rename f) vts) ↘ domain_rename f d.
  Proof. intros * H; rewrite <- env_extend_typed_rn; exact (proj1 (eval_rn Θ Ξ f) _ _ _ H). Qed.

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
    cbn [env_rename List.map dentry_rename extend_env entry_type_rename domain_rename domain_ne_rename] in IH.
    rewrite (Hf s) in IH by lia; replace (s + (s' - s)) with s' in IH by lia; exact IH.
  Qed.

  Lemma shape_type_rn : forall p ups ρ t a,
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
      cbn [env_rename List.map dentry_rename extend_env entry_type_rename domain_rename domain_ne_rename] in IH.
      rewrite (Hf s) in IH by lia; replace (s + (s' - s)) with s' in IH by lia; exact IH.
    - cbn [domain_rename domain_ne_rename]; rewrite (Hf s) by lia; replace (s + (s' - s)) with s' by lia.
      constructor; [ exact (shape_type_rn _ _ _ _ _ H) |].
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
      cbn [env_rename List.map dentry_rename extend_env entry_type_rename] in IH |- *; exact IH.
    - rewrite List.map_app; econstructor;
        [ eassumption | exact (ihty_rn _ _ _ _ _ _ _ _ H0) | exact (fresh_leaf_vars_rn _ _ _ _ H1 s' Hf Hs) |].
      rewrite List.length_map; apply (IHfresh_ihs (List.length ihs1 + s')); [ intros; rewrite Hf by lia; lia | lia ].
    - apply fresh_ihs_nest; exact (IHfresh_ihs s' Hf Hs).
  Qed.

  (** The steps of [read_rn].  The lengths a renaming relates: the base
      ones, and those under [n] more binders. *)
  Ltac rn_ok_solve :=
    match goal with
    | Hok : rn_ok f ?s ?s' ?φ |- rn_ok f _ _ _ =>
        first [ exact Hok | apply rn_ok_q; exact Hok | apply rn_ok_q, rn_ok_q; exact Hok
              | match goal with |- rn_ok f _ _ (wk_qn ?n _) => apply (rn_ok_add n _ _ _ _ _ _ Hok); lia end ]
    end.

  (** The side conditions of an induction hypothesis: the lengths, and the
      bounds of the original's parts. *)
  Ltac rn_side :=
    first [ rn_ok_solve
          | assumption
          | progress cbn [fst snd]; rn_side
          | exact (env_domain_bounded_nil _)
          | match goal with |- im_nn ?Mv = im_nn ?Mi =>
              match goal with
              | Hnm : forall D, ind_lookup _ _ ?p = Some D -> blocks_binder_count_at D None _,
                Hl : ind_lookup _ _ ?p = Some ?D, Hv : ind_member ?D _ = Some Mv, Hb : List.nth_error _ _ = Some ?bk,
                Hc : eb_binder_count ?bk = S (im_nn Mi) |- _ =>
                  let Hx := fresh in pose proof (Hnm _ Hl _ _ _ Hv Hb) as Hx; congruence
              end end
          | match goal with
            | Hb : List.nth_error ?Bks _ = Some ?bk, HB : domain_bounded_blocks _ _ ?Bks, Hc : eb_binder_count ?bk = ?n
              |- domain_bounded_eclo _ _ (eb_motive ?bk) ?n =>
                rewrite <- Hc; exact (domain_bounded_blocks_motive _ _ _ _ HB (List.nth_error_In _ _ Hb))
            end
          | match goal with
            | Hb : List.nth_error ?Bks _ = Some ?bk, HB : domain_bounded_blocks _ _ ?Bks
              |- forall c n B, In (c, n, B) (eb_brs ?bk) -> _ =>
                exact (domain_bounded_blocks_branch _ _ _ _ HB (List.nth_error_In _ _ Hb))
            end
          | match goal with
            | HBs : forall c n B, In (c, n, B) ((?c0, ?n0, ?B0) :: _) -> domain_bounded_clon ?b ?ρ B n
              |- domain_bounded_clon ?b ?ρ ?B0 ?n0 => exact (HBs _ _ _ (or_introl eq_refl))
            | HBs : forall c n B, In (c, n, B) (_ :: ?Bs) -> domain_bounded_clon ?b ?ρ B n
              |- forall c n B, In (c, n, B) ?Bs -> domain_bounded_clon ?b ?ρ B n =>
                let c := fresh in let n := fresh in let B := fresh in let Hin := fresh in
                intros c n B Hin; exact (HBs _ _ _ (or_intror Hin))
            end
          | match goal with |- domain_bounded (S (?s + im_nn ?Mi)) ?a =>
              solve [ eapply (motive_domain_bounded _ _ _ _ _ _ _ _ _ _ _ _ s);
                      [ eassumption | rn_side | eassumption | lia | rn_side | rn_side | rn_side ] ]
            end
          | solve [ eapply proj1, branch_domain_bounded; first [ eassumption | reflexivity | rn_side ] ]
          | solve [ eapply proj2, branch_domain_bounded; first [ eassumption | reflexivity | rn_side ] ]
          | solve [ all_in_with assumption ]
          | match goal with H : forall a, In a (?x :: _) -> ?P a |- ?P ?x => apply H; left; reflexivity end
          | apply domain_nf_bounded_dom; rn_side
          | apply env_domain_bounded_cons; rn_side
          | apply env_domain_bounded_tele; rn_side
          | apply env_domain_bounded_decl_env; rn_side
          | apply env_domain_bounded_extend_typed; rn_side
          | solve [ eapply eval_domain_bounded; [ eassumption | rn_side ] ]
          | solve [ eapply projs_domain_bounded; [ eassumption | rn_side ] ]
          | solve [ eapply eval_exps_domain_bounded; [ eassumption | rn_side ] ]
          | solve [ eapply domain_bounded_proj; [ eassumption | rn_side ] ]
          | apply domain_bounded_indty; rn_side
          | apply domain_bounded_con; rn_side
          | apply all_in_app; rn_side
          | apply domain_bounded_fresh; [ lia | rn_side ]
          | solve [ eapply domain_bounded_app; [ eassumption | rn_side | rn_side ] ]
          | solve [ eapply env_domain_bounded_mono; [| eassumption ]; lia ]
          | solve [ eapply domain_bounded_mono; [| eassumption ]; lia ]
          | solve [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
                    match goal with H : forall a, In a ?l -> domain_bounded ?b0 a, Ha : In a ?l |- domain_bounded ?b a =>
                      apply (domain_bounded_mono b0 b a); [ lia | exact (H a Ha) ] end ]
          | match goal with e : eval_mref _ _ _ _ _ (_, _, ?pre) |- forall a, In a ?pre -> _ =>
              exact (mref_domain_bounded _ _ _ _ _ e ltac:(rn_side)) end
          | domain_bounded_solve
          | let D' := fresh "D" in let HD := fresh "HD" in
            intros D' HD;
            match goal with He : ind_lookup _ _ _ = Some _ |- _ => rewrite He in HD; injection HD as <-; assumption end ].

  (** Each readback of a renamed part, given to the induction hypothesis of
      the original part: an equation between the erasures. *)
  Ltac rn_feed :=
    repeat match goal with
      | IH : forall s0 φ0 W0, _ -> rn_ok f _ s0 φ0 -> _, Hr : _ |- _ =>
          let E := fresh "E" in
          epose proof (IH _ _ _ Hr) as E;
          let rec discharge :=
            lazymatch type of E with
            | ?P -> _ => let H := fresh in eassert (H : P) by rn_side; specialize (E H); clear H; discharge
            | _ => idtac
            end in
          discharge; clear Hr IH
      end.

  (** From a length past the base one on, the renaming is the shift to the
      corresponding other length. *)
  Ltac rn_shift_solve :=
    match goal with
    | Hok : rn_ok f ?s ?s' _ |- forall x, _ <= x -> f x = _ =>
        let x := fresh "x" in let Hx := fresh "Hx" in
        intros x Hx; pose proof (rn_le _ _ _ _ Hok); rewrite (rn_above _ _ _ _ Hok x) by lia; lia
    end.

  Ltac rn_le_solve := match goal with Hok : rn_ok f _ _ _ |- _ => pose proof (rn_le _ _ _ _ Hok); lia end.

  (** A renamed value's readback by a rule its type's kind excludes: the
      renaming keeps the kind. *)
  Ltac rn_kind_contra :=
    exfalso;
    repeat match goal with
      | H : ?X = domain_rename f ?a, H' : context [ domain_kind ?a ] |- _ =>
          rewrite <- (domain_kind_rn f a), <- H in H'
      | H : context [ domain_kind (d_neut (domain_rename f ?a) (domain_ne_rename f ?b)) ] |- _ =>
          rewrite (domain_kind_neut_rn f a (domain_ne_rename f b) b) in H
      | H : context [ domain_kind (domain_rename f ?a) ] |- _ => rewrite domain_kind_rn in H
      end;
    cbn [domain_kind] in *;
    first [ congruence
          | match goal with H : evaluated_kind ?k, H' : ?k = ak_propositional |- _ =>
              exact (evaluated_kind_not_propositional _ H H') end
          | match goal with H : evaluated_kind ak_propositional |- _ => inversion H end ].

  (** Readback is equivariant up to erasure: if a value and its renaming
      both read back, at the two lengths, the second readback is the
      weakening of the first, but for the proofs.  The bound does not reach
      into the environment of a kept proof ([domain_avoids_proof]), whose
      entries its readback reads ([read_proof_kept]): for [⋆ᵈ⟨M, ρ⟩] the
      bound says nothing of [ρ], so the renamed proof's readback cannot be
      built from the original's, and is given instead; the two are compared
      erased, both [⋆ⁿ], and the proofs' clauses state nothing. *)
  Lemma read_rn :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall s' φ W', Rnf domain_nf_rename f m in Θ ⍮ Ξ ⍮ s' ↘ W' -> rn_ok f s s' φ -> domain_nf_bounded s m ->
       nf_erase W' = nf_erase (nf_wk φ W)) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall s' φ M', Rne domain_ne_rename f m in Θ ⍮ Ξ ⍮ s' ↘ M' -> rn_ok f s s' φ -> domain_ne_bounded s m ->
       ne_erase M' = ne_erase (ne_wk φ M)) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall s' φ A', Rtyp domain_rename f a in Θ ⍮ Ξ ⍮ s' ↘ A' -> rn_ok f s s' φ -> domain_bounded s a ->
       nf_erase A' = nf_erase (nf_wk φ A)) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall s' φ ys', Rla level_atoms_rename f xs in Θ ⍮ Ξ ⍮ s' ↘ ys' -> rn_ok f s s' φ -> level_atoms_bounded s xs ->
       List.map (map_level_atom ne_erase) ys' = List.map (map_level_atom ne_erase) (List.map (map_level_atom (ne_wk φ)) ys)) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall s' φ Ms', Rps List.map (domain_rename f) vs at T in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ Ms' ->
       rn_ok f s s' φ -> env_domain_bounded s ρ -> (forall a, In a vs -> domain_bounded s a) ->
       List.map nf_erase Ms' = List.map nf_erase (List.map (nf_wk φ) Ms)) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall s' φ Ms', Rcargs List.map (domain_rename f) vs at gs of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ Ms' ->
       rn_ok f s s' φ -> (forall a, In a ups -> domain_bounded s a) -> env_domain_bounded s ρ ->
       (forall a, In a vs -> domain_bounded s a) ->
       List.map nf_erase Ms' = List.map nf_erase (List.map (nf_wk φ) Ms)) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       forall s' φ X', Rsh domain_rename f x at t of p (List.map (domain_rename f) ups) in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ X' ->
       rn_ok f s s' φ -> (forall a, In a ups -> domain_bounded s a) -> env_domain_bounded s ρ -> domain_bounded s x ->
       nf_erase X' = nf_erase (nf_wk φ X)) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       forall s' φ NBks', Rblks i Ms of Dc from p (List.map (domain_rename f) ups) Bks sel in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ NBks' ->
       rn_ok f s s' φ -> domain_bounded_blocks s ρ Bks ->
       (forall D, ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks) ->
       (forall D, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D) -> (forall a, In a ups -> domain_bounded s a) ->
       List.map (map_normal_block (fun _ => nf_erase)) NBks'
       = List.map (map_normal_block (fun _ => nf_erase)) (List.map (map_normal_block (fun n => nf_wk (wk_qn n φ))) NBks)) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall s' φ Bs'',
       Rbrs Bs at cs of Mi (fst (fst r), snd (fst r), List.map (domain_rename f) (snd r)) of Dc from p (List.map (domain_rename f) ups)
         Bks Mv A in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ Bs'' ->
       rn_ok f s s' φ -> domain_bounded_blocks s ρ Bks ->
       (forall D, ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks) ->
       (forall D, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D) -> im_nn Mv = im_nn Mi ->
       domain_bounded_eclo s ρ A (S (im_nn Mi)) ->
       (forall c n B, In (c, n, B) Bs -> domain_bounded_clon s ρ B n) -> (forall a, In a ups -> domain_bounded s a) ->
       (forall a, In a (snd r) -> domain_bounded s a) ->
       List.map (map_normal_branch (fun _ => nf_erase)) Bs''
       = List.map (map_normal_branch (fun _ => nf_erase)) (List.map (map_normal_branch (fun n => nf_wk (wk_qn n φ))) Bs')) /\
    (forall s ρ fl d Fs, Rflds d at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       forall s' φ Fs', Rflds domain_rename f d at fl in Θ ⍮ Ξ ⍮ env_rename f ρ ⍮ s' ↘ Fs' ->
       rn_ok f s s' φ -> env_domain_bounded s ρ -> domain_bounded s d ->
       List.map nf_erase Fs' = List.map nf_erase (List.map (nf_wk φ) Fs)) /\
    (forall s m M, Rprf m in Θ ⍮ Ξ ⍮ s ↘ M -> True) /\
    (forall s ρ k bs, Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs -> True) /\
    (forall s e b, Rent e in Θ ⍮ Ξ ⍮ s ↘ b -> True).
  Proof.
    apply read_mut_ind; intros; try exact I.
    (** The readback of the renamed value, inverted. *)
    all: match goal with H : rn_ok f _ _ _ |- _ => rename H into Hok end.
    all: match goal with
         | H : ?P |- _ =>
             lazymatch P with
             | forall _, _ => fail
             | rn_ok _ _ _ _ => fail
             | context [ f ] => rename H into Hrd
             end
         end.
    all: cbn [domain_nf_rename] in Hrd; rewrite ?domain_rename_lvl, ?level_atoms_rename_cons, ?level_atoms_rename_nil in Hrd;
      cbn [domain_rename domain_ne_rename dmod_rename dentry_rename List.map fst snd entry_type_rename] in Hrd.
    all: inversion Hrd; subst; clear Hrd.
    (** Two proofs: erased alike. *)
    all: try solve [ cbn [nf_erase nf_wk]; reflexivity ].
    (** A rule the original's excludes by the relevance of the type, which
        the renaming keeps. *)
    all: try solve [ rn_kind_contra ].
    (** The renamings of the original's evaluations, with the renaming
        pushed to the values, as the inverted premises have it. *)
    all: pose proof (rn_ok_fresh _ _ _ _ Hok) as Hf0; pose proof (rn_ok_fresh _ _ _ _ (rn_ok_q _ _ _ _ Hok)) as Hf1.
    all: on_all_hyp: fun H => tryif (match type of H with context [ f ] => idtac end) then idtac else
           match type of H with
           | ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ => let H' := fresh "Er" in pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H) as H'
           | $| _ & _ | _ ⍮ _ ↘ _ => let H' := fresh "Er" in pose proof (app_rn _ _ _ H) as H'
           | ⟦ _ ⟧* _ ⍮ _ ⍮ _ ↘ _ => let H' := fresh "Er" in pose proof (proj1 (proj2 (proj2 (eval_rn Θ Ξ f))) _ _ _ H) as H'
           | eval_proj _ _ _ _ _ => let H' := fresh "Er" in pose proof (proj_rn _ _ _ H) as H'
           | eval_projs _ _ _ _ _ => let H' := fresh "Er" in pose proof (projs_rn _ _ _ H) as H'
           | eval_mref _ _ _ _ _ (_, _, _) => let H' := fresh "Er" in pose proof (mref_rn _ _ _ _ _ _ H) as H'
           | _ => idtac
           end.
    all: rewrite <- ?List.skipn_map, <- ?List.firstn_map, ?List.map_app, ?env_tele_rn, ?env_extend_typed_rn, ?tele_entries_rn,
      ?motive_entries_rn, ?branch_entries_rn, ?decl_env_rn, ?cargs_entries_rn, ?env_rename_extend_env in *.
    all: unfold env_rename in *; cbn [domain_nf_rename domain_rename domain_ne_rename entry_type_rename dentry_rename List.map] in *.
    all: rewrite <- ?List.skipn_map, <- ?List.firstn_map, ?List.map_app in *.
    all: rewrite ?Hf0, ?Hf1 in *; clear Hf0 Hf1.
    (** The fresh levels past the readback length, renamed: shifted to the
        other length. *)
    all: repeat match goal with
      | Hok : rn_ok f ?s ?s' _, H : context [ f (?s + ?n + ?m) ] |- _ =>
          let E := fresh "E" in
          assert (E : f (s + n + m) = s' + n + m)
            by (pose proof (rn_le _ _ _ _ Hok); rewrite (rn_above _ _ _ _ Hok) by lia; lia);
          rewrite E in H; clear E
      | Hok : rn_ok f ?s ?s' _, H : context [ f (?s + ?n) ] |- _ =>
          let E := fresh "E" in
          assert (E : f (s + n) = s' + n)
            by (pose proof (rn_le _ _ _ _ Hok); rewrite (rn_above _ _ _ _ Hok) by lia; lia);
          rewrite E in H; clear E
      end.
    all: try functional_fresh_rewrite_clear; functional_eval_rewrite_clear.
    (** The fresh variables of the renamed readback: the renamings of the
        original's. *)
    all: on_all_hyp: fun F => tryif (match type of F with context [ f ] => idtac end) then idtac else
           match type of F with
           | fresh_tele _ _ _ ?T ?a _ =>
               match goal with F' : fresh_tele _ _ _ T ?a' _ |- _ =>
                 lazymatch type of F' with context [ f ] => idtac end;
                 let H := fresh "Fr" in
                 pose proof (fresh_tele_rn _ _ _ _ F a' ltac:(rn_shift_solve) ltac:(rn_le_solve)) as H
               end
           | fresh_cargs _ _ _ _ _ ?gs ?a _ =>
               match goal with F' : fresh_cargs _ _ _ _ _ gs ?a' _ |- _ =>
                 lazymatch type of F' with context [ f ] => idtac end;
                 let H := fresh "Fr" in
                 pose proof (fresh_cargs_rn _ _ _ _ _ _ F a' ltac:(rn_shift_solve) ltac:(rn_le_solve)) as H
               end
           | fresh_ihs _ _ _ _ _ _ _ _ ?gs' ?gs _ ?a _ =>
               match goal with F' : fresh_ihs _ _ _ _ _ _ _ _ gs' gs _ ?a' _ |- _ =>
                 lazymatch type of F' with context [ f ] => idtac end;
                 let H := fresh "Fr" in
                 pose proof (fresh_ihs_rn _ _ _ _ _ _ _ _ _ _ _ F a' ltac:(rn_shift_solve) ltac:(rn_le_solve)) as H
               end
           | wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ _ =>
               let H := fresh "Fr" in pose proof (wrap_ihs_eval_rn _ _ _ _ _ _ _ _ _ _ F) as H
           | _ => idtac
           end.
    all: rewrite ?env_tele_rn, ?env_extend_typed_rn, ?tele_entries_rn, ?decl_env_rn, ?List.map_app in *.
    all: unfold env_rename in *; cbn [domain_rename domain_ne_rename entry_type_rename dentry_rename List.map] in *.
    all: try functional_fresh_rewrite_clear; functional_eval_rewrite_clear; try functional_fresh_rewrite_clear.
    all: functional_eval_rewrite_clear; try functional_fresh_rewrite_clear; functional_eval_rewrite_clear.
    (** Two splits of the same arguments at the same arity. *)
    all: rewrite ?List.length_map in *.
    all: repeat match goal with
      | H1 : List.length ?v = (?a + ?g)%nat, H2 : List.length ?v = (?b + ?g)%nat |- _ =>
          assert_fails (constr_eq a b); assert (a = b) by lia; subst b
      end.
    (** The bounds of the parts. *)
    all: repeat match goal with
      | H : domain_nf_bounded _ (d_dom _ _) |- _ => apply domain_nf_bounded_inv in H as [? ?]
      | H : domain_bounded _ (d_neut _ _) |- _ => apply domain_bounded_neut_inv in H as [? ?]
      | H : domain_bounded _ (d_suniv _) |- _ => apply domain_bounded_suniv_inv in H
      | H : domain_bounded _ (d_lvl _ _) |- _ => apply domain_bounded_lvl_inv in H
      | H : domain_bounded _ (d_pi _ _ _ _ _) |- _ => apply domain_bounded_pi_inv in H as [? ?]
      | H : level_atoms_bounded _ ((_, _) :: _) |- _ => apply level_atoms_bounded_inv in H as [? ?]
      | H : domain_ne_bounded _ (d_app _ _) |- _ => apply domain_bounded_app_inv in H as [? ?]
      | H : domain_bounded _ (d_and _ _ _) |- _ => apply domain_bounded_and_inv in H as [? ?]
      | H : domain_ne_bounded _ (d_absurd _ _) |- _ => apply domain_bounded_absurd_inv in H
      | H : domain_bounded _ (d_ind _ _ _) |- _ => pose proof (domain_bounded_indty_inv _ _ _ _ H); clear H
      | H : domain_bounded _ (d_con _ _ _ _) |- _ => pose proof (domain_bounded_con_inv _ _ _ _ _ H); clear H
      | H : domain_ne_bounded _ (d_elim _ _ _ _ _ _ _) |- _ => apply domain_bounded_elim_inv in H as (? & ? & ? & ?)
      | H : domain_bounded _ (d_record _ _) |- _ => pose proof (domain_bounded_record_inv _ _ _ H); clear H
      | H : domain_ne_bounded _ (d_proj _ _) |- _ => apply domain_bounded_proj_inv in H
      end.
    (** Each renamed part's readback compared by its induction hypothesis. *)
    all: rn_feed.
    (** A level: its canonical form sees the atoms erased. *)
    all: try solve [ match goal with E : List.map _ ?ys0 = List.map _ (List.map _ ?ys) |- nf_erase (nf_lvl_of (lvl_canon (?c, _))) = _ =>
                       rewrite (lvl_canon_erase_wk _ c ys ys0 (rn_mono _ _ _ _ Hok) E); reflexivity end ].
    (** A small universe: at its level's canonical form. *)
    all: try solve [ match goal with E : nf_erase (nf_lvl_of ?L0) = _, L : lvl |- _ =>
                       destruct L0, L; cbn in E |- *; injection E as -> ->; reflexivity end ].
    (** The rest part by part. *)
    all: cbn [nf_erase ne_erase nf_wk ne_wk]; rewrite ?List.map_app in *.
    (** A variable: the index of [x] at [s] is renamed to that of [f x] at [s']. *)
    all: try solve [ match goal with H1 : domain_ne_bounded _ (#ᵈ ?x) |- _ =>
                       rewrite (rn_index _ _ _ _ Hok x (domain_bounded_var_inv _ _ H1)); reflexivity end ].
    all: unfold map_level_atom in *; cbn [List.map atom_offset atom_sort atom_level] in *.
    all: rewrite ?domain_level_sort_rn, ?ne_erase_idem, ?ne_erase_wk_erase.
    all: try solve [ repeat match goal with E : ?X = _ |- context [ ?X ] => rewrite E; clear E end; reflexivity ].
    (** A block: the scrutinee's type at the non-uniform parameters' fresh
        variables, and the motive one binder further, past the readback
        length. *)
    all: try match goal with |- map_normal_block _ _ :: _ = _ =>
      match goal with
      | Hok : rn_ok f ?s ?s' ?φ,
        Hnm : forall D, ind_lookup _ _ ?p = Some D -> blocks_binder_count_at D None ?Bks,
        Hl : ind_lookup _ _ ?p = Some ?D, Hv : ind_member ?D _ = Some ?Mv, Hb : List.nth_error ?Bks _ = Some ?bk,
        Hc : eb_binder_count ?bk = S (im_nn ?Mi), HBd : domain_bounded_blocks ?s ?ρ ?Bks,
        Hu : forall a, In a ?ups -> domain_bounded ?s a,
        F : fresh_tele _ _ (decl_env ?D ?ups) _ ?s ?ns, Hm : eval_mref _ _ ?p ?ups _ (_, _, ?pre),
        e : ⟦ eb_motive ?bk ⟧ _ ⍮ _ ⍮ env_extend_typed ?ρ (motive_entries _ _ _ _ _ _) ↘ ?a,
        IHZ : forall s0 φ0 A0, read_typ _ _ s0 (d_ind _ _ _) A0 -> rn_ok f (?s + _) s0 φ0 -> _ -> _,
        HZ : read_typ _ _ (?s' + _) (d_ind _ _ _) _,
        IHA : forall s0 φ0 A0, read_typ _ _ s0 (domain_rename f ?a) A0 -> _ -> _ -> _,
        HA : read_typ _ _ _ (domain_rename f ?a) _ |- _ =>
          let Hnn := fresh "Hnn" in let Hns := fresh "Hns" in let Hp := fresh "Hp" in
          let EZ := fresh "EZ" in let EA := fresh "EA" in
          assert (Hnn : im_nn Mv = im_nn Mi) by (let Hx := fresh in pose proof (Hnm _ Hl _ _ _ Hv Hb) as Hx; congruence);
          assert (Hns : forall x, In x ns -> domain_bounded (s + im_nn Mi) x)
            by (let Hx := fresh in
                pose proof (fresh_tele_domain_bounded _ _ _ _ F (env_domain_bounded_decl_env _ _ _ Hu)) as Hx;
                rewrite List.length_rev in Hx; change (List.length (im_nparams Mv)) with (im_nn Mv) in Hx; rewrite Hnn in Hx; exact Hx);
          pose proof (mref_domain_bounded _ _ _ _ _ Hm Hu) as Hp; cbn [snd] in Hp;
          pose proof (IHZ _ _ _ HZ (rn_ok_add (im_nn Mi) f s s' φ (s + im_nn Mi) (s' + im_nn Mi) Hok ltac:(lia) ltac:(lia))
                        ltac:(apply domain_bounded_indty, all_in_app;
                              [ intros; eapply domain_bounded_mono; [| apply Hp; eassumption ]; lia | exact Hns ])) as EZ;
          pose proof (IHA _ _ _ HA (rn_ok_add (S (im_nn Mi)) f s s' φ (S (s + im_nn Mi)) (S (s' + im_nn Mi)) Hok ltac:(lia) ltac:(lia))
                        ltac:(eapply (motive_domain_bounded _ _ _ _ _ _ _ _ _ _ _ _ s);
                              [ exact F | exact Hnn | exact e | lia | | exact Hu | exact Hp ];
                              rewrite <- Hc; exact (domain_bounded_blocks_motive _ _ _ _ HBd (List.nth_error_In _ _ Hb)))) as EA;
          unfold map_normal_block in *; cbn [block_arity block_scrutinee_type block_motive block_branches List.map] in *;
          replace (S (im_nn Mi) - 1) with (im_nn Mi) by lia;
          rewrite EZ, EA;
          repeat match goal with E : ?X = _ |- context [ ?X ] => rewrite E; clear E end; reflexivity
      end end.
    (** A branch: under the fresh variables of the group read, as many as it
        binds. *)
    all: match goal with |- map_normal_branch _ _ :: _ = _ =>
      match goal with
      | Hok : rn_ok f ?s ?s' ?φ,
        F : fresh_tele _ _ _ _ ?s _, F0 : fresh_cargs _ _ _ _ _ _ _ _, F2 : fresh_ihs _ _ _ _ _ _ _ _ _ _ _ _ _,
        Fw : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ _,
        e0 : ⟦ ?B ⟧ _ ⍮ _ ⍮ env_extend_typed _ (branch_entries _ _ _ _ _ _ _ _ _ _) ↘ _,
        e1 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_extend_typed _ (motive_entries _ _ _ _ _ (d_con _ _ _ _)) ↘ _,
        HD : ind_lookup _ _ ?p = Some ?D, Hnn : im_nn ?Mv = im_nn ?Mi,
        Hcnt : cargs_container_count _ _ _ _ = _, Hpl : cargs_params_length _ _,
        Hnm : forall D0, ind_lookup _ _ ?p = Some D0 -> blocks_binder_count_at D0 None _,
        Har : forall D0, ind_lookup _ _ ?p = Some D0 -> rview_leaf_arity D0,
        HBd : domain_bounded_blocks ?s _ _, Hu : forall a, In a _ -> domain_bounded ?s a,
        HAd : domain_bounded_eclo ?s _ ?A _, HBs : forall c n B0, In (c, n, B0) ((_, _, ?B) :: _) -> domain_bounded_clon _ _ B0 n,
        Hp : forall a, In a (snd _) -> domain_bounded ?s a,
        IH : forall s0 φ0 W0, read_nf _ _ s0 _ W0 -> rn_ok f (?s + _) s0 φ0 -> _ -> _,
        HW : read_nf _ _ (?s' + _) _ _ |- _ =>
          let Ht := fresh "Ht" in let Hb := fresh "Hb" in let EB := fresh "EB" in
          destruct (branch_domain_bounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F F0 F2 Fw e0 e1 HD eq_refl Hnn Hcnt Hpl
                      (Hnm _ HD) (Har _ HD) HBd Hu HAd (HBs _ _ _ (or_introl eq_refl)) Hp) as [Ht Hb];
          match type of HW with read_nf _ _ (s' + ?n) _ _ =>
            pose proof (IH _ _ _ HW (rn_ok_add n f s s' φ (s + n) (s' + n) Hok ltac:(lia) ltac:(lia))
                          (domain_nf_bounded_dom _ _ _ Ht Hb)) as EB
          end;
          unfold map_normal_branch in *; cbn [branch_constructor branch_arity branch_body List.map] in *;
          rewrite EB;
          repeat match goal with E : ?X = _ |- context [ ?X ] => rewrite E; clear E end; reflexivity
      end end.
  Qed.

  Corollary read_nf_rn : forall s s' φ m W W',
      rn_ok f s s' φ -> domain_nf_bounded s m ->
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> Rnf domain_nf_rename f m in Θ ⍮ Ξ ⍮ s' ↘ W' -> nf_erase W' = nf_erase (nf_wk φ W).
  Proof. intros * ? ? H H'; exact (proj1 read_rn _ _ _ H _ _ _ H' ltac:(eassumption) ltac:(eassumption)). Qed.

  Corollary read_typ_rn : forall s s' φ a A A',
      rn_ok f s s' φ -> domain_bounded s a ->
      Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> Rtyp domain_rename f a in Θ ⍮ Ξ ⍮ s' ↘ A' -> nf_erase A' = nf_erase (nf_wk φ A).
  Proof. intros * ? ? H H'; exact (proj1 (proj2 (proj2 read_rn)) _ _ _ H _ _ _ H' ltac:(eassumption) ltac:(eassumption)). Qed.
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
  induction 1; intros f Hf; cbn [List.length] in Hf; [ reflexivity | | | | |].
  all: assert (Hρ : env_rename f ρ = ρ) by (apply IHinitial_env; intros; apply Hf; lia).
  (** Each new entry: its values, evaluated in [ρ], which the renaming
      fixes; a fresh variable, of a level of the context; a kept proof, over
      [ρ]. *)
  all: cbn [extend_env extend_env_mod extend_env_dm env_rename List.map dentry_rename domain_rename domain_ne_rename
            entry_type_rename]; fold (env_rename f ρ); rewrite Hρ.
  all: repeat match goal with
    | Hρ : env_rename ?f ?ρ = ?ρ, H : ⟦ _ ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a |- context [ domain_rename ?f ?a ] =>
        let E := fresh "E" in let Ha := fresh "Ha" in
        assert (E : domain_rename f a = a)
          by (pose proof (proj1 (eval_rn Θ Ξ f) _ _ _ H) as Ha; rewrite Hρ in Ha; eapply functional_eval_exp; eassumption);
        rewrite E; clear E
    | Hρ : env_rename ?f ?ρ = ?ρ, H : ⟦ _ ⟧ᵐ _ ⍮ _ ⍮ ?ρ ↘ ?h |- context [ dmod_rename ?f ?h ] =>
        let E := fresh "E" in let Hh := fresh "Hh" in
        assert (E : dmod_rename f h = h)
          by (pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (eval_rn Θ Ξ f))))) _ _ _ H) as Hh; rewrite Hρ in Hh;
              eapply functional_eval_modexp; eassumption);
        rewrite E; clear E
    end.
  all: rewrite ?Hf by lia; reflexivity.
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
Lemma eval_initial_domain_bounded : forall Θ Ξ Γ ρ M m,
    initial_env Θ Ξ Γ ρ -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> domain_bounded Θ Ξ (List.length Γ) m.
Proof.
  intros * Hρ Hm v Hv.
  apply (proj1 (eval_avoids Θ Ξ v (List.length Γ)) _ _ _ Hm None); [| exact I ].
  eapply initial_env_avoids; [ exact Hρ | exact Hv | reflexivity ].
Qed.

Lemma lvl_shift_above_lt : forall s x, x < s -> lvl_shift_above s x = x.
Proof. intros; unfold lvl_shift_above; destruct (Nat.ltb_spec x s); lia. Qed.

(** Readback shift: a value of [Γ] reads back one variable further out as
    the weakening of its normal form, up to erasure: its proofs are kept
    over environments the bound does not reach ([read_rn]). *)
Theorem read_shift : forall Θ Ξ Γ ρ A M a m W W',
    initial_env Θ Ξ Γ ρ ->
    ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    Rnf ⇓ a m in Θ ⍮ Ξ ⍮ List.length Γ ↘ W ->
    Rnf ⇓ a m in Θ ⍮ Ξ ⍮ S (List.length Γ) ↘ W' ->
    nf_erase W' = nf_erase (nf_wk ↑ W).
Proof.
  intros * Hρ Ha Hm HW HW'.
  rewrite <- (eval_initial_rn _ _ _ _ _ _ Hρ Ha _ (lvl_shift_above_lt _)),
    <- (eval_initial_rn _ _ _ _ _ _ Hρ Hm _ (lvl_shift_above_lt _)) in HW'.
  exact (read_nf_rn Θ Ξ (lvl_shift_above (List.length Γ)) _ _ _ (⇓ a m) _ _ (rn_ok_shift _)
           (domain_nf_bounded_dom _ _ _ _ _ (eval_initial_domain_bounded _ _ _ _ _ _ Hρ Ha) (eval_initial_domain_bounded _ _ _ _ _ _ Hρ Hm))
           HW HW').
Qed.

Theorem read_typ_shift : forall Θ Ξ Γ ρ A a W W',
    initial_env Θ Ξ Γ ρ ->
    ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    Rtyp a in Θ ⍮ Ξ ⍮ List.length Γ ↘ W ->
    Rtyp a in Θ ⍮ Ξ ⍮ S (List.length Γ) ↘ W' ->
    nf_erase W' = nf_erase (nf_wk ↑ W).
Proof.
  intros * Hρ Ha HW HW'.
  rewrite <- (eval_initial_rn _ _ _ _ _ _ Hρ Ha _ (lvl_shift_above_lt _)) in HW'.
  exact (read_typ_rn Θ Ξ (lvl_shift_above (List.length Γ)) _ _ _ _ _ _ (rn_ok_shift _)
           (eval_initial_domain_bounded _ _ _ _ _ _ Hρ Ha) HW HW').
Qed.
