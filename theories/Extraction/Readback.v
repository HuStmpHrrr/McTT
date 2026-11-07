From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Extraction Require Import FastDomain Evaluation.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** * The Readback the Checker Runs

    The functions computing the readback of [Extraction.FastRead], with
    closures evaluated by [Extraction.Evaluation], each by structural
    recursion on an order the readback derivation gives. *)

(** The canonical level a level normal form encodes.  A level always reads
    back as [nf_lvl_of] of a canonical level ([read_nf_level_lvl_of_nf]), so
    the default is never reached. *)
Definition lvl_of_nf (W : nf) : lvl :=
  match W with nf_lvl c xs => (c, xs) | _ => (ordinal_zero, nil) end.

Lemma read_nf_level_lvl_of_nf : forall Θ Ξ s l W,
    Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    W = nf_lvl_of (lvl_of_nf W).
Proof.
  inversion 1; subst; first [ reflexivity | match goal with H : domain_kind _ = _ |- _ => cbn in H; discriminate H end ].
Qed.

Lemma read_typ_suniv_of_nf : forall Θ Ξ s l W,
    Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    Rtyp 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of (lvl_of_nf W).
Proof.
  intros * H; apply read_typ_suniv.
  rewrite <- (read_nf_level_lvl_of_nf _ _ _ _ _ H); exact H.
Qed.

(** ** The Kind of a Fast Type

    Whether a fast type is a proposition, read off its head
    ([fdomain_kind]). *)
Definition fdomain_is_prop (a : fdomain) : bool :=
  match fdomain_kind a with ak_propositional => true | _ => false end.

Lemma fdomain_is_prop_true : forall a, fdomain_is_prop a = true -> domain_kind (fdomain_erase a) = ak_propositional.
Proof. intros a; unfold fdomain_is_prop; rewrite fdomain_kind_erase; destruct (fdomain_kind a); congruence. Qed.

Lemma fdomain_is_prop_false : forall a, fdomain_is_prop a = false -> evaluated_kind (domain_kind (fdomain_erase a)).
Proof. intros a; unfold fdomain_is_prop; rewrite fdomain_kind_erase; destruct (fdomain_kind a); intros; first [ discriminate | constructor ]. Qed.

(** ** The Positions a Kept Proof Reads

    [proof_scope] on a fast environment, through the twin of
    [entry_unit_bound]. *)
Definition fentry_unit_bound (e : fdentry) : nat :=
  match e with
  | fde_mod _ U => gunit_free_bound U
  | _ => 0
  end.

Lemma fentry_unit_bound_erase : forall e, entry_unit_bound (fdentry_erase e) = fentry_unit_bound e.
Proof. intros []; reflexivity. Qed.

Fixpoint fproof_scope_from (ρ : fenv) (j n : nat) : nat :=
  match ρ with
  | nil => n
  | e :: ρ' => if Nat.ltb j n then fproof_scope_from ρ' (S j) (Nat.max n (S j + fentry_unit_bound e)) else n
  end.

Lemma fproof_scope_from_erase : forall ρ j n, proof_scope_from (fenv_erase ρ) j n = fproof_scope_from ρ j n.
Proof.
  induction ρ as [| e ρ IH]; intros j n; cbn [proof_scope_from fproof_scope_from List.map]; [ reflexivity |].
  rewrite fentry_unit_bound_erase; destruct (Nat.ltb j n); [ apply IH | reflexivity ].
Qed.

Definition fproof_scope (M : exp) (ρ : fenv) : nat := fproof_scope_from ρ 0 (exp_free_bound M).

Lemma fproof_scope_erase : forall M ρ, proof_scope M (fenv_erase ρ) = fproof_scope M ρ.
Proof. intros; unfold proof_scope, fproof_scope; apply fproof_scope_from_erase. Qed.

(** ** Along the Leaf Paths of a Recursive Argument

    The computations of [fresh_leaf_vars] and [wrap_leaf_vals], by the
    paths' flags [bs], each sound at lengths its relation has. *)

(** The fresh variables at the flagged paths, from [s], at the types [as'] *)
Fixpoint leaf_vars_f (bs : list bool) (as' : list domain) (s : nat) : list domain :=
  match bs, as' with
  | true :: bs, a :: as' => ⇑! a s :: leaf_vars_f bs as' (S s)
  | false :: bs, _ :: as' => leaf_vars_f bs as' s
  | _, _ => nil
  end.

Lemma leaf_vars_f_sound : forall bs as' s, List.length as' = List.length bs -> fresh_leaf_vars bs as' s (leaf_vars_f bs as' s).
Proof.
  induction bs as [| b bs IH]; intros [| a as'] s Hl; cbn in Hl |- *; try discriminate; [ constructor |].
  injection Hl as Hl; destruct b; constructor; apply IH; exact Hl.
Qed.

Lemma fresh_leaf_vars_f : forall bs as' s vs, fresh_leaf_vars bs as' s vs -> vs = leaf_vars_f bs as' s.
Proof. induction 1; cbn; congruence. Qed.

Lemma fresh_leaf_vars_types_length : forall bs as' s vs, fresh_leaf_vars bs as' s vs -> List.length as' = List.length bs.
Proof. induction 1; cbn; congruence. Qed.

(** The results along the paths: the next of [ihs] at a flagged path, the
    path's own result at another; and the rest of [ihs] *)
Fixpoint leaf_wrap_f (bs : list bool) (rs ihs : list domain) : (list domain * list domain)%type :=
  match bs, rs with
  | true :: bs, _ :: rs =>
      match ihs with
      | ih :: ihs => let (out, rest) := leaf_wrap_f bs rs ihs in (ih :: out, rest)
      | nil => (nil, nil)
      end
  | false :: bs, r :: rs => let (out, rest) := leaf_wrap_f bs rs ihs in (r :: out, rest)
  | _, _ => (nil, ihs)
  end.

Lemma leaf_wrap_f_sound : forall bs rs ihs, List.length rs = List.length bs ->
    List.length (List.filter (fun b => b) bs) <= List.length ihs ->
    wrap_leaf_vals bs rs ihs (snd (leaf_wrap_f bs rs ihs)) (fst (leaf_wrap_f bs rs ihs)).
Proof.
  induction bs as [| b bs IH]; intros [| r rs] ihs Hl Hi; cbn in Hl, Hi |- *; try discriminate; [ constructor |].
  injection Hl as Hl; destruct b.
  - destruct ihs as [| ih ihs]; cbn in Hi; [ lia |].
    specialize (IH rs ihs Hl ltac:(lia)); destruct (leaf_wrap_f bs rs ihs); constructor; exact IH.
  - specialize (IH rs ihs Hl Hi); destruct (leaf_wrap_f bs rs ihs); constructor; exact IH.
Qed.

Lemma wrap_leaf_vals_f : forall bs rs ihs ihs' out, wrap_leaf_vals bs rs ihs ihs' out ->
    leaf_wrap_f bs rs ihs = (out, ihs').
Proof. induction 1; cbn; [ reflexivity | rewrite IHwrap_leaf_vals; reflexivity | rewrite IHwrap_leaf_vals; reflexivity ]. Qed.

Lemma wrap_leaf_vals_lengths : forall bs rs ihs ihs' out, wrap_leaf_vals bs rs ihs ihs' out ->
    List.length rs = List.length bs /\ List.length (List.filter (fun b => b) bs) <= List.length ihs.
Proof. induction 1; cbn; lia. Qed.

(** [leaf_vars_f]'s twin, on fast values *)
Fixpoint fleaf_vars_f (bs : list bool) (as' : list fdomain) (s : nat) : list fdomain :=
  match bs, as' with
  | true :: bs, a :: as' => fd_neut a (fd_var s) :: fleaf_vars_f bs as' (S s)
  | false :: bs, _ :: as' => fleaf_vars_f bs as' s
  | _, _ => nil
  end.

Lemma fleaf_vars_f_erase : forall bs as' s, fdomains_erase (fleaf_vars_f bs as' s) = leaf_vars_f bs (fdomains_erase as') s.
Proof. induction bs as [| [|] bs IH]; intros [| a as'] s; cbn; f_equal; auto. Qed.

Lemma fleaf_vars_f_ok : forall Θ Ξ bs as' s, Forall (fdomain_ok Θ Ξ) as' -> Forall (fdomain_ok Θ Ξ) (fleaf_vars_f bs as' s).
Proof.
  intros Θ Ξ; induction bs as [| [|] bs IH]; intros [| a as'] s H; cbn; try constructor; inversion H; subst; auto with mctt.
Qed.

(** [leaf_wrap_f]'s twin, on fast values *)
Fixpoint fleaf_wrap_f (bs : list bool) (rs ihs : list fdomain) : (list fdomain * list fdomain)%type :=
  match bs, rs with
  | true :: bs, _ :: rs =>
      match ihs with
      | ih :: ihs => let (out, rest) := fleaf_wrap_f bs rs ihs in (ih :: out, rest)
      | nil => (nil, nil)
      end
  | false :: bs, r :: rs => let (out, rest) := fleaf_wrap_f bs rs ihs in (r :: out, rest)
  | _, _ => (nil, ihs)
  end.

Lemma fleaf_wrap_f_erase : forall bs rs ihs,
    leaf_wrap_f bs (fdomains_erase rs) (fdomains_erase ihs) =
    (fdomains_erase (fst (fleaf_wrap_f bs rs ihs)), fdomains_erase (snd (fleaf_wrap_f bs rs ihs))).
Proof.
  induction bs as [| [|] bs IH]; intros [| r rs] ihs; cbn; try reflexivity.
  - destruct ihs as [| ih ihs]; cbn; [ reflexivity |]; rewrite IH; destruct (fleaf_wrap_f bs rs ihs); reflexivity.
  - rewrite IH; destruct (fleaf_wrap_f bs rs ihs); reflexivity.
Qed.

Lemma fleaf_wrap_f_ok : forall Θ Ξ bs rs ihs, Forall (fdomain_ok Θ Ξ) rs -> Forall (fdomain_ok Θ Ξ) ihs ->
    Forall (fdomain_ok Θ Ξ) (fst (fleaf_wrap_f bs rs ihs)) /\ Forall (fdomain_ok Θ Ξ) (snd (fleaf_wrap_f bs rs ihs)).
Proof.
  intros Θ Ξ; induction bs as [| [|] bs IH]; intros [| r rs] ihs Hr Hi; cbn; auto; inversion Hr; subst.
  - destruct ihs as [| ih ihs]; cbn; [ auto |]; inversion Hi; subst.
    destruct (IH rs ihs) as [Hout Hrest]; [ assumption | assumption |]; destruct (fleaf_wrap_f bs rs ihs); cbn in *; auto.
  - destruct (IH rs ihs) as [Hout Hrest]; [ assumption | assumption |]; destruct (fleaf_wrap_f bs rs ihs); cbn in *; auto.
Qed.

Lemma fleaf_wrap_f_ok_fst : forall Θ Ξ bs rs ihs, Forall (fdomain_ok Θ Ξ) rs -> Forall (fdomain_ok Θ Ξ) ihs ->
    Forall (fdomain_ok Θ Ξ) (fst (fleaf_wrap_f bs rs ihs)).
Proof. intros; apply fleaf_wrap_f_ok; assumption. Qed.

Lemma fleaf_wrap_f_ok_snd : forall Θ Ξ bs rs ihs, Forall (fdomain_ok Θ Ξ) rs -> Forall (fdomain_ok Θ Ξ) ihs ->
    Forall (fdomain_ok Θ Ξ) (snd (fleaf_wrap_f bs rs ihs)).
Proof. intros; apply fleaf_wrap_f_ok; assumption. Qed.

#[export]
Hint Resolve fleaf_vars_f_ok fleaf_wrap_f_ok_fst fleaf_wrap_f_ok_snd : mctt.

Lemma fleaf_vars_f_length : forall bs as' s,
    List.length (fleaf_vars_f bs as' s) = List.length (leaf_vars_f bs (fdomains_erase as') s).
Proof. intros; rewrite <- fleaf_vars_f_erase, List.length_map; reflexivity. Qed.

Lemma fleaf_wrap_f_erase_fst : forall bs rs ihs,
    fdomains_erase (fst (fleaf_wrap_f bs rs ihs)) = fst (leaf_wrap_f bs (fdomains_erase rs) (fdomains_erase ihs)).
Proof. intros; rewrite fleaf_wrap_f_erase; reflexivity. Qed.

Lemma fleaf_wrap_f_erase_snd : forall bs rs ihs,
    fdomains_erase (snd (fleaf_wrap_f bs rs ihs)) = snd (leaf_wrap_f bs (fdomains_erase rs) (fdomains_erase ihs)).
Proof. intros; rewrite fleaf_wrap_f_erase; reflexivity. Qed.

(** The environments of a branch and of a motive, right when their parts
    are ([fbranch_entries_ok], [fmotive_entries_ok]) *)
Lemma fenv_extend_typed_branch_ok : forall Θ Ξ ρ D Mj p ups As ρm gs ns vs ihs,
    fenv_ok Θ Ξ ρ -> Forall (fdomain_ok Θ Ξ) ups -> fenv_ok Θ Ξ ρm -> Forall (fdomain_ok Θ Ξ) ns ->
    Forall (fdomain_ok Θ Ξ) vs -> Forall (fdomain_ok Θ Ξ) ihs ->
    fenv_ok Θ Ξ (fenv_extend_typed ρ (fbranch_entries D Mj p ups As ρm gs ns vs ihs)).
Proof. intros; apply fenv_extend_typed_ok; [ assumption | apply fbranch_entries_ok; assumption ]. Qed.

Lemma fenv_extend_typed_motive_ok : forall Θ Ξ ρ D Mk ups ns a m,
    fenv_ok Θ Ξ ρ -> Forall (fdomain_ok Θ Ξ) ups -> Forall (fdomain_ok Θ Ξ) ns -> fdomain_ok Θ Ξ a -> fdomain_ok Θ Ξ m ->
    fenv_ok Θ Ξ (fenv_extend_typed ρ (fmotive_entries D Mk ups ns a m)).
Proof. intros; apply fenv_extend_typed_ok; [ assumption | apply fmotive_entries_ok; assumption ]. Qed.

#[local]
Hint Resolve fdecl_env_ok fenv_extend_typed_branch_ok fenv_extend_typed_motive_ok fenv_entry_ok : mctt.

(** The operations on fast values, read through their erasure equations *)
#[local] Opaque fleaf_vars_f fleaf_wrap_f fenv_entry fenv_var fenv_type fenv_mod fextend_env fextend_env_mod fextend_env_dm
  fenv_extend_typed fenv_tele fdomain_level_suc fdomain_level_max fdomain_level_lit fdm_clo fkinds_pads fkinds_body_entry carry
  fdecl_env fbranch_entries fmotive_entries fglobal_proof_env fproof_scope.

(** The erasures of the leaf paths' computations and of the proof scope,
    read as Core ones *)
Ltac fleaf_norm :=
  rewrite ?fleaf_vars_f_erase, ?fleaf_vars_f_length, ?fleaf_wrap_f_erase_fst, ?fleaf_wrap_f_erase_snd,
    <- ?fenv_entry_erase, <- ?fproof_scope_erase, ?fbranch_entries_erase, ?fmotive_entries_erase, ?fdecl_env_erase in *.

(** ** The Fresh Variables of the Telescopes of a Group

    Their orders, and the functions that compute them. *)

(** The variables of a telescope *)
Inductive fresh_tele_order (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> Prop :=
(** No entry *)
| fresh_tele_order_nil :
  `( fresh_tele_order Θ Ξ ρ nil s )
(** The first entry's type, then the rest under its variable *)
| fresh_tele_order_cons :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> fresh_tele_order Θ Ξ (ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ) T (S s)) ->
     fresh_tele_order Θ Ξ ρ (ce_ass κ A :: T) s ).

(** The variables of the arguments of a constructor *)
Inductive fresh_cargs_order (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> Prop :=
(** No argument *)
| fresh_cargs_order_nil :
  `( fresh_cargs_order Θ Ξ p ups ρ nil s )
(** A non-recursive argument's type, then the rest *)
| fresh_cargs_order_arg :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> fresh_cargs_order Θ Ξ p ups (ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ) gs (S s)) ->
     fresh_cargs_order Θ Ξ p ups ρ (ca_arg r A :: gs) s )
(** A recursive argument's type, then the rest *)
| fresh_cargs_order_rec_case :
  `( eval_shape_type_order Θ Ξ p ups ρ t ->
     fresh_cargs_order Θ Ξ p ups ρ gs (S s) ->
     fresh_cargs_order Θ Ξ p ups ρ (ca_rec t :: gs) s ).

(** The variables of the recursive results of a branch, of the group read
    [Dc] *)
Inductive fresh_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (As : list exp) (p : qname) (ups : list domain)
  (Dc : ind_decl) : env -> list carg -> list carg -> list domain -> nat -> Prop :=
(** No argument *)
| fresh_ihs_order_nil :
  `( fresh_ihs_order Θ Ξ ρ As p ups Dc ρa nil nil nil s )
(** A non-recursive argument, entering the environment *)
| fresh_ihs_order_arg :
  `( fresh_ihs_order Θ Ξ ρ As p ups Dc (ρa ↦ v ⦂ entry_type_closure T ρa) gs' gs vs s ->
     fresh_ihs_order Θ Ξ ρ As p ups Dc ρa (ca_arg ra' T' :: gs') (ca_arg ra T :: gs) (v :: vs) s )
(** Recursive in both: the types of its results, one per leaf path, then
    the rest after the variables at the paths of the container's *)
| fresh_ihs_order_rec_case :
  `( ind_lookup Θ Ξ p = Some D ->
     eval_ihty_order Θ Ξ p ups ρ As ρa t v ->
     (forall as', ⟦ihty v of t at p ups under ρ As ⟧ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
        List.length as' = List.length (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t))) ->
     (forall as', ⟦ihty v of t at p ups under ρ As ⟧ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
        fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs
          (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s) + s)) ->
     fresh_ihs_order Θ Ξ ρ As p ups Dc ρa (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) s )
(** Nested through: the rest *)
| fresh_ihs_order_nest :
  `( fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs s ->
     fresh_ihs_order Θ Ξ ρ As p ups Dc ρa (ca_arg ra' T' :: gs') (ca_rec t :: gs) (v :: vs) s ).

(** The recursive results a branch is read under, wrapped *)
Inductive wrap_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (p : qname) (ups : list domain) (Bks : list eblock)
  (Dc : ind_decl) : list carg -> list carg -> list domain -> list domain -> Prop :=
(** No argument *)
| wrap_ihs_order_nil :
  `( wrap_ihs_order Θ Ξ ρ p ups Bks Dc nil nil nil nil )
(** Recursive in both: the eliminator's results at the argument, along
    its paths, then the rest *)
| wrap_ihs_order_rec_case :
  `( ind_lookup Θ Ξ p = Some D ->
     eval_ih_order Θ Ξ ρ p ups Bks t v ->
     (forall rs, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
        List.length rs = List.length (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) /\
        List.length (List.filter (fun b => b) (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)))
          <= List.length ihs) ->
     (forall rs, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
        wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs
          (snd (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs))) ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Nested through: the eliminator at the argument, then the rest *)
| wrap_ihs_order_nest :
  `( eval_ih_order Θ Ξ ρ p ups Bks t v ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_arg ra' T' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Non-recursive: the rest *)
| wrap_ihs_order_arg :
  `( wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_arg ra' T' :: gs') (ca_arg ra T :: gs) (v :: vs) ihs ).

(** The type value of an environment's entry: the evaluation it makes *)
Inductive eval_entry_type_order (Θ : gdeps) (Ξ : gstack) : entry_type -> Prop :=
(** A type value: none *)
| eval_entry_type_order_value :
  `( eval_entry_type_order Θ Ξ (entry_type_value a) )
(** A type in an environment *)
| eval_entry_type_order_closure :
  `( eval_exp_order Θ Ξ A ρ ->
     eval_entry_type_order Θ Ξ (entry_type_closure A ρ) )
(** The type of a recursive argument of a shape *)
| eval_entry_type_order_shape :
  `( eval_shape_type_order Θ Ξ p ups ρ t ->
     eval_entry_type_order Θ Ξ (entry_type_shape p ups ρ t) )
(** The type of a recursive result: the types of the argument's results,
    of which there is the [i]-th *)
| eval_entry_type_order_induction_hypothesis :
  `( eval_ihty_order Θ Ξ p ups ρm As ρ t v ->
     (forall as', ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' -> i < List.length as') ->
     eval_entry_type_order Θ Ξ (entry_type_induction_hypothesis ρm As p ups ρ t v i) ).

#[local]
Hint Constructors fresh_tele_order fresh_cargs_order fresh_ihs_order wrap_ihs_order
  eval_entry_type_order : mctt.

Lemma fresh_tele_order_sound : forall Θ Ξ ρ T s vs, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> fresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

Lemma fresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs,
    Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> fresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

Lemma fresh_ihs_order_sound : forall Θ Ξ ρ As p ups Dc ρa gs' gs vs s ihs,
    Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
    fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs s.
Proof.
  induction 1; try solve [ econstructor; eassumption ].
  - eapply fresh_ihs_order_rec_case; try eassumption; [ mauto | |];
      intros; functional_eval_rewrite_clear.
    + exact (fresh_leaf_vars_types_length _ _ _ _ H1).
    + rewrite <- (fresh_leaf_vars_f _ _ _ _ H1); assumption.
Qed.

Lemma wrap_ihs_order_sound : forall Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r,
    ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs.
Proof.
  induction 1; try solve [ econstructor; try eassumption; mauto ].
  eapply wrap_ihs_order_rec_case; try eassumption; [ mauto | |];
    intros; functional_eval_rewrite_clear.
  - exact (wrap_leaf_vals_lengths _ _ _ _ _ H1).
  - rewrite (wrap_leaf_vals_f _ _ _ _ _ H1); assumption.
Qed.

Lemma eval_entry_type_order_sound : forall Θ Ξ t a, eval_entry_type Θ Ξ t a -> eval_entry_type_order Θ Ξ t.
Proof.
  induction 1; econstructor; mauto.
  intros; functional_eval_rewrite_clear; apply List.nth_error_Some; congruence.
Qed.

#[export]
Hint Resolve fresh_tele_order_sound fresh_cargs_order_sound fresh_ihs_order_sound wrap_ihs_order_sound
  eval_entry_type_order_sound : mctt.

Section FreshImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[local]
  Ltac fast_readback_obligation_rel :=
    repeat match goal with
      | H : fresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : fresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : eval_entry_type_order _ _ _ |- _ => progressive_invert H
      end;
    (** The lookups the order records are the ones computed. *)
    repeat match goal with
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ?x = true, H2 : ?x = false |- _ => rewrite H1 in H2; discriminate H2
      (** The group of the recursive results of an argument has a
          declaration. *)
      | H1 : eval_ih_order _ _ _ ?p _ _ _ _, H2 : ind_lookup _ _ ?p = None |- _ =>
          exfalso; destruct (eval_ih_order_lookup _ _ _ _ _ _ _ _ H1) as (? & ?); congruence
      (** The [i]-th type of the recursive results is there. *)
      | H : forall as', ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ as' -> _ < _,
        Hi : ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ fdomains_erase ?l, E : List.nth_error ?l _ = None |- _ =>
          exfalso; pose proof (H _ Hi); apply List.nth_error_None in E; rewrite List.length_map in *; lia
      end;
    first [ eassumption | solve [ eauto 2 ]
          (** The [i]-th type of the recursive results, read off the fast
              list *)
          | solve [ econstructor; [ eassumption | rewrite List.nth_error_map;
                                    match goal with E : List.nth_error _ _ = Some _ |- _ => rewrite E; reflexivity end ] ]
          (** The leaf paths' computations, at the lengths the order
              records *)
          | solve [ eapply fresh_ihs_rec; [ eassumption | eassumption
                                           | apply leaf_vars_f_sound; eauto | eassumption ] ]
          | solve [ eapply wrap_ihs_eval_rec; [ eassumption | eassumption | | eassumption ];
                    match goal with H : forall rs, _ -> _ /\ _, Hr : eval_ih _ _ _ _ _ _ _ _ ?rs |- _ =>
                      destruct (H _ Hr); apply leaf_wrap_f_sound; assumption end ]
          | econstructor; eassumption ].

  (** The erasures read as Core values, and the results' two parts apart *)
  #[local]
  Ltac fast_readback_obligation_norm :=
    intros; cbv beta iota in *; cbn [fst snd] in *; ferase_norm; fleaf_norm; ferase_norm;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.

  #[local]
  Ltac fast_readback_obligation :=
    fast_readback_obligation_norm;
    lazymatch goal with
    | |- _ /\ _ => split; [ fast_readback_obligation_rel | ok_solve ]
    | |- Forall _ _ => ok_solve
    | |- fenv_ok _ _ _ => ok_solve
    | |- fdomain_ok _ _ _ => ok_solve
    | |- fentry_type_ok _ _ _ => ok_solve
    | |- _ => fast_readback_obligation_rel
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_tele_impl (ρ : fenv) T s (Hρ : fenv_ok Θ Ξ ρ) (H : fresh_tele_order Θ Ξ (fenv_erase ρ) T s) :
      { vs | Ftele T in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ fdomains_erase vs /\ Forall (fdomain_ok Θ Ξ) vs } by struct H :=
  | ρ, nil, s, Hρ, H => exist _ nil _
  | ρ, ce_ass κ A :: T, s, Hρ, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
      let (vs, Hvs) := fast_fresh_tele_impl (fextend_env ρ (fd_neut a (fd_var s)) (fentry_type_closure A ρ)) T (S s) _ _ in
      exist _ (fd_neut a (fd_var s) :: vs) _
  | ρ, _, s, Hρ, H => False_rect _ _.
  Solve All Obligations with fast_readback_obligation.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_cargs_impl p (ups : list fdomain) (ρ : fenv) gs s (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρ : fenv_ok Θ Ξ ρ)
      (H : fresh_cargs_order Θ Ξ p (fdomains_erase ups) (fenv_erase ρ) gs s) :
    { vs | Fcargs gs of p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ fdomains_erase vs /\ Forall (fdomain_ok Θ Ξ) vs } by struct H :=
  | p, ups, ρ, nil, s, Hups, Hρ, H => exist _ nil _
  | p, ups, ρ, ca_arg r A :: gs, s, Hups, Hρ, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl p ups (fextend_env ρ (fd_neut a (fd_var s)) (fentry_type_closure A ρ)) gs (S s) Hups _ _ in
      exist _ (fd_neut a (fd_var s) :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, Hups, Hρ, H =>
      let (a, Ha) := fast_eval_shape_type_impl F p ups ρ t Hups Hρ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl p ups ρ gs (S s) Hups Hρ _ in
      exist _ (fd_neut a (fd_var s) :: vs) _.
  Solve All Obligations with fast_readback_obligation.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  (** The recursive results' variables of a stuck eliminator's branch, at
      the declaration [D] of the group the readback holds *)
  Equations fast_fresh_ihs_impl (ρ : fenv) As p (ups : list fdomain) Dc (ρa : fenv) gs' gs (vs : list fdomain) s
      (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D)
      (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρa : fenv_ok Θ Ξ ρa) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : fresh_ihs_order Θ Ξ (fenv_erase ρ) As p (fdomains_erase ups) Dc (fenv_erase ρa) gs' gs (fdomains_erase vs) s) :
    { ihs | Fihs (fdomains_erase vs) at gs' gs of Dc under (fenv_erase ρ) As at p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ (fenv_erase ρa) ⍮ s
              ↘ fdomains_erase ihs /\ Forall (fdomain_ok Θ Ξ) ihs } by struct H :=
  | ρ, As, p, ups, Dc, ρa, nil, nil, nil, s, D, Ed, Hρ, Hups, Hρa, Hvs, H => exist _ nil _
  | ρ, As, p, ups, Dc, ρa, ca_arg _ _ :: gs', ca_arg _ T :: gs, v :: vs, s, D, Ed, Hρ, Hups, Hρa, Hvs, H =>
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc (fextend_env ρa v (fentry_type_closure T ρa)) gs' gs vs s D Ed Hρ Hups _ _ _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, ρa, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, s, D, Ed, Hρ, Hups, Hρa, Hvs, H =>
      let (as', Has) := fast_eval_ihty_impl F p ups ρ As ρa t v Hups Hρ Hρa _ _ in
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs
                           (List.length (fleaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s) + s) D Ed Hρ Hups Hρa _ _ in
      exist _ (fleaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s ++ ihs) _
  | ρ, As, p, ups, Dc, ρa, ca_arg _ _ :: gs', ca_rec t :: gs, v :: vs, s, D, Ed, Hρ, Hups, Hρa, Hvs, H =>
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs s D Ed Hρ Hups Hρa _ _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, ρa, _, _, _, s, D, Ed, Hρ, Hups, Hρa, Hvs, H => False_rect _ _.
  Solve All Obligations with fast_readback_obligation.

  (** The recursive results a stuck eliminator's branch is read under, at
      the declaration [D] of the group the readback holds *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_wrap_ihs_impl (ρ : fenv) p (ups : list fdomain) Bks Dc gs' gs (vs ihs : list fdomain)
      (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D)
      (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hvs : Forall (fdomain_ok Θ Ξ) vs) (Hihs : Forall (fdomain_ok Θ Ξ) ihs)
      (H : wrap_ihs_order Θ Ξ (fenv_erase ρ) p (fdomains_erase ups) Bks Dc gs' gs (fdomains_erase vs) (fdomains_erase ihs)) :
    { r | ⟦wihs (fdomains_erase vs) of gs' gs of Dc with (fdomains_erase ihs) under p (fdomains_erase ups) Bks ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ
            ↘ fdomains_erase r /\ Forall (fdomain_ok Θ Ξ) r } by struct H :=
  | ρ, p, ups, Bks, Dc, nil, nil, nil, nil, D, Ed, Hρ, Hups, Hvs, Hihs, H => exist _ nil _
  | ρ, p, ups, Bks, Dc, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, ihs, D, Ed, Hρ, Hups, Hvs, Hihs, H =>
        let (rs, Hrs) := fast_eval_ih_impl F ρ p ups Bks t v D Ed Hρ Hups _ _ in
        let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs
                         (snd (fleaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs)) D Ed Hρ Hups _ _ _ in
        exist _ (fst (fleaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs) ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ _ :: gs', ca_rec t :: gs, v :: vs, ihs, D, Ed, Hρ, Hups, Hvs, Hihs, H =>
        let (rs, Hrs) := fast_eval_ih_impl F ρ p ups Bks t v D Ed Hρ Hups _ _ in
        let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs D Ed Hρ Hups _ Hihs _ in
        exist _ (rs ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ _ :: gs', ca_arg _ _ :: gs, _ :: vs, ihs, D, Ed, Hρ, Hups, Hvs, Hihs, H =>
      let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs D Ed Hρ Hups _ Hihs _ in
      exist _ r _
  | ρ, p, ups, Bks, Dc, _, _, _, _, D, Ed, Hρ, Hups, Hvs, Hihs, H => False_rect _ _.
  Solve All Obligations with fast_readback_obligation.

  (** The type value of an environment's entry *)
  #[tactic="idtac"]
  Equations fast_eval_entry_type_impl (t : fentry_type) (Ht : fentry_type_ok Θ Ξ t)
      (H : eval_entry_type_order Θ Ξ (fentry_type_erase t)) :
      { a | eval_entry_type Θ Ξ (fentry_type_erase t) (fdomain_erase a) /\ fdomain_ok Θ Ξ a } :=
  | fentry_type_value a, Ht, H => exist _ a _
  | fentry_type_closure A ρ, Ht, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ _ _ in
      exist _ a _
  | fentry_type_shape p ups ρ t, Ht, H =>
      let (a, Ha) := fast_eval_shape_type_impl F p ups ρ t _ _ _ in
      exist _ a _
  | fentry_type_induction_hypothesis ρm As p ups ρ t v i, Ht, H with fast_eval_ihty_impl F p ups ρm As ρ t v _ _ _ _ _ := {
    | exist _ as' Has with inspect (List.nth_error as' i) := {
      | exist _ (Some a) E => exist _ a _
      | exist _ None E => False_rect _ _ } }
  | fentry_type_none, Ht, H => False_rect _ _.
  Solve All Obligations with fast_readback_obligation.
End FreshImpl.

(** ** The Orders of Readback *)

Inductive read_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
(** A type, as an element of a large universe *)
| read_nf_order_type :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
(** A type, as an element of a small universe *)
| read_nf_order_stype :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌@n a )
(** A level: its atoms *)
| read_nf_order_lvl :
  `( read_level_atoms_order Θ Ξ s xs ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
(** A neutral level *)
| read_nf_order_lvl_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
(** A proposition, as a type *)
| read_nf_order_prop :
  `( read_typ_order Θ Ξ s a ->
     read_nf_order Θ Ξ s ⇓ Propᵈ a )
(** A type of levels, as a type *)
| read_nf_order_at_level_sort :
  `( read_typ_order Θ Ξ s a ->
     read_nf_order Θ Ξ s ⇓ LevelSortᵈ a )
(** A function: its domain, then its body under a fresh variable *)
| read_nf_order_fn :
  `( evaluated_kind κc ->
     read_typ_order Θ Ξ s a ->
     eval_app_order Θ Ξ m (⇑! a s) ->
     eval_exp_order Θ Ξ B (ρ ↦ ⇑! a s ⦂ entry_type_value a) ->
     (forall m' b,
         $| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
         read_nf_order Θ Ξ (S s) ⇓ b m') ->
     read_nf_order Θ Ξ s ⇓ (d_pi κd κc a ρ B) m )
(** A neutral at a neutral type *)
| read_nf_order_neut :
  `( evaluated_kind (domain_kind (⇑ a b)) ->
     read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (⇑ a b) (⇑ c m) )
(** A constructor of a declared member *)
| read_nf_order_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length as' = im_np D Mk ->
     List.length vs = (im_np D Mk + List.length gs)%nat ->
     read_ps_order Θ Ξ s nil (List.rev (im_params D Mk)) as' ->
     read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_tele nil (List.rev (im_params D Mk)) as') gs
       (List.skipn (im_np D Mk) vs) ->
     read_nf_order Θ Ξ s ⇓ (d_ind p k as') (d_con p k c vs) )
(** A constructor at a view: its arguments are the last values *)
| read_nf_order_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_con Mj c = Some gs ->
     List.length as' = im_np D Mj ->
     List.length gs <= List.length vs ->
     read_ps_order Θ Ξ s nil (List.rev (im_params D Mj)) as' ->
     read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_tele nil (List.rev (im_params D Mj)) as') gs
       (List.skipn (List.length vs - List.length gs) vs) ->
     read_nf_order Θ Ξ s ⇓ (d_ind p j as') (d_con qc k c vs) )
(** Any value at a record view: the view's constructor at the uniform
    parameters, its arguments the value's projections *)
| read_nf_order_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     List.length as' = ind_nu D ->
     eval_projs_order Θ Ξ fl v ->
     read_ps_order Θ Ξ s nil (List.rev (ind_uparams D)) as' ->
     (forall ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> read_cargs_order Θ Ξ s p as' (decl_env D as') gs ws) ->
     read_nf_order Θ Ξ s ⇓ (d_ind p j as') v )
(** A neutral of a member with a block *)
| read_nf_order_ind_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_is_rview Mk = false ->
     read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (d_ind p k as') (⇑ a m) )
(** A value of a record type: the type's parameters, then the fields *)
| read_nf_order_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     read_ps_order Θ Ξ s nil (List.rev (record_params R)) ns ->
     read_fields_order Θ Ξ s (env_tele nil (List.rev (record_params R)) ns) (record_fields R) v ->
     read_nf_order Θ Ξ s ⇓ (d_record p ns) v )
(** A value of a proposition: the proposition as a type, the proof as a
    term.  Last, so that a constructor tried in order meets the rules of
    each head first. *)
| read_nf_order_proof :
  `( domain_kind a = ak_propositional ->
     read_typ_order Θ Ξ s a ->
     read_proof_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ a m )

with read_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
(** A variable *)
| read_ne_order_var :
  `( read_ne_order Θ Ξ s #ᵈ x )
(** An application *)
| read_ne_order_app :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s n ->
     read_ne_order Θ Ξ s (m $ᵈ n) )
(** A stuck [efq]: its type and its proof *)
| read_ne_order_absurd :
  `( read_typ_order Θ Ξ s c ->
     read_proof_order Θ Ξ s p ->
     read_ne_order Θ Ξ s (efqᵈ p return c) )
(** A global without a value *)
| read_ne_order_glob :
  `( read_ne_order Θ Ξ s (d_glob p) )
(** A stuck eliminator: the container's uniform parameters, the blocks
    read as the container's group's, and the scrutinee *)
| read_ne_order_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     blocks_binder_count_at D None Bks ->
     rview_leaf_arity D ->
     eval_mref_order Θ Ξ p ups j ->
     (forall pre, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (pc, k, pre) -> read_ps_order Θ Ξ s nil (List.rev (ind_uparams Dq)) pre) ->
     read_blocks_order Θ Ξ s ρ p ups Bks Dq (im_sel Mj) 0 (ind_block_members Dq) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s (d_elim ρ Bks p ups j as' m) )
(** The field of a neutral *)
| read_ne_order_proj :
  `( read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s (d_proj f m) )

(** A proof, as a term *)
with read_proof_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
(** A neutral proof *)
| read_proof_order_neut :
  `( read_ne_order Θ Ξ s m ->
     read_proof_order Θ Ξ s (⇑ a m) )
(** A kept proof: the definitions of the positions it reads *)
| read_proof_order_kept :
  `( read_lets_order Θ Ξ s ρ (proof_scope M ρ) ->
     read_proof_order Θ Ξ s ⋆ᵈ⟨M, ρ⟩ )

(** The definitions binding the positions [k - 1], …, [0] of [ρ] *)
with read_lets_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> nat -> Prop :=
(** No position *)
| read_lets_order_nil :
  `( read_lets_order Θ Ξ s ρ 0 )
(** The outermost position, then the rest under it *)
| read_lets_order_cons :
  `( read_entry_order Θ Ξ s (env_entry ρ k) ->
     read_lets_order Θ Ξ (S s) ρ k ->
     read_lets_order Θ Ξ s ρ (S k) )

(** The definition an entry is bound by *)
with read_entry_order (Θ : gdeps) (Ξ : gstack) : nat -> dentry -> Prop :=
(** A term: its type value, read back, and its value at it *)
| read_entry_order_term :
  `( eval_entry_type_order Θ Ξ t ->
     (forall a, eval_entry_type Θ Ξ t a -> read_typ_order Θ Ξ s a) ->
     (forall a, eval_entry_type Θ Ξ t a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_entry_order Θ Ξ s (de_term v t) )
(** The term part of a definition with a module part, alike *)
| read_entry_order_dm :
  `( eval_entry_type_order Θ Ξ t ->
     (forall a, eval_entry_type Θ Ξ t a -> read_typ_order Θ Ξ s a) ->
     (forall a, eval_entry_type Θ Ξ t a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_entry_order Θ Ξ s (de_dm v t h U) )
(** A module: its stored unit *)
| read_entry_order_mod :
  `( read_entry_order Θ Ξ s (de_mod h U) )

with read_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
(** A large universe *)
| read_typ_order_univ :
  `( read_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| read_typ_order_suniv :
  `( read_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     read_typ_order Θ Ξ s 𝕌@l )
(** A type of levels *)
| read_typ_order_level :
  `( read_typ_order Θ Ξ s (Levelᵈ@n) )
(** The sort of the types of levels *)
| read_typ_order_level_sort :
  `( read_typ_order Θ Ξ s LevelSortᵈ )
(** [Prop] *)
| read_typ_order_prop :
  `( read_typ_order Θ Ξ s Propᵈ )
(** [⊤] *)
| read_typ_order_True :
  `( read_typ_order Θ Ξ s ⊤ᵈ )
(** [⊥] *)
| read_typ_order_False :
  `( read_typ_order Θ Ξ s ⊥ᵈ )
(** A [Π] at any kinds: its domain, then its codomain under a fresh
    variable *)
| read_typ_order_pi :
  `( read_typ_order Θ Ξ s a ->
     eval_exp_order Θ Ξ B (ρ ↦ ⇑! a s ⦂ entry_type_value a) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_typ_order Θ Ξ s (d_pi κd κc a ρ B))
(** A dependent conjunction *)
| read_typ_order_and :
  `( read_typ_order Θ Ξ s a ->
     eval_exp_order Θ Ξ Q (ρ ↦ ⇑! a s ⦂ entry_type_value a) ->
     (forall b,
         ⟦ Q ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_typ_order Θ Ξ s (Σₚᵈ a ρ Q))
(** A neutral type *)
| read_typ_order_neut :
  `( read_ne_order Θ Ξ s b ->
    read_typ_order Θ Ξ s ⇑ a b )
(** A member of a group at all its parameters *)
| read_typ_order_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length as' = im_np D Mk ->
     read_ps_order Θ Ξ s nil (List.rev (im_params D Mk)) as' ->
     read_typ_order Θ Ξ s (d_ind p k as') )
(** A record type at all its parameters *)
| read_typ_order_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     read_ps_order Θ Ξ s nil (List.rev (record_params R)) ns ->
     read_typ_order Θ Ξ s (d_record p ns) )

with read_level_atoms_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
(** No atom *)
| read_level_atoms_order_nil :
  `( read_level_atoms_order Θ Ξ s nil )
(** The first atom's neutral, then the rest *)
| read_level_atoms_order_cons :
  `( read_ne_order Θ Ξ s m ->
     read_level_atoms_order Θ Ξ s xs ->
     read_level_atoms_order Θ Ξ s ((k, n, m) :: xs) )

with read_ps_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> Prop :=
(** No value *)
| read_ps_order_nil :
  `( read_ps_order Θ Ξ s ρ nil nil )
(** The first value at its type, then the rest *)
| read_ps_order_cons :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_ps_order Θ Ξ s (ρ ↦ v ⦂ entry_type_closure A ρ) T vs ->
     read_ps_order Θ Ξ s ρ (ce_ass κ A :: T) (v :: vs) )

(** The fields of a record value, each its projection at its type *)
with read_fields_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list (string * exp) -> domain -> Prop :=
(** No field left *)
| read_fields_order_nil :
  `( read_fields_order Θ Ξ s ρ nil v )
(** The next field: its projection, its type, its readback, then the rest
    with the projection in the environment *)
| read_fields_order_cons :
  `( eval_proj_order Θ Ξ f v ->
     eval_exp_order Θ Ξ T ρ ->
     (forall r t, eval_proj Θ Ξ f v r -> ⟦ T ⟧ Θ ⍮ Ξ ⍮ ρ ↘ t -> read_nf_order Θ Ξ s ⇓ t r) ->
     (forall r, eval_proj Θ Ξ f v r -> read_fields_order Θ Ξ s (ρ ↦ r ⦂ entry_type_closure T ρ) fl v) ->
     read_fields_order Θ Ξ s ρ ((f, T) :: fl) v )

with read_cargs_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> Prop :=
(** No argument *)
| read_cargs_order_nil :
  `( read_cargs_order Θ Ξ s p ups ρ nil nil )
(** A non-recursive argument, at its declared type *)
| read_cargs_order_arg :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_cargs_order Θ Ξ s p ups (ρ ↦ v ⦂ entry_type_closure A ρ) gs vs ->
     read_cargs_order Θ Ξ s p ups ρ (ca_arg r A :: gs) (v :: vs) )
(** A recursive argument, along its shape *)
| read_cargs_order_rec_case :
  `( read_shape_order Θ Ξ s p ups ρ t v ->
     read_cargs_order Θ Ξ s p ups ρ gs vs ->
     read_cargs_order Θ Ξ s p ups ρ (ca_rec t :: gs) (v :: vs) )

(** A recursive argument of a shape *)
with read_shape_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> ptyp -> domain -> Prop :=
(** At the end: the parameters, then the value at the member *)
| read_shape_order_self :
  `( eval_exps_order Θ Ξ Ps ρ ->
     (forall bs, ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs -> read_nf_order Θ Ξ s ⇓ (d_ind p j (ups ++ bs)) v) ->
     read_shape_order Θ Ξ s p ups ρ (pt_self j Ps) v )
(** At a domain: under a fresh variable of it *)
| read_shape_order_pi :
  `( eval_exp_order Θ Ξ B ρ ->
     (forall b, ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b -> read_typ_order Θ Ξ s b) ->
     (forall b, ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b -> eval_app_order Θ Ξ v (⇑! b s)) ->
     (forall b r, ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b -> $| v & ⇑! b s | Θ ⍮ Ξ ↘ r ->
        read_shape_order Θ Ξ (S s) p ups (ρ ↦ ⇑! b s ⦂ entry_type_closure B ρ) t r) ->
     read_shape_order Θ Ξ s p ups ρ (pt_pi B t) v )

(** The blocks of a stuck eliminator *)
with read_blocks_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                                  option (list nat) -> nat -> list imember -> Prop :=
(** No member left *)
| read_blocks_order_nil :
  `( read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i nil )
(** The block of the member [Mi]: the scrutinee's type, its motive, its
    branches, then the rest *)
| read_blocks_order_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     Nat.eqb (eb_binder_count b) (S (im_nn Mi)) = true ->
     eval_mref_order Θ Ξ p ups (elim_src sel i) ->
     fresh_tele_order Θ Ξ (decl_env D ups) (List.rev (im_nparams Mv)) s ->
     (forall pk k pre ns, ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
        read_typ_order Θ Ξ (s + im_nn Mi) (d_ind pk k (pre ++ ns))) ->
     (forall pk k pre ns, ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
        eval_exp_order Θ Ξ (eb_motive b)
          (env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns)) (⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat))))) ->
     (forall pk k pre ns a, ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
        ⟦ eb_motive b ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns))
                                                     (⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat))) ↘ a ->
        read_typ_order Θ Ξ (S (s + im_nn Mi)) a) ->
     (forall pk k pre, ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        read_brs_order Θ Ξ s ρ p ups Bks Dc Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b)) ->
     read_blocks_order Θ Ξ s ρ p ups Bks Dc sel (S i) Ms ->
     read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i (Mi :: Ms) )

(** The branches of a block *)
with read_brs_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                               imember -> exp -> imember -> (qname * nat * list domain) ->
                                               list (string * list carg) -> list (string * nat * exp) -> Prop :=
(** No constructor left *)
| read_brs_order_nil :
  `( read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r nil nil )
(** The branch of the next constructor, then the rest *)
| read_brs_order_cons :
  `( ind_con Mv c = Some gs ->
     Nat.eqb n0 (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat = true ->
     ind_lookup Θ Ξ p = Some D ->
     cargs_container_count D Dc gs' gs = cargs_nrec Dc gs' ->
     cargs_params_length D gs ->
     fresh_tele_order Θ Ξ (decl_env D ups) (List.rev (im_nparams Mv)) s ->
     (forall ns,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
         fresh_cargs_order Θ Ξ p ups (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns) gs (s + im_nn Mi)) ->
     (forall ns vs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
         fresh_ihs_order Θ Ξ ρ (blocks_motives Bks) p ups Dc (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns)
           gs' gs vs (s + im_nn Mi + List.length gs')) ->
     (forall ns vs ihs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
         Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ
           ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs) ->
     (forall ns vs ihs wihs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
         Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ
           ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         eval_exp_order Θ Ξ B (env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs))) ->
     (forall ns vs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
         eval_exp_order Θ Ξ A (env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns)) (d_con pk k c (pre ++ ns ++ vs))))) ->
     (forall ns vs ihs wihs b t,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
         Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ
           ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs) ↘ b ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns)) (d_con pk k c (pre ++ ns ++ vs))) ↘ t ->
         read_nf_order Θ Ξ (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) ⇓ t b) ->
     read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi (pk, k, pre) cs Bs ->
     read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi (pk, k, pre) ((c, gs') :: cs) ((c, n0, B) :: Bs) ).

#[local]
Hint Constructors read_nf_order read_ne_order read_proof_order read_lets_order read_entry_order
  read_typ_order read_level_atoms_order read_ps_order read_fields_order read_cargs_order
  read_shape_order read_blocks_order read_brs_order : mctt.

(** Every readback derivation is within its order: by the mutual induction
    on readback, the evaluations the orders quantify over being the ones
    the derivation makes ([functional_eval]). *)
Lemma read_order_sound : forall Θ Ξ,
    (forall s d m, Rnf d in Θ ⍮ Ξ ⍮ s ↘ m -> read_nf_order Θ Ξ s d) /\
    (forall s d m, Rne d in Θ ⍮ Ξ ⍮ s ↘ m -> read_ne_order Θ Ξ s d) /\
    (forall s d m, Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m -> read_typ_order Θ Ξ s d) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> read_level_atoms_order Θ Ξ s xs) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> read_ps_order Θ Ξ s ρ T vs) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> read_cargs_order Θ Ξ s p ups ρ gs vs) /\
    (forall s p ups ρ t v V, Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> read_shape_order Θ Ξ s p ups ρ t v) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs) /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> read_fields_order Θ Ξ s ρ fl v) /\
    (forall s d M, Rprf d in Θ ⍮ Ξ ⍮ s ↘ M -> read_proof_order Θ Ξ s d) /\
    (forall s ρ k bs, Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs -> read_lets_order Θ Ξ s ρ k) /\
    (forall s e b, Rent e in Θ ⍮ Ξ ⍮ s ↘ b -> read_entry_order Θ Ξ s e).
Proof.
  intros Θ Ξ; apply read_mut_ind; intros;
    (** A constructor at a view: its arguments are the last values, as
        many as the constructor takes. *)
    try match goal with Hh : im_head _ = mh_view _ _ _ _, Hl : List.length ?vs = (?n + List.length ?gs)%nat
                        |- read_nf_order _ _ _ (⇓ _ (d_con _ _ _ ?vs)) =>
          replace n with (List.length vs - List.length gs) in * by lia end;
    first [ solve [ eapply read_nf_order_ind_neut; eassumption ]
          | solve [ eapply read_nf_order_proof; eassumption ]
          | (econstructor; try eassumption; try lia; try (apply Nat.eqb_eq; first [ assumption | subst; reflexivity ]);
             intros; functional_eval_rewrite_clear; functional_fresh_rewrite_clear;
             functional_eval_rewrite_clear; subst; mauto) ].
Qed.

Lemma read_nf_order_sound : forall Θ Ξ s d m, Rnf d in Θ ⍮ Ξ ⍮ s ↘ m -> read_nf_order Θ Ξ s d.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_ne_order_sound : forall Θ Ξ s d m, Rne d in Θ ⍮ Ξ ⍮ s ↘ m -> read_ne_order Θ Ξ s d.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_typ_order_sound : forall Θ Ξ s d m, Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m -> read_typ_order Θ Ξ s d.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_level_atoms_order_sound : forall Θ Ξ s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> read_level_atoms_order Θ Ξ s xs.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_ps_order_sound : forall Θ Ξ s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> read_ps_order Θ Ξ s ρ T vs.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_cargs_order_sound : forall Θ Ξ s p ups ρ gs vs Ms,
    Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> read_cargs_order Θ Ξ s p ups ρ gs vs.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_shape_order_sound : forall Θ Ξ s p ups ρ t v V,
    Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> read_shape_order Θ Ξ s p ups ρ t v.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_blocks_order_sound : forall Θ Ξ s ρ p ups Bks Dc sel i Ms NBks,
    Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks -> read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_brs_order_sound : forall Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs',
    Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' -> read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_fields_order_sound : forall Θ Ξ s ρ fl v Fs,
    Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> read_fields_order Θ Ξ s ρ fl v.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_proof_order_sound : forall Θ Ξ s d M, Rprf d in Θ ⍮ Ξ ⍮ s ↘ M -> read_proof_order Θ Ξ s d.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_lets_order_sound : forall Θ Ξ s ρ k bs, Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs -> read_lets_order Θ Ξ s ρ k.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma read_entry_order_sound : forall Θ Ξ s e b, Rent e in Θ ⍮ Ξ ⍮ s ↘ b -> read_entry_order Θ Ξ s e.
Proof. intros Θ Ξ; pose proof (read_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound read_level_atoms_order_sound
  read_ps_order_sound read_cargs_order_sound read_shape_order_sound read_blocks_order_sound
  read_brs_order_sound read_fields_order_sound read_proof_order_sound read_lets_order_sound
  read_entry_order_sound : mctt.

(** A constructor at a view, its arguments the last values, as many as the
    constructor takes ([read_nf_con_view]). *)
Lemma read_nf_con_view_last : forall Θ Ξ s p D j Mj qc k Is vm c gs as' vs n Ps Args,
    ind_lookup Θ Ξ p = Some D ->
    ind_member D j = Some Mj ->
    im_head Mj = mh_view qc k Is vm ->
    ind_con Mj c = Some gs ->
    List.length as' = im_np D Mj ->
    Rps as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
    Rcargs List.skipn (n - List.length gs) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ
      ⍮ env_tele nil (List.rev (im_params D Mj)) as' ⍮ s ↘ Args ->
    List.length gs <= n ->
    (** The number of values, as the readback computes it *)
    n = List.length vs ->
    Rnf ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args).
Proof. intros; subst; eapply read_nf_con_view; try eassumption; lia. Qed.

#[local]
Ltac impl_obligation_tac1 :=
  match goal with
  | H : read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : read_proof_order _ _ _ _ |- _ => progressive_invert H
  | H : read_lets_order _ _ _ _ _ |- _ => progressive_invert H
  | H : read_entry_order _ _ _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : read_level_atoms_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ps_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_fields_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_cargs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_shape_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_blocks_order _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  (** A value at a member of a group: a constructor at a declared member
      or at a view, a neutral, or any value at a record view, the lookups
      then excluding all but one *)
  | H : read_nf_order _ _ _ (⇓ (d_ind _ _ _) _) |- _ => inversion H; subst; clear H
  (** A value at a [Π] or at a neutral type: a function or a neutral, or a
      proof, the kind then excluding one *)
  | H : read_nf_order _ _ _ (⇓ (d_pi _ _ _ _ _) _) |- _ => inversion H; subst; clear H
  | H : read_nf_order _ _ _ (⇓ (⇑ _ _) _) |- _ => inversion H; subst; clear H
  end.

Section ReadbackImpl.
Variable F : FCtx.
#[local] Abbreviation Θ := (fc_deps F).
#[local] Abbreviation Ξ := (fc_stack F).

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations fast_read_nf_impl_c s (d : fdomain_nf) (ck : lookup_cache Θ Ξ) (Hd : fdomain_nf_ok Θ Ξ d)
    (H : read_nf_order Θ Ξ s (fdomain_nf_erase d)) : { m | Rnf fdomain_nf_erase d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, fd_dom (fd_univ i) a, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    exist _ A _
| s, fd_dom (fd_suniv n) a, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    exist _ A _
| s, fd_dom (fd_level n) (fd_lvl c xs), ck, Hd, H =>
    let (ys, Hys) := fast_read_level_atoms_impl_c s xs ck _ _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, fd_dom (fd_level n) (fd_neut a m), ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ (lvⁿ ordinal_zero (cons (mk_level_atom 0 (fdomain_level_sort a) M) nil)) _
(** A value of a proposition: the proposition as a type, the proof as a
    term *)
| s, fd_dom fd_True m, ck, Hd, H =>
    let (M, HM) := fast_read_proof_impl_c s m ck _ _ in
    exist _ (nf_proof ⊤ⁿ M) _
| s, fd_dom fd_False m, ck, Hd, H =>
    let (M, HM) := fast_read_proof_impl_c s m ck _ _ in
    exist _ (nf_proof ⊥ⁿ M) _
| s, fd_dom (fd_and a ρ Q) m, ck, Hd, H =>
    let (P, HP) := fast_read_typ_impl_c s (fd_and a ρ Q) ck _ _ in
    let (M, HM) := fast_read_proof_impl_c s m ck _ _ in
    exist _ (nf_proof P M) _
(** A proposition, as a type *)
| s, fd_dom fd_prop a, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    exist _ A _
(** A type of levels, as a type *)
| s, fd_dom fd_level_sort a, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    exist _ A _
(** A [Π]: a proof into a proposition, a function otherwise *)
| s, fd_dom (fd_pi κd κc a ρ B) m, ck, Hd, H with inspect (fdomain_is_prop (fd_pi κd κc a ρ B)) := {
  | exist _ true Ek =>
      let (P, HP) := fast_read_typ_impl_c s (fd_pi κd κc a ρ B) ck _ _ in
      let (M, HM) := fast_read_proof_impl_c s m ck _ _ in
      exist _ (nf_proof P M) _
  | exist _ false Ek =>
      let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
      let (m', Hm') := fast_eval_app_impl F m (fd_neut a (fd_var s)) _ _ _ in
      let (b, Hb) := fast_eval_exp_impl F B (fextend_env ρ (fd_neut a (fd_var s)) (fentry_type_value a)) _ _ in
      let (M, HM) := fast_read_nf_impl_c (S s) (fd_dom b m') ck _ _ in
      exist _ (λⁿ A M) _ }
(** A neutral type: the proof at a proposition, a neutral otherwise *)
| s, fd_dom (fd_neut a b) v, ck, Hd, H with inspect (fdomain_is_prop (fd_neut a b)) := {
  | exist _ true Ek =>
      let (P, HP) := fast_read_typ_impl_c s (fd_neut a b) ck _ _ in
      let (M, HM) := fast_read_proof_impl_c s v ck _ _ in
      exist _ (nf_proof P M) _
  | exist _ false Ek with v := {
    | fd_neut c m =>
        let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
        exist _ (⇑ⁿ{fdomain_kind (fd_neut a b)} M) _
    | _ => False_rect _ _ } }
| s, fd_dom (fd_ind p oD j as') v, ck, Hd, H with carried_lookup F ck p oD (fdomain_nf_ok_dom_ind_carried _ _ _ _ _ _ _ Hd) := {
  | inleft (exist _ D Ed) with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_head Mj) := {
      (** At a record view, any value: the view's constructor, its
          arguments the value's projections *)
      | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
        | exist _ ((c, gs) :: nil) Ec =>
            let (ws, Hws) := fast_eval_projs_impl F fl v _ _ in
            let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (ind_uparams D)) as' ck _ _ _ in
            let (Args, HArgs) := fast_read_cargs_impl_c s p as' (fdecl_env D as') gs ws (Some (exist _ (p, D) Ed)) _ _ _ _ in
            exist _ (nf_con p j c (Ps ++ Args)%list) _
        | exist _ _ Ec => False_rect _ _ }
      | exist _ (mh_decl pm) Eh with v := {
        (** A constructor of a declared member: its arguments after its
            parameters *)
        | fd_con _ _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ _ _ in
              let (Args, HArgs) := fast_read_cargs_impl_c s p (List.firstn (ind_nu D) as') (fenv_tele nil (List.rev (im_params D Mj)) as') gs
                                     (List.skipn (im_np D Mj) vs) (Some (exist _ (p, D) Ed)) _ _ _ _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | fd_neut a m =>
            let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
            exist _ (⇑ⁿ{ak_relevant} M) _
        | _ => False_rect _ _ }
      | exist _ (mh_view qv kv Iv vmv) Eh with v := {
        (** At a view: its arguments are the last values *)
        | fd_con _ _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ _ _ in
              let (Args, HArgs) := fast_read_cargs_impl_c s p (List.firstn (ind_nu D) as') (fenv_tele nil (List.rev (im_params D Mj)) as') gs
                                     (List.skipn (List.length vs - List.length gs) vs) (Some (exist _ (p, D) Ed)) _ _ _ _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | fd_neut a m =>
            let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
            exist _ (⇑ⁿ{ak_relevant} M) _
        | _ => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | inright Ed => False_rect _ _ }
| s, fd_dom (fd_record p ns) v, ck, Hd, H with record_lookup_f F p := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (record_params R)) ns ck _ _ _ in
      let (Fs, HFs) := fast_read_fields_impl_c s (fenv_tele nil (List.rev (record_params R)) ns) (record_fields R) v ck _ _ _ in
      exist _ (nf_tuple p Ps (List.map fst (record_fields R)) Fs) _
  | exist _ None El => False_rect _ _ }
(** No other value has a readback order *)
| s, _, ck, Hd, H => False_rect _ _

  with fast_read_ne_impl_c s (d : fdomain_ne) (ck : lookup_cache Θ Ξ) (Hd : fdomain_ne_ok Θ Ξ d)
      (H : read_ne_order Θ Ξ s (fdomain_ne_erase d)) : { m | Rne fdomain_ne_erase d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, fd_var x, ck, Hd, H => exist _ #ⁿ (s - x - 1) _
| s, fd_glob p, ck, Hd, H => exist _ (ne_glob p) _
| s, fd_app m n, ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    let (N, HN) := fast_read_nf_impl_c s n ck _ _ in
    exist _ (M $ⁿ N) _
| s, fd_absurd c p, ck, Hd, H =>
    let (C, HC) := fast_read_typ_impl_c s c ck _ _ in
    let (M, HM) := fast_read_proof_impl_c s p ck _ _ in
    exist _ (efqⁿ M return C) _
(** The stuck eliminator carries the declaration of its group *)
| s, fd_elim ρ Bks p D ups j as' m, ck, Hd, H with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_ref p j Mj) := {
      | exist _ (pc, k) Er with decl_lookup F (Some (exist _ (p, D) (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd))) pc := {
        | inleft (exist _ Dq Edq) with fast_eval_mref_impl F p ups j _ _ := {
          | exist _ (mk_fast_member_reference _ _ _ pre) Hm =>
              let (Us, HUs) := fast_read_ps_impl_c s nil (List.rev (ind_uparams Dq)) pre ck _ _ _ in
              let (NBks, HNBks) := fast_read_blocks_impl_c s ρ p ups Bks Dq (im_sel Mj) 0 (ind_block_members Dq)
                                     D (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd)
                                     (Some (exist _ (p, D) (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd))) _ _ _ in
              let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
              exist _ (ne_elim pc Us k NBks M) _ }
        | inright Edq => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
| s, fd_proj f m, ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ (ne_proj f M) _

  (** A proof, as a term: a neutral, or a kept proof under the definitions
      of the positions it reads *)
  with fast_read_proof_impl_c s (d : fdomain) (ck : lookup_cache Θ Ξ) (Hd : fdomain_ok Θ Ξ d)
      (H : read_proof_order Θ Ξ s (fdomain_erase d)) : { M | Rprf fdomain_erase d in Θ ⍮ Ξ ⍮ s ↘ M } by struct H :=
| s, fd_neut a m, ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ (ne_to_exp M) _
| s, fd_proof M ρ, ck, Hd, H =>
    let (bs, Hbs) := fast_read_lets_impl_c s ρ (fproof_scope M ρ) ck _ _ in
    exist _ (lets_exp bs M) _
| s, _, ck, Hd, H => False_rect _ _

  (** The definitions binding the positions [k - 1], …, [0] of [ρ],
      outermost first *)
  with fast_read_lets_impl_c s (ρ : fenv) k (ck : lookup_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ)
      (H : read_lets_order Θ Ξ s (fenv_erase ρ) k) : { bs | Rlets fenv_erase ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs } by struct H :=
| s, ρ, 0, ck, Hρ, H => exist _ nil _
| s, ρ, S k, ck, Hρ, H =>
    let (b, Hb) := fast_read_entry_impl_c s (fenv_entry ρ k) ck _ _ in
    let (bs, Hbs) := fast_read_lets_impl_c (S s) ρ k ck Hρ _ in
    exist _ (b :: bs) _

  (** The definition an entry is bound by *)
  with fast_read_entry_impl_c s (e : fdentry) (ck : lookup_cache Θ Ξ) (He : fdentry_ok Θ Ξ e)
      (H : read_entry_order Θ Ξ s (fdentry_erase e)) : { b | Rent fdentry_erase e in Θ ⍮ Ξ ⍮ s ↘ b } by struct H :=
| s, fde_term v t, ck, He, H =>
    let (a, Ha) := fast_eval_entry_type_impl F t _ _ in
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    let (W, HW) := fast_read_nf_impl_c s (fd_dom a v) ck _ _ in
    exist _ (b_def A W) _
(** A definition with a module part, as [read_entry_dm]: its term part as
    a definition's, its stored unit as a module's *)
| s, fde_dm v t h U, ck, He, H =>
    let (a, Ha) := fast_eval_entry_type_impl F t _ _ in
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    let (W, HW) := fast_read_nf_impl_c s (fd_dom a v) ck _ _ in
    exist _ (b_def_mod A W U) _
| s, fde_mod h U, ck, He, H => exist _ (b_mod U) _

  with fast_read_typ_impl_c s (d : fdomain) (ck : lookup_cache Θ Ξ) (Hd : fdomain_ok Θ Ξ d)
      (H : read_typ_order Θ Ξ s (fdomain_erase d)) : { m | Rtyp fdomain_erase d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, fd_univ i, ck, Hd, H => exist _ Typeωⁿ@i _
| s, fd_suniv l, ck, Hd, H =>
    let (W, HW) := fast_read_nf_impl_c s (fd_dom (fd_level 0) l) ck _ _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, fd_level n, ck, Hd, H => exist _ (Levelⁿ@n) _
| s, fd_level_sort, ck, Hd, H => exist _ LevelSortⁿ _
| s, fd_prop, ck, Hd, H => exist _ Propⁿ _
| s, fd_True, ck, Hd, H => exist _ ⊤ⁿ _
| s, fd_False, ck, Hd, H => exist _ ⊥ⁿ _
| s, fd_pi κd κc a ρ B, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    let (b, Hb) := fast_eval_exp_impl F B (fextend_env ρ (fd_neut a (fd_var s)) (fentry_type_value a)) _ _ in
    let (B', HB') := fast_read_typ_impl_c (S s) b ck _ _ in
    exist _ (nf_pi κd κc A B') _
| s, fd_and a ρ Q, ck, Hd, H =>
    let (P', HP') := fast_read_typ_impl_c s a ck _ _ in
    let (b, Hb) := fast_eval_exp_impl F Q (fextend_env ρ (fd_neut a (fd_var s)) (fentry_type_value a)) _ _ in
    let (Q', HQ') := fast_read_typ_impl_c (S s) b ck _ _ in
    exist _ (Σₚⁿ P' Q') _
| s, fd_neut a b, ck, Hd, H =>
    let (B, HB) := fast_read_ne_impl_c s b ck _ _ in
    exist _ (⇑ⁿ{fdomain_kind (fd_neut a b)} B) _
| s, fd_ind p oD k as', ck, Hd, H with carried_lookup F ck p oD (fdomain_ok_ind_carried _ _ _ _ _ _ Hd) := {
  | inleft (exist _ D Ed) with inspect (ind_member D k) := {
    | exist _ (Some Mk) Em =>
        let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mk)) as' ck _ _ _ in
        exist _ (nf_indty p k Ps) _
    | exist _ None Em => False_rect _ _ }
  | inright Ed => False_rect _ _ }
| s, fd_record p ns, ck, Hd, H with record_lookup_f F p := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (record_params R)) ns ck _ _ _ in
      exist _ (nf_record p Ps) _
  | exist _ None El => False_rect _ _ }
(** No other value has a readback order as a type *)
| s, _, ck, Hd, H => False_rect _ _

  with fast_read_level_atoms_impl_c s (xs : list (nat * nat * fdomain_ne)) (ck : lookup_cache Θ Ξ)
      (Hxs : Forall (fun ka => fdomain_ne_ok Θ Ξ (snd ka)) xs)
      (H : read_level_atoms_order Θ Ξ s (List.map (fun ka => (fst ka, fdomain_ne_erase (snd ka))) xs)) :
      { ys | Rla List.map (fun ka => (fst ka, fdomain_ne_erase (snd ka))) xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, ck, Hxs, H => exist _ nil _
| s, cons (k, n, m) xs, ck, Hxs, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    let (ys, Hys) := fast_read_level_atoms_impl_c s xs ck _ _ in
    exist _ (cons (mk_level_atom k n M) ys) _

  with fast_read_ps_impl_c s (ρ : fenv) T (vs : list fdomain) (ck : lookup_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ)
      (Hvs : Forall (fdomain_ok Θ Ξ) vs) (H : read_ps_order Θ Ξ s (fenv_erase ρ) T (fdomains_erase vs)) :
      { Ms | Rps fdomains_erase vs at T in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, ck, Hρ, Hvs, H => exist _ nil _
| s, ρ, ce_ass κ A :: T, v :: vs, ck, Hρ, Hvs, H =>
    let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom a v) ck _ _ in
    let (Vs, HVs) := fast_read_ps_impl_c s (fextend_env ρ v (fentry_type_closure A ρ)) T vs ck _ _ _ in
    exist _ (cons V Vs) _
| s, ρ, _, _, ck, Hρ, Hvs, H => False_rect _ _

  with fast_read_fields_impl_c s (ρ : fenv) fl (v : fdomain) (ck : lookup_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ) (Hv : fdomain_ok Θ Ξ v)
      (H : read_fields_order Θ Ξ s (fenv_erase ρ) fl (fdomain_erase v)) :
    { Fs | Rflds fdomain_erase v at fl in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Fs } by struct H :=
| s, ρ, nil, v, ck, Hρ, Hv, H => exist _ nil _
| s, ρ, (f, T) :: fl, v, ck, Hρ, Hv, H =>
    let (r, Hr) := fast_eval_proj_impl F f v Hv _ in
    let (t, Ht) := fast_eval_exp_impl F T ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom t r) ck _ _ in
    let (Vs, HVs) := fast_read_fields_impl_c s (fextend_env ρ r (fentry_type_closure T ρ)) fl v ck _ Hv _ in
    exist _ (cons V Vs) _

  with fast_read_cargs_impl_c s p (ups : list fdomain) (ρ : fenv) gs (vs : list fdomain) (ck : lookup_cache Θ Ξ)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρ : fenv_ok Θ Ξ ρ) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : read_cargs_order Θ Ξ s p (fdomains_erase ups) (fenv_erase ρ) gs (fdomains_erase vs)) :
    { Ms | Rcargs fdomains_erase vs at gs of p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Ms } by struct H :=
| s, p, ups, ρ, nil, nil, ck, Hups, Hρ, Hvs, H => exist _ nil _
| s, p, ups, ρ, ca_arg r A :: gs, v :: vs, ck, Hups, Hρ, Hvs, H =>
    let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom a v) ck _ _ in
    let (Vs, HVs) := fast_read_cargs_impl_c s p ups (fextend_env ρ v (fentry_type_closure A ρ)) gs vs ck Hups _ _ _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, ca_rec t :: gs, v :: vs, ck, Hups, Hρ, Hvs, H =>
    let (V, HV) := fast_read_shape_impl_c s p ups ρ t v ck Hups Hρ _ _ in
    let (Vs, HVs) := fast_read_cargs_impl_c s p ups ρ gs vs ck Hups Hρ _ _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, _, _, ck, Hups, Hρ, Hvs, H => False_rect _ _

  with fast_read_shape_impl_c s p (ups : list fdomain) (ρ : fenv) t (v : fdomain) (ck : lookup_cache Θ Ξ)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρ : fenv_ok Θ Ξ ρ) (Hv : fdomain_ok Θ Ξ v)
      (H : read_shape_order Θ Ξ s p (fdomains_erase ups) (fenv_erase ρ) t (fdomain_erase v)) :
    { V | Rsh fdomain_erase v at t of p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ V } by struct H :=
| s, p, ups, ρ, pt_self j Ps, v, ck, Hups, Hρ, Hv, H =>
    let (bs, Hbs) := fast_eval_exps_impl F Ps ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom (fd_ind p None j (ups ++ bs)) v) ck _ _ in
    exist _ V _
| s, p, ups, ρ, pt_pi B t, v, ck, Hups, Hρ, Hv, H =>
    let (b, Hb) := fast_eval_exp_impl F B ρ Hρ _ in
    let (A, HA) := fast_read_typ_impl_c s b ck _ _ in
    let (r, Hr) := fast_eval_app_impl F v (fd_neut b (fd_var s)) Hv _ _ in
    let (V, HV) := fast_read_shape_impl_c (S s) p ups (fextend_env ρ (fd_neut b (fd_var s)) (fentry_type_closure B ρ)) t r ck Hups _ _ _ in
    exist _ (λⁿ A V) _

  (** The blocks of a stuck eliminator, at the declaration [D] of its
      group *)
  with fast_read_blocks_impl_c s (ρ : fenv) p (ups : list fdomain) Bks Dc sel i Ms (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D)
      (ck : lookup_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups)
      (H : read_blocks_order Θ Ξ s (fenv_erase ρ) p (fdomains_erase ups) Bks Dc sel i Ms) :
    { NBks | Rblks i Ms of Dc from p (fdomains_erase ups) Bks sel in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ NBks } by struct H :=
| s, ρ, p, ups, Bks, Dc, sel, i, nil, D, Ed, ck, Hρ, Hups, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, sel, i, Mi :: Ms, D, Ed, ck, Hρ, Hups, H with inspect (ind_member D (elim_src sel i)) := {
    | exist _ (Some Mv) Em with inspect (List.nth_error Bks (elim_src sel i)) := {
      | exist _ (Some b) Eb with fast_eval_mref_impl F p ups (elim_src sel i) Hups _ := {
        | exist _ (mk_fast_member_reference pk oDk k pre) Hm =>
            let (ns, Hns) := fast_fresh_tele_impl F (fdecl_env D ups) (List.rev (im_nparams Mv)) s _ _ in
            let (Z', HZ') := fast_read_typ_impl_c (s + im_nn Mi) (fd_ind pk oDk k (pre ++ ns)) ck _ _ in
            let (a, Ha) := fast_eval_exp_impl F (eb_motive b)
                             (fenv_extend_typed ρ (fmotive_entries D Mv ups ns (fd_ind pk oDk k (pre ++ ns))
                                                    (fd_neut (fd_ind pk oDk k (pre ++ ns)) (fd_var (s + im_nn Mi)%nat)))) _ _ in
            let (A', HA') := fast_read_typ_impl_c (S (s + im_nn Mi)) a ck _ _ in
            let (Bs', HBs') := fast_read_brs_impl_c s ρ p ups Bks Dc Mv (eb_motive b) Mi (mk_fast_member_reference pk oDk k pre)
                                 (im_cons Mi) (eb_brs b)
                                 D Ed ck Hρ Hups _ _ in
            let (NBks, HNBks) := fast_read_blocks_impl_c s ρ p ups Bks Dc sel (S i) Ms D Ed ck Hρ Hups _ in
            exist _ (cons (mk_normal_block (S (im_nn Mi)) Z' A' Bs') NBks) _ }
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }

  (** The branches of a block, at the declaration [D] of the group *)
  with fast_read_brs_impl_c s (ρ : fenv) p (ups : list fdomain) Bks Dc Mv A Mi (r : fast_member_reference) cs Bs
         (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D) (ck : lookup_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups)
         (Hr : fast_member_reference_ok Θ Ξ r)
         (H : read_brs_order Θ Ξ s (fenv_erase ρ) p (fdomains_erase ups) Bks Dc Mv A Mi (fast_member_reference_erase r) cs Bs) :
    { Bs' | Rbrs Bs at cs of Mi (fast_member_reference_erase r) of Dc from p (fdomains_erase ups) Bks Mv A
              in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Bs' } by struct H :=
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, nil, nil, D, Ed, ck, Hρ, Hups, Hr, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, mk_fast_member_reference pk oDk k pre, (c, gs') :: cs, (_, _, B) :: Bs, D, Ed, ck, Hρ, Hups, Hr, H
    with inspect (ind_con Mv c) := {
  | exist _ (Some gs) Ec =>
      let (ns, Hns) := fast_fresh_tele_impl F (fdecl_env D ups) (List.rev (im_nparams Mv)) s _ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl F p ups (fenv_tele (fdecl_env D ups) (List.rev (im_nparams Mv)) ns) gs (s + im_nn Mi) Hups _ _ in
      let (ihs, Hihs) := fast_fresh_ihs_impl F ρ (blocks_motives Bks) p ups Dc (fenv_tele (fdecl_env D ups) (List.rev (im_nparams Mv)) ns)
                           gs' gs vs (s + im_nn Mi + List.length gs') D Ed Hρ Hups _ _ _ in
      let (wihs, Hw) := fast_wrap_ihs_impl F ρ p ups Bks Dc gs' gs vs ihs D Ed Hρ Hups _ _ _ in
      let (b, Hb) := fast_eval_exp_impl F B (fenv_extend_typed ρ (fbranch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs)) _ _ in
      let (t, Ht) := fast_eval_exp_impl F A (fenv_extend_typed ρ (fmotive_entries D Mv ups ns (fd_ind pk oDk k (pre ++ ns))
                                                                   (fd_con pk oDk k c (pre ++ ns ++ vs)))) _ _ in
      let (B', HB') := fast_read_nf_impl_c (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) (fd_dom t b) ck _ _ in
      let (Bs', HBs') := fast_read_brs_impl_c s ρ p ups Bks Dc Mv A Mi (mk_fast_member_reference pk oDk k pre) cs Bs D Ed ck Hρ Hups Hr _ in
      exist _ (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dc gs') B') Bs') _
  | exist _ None Ec => False_rect _ _ }
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, _, _, D, Ed, ck, Hρ, Hups, Hr, H => False_rect _ _.

(** Each hole is either a readback order of a subterm, read off the order of
    the whole by inversion, or the readback itself, by its rule. *)
(** The lookups the order records are the ones computed.  The computed
    one is replaced, in the goal, by the recorded one: the order premises
    about the recorded one are then the arguments of the recursion as they
    stand, which the structural recursion needs. *)
#[local]
Ltac readback_unify x y :=
  let Heq := fresh "Heq" in
  intro Heq;
  first [ is_var y; lazymatch goal with |- context [y] => subst y end
        | is_var x; lazymatch goal with |- context [x] => subst x end
        | subst ].

#[local]
Ltac readback_glob :=
  repeat match goal with
    | H1 : ind_lookup _ _ ?p = Some ?x, H2 : ind_lookup _ _ ?p = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : ind_con ?D ?c = Some ?x, H2 : ind_con ?D ?c = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : ind_member ?D ?k = Some ?x, H2 : ind_member ?D ?k = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : List.nth_error ?Bks ?j = Some ?x, H2 : List.nth_error ?Bks ?j = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
        rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
    | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
        rewrite H1 in H2; injection H2; clear H2; intros; subst
    (** A record view, by its head; its one constructor *)
    | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
        exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
    | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
        rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
    (** The kind of a type of a known head, computed: a proof's order at a
        type that is no proposition is ruled out *)
    | H : domain_kind _ = _ |- _ => progress cbn [domain_kind] in H; try discriminate H
    | H : evaluated_kind ak_propositional |- _ => exfalso; exact (evaluated_kind_not_propositional _ H eq_refl)
    | H1 : evaluated_kind ?k, H2 : ?k = ak_propositional |- _ => exfalso; exact (evaluated_kind_not_propositional _ H1 H2)
    (** A record, looked up once *)
    | H1 : record_lookup _ _ ?p = Some ?x, H2 : record_lookup _ _ ?p = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    (** The member a member stands for, at the reference the order records *)
    | Hm : eval_mref _ _ ?p _ ?j (?a, ?b, _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
      Hr : im_ref ?p ?j _ = (?c, ?d) |- _ =>
        assert_fails (constr_eq a c);
        let E := fresh "Er" in
        pose proof (eval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) as E;
        rewrite E in Hr; injection Hr; clear Hr; intros; subst
    end.

(** The order of a part, a premise of the order of the whole: the
    hypotheses are inverted one at a time, so that a premise that is the
    goal is taken as it stands, a subterm, before its own inversion takes
    it apart. *)
#[local]
Ltac readback_order :=
  rewrite ?List.length_map in *; readback_glob;
  first [ eassumption
        (** A readback under a binder: the order of the body is a premise
            quantified over the results of the evaluations above it. *)
        | solve [ eauto 2 ]
        | impl_obligation_tac1; readback_order ].

#[local]
Ltac readback_eqb := repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end.

#[local]
Ltac readback_run := repeat impl_obligation_tac1; rewrite ?List.length_map in *; readback_glob; readback_eqb;
  econstructor; first [ eassumption | reflexivity ].

(** The rules of inductive types have premises the order records under
    quantifiers, and lookups the order rules out when they fail. *)
#[local]
Ltac readback_ind :=
  repeat impl_obligation_tac1; rewrite ?List.length_map in *; readback_glob; readback_eqb;
  first [ congruence
        (** The number of values, read on the fast values *)
        | solve [ eapply read_nf_con_view_last; try eassumption; rewrite ?List.length_map in *;
                  first [ reflexivity | lia ] ]
        (** A neutral of a member with a block: its head is not a record
            view's *)
        | solve [ eapply read_nf_ind_neut; try eassumption;
                  unfold im_is_rview; match goal with H : im_head _ = _ |- _ => rewrite H; reflexivity end ]
        (** The lengths the rules ask, of the erasures *)
        | econstructor; try eassumption; rewrite ?List.length_map; eauto 3 ].

(** The erasures read as Core values, and the evaluations' results their
    two parts apart *)
#[local]
Ltac readback_norm :=
  intros;
  (** The recursive functions in scope are not needed by an obligation;
      dropped, the rewriting below has far less to go through. *)
  repeat match goal with f : _ |- _ => lazymatch type of f with context [@sig _ _] => clear f end end;
  cbv beta iota in *; cbn [fst snd] in *; ferase_norm; fleaf_norm; ferase_norm;
  rewrite <- ?fdomain_level_sort_erase, <- ?fdomain_kind_erase in *;
  cbn [fdomain_erase fdomain_ne_erase] in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  (** Whether a fast type is a proposition, as its erasure's kind *)
  repeat match goal with
         | H : fdomain_is_prop _ = true |- _ => apply fdomain_is_prop_true in H; cbn [fdomain_erase] in H
         | H : fdomain_is_prop _ = false |- _ => apply fdomain_is_prop_false in H; cbn [fdomain_erase] in H
         end;
  (** A kind an order records of a known head, computed *)
  repeat match goal with H : domain_kind _ = _ |- _ =>
           progress cbn [domain_kind] in H; try discriminate H end;
  (** The declaration a stuck eliminator carries is its group's *)
  try match goal with Hd : fdomain_ne_ok _ _ (fd_elim _ _ _ _ _ _ _ _) |- _ =>
        pose proof (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd) end.

#[local]
Ltac readback_obligation_auto :=
  readback_norm;
  lazymatch goal with
  | |- _ /\ _ => ok_solve
  | |- fdomain_ok _ _ _ => ok_solve
  | |- fdomain_ne_ok _ _ _ => ok_solve
  | |- fdomain_nf_ok _ _ _ => ok_solve
  | |- fdentry_ok _ _ _ => first [ ok_solve | ok_invert; apply fenv_entry_ok; assumption ]
  | |- fentry_type_ok _ _ _ => ok_solve
  | |- decl_carried_ok _ _ _ _ => ok_solve
  | |- fenv_ok _ _ _ => ok_solve
  | |- Forall _ _ => ok_solve
  | |- read_nf_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_ne_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_proof_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_lets_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_entry_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_entry_type_order _ _ _ => first [ readback_order | readback_run ]
  | |- read_typ_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_level_atoms_order _ _ _ _ => first [ readback_order | readback_run ]
  (** The parameters of a type former with arguments: read off its order
      before inversion takes the arguments apart. *)
  | |- read_ps_order _ _ _ _ _ _ =>
      first [ solve [ match goal with H : read_typ_order _ _ _ (d_ind _ _ _) |- _ =>
                        inversion H; subst; readback_glob; assumption end ]
            | readback_order | readback_run ]
  | |- read_fields_order _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_proj_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_cargs_order _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_shape_order _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_blocks_order _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fresh_tele_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fresh_cargs_order _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_projs_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_exp_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_exps_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_app_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_mref_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- _ => abstract (first [ readback_order
                             (** A value of a proposition: the proposition as a type, the proof *)
                             | solve [ eapply read_nf_proof; first [ eassumption | reflexivity | econstructor ] ]
                             | readback_run | eapply read_typ_suniv_of_nf; eassumption | readback_ind ])
  end.

Solve All Obligations with readback_obligation_auto.

(** The [read_*_impl] functions are sound by construction. *)

(** The entries of readback, from the declaration the command looked up
    ([fc_seed]). *)
Definition fast_read_nf_impl s (d : fdomain_nf) (Hd : fdomain_nf_ok Θ Ξ d) (H : read_nf_order Θ Ξ s (fdomain_nf_erase d)) :
    { m | Rnf fdomain_nf_erase d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_nf_impl_c s d (fc_seed F) Hd H.
Definition fast_read_ne_impl s (d : fdomain_ne) (Hd : fdomain_ne_ok Θ Ξ d) (H : read_ne_order Θ Ξ s (fdomain_ne_erase d)) :
    { m | Rne fdomain_ne_erase d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_ne_impl_c s d (fc_seed F) Hd H.
Definition fast_read_typ_impl s (d : fdomain) (Hd : fdomain_ok Θ Ξ d) (H : read_typ_order Θ Ξ s (fdomain_erase d)) :
    { m | Rtyp fdomain_erase d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_typ_impl_c s d (fc_seed F) Hd H.

End ReadbackImpl.

Extraction Inline fast_read_nf_impl_c_functional
  fast_read_ne_impl_c_functional
  fast_read_proof_impl_c_functional
  fast_read_lets_impl_c_functional
  fast_read_entry_impl_c_functional
  fast_read_typ_impl_c_functional
  fast_read_level_atoms_impl_c_functional
  fast_read_ps_impl_c_functional
  fast_read_fields_impl_c_functional
  fast_read_cargs_impl_c_functional
  fast_read_shape_impl_c_functional
  fast_read_blocks_impl_c_functional
  fast_read_brs_impl_c_functional.
