From Equations Require Import Equations.
From Stdlib Require Import List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Extraction Require Import FastEval FastDomain Evaluation.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** * The Readback the Checker Runs

    Readback of the relation of [Extraction.FastEval]: the reference one
    ([Reference.Readback]), with closures evaluated by [Extraction.Evaluation]. *)

(** The canonical level a level normal form encodes.  A level always reads
    back as [nf_lvl_of] of a canonical level ([fast_read_nf_level_lvl_of_nf]), so
    the default is never reached. *)
Definition lvl_of_nf (W : nf) : lvl :=
  match W with nf_lvl c xs => (c, xs) | _ => (ordinal_zero, nil) end.

Lemma fast_read_nf_level_lvl_of_nf : forall Θ Ξ s l W,
    Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    W = nf_lvl_of (lvl_of_nf W).
Proof. inversion 1; subst; reflexivity. Qed.

Lemma fast_read_typ_suniv_of_nf : forall Θ Ξ s l W,
    Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    Rtypᶠ 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of (lvl_of_nf W).
Proof.
  intros * H; apply fast_read_typ_suniv.
  rewrite <- (fast_read_nf_level_lvl_of_nf _ _ _ _ _ H); exact H.
Qed.

(** ** Along the Leaf Paths of a Recursive Argument

    The computations of [fresh_leaf_vars] and [wrap_leaf_vals], by the
    paths' flags [bs], each sound at lengths its relation has. *)

(** The fresh variables at the flagged paths, from [s], at the types
    [as'] *)
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

(** The operations on fast values, read through their erasure equations *)
#[local] Opaque fleaf_vars_f fleaf_wrap_f fenv_var fenv_mod fextend_env fextend_env_mod fextend_env_dm fenv_args
  fdlvl_suc fdlvl_max fdlvl_lit fdm_clo fkinds_placeholders fkinds_body_entry fkinds_items_gen_env felim_grp_of carry.

(** The erasures of the leaf paths' computations, read as Core ones *)
Ltac fleaf_norm :=
  rewrite ?fleaf_vars_f_erase, ?fleaf_vars_f_length, ?fleaf_wrap_f_erase_fst, ?fleaf_wrap_f_erase_snd in *.

(** ** The Fresh Variables of the Telescopes of a Group

    Their orders, and the functions that compute them. *)

(** The variables of a telescope *)
Inductive fast_fresh_tele_order (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> Prop :=
(** No entry *)
| fast_fresh_tele_order_nil :
  `( fast_fresh_tele_order Θ Ξ ρ nil s )
(** The first entry's type, then the rest under its variable *)
| fast_fresh_tele_order_cons :
  `( fast_eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fast_fresh_tele_order Θ Ξ (ρ ↦ ⇑! a s) T (S s)) ->
     fast_fresh_tele_order Θ Ξ ρ (ce_ass A :: T) s ).

(** The variables of the arguments of a constructor *)
Inductive fast_fresh_cargs_order (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> Prop :=
(** No argument *)
| fast_fresh_cargs_order_nil :
  `( fast_fresh_cargs_order Θ Ξ p ups ρ nil s )
(** A non-recursive argument's type, then the rest *)
| fast_fresh_cargs_order_arg :
  `( fast_eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fast_fresh_cargs_order Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s)) ->
     fast_fresh_cargs_order Θ Ξ p ups ρ (ca_arg A :: gs) s )
(** A recursive argument's type, then the rest *)
| fast_fresh_cargs_order_rec_case :
  `( fast_eval_shty_order Θ Ξ p ups ρ t ->
     fast_fresh_cargs_order Θ Ξ p ups ρ gs (S s) ->
     fast_fresh_cargs_order Θ Ξ p ups ρ (ca_rec t :: gs) s ).

(** The variables of the recursive results of a branch [B], of the group
    read [Dc] *)
Inductive fast_fresh_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (As : list exp) (p : qname) (ups : list domain)
  (Dc : ind_decl) (B : exp) : env -> list carg -> list carg -> list domain -> nat -> Prop :=
(** No argument *)
| fast_fresh_ihs_order_nil :
  `( fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa nil nil nil s )
(** A non-recursive argument, entering the environment *)
| fast_fresh_ihs_order_arg :
  `( fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B (ρa ↦ v) gs' gs vs s ->
     fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa (ca_arg T' :: gs') (ca_arg T :: gs) (v :: vs) s )
(** Recursive in both, one result read: the types of its results, one per
    leaf path, then the rest after the variables at the paths of the
    container's *)
| fast_fresh_ihs_order_rec_case :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = false ->
     fast_eval_ihty_order Θ Ξ p ups ρ As ρa t v ->
     (forall as', ⟦ihtyᶠ v of t at p ups under ρ As ⟧ᶠ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
        List.length as' = List.length (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))) ->
     (forall as', ⟦ihtyᶠ v of t at p ups under ρ As ⟧ᶠ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
        fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa gs' gs vs
          (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s) + s)) ->
     fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) s )
(** Recursive in both, no result read: the rest after the variables *)
| fast_fresh_ihs_order_skip :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = true ->
     fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa gs' gs vs
       (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                       (List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t))) s) + s) ->
     fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) s )
(** Nested through: the rest *)
| fast_fresh_ihs_order_nest :
  `( fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa gs' gs vs s ->
     fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa (ca_arg T' :: gs') (ca_rec t :: gs) (v :: vs) s ).

(** The recursive results a branch is read under, wrapped *)
Inductive fast_wrap_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (p : qname) (ups : list domain) (Bks : list eblock)
  (Dc : ind_decl) : list carg -> list carg -> list domain -> list domain -> Prop :=
(** No argument *)
| fast_wrap_ihs_order_nil :
  `( fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc nil nil nil nil )
(** Recursive in both: the eliminator's results at the argument, along
    its paths, then the rest *)
| fast_wrap_ihs_order_rec_case :
  `( ind_lookup Θ Ξ p = Some D ->
     fast_eval_ih_order Θ Ξ ρ p ups Bks t v ->
     (forall rs, ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
        List.length rs = List.length (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) /\
        List.length (List.filter (fun b => b) (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)))
          <= List.length ihs) ->
     (forall rs, ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
        fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs
          (snd (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs))) ->
     fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Nested through: the eliminator at the argument, then the rest *)
| fast_wrap_ihs_order_nest :
  `( fast_eval_ih_order Θ Ξ ρ p ups Bks t v ->
     fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs ->
     fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_arg T' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Non-recursive: the rest *)
| fast_wrap_ihs_order_arg :
  `( fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs ->
     fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_arg T' :: gs') (ca_arg T :: gs) (v :: vs) ihs ).

#[local]
Hint Constructors fast_fresh_tele_order fast_fresh_cargs_order fast_fresh_ihs_order fast_wrap_ihs_order : mctt.

Lemma fast_fresh_tele_order_sound : forall Θ Ξ ρ T s vs, Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> fast_fresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_fast_eval_rewrite_clear; mauto. Qed.

Lemma fast_fresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs,
    Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> fast_fresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_fast_eval_rewrite_clear; mauto. Qed.

Lemma fast_fresh_ihs_order_sound : forall Θ Ξ ρ As p ups Dc B ρa gs' gs vs s ihs,
    Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
    fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa gs' gs vs s.
Proof.
  induction 1; try solve [ econstructor; eassumption ].
  - eapply fast_fresh_ihs_order_rec_case; try eassumption; [ mauto | |];
      intros; functional_fast_eval_rewrite_clear.
    + exact (fresh_leaf_vars_types_length _ _ _ _ H2).
    + rewrite <- (fresh_leaf_vars_f _ _ _ _ H2); assumption.
  - eapply fast_fresh_ihs_order_skip; try eassumption.
    rewrite <- (fresh_leaf_vars_f _ _ _ _ H1); assumption.
Qed.

Lemma fast_wrap_ihs_order_sound : forall Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r,
    ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r -> fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs.
Proof.
  induction 1; try solve [ econstructor; try eassumption; mauto ].
  eapply fast_wrap_ihs_order_rec_case; try eassumption; [ mauto | |];
    intros; functional_fast_eval_rewrite_clear.
  - exact (wrap_leaf_vals_lengths _ _ _ _ _ H1).
  - rewrite (wrap_leaf_vals_f _ _ _ _ _ H1); assumption.
Qed.

#[export]
Hint Resolve fast_fresh_tele_order_sound fast_fresh_cargs_order_sound fast_fresh_ihs_order_sound fast_wrap_ihs_order_sound : mctt.

Section FreshImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[local]
  Ltac fr_rel :=
    repeat match goal with
      | H : fast_fresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : fast_fresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : fast_fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : fast_wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    (** An argument recursive in both: computed or skipped, as the branch
        reads it *)
    try match goal with H : fast_fresh_ihs_order _ _ _ _ _ _ _ _ _ (ca_rec _ :: _) (ca_rec _ :: _) _ _ |- _ =>
          inversion H; subst; clear H end;
    cbn [ihs_skipb] in *;
    (** The lookups the order records are the ones computed. *)
    repeat match goal with
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ?x = true, H2 : ?x = false |- _ => rewrite H1 in H2; discriminate H2
      (** The group of the recursive results of an argument has a
          declaration. *)
      | H1 : fast_eval_ih_order _ _ _ ?p _ _ _ _, H2 : ind_lookup _ _ ?p = None |- _ =>
          exfalso; destruct (fast_eval_ih_order_lookup _ _ _ _ _ _ _ _ H1) as (? & ?); congruence
      end;
    first [ eassumption | solve [ eauto 2 ]
          | solve [ eapply fast_fresh_ihs_skip; [ eassumption | eassumption
                                            | apply leaf_vars_f_sound; rewrite List.repeat_length, List.length_map; reflexivity
                                            | eassumption ] ]
          (** The leaf paths' computations, at the lengths the order
              records *)
          | solve [ eapply fast_fresh_ihs_rec; [ eassumption | eassumption | eassumption
                                           | apply leaf_vars_f_sound; eauto | eassumption ] ]
          | solve [ eapply fast_wrap_ihs_eval_rec; [ eassumption | eassumption | | eassumption ];
                    match goal with H : forall rs, _ -> _ /\ _, Hr : fast_eval_ih _ _ _ _ _ _ _ _ ?rs |- _ =>
                      destruct (H _ Hr); apply leaf_wrap_f_sound; assumption end ]
          | econstructor; eassumption ].

  (** The erasures read as Core values, and the results' two parts apart *)
  #[local]
  Ltac fr_norm :=
    intros; cbv beta iota in *; cbn [fst snd] in *; ferase_norm; fleaf_norm; ferase_norm;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.

  #[local]
  Ltac fr_obl :=
    fr_norm;
    lazymatch goal with
    | |- _ /\ _ => split; [ fr_rel | ok_solve ]
    | |- Forall _ _ => ok_solve
    | |- fenv_ok _ _ _ => ok_solve
    | |- fdomain_ok _ _ _ => ok_solve
    | |- _ => fr_rel
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_tele_impl (ρ : fenv) T s (Hρ : fenv_ok Θ Ξ ρ) (H : fast_fresh_tele_order Θ Ξ (fenv_erase ρ) T s) :
      { vs | Fteleᶠ T in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ fdomains_erase vs /\ Forall (fdomain_ok Θ Ξ) vs } by struct H :=
  | ρ, nil, s, Hρ, H => exist _ nil _
  | ρ, ce_ass A :: T, s, Hρ, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
      let (vs, Hvs) := fast_fresh_tele_impl (fextend_env ρ (fd_neut a (fd_var s))) T (S s) _ _ in
      exist _ (fd_neut a (fd_var s) :: vs) _
  | ρ, _, s, Hρ, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_cargs_impl p (ups : list fdomain) (ρ : fenv) gs s (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρ : fenv_ok Θ Ξ ρ)
      (H : fast_fresh_cargs_order Θ Ξ p (fdomains_erase ups) (fenv_erase ρ) gs s) :
    { vs | Fcargsᶠ gs of p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ fdomains_erase vs /\ Forall (fdomain_ok Θ Ξ) vs } by struct H :=
  | p, ups, ρ, nil, s, Hups, Hρ, H => exist _ nil _
  | p, ups, ρ, ca_arg A :: gs, s, Hups, Hρ, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl p ups (fextend_env ρ (fd_neut a (fd_var s))) gs (S s) Hups _ _ in
      exist _ (fd_neut a (fd_var s) :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, Hups, Hρ, H =>
      let (a, Ha) := fast_eval_shty_impl F p ups ρ t Hups Hρ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl p ups ρ gs (S s) Hups Hρ _ in
      exist _ (fd_neut a (fd_var s) :: vs) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  (** The recursive results' variables of a stuck eliminator's branch, at
      the declaration [D] of the group the readback holds *)
  Equations fast_fresh_ihs_impl (ρ : fenv) As p (ups : list fdomain) Dc B (ρa : fenv) gs' gs (vs : list fdomain) s
      (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D)
      (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρa : fenv_ok Θ Ξ ρa) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : fast_fresh_ihs_order Θ Ξ (fenv_erase ρ) As p (fdomains_erase ups) Dc B (fenv_erase ρa) gs' gs (fdomains_erase vs) s) :
    { ihs | Fihsᶠ (fdomains_erase vs) at gs' gs of Dc under (fenv_erase ρ) As at p (fdomains_erase ups) for B in Θ ⍮ Ξ ⍮ (fenv_erase ρa) ⍮ s
              ↘ fdomains_erase ihs /\ Forall (fdomain_ok Θ Ξ) ihs } by struct H :=
  | ρ, As, p, ups, Dc, B, ρa, nil, nil, nil, s, D, Ed, Hρ, Hups, Hρa, Hvs, H => exist _ nil _
  | ρ, As, p, ups, Dc, B, ρa, ca_arg _ :: gs', ca_arg _ :: gs, v :: vs, s, D, Ed, Hρ, Hups, Hρa, Hvs, H =>
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B (fextend_env ρa v) gs' gs vs s D Ed Hρ Hups _ _ _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, B, ρa, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, s, D, Ed, Hρ, Hups, Hρa, Hvs, H
        with inspect (ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t))) := {
      (** The branch reads none of the argument's results: their types are
          not computed. *)
      | exist _ true E =>
          let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs
                               (List.length (fleaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                                               (List.repeat (fd_univ 0) (List.length (shape_leaves (rv_leaves D) 0 t))) s) + s) D Ed Hρ Hups Hρa _ _ in
          exist _ (fleaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                     (List.repeat (fd_univ 0) (List.length (shape_leaves (rv_leaves D) 0 t))) s ++ ihs) _
      | exist _ false E =>
          let (as', Has) := fast_eval_ihty_impl F p ups ρ As ρa t v Hups Hρ Hρa _ _ in
          let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs
                               (List.length (fleaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s) + s) D Ed Hρ Hups Hρa _ _ in
          exist _ (fleaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s ++ ihs) _ }
  | ρ, As, p, ups, Dc, B, ρa, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, s, D, Ed, Hρ, Hups, Hρa, Hvs, H =>
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs s D Ed Hρ Hups Hρa _ _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, B, ρa, _, _, _, s, D, Ed, Hρ, Hups, Hρa, Hvs, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  (** The recursive results a stuck eliminator's branch is read under, at
      the declaration [D] of the group the readback holds *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_wrap_ihs_impl (ρ : fenv) p (ups : list fdomain) Bks Dc gs' gs (vs ihs : list fdomain)
      (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D)
      (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hvs : Forall (fdomain_ok Θ Ξ) vs) (Hihs : Forall (fdomain_ok Θ Ξ) ihs)
      (H : fast_wrap_ihs_order Θ Ξ (fenv_erase ρ) p (fdomains_erase ups) Bks Dc gs' gs (fdomains_erase vs) (fdomains_erase ihs)) :
    { r | ⟦wihsᶠ (fdomains_erase vs) of gs' gs of Dc with (fdomains_erase ihs) under p (fdomains_erase ups) Bks ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ
            ↘ fdomains_erase r /\ Forall (fdomain_ok Θ Ξ) r } by struct H :=
  | ρ, p, ups, Bks, Dc, nil, nil, nil, nil, D, Ed, Hρ, Hups, Hvs, Hihs, H => exist _ nil _
  | ρ, p, ups, Bks, Dc, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, ihs, D, Ed, Hρ, Hups, Hvs, Hihs, H =>
        let (rs, Hrs) := fast_eval_ih_impl F ρ p ups Bks t v D Ed Hρ Hups _ _ in
        let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs
                         (snd (fleaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs)) D Ed Hρ Hups _ _ _ in
        exist _ (fst (fleaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs) ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, ihs, D, Ed, Hρ, Hups, Hvs, Hihs, H =>
        let (rs, Hrs) := fast_eval_ih_impl F ρ p ups Bks t v D Ed Hρ Hups _ _ in
        let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs D Ed Hρ Hups _ Hihs _ in
        exist _ (rs ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ :: gs', ca_arg _ :: gs, _ :: vs, ihs, D, Ed, Hρ, Hups, Hvs, Hihs, H =>
      let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs D Ed Hρ Hups _ Hihs _ in
      exist _ r _
  | ρ, p, ups, Bks, Dc, _, _, _, _, D, Ed, Hρ, Hups, Hvs, Hihs, H => False_rect _ _.
  Solve All Obligations with fr_obl.
End FreshImpl.

(** ** The Orders of Readback *)

Inductive fast_read_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| fast_read_nf_order_type :
  `( fast_read_typ_order Θ Ξ s a ->
    fast_read_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
| fast_read_nf_order_stype :
  `( fast_read_typ_order Θ Ξ s a ->
    fast_read_nf_order Θ Ξ s ⇓ 𝕌@n a )
| fast_read_nf_order_lvl :
  `( fast_read_level_atoms_order Θ Ξ s xs ->
     fast_read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
| fast_read_nf_order_lvl_neut :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
| fast_read_nf_order_true :
  `( fast_read_nf_order Θ Ξ s ⇓ ⊤ᵈ m )
| fast_read_nf_order_False_neut :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_nf_order Θ Ξ s ⇓ ⊥ᵈ (⇑ a m) )
| fast_read_nf_order_fn :
  `( fast_read_typ_order Θ Ξ s a ->
     fast_eval_app_order Θ Ξ m ⇑! a s ->
     fast_eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall m' b,
         $ᶠ| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         fast_read_nf_order Θ Ξ (S s) ⇓ b m') ->
     fast_read_nf_order Θ Ξ s ⇓ (Πᵈ a p B) m )
| fast_read_nf_order_neut :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_nf_order Θ Ξ s ⇓ (⇑ a b) (⇑ c m) )
(** A constructor of a declared member *)
| fast_read_nf_order_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length as' = im_np D Mk ->
     List.length vs = (im_np D Mk + List.length gs)%nat ->
     fast_read_ps_order Θ Ξ s nil (List.rev (im_params D Mk)) as' ->
     fast_read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (im_np D Mk) vs) ->
     fast_read_nf_order Θ Ξ s ⇓ (d_ind p k as') (d_con p k c vs) )
(** A constructor at a view: its arguments are the last values *)
| fast_read_nf_order_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_con Mj c = Some gs ->
     List.length as' = im_np D Mj ->
     List.length gs <= List.length vs ->
     fast_read_ps_order Θ Ξ s nil (List.rev (im_params D Mj)) as' ->
     fast_read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs
       (List.skipn (List.length vs - List.length gs) vs) ->
     fast_read_nf_order Θ Ξ s ⇓ (d_ind p j as') (d_con qc k c vs) )
(** Any value at a record view: the view's constructor at the uniform
    parameters, its arguments the value's projections *)
| fast_read_nf_order_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     List.length as' = ind_nu D ->
     fast_eval_projs_order Θ Ξ fl v ->
     fast_read_ps_order Θ Ξ s nil (List.rev (ind_uparams D)) as' ->
     (forall ws, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws -> fast_read_cargs_order Θ Ξ s p as' (env_args nil as') gs ws) ->
     fast_read_nf_order Θ Ξ s ⇓ (d_ind p j as') v )
(** A neutral of a member with a block *)
| fast_read_nf_order_ind_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_is_rview Mk = false ->
     fast_read_ne_order Θ Ξ s m ->
     fast_read_nf_order Θ Ξ s ⇓ (d_ind p k as') (⇑ a m) )
(** A value of a record type: the type's parameters, then the fields *)
| fast_read_nf_order_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     fast_read_ps_order Θ Ξ s nil (List.rev (record_params R)) ns ->
     fast_read_fields_order Θ Ξ s (env_args nil ns) (record_fields R) v ->
     fast_read_nf_order Θ Ξ s ⇓ (d_record p ns) v )

with fast_read_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
| fast_read_ne_order_var :
  `( fast_read_ne_order Θ Ξ s #ᵈ x )
| fast_read_ne_order_app :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_nf_order Θ Ξ s n ->
     fast_read_ne_order Θ Ξ s (m $ᵈ n) )
| fast_read_ne_order_exfalso :
  `( fast_eval_exp_order Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ⊥ᵈ s ↘ b ->
         fast_read_typ_order Θ Ξ (S s) b) ->
     fast_read_ne_order Θ Ξ s m ->
     fast_read_ne_order Θ Ξ s efqᵈ m under p return B )
| fast_read_ne_order_glob :
  `( fast_read_ne_order Θ Ξ s (d_glob p) )
(** A stuck eliminator: the container's uniform parameters, the blocks
    read as the container's group's, and the scrutinee *)
| fast_read_ne_order_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     blocks_nm_at D None Bks ->
     rview_leaf_arity D ->
     fast_eval_mref_order Θ Ξ p ups j ->
     (forall pre, ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) -> fast_read_ps_order Θ Ξ s nil (List.rev (ind_uparams Dq)) pre) ->
     fast_read_blocks_order Θ Ξ s ρ p ups Bks Dq (im_sel Mj) 0 (ind_bmembers Dq) ->
     fast_read_ne_order Θ Ξ s m ->
     fast_read_ne_order Θ Ξ s (d_elim ρ Bks p ups j as' m) )
(** The field of a neutral *)
| fast_read_ne_order_proj :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_ne_order Θ Ξ s (d_proj f m) )

with fast_read_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| fast_read_typ_order_univ :
  `( fast_read_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| fast_read_typ_order_suniv :
  `( fast_read_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     fast_read_typ_order Θ Ξ s 𝕌@l )
| fast_read_typ_order_level :
  `( fast_read_typ_order Θ Ξ s (Levelᵈ@n) )
| fast_read_typ_order_True :
  `( fast_read_typ_order Θ Ξ s ⊤ᵈ )
| fast_read_typ_order_False :
  `( fast_read_typ_order Θ Ξ s ⊥ᵈ )
| fast_read_typ_order_pi :
  `( fast_read_typ_order Θ Ξ s a ->
     fast_eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         fast_read_typ_order Θ Ξ (S s) b) ->
     fast_read_typ_order Θ Ξ s Πᵈ a p B)
| fast_read_typ_order_neut :
  `( fast_read_ne_order Θ Ξ s b ->
    fast_read_typ_order Θ Ξ s ⇑ a b )
(** A type former without arguments: no lookup *)
| fast_read_typ_order_indty_nil :
  `( fast_read_typ_order Θ Ξ s (d_ind p k nil) )
(** At one argument or more *)
| fast_read_typ_order_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length (a :: as') = im_np D Mk ->
     fast_read_ps_order Θ Ξ s nil (List.rev (im_params D Mk)) (a :: as') ->
     fast_read_typ_order Θ Ξ s (d_ind p k (a :: as')) )
(** A record type at all its parameters *)
| fast_read_typ_order_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     fast_read_ps_order Θ Ξ s nil (List.rev (record_params R)) ns ->
     fast_read_typ_order Θ Ξ s (d_record p ns) )

with fast_read_level_atoms_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
| fast_read_level_atoms_order_nil :
  `( fast_read_level_atoms_order Θ Ξ s nil )
| fast_read_level_atoms_order_cons :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_level_atoms_order Θ Ξ s xs ->
     fast_read_level_atoms_order Θ Ξ s ((k, n, m) :: xs) )

with fast_read_ps_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> Prop :=
| fast_read_ps_order_nil :
  `( fast_read_ps_order Θ Ξ s ρ nil nil )
| fast_read_ps_order_cons :
  `( fast_eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fast_read_nf_order Θ Ξ s ⇓ a v) ->
     fast_read_ps_order Θ Ξ s (ρ ↦ v) T vs ->
     fast_read_ps_order Θ Ξ s ρ (ce_ass A :: T) (v :: vs) )

(** The fields of a record value, each its projection at its type *)
with fast_read_fields_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list (string * exp) -> domain -> Prop :=
(** No field left *)
| fast_read_fields_order_nil :
  `( fast_read_fields_order Θ Ξ s ρ nil v )
(** The next field: its projection, its type, its readback, then the rest
    with the projection in the environment *)
| fast_read_fields_order_cons :
  `( fast_eval_proj_order Θ Ξ f v ->
     fast_eval_exp_order Θ Ξ T ρ ->
     (forall r t, fast_eval_proj Θ Ξ f v r -> ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ t -> fast_read_nf_order Θ Ξ s ⇓ t r) ->
     (forall r, fast_eval_proj Θ Ξ f v r -> fast_read_fields_order Θ Ξ s (ρ ↦ r) fl v) ->
     fast_read_fields_order Θ Ξ s ρ ((f, T) :: fl) v )

with fast_read_cargs_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> Prop :=
| fast_read_cargs_order_nil :
  `( fast_read_cargs_order Θ Ξ s p ups ρ nil nil )
| fast_read_cargs_order_arg :
  `( fast_eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fast_read_nf_order Θ Ξ s ⇓ a v) ->
     fast_read_cargs_order Θ Ξ s p ups (ρ ↦ v) gs vs ->
     fast_read_cargs_order Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) )
(** A recursive argument, along its shape *)
| fast_read_cargs_order_rec_case :
  `( fast_read_shape_order Θ Ξ s p ups ρ t v ->
     fast_read_cargs_order Θ Ξ s p ups ρ gs vs ->
     fast_read_cargs_order Θ Ξ s p ups ρ (ca_rec t :: gs) (v :: vs) )

(** A recursive argument of a shape *)
with fast_read_shape_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> ptyp -> domain -> Prop :=
(** At the end: the parameters, then the value at the member *)
| fast_read_shape_order_self :
  `( fast_eval_exps_order Θ Ξ Ps ρ ->
     (forall bs, ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs -> fast_read_nf_order Θ Ξ s ⇓ (d_ind p j (ups ++ bs)) v) ->
     fast_read_shape_order Θ Ξ s p ups ρ (pt_self j Ps) v )
(** At a domain: under a fresh variable of it *)
| fast_read_shape_order_pi :
  `( fast_eval_exp_order Θ Ξ B ρ ->
     (forall b, ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b -> fast_read_typ_order Θ Ξ s b) ->
     (forall b, ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b -> fast_eval_app_order Θ Ξ v (⇑! b s)) ->
     (forall b r, ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b -> $ᶠ| v & ⇑! b s | Θ ⍮ Ξ ↘ r ->
        fast_read_shape_order Θ Ξ (S s) p ups (ρ ↦ ⇑! b s) t r) ->
     fast_read_shape_order Θ Ξ s p ups ρ (pt_pi B t) v )

(** The blocks of a stuck eliminator *)
with fast_read_blocks_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                                  option (list nat) -> nat -> list imember -> Prop :=
(** No member left *)
| fast_read_blocks_order_nil :
  `( fast_read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i nil )
(** The block of the member [Mi]: its motive, its branches, then the rest *)
| fast_read_blocks_order_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     Nat.eqb (eb_nm b) (S (im_nn Mi)) = true ->
     fast_eval_mref_order Θ Ξ p ups (elim_src sel i) ->
     fast_fresh_tele_order Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s ->
     (forall pk k pre ns, ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
        fast_eval_exp_order Θ Ξ (eb_motive b) (env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil))) ->
     (forall pk k pre ns a, ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
        ⟦ eb_motive b ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil) ↘ a ->
        fast_read_typ_order Θ Ξ (S (s + im_nn Mi)) a) ->
     (forall pk k pre, ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b)) ->
     fast_read_blocks_order Θ Ξ s ρ p ups Bks Dc sel (S i) Ms ->
     fast_read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i (Mi :: Ms) )

(** The branches of a block *)
with fast_read_brs_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                               imember -> exp -> imember -> (qname * nat * list domain) ->
                                               list (string * list carg) -> list (string * nat * exp) -> Prop :=
(** No constructor left *)
| fast_read_brs_order_nil :
  `( fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r nil nil )
(** The branch of the next constructor, then the rest *)
| fast_read_brs_order_cons :
  `( ind_con Mv c = Some gs ->
     Nat.eqb n0 (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat = true ->
     ind_lookup Θ Ξ p = Some D ->
     cargs_nin D Dc gs' gs = cargs_nrec Dc gs' ->
     cargs_plen D gs ->
     fast_fresh_tele_order Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s ->
     (forall ns,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         fast_fresh_cargs_order Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + im_nn Mi)) ->
     (forall ns vs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         fast_fresh_ihs_order Θ Ξ ρ (blocks_motives Bks) p ups Dc B (env_args nil (ups ++ ns)) gs' gs vs (s + im_nn Mi + List.length gs')) ->
     (forall ns vs ihs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihsᶠ vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs) ->
     (forall ns vs ihs wihs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihsᶠ vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         fast_eval_exp_order Θ Ξ B (env_args ρ (ns ++ vs ++ wihs))) ->
     (forall ns vs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         fast_eval_exp_order Θ Ξ A (env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil))) ->
     (forall ns vs ihs wihs b t,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihsᶠ vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ wihs) ↘ b ->
         ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil) ↘ t ->
         fast_read_nf_order Θ Ξ (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) ⇓ t b) ->
     fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi (pk, k, pre) cs Bs ->
     fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi (pk, k, pre) ((c, gs') :: cs) ((c, n0, B) :: Bs) ).

#[local]
Hint Constructors fast_read_nf_order fast_read_ne_order fast_read_typ_order fast_read_level_atoms_order
  fast_read_ps_order fast_read_fields_order fast_read_cargs_order fast_read_shape_order fast_read_blocks_order fast_read_brs_order : mctt.

(** Every readback derivation is within its order: by the mutual induction
    on readback, the evaluations the orders quantify over being the ones
    the derivation makes ([functional_fast_eval]). *)
Lemma fast_read_order_sound : forall Θ Ξ,
    (forall s d m, Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_nf_order Θ Ξ s d) /\
    (forall s d m, Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_ne_order Θ Ξ s d) /\
    (forall s d m, Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_typ_order Θ Ξ s d) /\
    (forall s xs ys, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys -> fast_read_level_atoms_order Θ Ξ s xs) /\
    (forall s ρ T vs Ms, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fast_read_ps_order Θ Ξ s ρ T vs) /\
    (forall s p ups ρ gs vs Ms, Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fast_read_cargs_order Θ Ξ s p ups ρ gs vs) /\
    (forall s p ups ρ t v V, Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> fast_read_shape_order Θ Ξ s p ups ρ t v) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       fast_read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs) /\
    (forall s ρ fl v Fs, Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> fast_read_fields_order Θ Ξ s ρ fl v).
Proof.
  intros Θ Ξ; apply fast_read_mut_ind; intros;
    (** A constructor at a view: its arguments are the last values, as
        many as the constructor takes. *)
    try match goal with Hh : im_head _ = mh_view _ _ _ _, Hl : List.length ?vs = (?n + List.length ?gs)%nat
                        |- fast_read_nf_order _ _ _ (⇓ _ (d_con _ _ _ ?vs)) =>
          replace n with (List.length vs - List.length gs) in * by lia end;
    first [ solve [ eapply fast_read_nf_order_ind_neut; eassumption ] |
    (econstructor; try eassumption; try lia; try (apply Nat.eqb_eq; first [ assumption | subst; reflexivity ]);
     intros; functional_fast_eval_rewrite_clear; functional_fast_fresh_rewrite_clear;
     functional_fast_eval_rewrite_clear; subst; mauto) ].
Qed.

Lemma fast_read_nf_order_sound : forall Θ Ξ s d m, Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_nf_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (fast_read_order_sound Θ Ξ)). Qed.

Lemma fast_read_ne_order_sound : forall Θ Ξ s d m, Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_ne_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (proj2 (fast_read_order_sound Θ Ξ))). Qed.

Lemma fast_read_typ_order_sound : forall Θ Ξ s d m, Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_typ_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (fast_read_order_sound Θ Ξ)))). Qed.

Lemma fast_read_level_atoms_order_sound : forall Θ Ξ s xs ys, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys -> fast_read_level_atoms_order Θ Ξ s xs.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (fast_read_order_sound Θ Ξ))))). Qed.

Lemma fast_read_ps_order_sound : forall Θ Ξ s ρ T vs Ms, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fast_read_ps_order Θ Ξ s ρ T vs.
Proof. intros Θ Ξ; pose proof (fast_read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_read_cargs_order_sound : forall Θ Ξ s p ups ρ gs vs Ms,
    Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fast_read_cargs_order Θ Ξ s p ups ρ gs vs.
Proof. intros Θ Ξ; pose proof (fast_read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_read_shape_order_sound : forall Θ Ξ s p ups ρ t v V,
    Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> fast_read_shape_order Θ Ξ s p ups ρ t v.
Proof. intros Θ Ξ; pose proof (fast_read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_read_blocks_order_sound : forall Θ Ξ s ρ p ups Bks Dc sel i Ms NBks,
    Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks -> fast_read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms.
Proof. intros Θ Ξ; pose proof (fast_read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_read_brs_order_sound : forall Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs',
    Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' -> fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs.
Proof. intros Θ Ξ; pose proof (fast_read_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fast_read_fields_order_sound : forall Θ Ξ s ρ fl v Fs,
    Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> fast_read_fields_order Θ Ξ s ρ fl v.
Proof. intros Θ Ξ; pose proof (fast_read_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve fast_read_nf_order_sound fast_read_ne_order_sound fast_read_typ_order_sound fast_read_level_atoms_order_sound
  fast_read_ps_order_sound fast_read_cargs_order_sound fast_read_shape_order_sound fast_read_blocks_order_sound
  fast_read_brs_order_sound fast_read_fields_order_sound : mctt.

(** A constructor at a view, its arguments the last values, as many as the
    constructor takes ([fast_read_nf_con_view]). *)
Lemma fast_read_nf_con_view_last : forall Θ Ξ s p D j Mj qc k Is vm c gs as' vs n Ps Args,
    ind_lookup Θ Ξ p = Some D ->
    ind_member D j = Some Mj ->
    im_head Mj = mh_view qc k Is vm ->
    ind_con Mj c = Some gs ->
    List.length as' = im_np D Mj ->
    Rpsᶠ as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
    Rcargsᶠ List.skipn (n - List.length gs) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ
      ⍮ env_args nil as' ⍮ s ↘ Args ->
    List.length gs <= n ->
    (** The number of values, as the readback computes it *)
    n = List.length vs ->
    Rnfᶠ ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args).
Proof. intros; subst; eapply fast_read_nf_con_view; try eassumption; lia. Qed.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : fast_read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_level_atoms_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_ps_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_fields_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_cargs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_shape_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_blocks_order _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  (** A value at a member of a group: a constructor at a declared member
      or at a view, a neutral, or any value at a record view, the lookups
      then excluding all but one *)
  | H : fast_read_nf_order _ _ _ (⇓ (d_ind _ _ _) _) |- _ => inversion H; subst; clear H
  end.

Section ReadbackImpl.
Variable F : FCtx.
#[local] Abbreviation Θ := (fc_deps F).
#[local] Abbreviation Ξ := (fc_stack F).

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations fast_read_nf_impl_c s (d : fdomain_nf) (ck : lk_cache Θ Ξ) (Hd : fdomain_nf_ok Θ Ξ d)
    (H : fast_read_nf_order Θ Ξ s (fdomain_nf_erase d)) : { m | Rnfᶠ fdomain_nf_erase d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
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
| s, fd_dom fd_True m, ck, Hd, H => exist _ ⋆ⁿ _
| s, fd_dom fd_False (fd_neut _ m), ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ ⇑ⁿ M _
| s, fd_dom (fd_pi a p B) m, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    let (m', Hm') := fast_eval_app_impl F m (fd_neut a (fd_var s)) _ _ _ in
    let (b, Hb) := fast_eval_exp_impl F B (fextend_env p (fd_neut a (fd_var s))) _ _ in
    let (M, HM) := fast_read_nf_impl_c (S s) (fd_dom b m') ck _ _ in
    exist _ (λⁿ A M) _
| s, fd_dom (fd_neut a b) (fd_neut c m), ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ ⇑ⁿ M _
| s, fd_dom (fd_ind p oD j as') v, ck, Hd, H with carried_lookup F ck p oD (fdomain_nf_ok_dom_ind_carried _ _ _ _ _ _ _ Hd) := {
  | inleft (exist _ D Ed) with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_head Mj) := {
      (** At a record view, any value: the view's constructor, its
          arguments the value's projections *)
      | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
        | exist _ ((c, gs) :: nil) Ec =>
            let (ws, Hws) := fast_eval_projs_impl F fl v _ _ in
            let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (ind_uparams D)) as' ck _ _ _ in
            let (Args, HArgs) := fast_read_cargs_impl_c s p as' (fenv_args nil as') gs ws (Some (exist _ (p, D) Ed)) _ _ _ _ in
            exist _ (nf_con p j c (Ps ++ Args)%list) _
        | exist _ _ Ec => False_rect _ _ }
      | exist _ (mh_decl pm) Eh with v := {
        (** A constructor of a declared member: its arguments after its
            parameters *)
        | fd_con _ _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ _ _ in
              let (Args, HArgs) := fast_read_cargs_impl_c s p (List.firstn (ind_nu D) as') (fenv_args nil as') gs
                                     (List.skipn (im_np D Mj) vs) (Some (exist _ (p, D) Ed)) _ _ _ _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | fd_neut a m =>
            let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
            exist _ ⇑ⁿ M _
        | _ => False_rect _ _ }
      | exist _ (mh_view qv kv Iv vmv) Eh with v := {
        (** At a view: its arguments are the last values *)
        | fd_con _ _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ _ _ in
              let (Args, HArgs) := fast_read_cargs_impl_c s p (List.firstn (ind_nu D) as') (fenv_args nil as') gs
                                     (List.skipn (List.length vs - List.length gs) vs) (Some (exist _ (p, D) Ed)) _ _ _ _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | fd_neut a m =>
            let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
            exist _ ⇑ⁿ M _
        | _ => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | inright Ed => False_rect _ _ }
| s, fd_dom (fd_record p ns) v, ck, Hd, H with record_lookup_f F p := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (record_params R)) ns ck _ _ _ in
      let (Fs, HFs) := fast_read_fields_impl_c s (fenv_args nil ns) (record_fields R) v ck _ _ _ in
      exist _ (nf_tuple p Ps (List.map fst (record_fields R)) Fs) _
  | exist _ None El => False_rect _ _ }
(** No other value has a readback order *)
| s, _, ck, Hd, H => False_rect _ _

  with fast_read_ne_impl_c s (d : fdomain_ne) (ck : lk_cache Θ Ξ) (Hd : fdomain_ne_ok Θ Ξ d)
      (H : fast_read_ne_order Θ Ξ s (fdomain_ne_erase d)) : { m | Rneᶠ fdomain_ne_erase d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, fd_var x, ck, Hd, H => exist _ #ⁿ (s - x - 1) _
| s, fd_glob p, ck, Hd, H => exist _ (ne_glob p) _
| s, fd_app m n, ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    let (N, HN) := fast_read_nf_impl_c s n ck _ _ in
    exist _ (M $ⁿ N) _
| s, fd_exfalso p B m, ck, Hd, H =>
    let (b, Hb) := fast_eval_exp_impl F B (fextend_env p (fd_neut fd_False (fd_var s))) _ _ in
    let (B', HB') := fast_read_typ_impl_c (S s) b ck _ _ in
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ (efqⁿ M return B') _
(** The stuck eliminator carries the declaration of its group *)
| s, fd_elim ρ Bks p D ups j as' m, ck, Hd, H with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_ref p j Mj) := {
      | exist _ (pc, k) Er with decl_lookup F (Some (exist _ (p, D) (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd))) pc := {
        | inleft (exist _ Dq Edq) with fast_eval_mref_impl F p ups j _ _ := {
          | exist _ (mk_fast_member_reference _ _ _ pre) Hm =>
              let (Us, HUs) := fast_read_ps_impl_c s nil (List.rev (ind_uparams Dq)) pre ck _ _ _ in
              let (NBks, HNBks) := fast_read_blocks_impl_c s ρ p ups Bks Dq (im_sel Mj) 0 (ind_bmembers Dq)
                                     D (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd)
                                     (Some (exist _ (p, D) (fdomain_ne_ok_elim_decl _ _ _ _ _ _ _ _ _ _ Hd))) _ _ _ in
              let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
              exist _ (ne_elim pc Us k NBks M) _ }
        | inright Edq => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
| s, fd_proj f m, ck, Hd, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    exist _ (ne_proj f M) _

  with fast_read_typ_impl_c s (d : fdomain) (ck : lk_cache Θ Ξ) (Hd : fdomain_ok Θ Ξ d)
      (H : fast_read_typ_order Θ Ξ s (fdomain_erase d)) : { m | Rtypᶠ fdomain_erase d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, fd_univ i, ck, Hd, H => exist _ Typeωⁿ@i _
| s, fd_suniv l, ck, Hd, H =>
    let (W, HW) := fast_read_nf_impl_c s (fd_dom (fd_level 0) l) ck _ _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, fd_level n, ck, Hd, H => exist _ (Levelⁿ@n) _
| s, fd_True, ck, Hd, H => exist _ ⊤ⁿ _
| s, fd_False, ck, Hd, H => exist _ ⊥ⁿ _
| s, fd_pi a p B, ck, Hd, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ _ in
    let (b, Hb) := fast_eval_exp_impl F B (fextend_env p (fd_neut a (fd_var s))) _ _ in
    let (B', HB') := fast_read_typ_impl_c (S s) b ck _ _ in
    exist _ (Πⁿ A B') _
| s, fd_neut a b, ck, Hd, H =>
    let (B, HB) := fast_read_ne_impl_c s b ck _ _ in
    exist _ ⇑ⁿ B _
| s, fd_ind p oD k nil, ck, Hd, H => exist _ (nf_indty p k nil) _
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

  with fast_read_level_atoms_impl_c s (xs : list (nat * nat * fdomain_ne)) (ck : lk_cache Θ Ξ)
      (Hxs : Forall (fun ka => fdomain_ne_ok Θ Ξ (snd ka)) xs)
      (H : fast_read_level_atoms_order Θ Ξ s (List.map (fun ka => (fst ka, fdomain_ne_erase (snd ka))) xs)) :
      { ys | Rlaᶠ List.map (fun ka => (fst ka, fdomain_ne_erase (snd ka))) xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, ck, Hxs, H => exist _ nil _
| s, cons (k, n, m) xs, ck, Hxs, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ _ in
    let (ys, Hys) := fast_read_level_atoms_impl_c s xs ck _ _ in
    exist _ (cons (mk_level_atom k n M) ys) _

  with fast_read_ps_impl_c s (ρ : fenv) T (vs : list fdomain) (ck : lk_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ)
      (Hvs : Forall (fdomain_ok Θ Ξ) vs) (H : fast_read_ps_order Θ Ξ s (fenv_erase ρ) T (fdomains_erase vs)) :
      { Ms | Rpsᶠ fdomains_erase vs at T in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, ck, Hρ, Hvs, H => exist _ nil _
| s, ρ, ce_ass A :: T, v :: vs, ck, Hρ, Hvs, H =>
    let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom a v) ck _ _ in
    let (Vs, HVs) := fast_read_ps_impl_c s (fextend_env ρ v) T vs ck _ _ _ in
    exist _ (cons V Vs) _
| s, ρ, _, _, ck, Hρ, Hvs, H => False_rect _ _

  with fast_read_fields_impl_c s (ρ : fenv) fl (v : fdomain) (ck : lk_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ) (Hv : fdomain_ok Θ Ξ v)
      (H : fast_read_fields_order Θ Ξ s (fenv_erase ρ) fl (fdomain_erase v)) :
    { Fs | Rfldsᶠ fdomain_erase v at fl in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Fs } by struct H :=
| s, ρ, nil, v, ck, Hρ, Hv, H => exist _ nil _
| s, ρ, (f, T) :: fl, v, ck, Hρ, Hv, H =>
    let (r, Hr) := fast_eval_proj_impl F f v Hv _ in
    let (t, Ht) := fast_eval_exp_impl F T ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom t r) ck _ _ in
    let (Vs, HVs) := fast_read_fields_impl_c s (fextend_env ρ r) fl v ck _ Hv _ in
    exist _ (cons V Vs) _

  with fast_read_cargs_impl_c s p (ups : list fdomain) (ρ : fenv) gs (vs : list fdomain) (ck : lk_cache Θ Ξ)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρ : fenv_ok Θ Ξ ρ) (Hvs : Forall (fdomain_ok Θ Ξ) vs)
      (H : fast_read_cargs_order Θ Ξ s p (fdomains_erase ups) (fenv_erase ρ) gs (fdomains_erase vs)) :
    { Ms | Rcargsᶠ fdomains_erase vs at gs of p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Ms } by struct H :=
| s, p, ups, ρ, nil, nil, ck, Hups, Hρ, Hvs, H => exist _ nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, ck, Hups, Hρ, Hvs, H =>
    let (a, Ha) := fast_eval_exp_impl F A ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom a v) ck _ _ in
    let (Vs, HVs) := fast_read_cargs_impl_c s p ups (fextend_env ρ v) gs vs ck Hups _ _ _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, ca_rec t :: gs, v :: vs, ck, Hups, Hρ, Hvs, H =>
    let (V, HV) := fast_read_shape_impl_c s p ups ρ t v ck Hups Hρ _ _ in
    let (Vs, HVs) := fast_read_cargs_impl_c s p ups ρ gs vs ck Hups Hρ _ _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, _, _, ck, Hups, Hρ, Hvs, H => False_rect _ _

  with fast_read_shape_impl_c s p (ups : list fdomain) (ρ : fenv) t (v : fdomain) (ck : lk_cache Θ Ξ)
      (Hups : Forall (fdomain_ok Θ Ξ) ups) (Hρ : fenv_ok Θ Ξ ρ) (Hv : fdomain_ok Θ Ξ v)
      (H : fast_read_shape_order Θ Ξ s p (fdomains_erase ups) (fenv_erase ρ) t (fdomain_erase v)) :
    { V | Rshᶠ fdomain_erase v at t of p (fdomains_erase ups) in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ V } by struct H :=
| s, p, ups, ρ, pt_self j Ps, v, ck, Hups, Hρ, Hv, H =>
    let (bs, Hbs) := fast_eval_exps_impl F Ps ρ Hρ _ in
    let (V, HV) := fast_read_nf_impl_c s (fd_dom (fd_ind p None j (ups ++ bs)) v) ck _ _ in
    exist _ V _
| s, p, ups, ρ, pt_pi B t, v, ck, Hups, Hρ, Hv, H =>
    let (b, Hb) := fast_eval_exp_impl F B ρ Hρ _ in
    let (A, HA) := fast_read_typ_impl_c s b ck _ _ in
    let (r, Hr) := fast_eval_app_impl F v (fd_neut b (fd_var s)) Hv _ _ in
    let (V, HV) := fast_read_shape_impl_c (S s) p ups (fextend_env ρ (fd_neut b (fd_var s))) t r ck Hups _ _ _ in
    exist _ (λⁿ A V) _

  (** The blocks of a stuck eliminator, at the declaration [D] of its
      group *)
  with fast_read_blocks_impl_c s (ρ : fenv) p (ups : list fdomain) Bks Dc sel i Ms (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D)
      (ck : lk_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups)
      (H : fast_read_blocks_order Θ Ξ s (fenv_erase ρ) p (fdomains_erase ups) Bks Dc sel i Ms) :
    { NBks | Rblksᶠ i Ms of Dc from p (fdomains_erase ups) Bks sel in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ NBks } by struct H :=
| s, ρ, p, ups, Bks, Dc, sel, i, nil, D, Ed, ck, Hρ, Hups, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, sel, i, Mi :: Ms, D, Ed, ck, Hρ, Hups, H with inspect (ind_member D (elim_src sel i)) := {
    | exist _ (Some Mv) Em with inspect (List.nth_error Bks (elim_src sel i)) := {
      | exist _ (Some b) Eb with fast_eval_mref_impl F p ups (elim_src sel i) Hups _ := {
        | exist _ (mk_fast_member_reference pk oDk k pre) Hm =>
            let (ns, Hns) := fast_fresh_tele_impl F (fenv_args nil ups) (List.rev (im_nparams Mv)) s _ _ in
            let (a, Ha) := fast_eval_exp_impl F (eb_motive b)
                             (fenv_args ρ (ns ++ fd_neut (fd_ind pk oDk k (pre ++ ns)) (fd_var (s + im_nn Mi)%nat) :: nil)) _ _ in
            let (A', HA') := fast_read_typ_impl_c (S (s + im_nn Mi)) a ck _ _ in
            let (Bs', HBs') := fast_read_brs_impl_c s ρ p ups Bks Dc Mv (eb_motive b) Mi (mk_fast_member_reference pk oDk k pre)
                                 (im_cons Mi) (eb_brs b)
                                 D Ed ck Hρ Hups _ _ in
            let (NBks, HNBks) := fast_read_blocks_impl_c s ρ p ups Bks Dc sel (S i) Ms D Ed ck Hρ Hups _ in
            exist _ (cons (mk_normal_block (S (im_nn Mi)) A' Bs') NBks) _ }
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }

  (** The branches of a block, at the declaration [D] of the group *)
  with fast_read_brs_impl_c s (ρ : fenv) p (ups : list fdomain) Bks Dc Mv A Mi (r : fast_member_reference) cs Bs
         (D : ind_decl) (Ed : ind_lookup Θ Ξ p = Some D) (ck : lk_cache Θ Ξ) (Hρ : fenv_ok Θ Ξ ρ) (Hups : Forall (fdomain_ok Θ Ξ) ups)
         (Hr : fast_member_reference_ok Θ Ξ r)
         (H : fast_read_brs_order Θ Ξ s (fenv_erase ρ) p (fdomains_erase ups) Bks Dc Mv A Mi (fast_member_reference_erase r) cs Bs) :
    { Bs' | Rbrsᶠ Bs at cs of Mi (fast_member_reference_erase r) of Dc from p (fdomains_erase ups) Bks Mv A
              in Θ ⍮ Ξ ⍮ fenv_erase ρ ⍮ s ↘ Bs' } by struct H :=
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, nil, nil, D, Ed, ck, Hρ, Hups, Hr, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, mk_fast_member_reference pk oDk k pre, (c, gs') :: cs, (_, _, B) :: Bs, D, Ed, ck, Hρ, Hups, Hr, H
    with inspect (ind_con Mv c) := {
  | exist _ (Some gs) Ec =>
      let (ns, Hns) := fast_fresh_tele_impl F (fenv_args nil ups) (List.rev (im_nparams Mv)) s _ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl F p ups (fenv_args nil (ups ++ ns)) gs (s + im_nn Mi) Hups _ _ in
      let (ihs, Hihs) := fast_fresh_ihs_impl F ρ (blocks_motives Bks) p ups Dc B (fenv_args nil (ups ++ ns)) gs' gs vs
                           (s + im_nn Mi + List.length gs') D Ed Hρ Hups _ _ _ in
      let (wihs, Hw) := fast_wrap_ihs_impl F ρ p ups Bks Dc gs' gs vs ihs D Ed Hρ Hups _ _ _ in
      let (b, Hb) := fast_eval_exp_impl F B (fenv_args ρ (ns ++ vs ++ wihs)) _ _ in
      let (t, Ht) := fast_eval_exp_impl F A (fenv_args ρ (ns ++ fd_con pk oDk k c (pre ++ ns ++ vs) :: nil)) _ _ in
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
    (** A record, looked up once *)
    | H1 : record_lookup _ _ ?p = Some ?x, H2 : record_lookup _ _ ?p = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    (** The member a member stands for, at the reference the order records *)
    | Hm : fast_eval_mref _ _ ?p _ ?j (?a, ?b, _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
      Hr : im_ref ?p ?j _ = (?c, ?d) |- _ =>
        assert_fails (constr_eq a c);
        let E := fresh "Er" in
        pose proof (fast_eval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) as E;
        rewrite E in Hr; injection Hr; clear Hr; intros; subst
    end.

#[local]
Ltac readback_order :=
  repeat impl_obl_tac1; rewrite ?List.length_map in *; readback_glob;
  first [ eassumption
        (** A readback under a binder: the order of the body is a premise
            quantified over the results of the evaluations above it. *)
        | solve [ eauto 2 ] ].

#[local]
Ltac readback_eqb := repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end.

#[local]
Ltac readback_run := repeat impl_obl_tac1; rewrite ?List.length_map in *; readback_glob; readback_eqb; econstructor; eassumption.

(** The rules of inductive types have premises the order records under
    quantifiers, and lookups the order rules out when they fail. *)
#[local]
Ltac readback_ind :=
  repeat impl_obl_tac1; rewrite ?List.length_map in *; readback_glob; readback_eqb;
  first [ congruence
        (** The number of values, read on the fast values *)
        | solve [ eapply fast_read_nf_con_view_last; try eassumption; rewrite ?List.length_map in *;
                  first [ reflexivity | lia ] ]
        (** A neutral of a member with a block: its head is not a record
            view's *)
        | solve [ eapply fast_read_nf_ind_neut; try eassumption;
                  unfold im_is_rview; match goal with H : im_head _ = _ |- _ => rewrite H; reflexivity end ]
        (** The lengths the rules ask, of the erasures *)
        | econstructor; try eassumption; rewrite ?List.length_map; eauto 3 ].

(** The erasures read as Core values, and the evaluations' results their
    two parts apart *)
#[local]
Ltac readback_norm :=
  intros; cbv beta iota in *; cbn [fst snd] in *; ferase_norm; fleaf_norm; ferase_norm;
  rewrite <- ?fdomain_level_sort_erase in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
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
  | |- decl_carried_ok _ _ _ _ => ok_solve
  | |- fenv_ok _ _ _ => ok_solve
  | |- Forall _ _ => ok_solve
  | |- fast_read_nf_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_ne_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_typ_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_level_atoms_order _ _ _ _ => first [ readback_order | readback_run ]
  (** The parameters of a type former with arguments: read off its order
      before inversion takes the arguments apart. *)
  | |- fast_read_ps_order _ _ _ _ _ _ =>
      first [ solve [ match goal with H : fast_read_typ_order _ _ _ (d_ind _ _ (_ :: _)) |- _ =>
                        inversion H; subst; readback_glob; assumption end ]
            | readback_order | readback_run ]
  | |- fast_read_fields_order _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_eval_proj_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_cargs_order _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_shape_order _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_blocks_order _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_read_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_fresh_tele_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_fresh_cargs_order _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_eval_projs_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_eval_exp_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_eval_exps_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_eval_app_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- fast_eval_mref_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- _ => abstract (first [ readback_order | readback_run | eapply fast_read_typ_suniv_of_nf; eassumption | readback_ind ])
  end.

Solve All Obligations with readback_obligation_auto.

(** The [fast_read_*_impl] functions are sound by construction. *)

(** The entries of readback, from the declaration the command looked up
    ([fc_seed]). *)
Definition fast_read_nf_impl s (d : fdomain_nf) (Hd : fdomain_nf_ok Θ Ξ d) (H : fast_read_nf_order Θ Ξ s (fdomain_nf_erase d)) :
    { m | Rnfᶠ fdomain_nf_erase d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_nf_impl_c s d (fc_seed F) Hd H.
Definition fast_read_ne_impl s (d : fdomain_ne) (Hd : fdomain_ne_ok Θ Ξ d) (H : fast_read_ne_order Θ Ξ s (fdomain_ne_erase d)) :
    { m | Rneᶠ fdomain_ne_erase d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_ne_impl_c s d (fc_seed F) Hd H.
Definition fast_read_typ_impl s (d : fdomain) (Hd : fdomain_ok Θ Ξ d) (H : fast_read_typ_order Θ Ξ s (fdomain_erase d)) :
    { m | Rtypᶠ fdomain_erase d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_typ_impl_c s d (fc_seed F) Hd H.

End ReadbackImpl.

Extraction Inline fast_read_nf_impl_c_functional
  fast_read_ne_impl_c_functional
  fast_read_typ_impl_c_functional
  fast_read_level_atoms_impl_c_functional
  fast_read_ps_impl_c_functional
  fast_read_fields_impl_c_functional
  fast_read_cargs_impl_c_functional
  fast_read_shape_impl_c_functional
  fast_read_blocks_impl_c_functional
  fast_read_brs_impl_c_functional.
