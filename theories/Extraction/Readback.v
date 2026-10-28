From Equations Require Import Equations.
From Stdlib Require Import List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Extraction Require Import FastEval Evaluation.
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
  match W with nf_lvl c xs => (c, xs) | _ => (oz, nil) end.

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
  Ltac fr_obl :=
    intros; cbv beta in *;
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

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_tele_impl ρ T s (H : fast_fresh_tele_order Θ Ξ ρ T s) : { vs | Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | ρ, nil, s, H => exist _ nil _
  | ρ, ce_ass A :: T, s, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ _ in
      let (vs, Hvs) := fast_fresh_tele_impl (ρ ↦ ⇑! a s) T (S s) _ in
      exist _ (⇑! a s :: vs) _
  | ρ, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_cargs_impl p ups ρ gs s (H : fast_fresh_cargs_order Θ Ξ p ups ρ gs s) :
    { vs | Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ nil _
  | p, ups, ρ, ca_arg A :: gs, s, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ _ in
      let (vs, Hvs) := fast_fresh_cargs_impl p ups (ρ ↦ ⇑! a s) gs (S s) _ in
      exist _ (⇑! a s :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, H =>
      let (a, Ha) := fast_eval_shty_impl F p ups ρ t _ in
      let (vs, Hvs) := fast_fresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! a s :: vs) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs s (H : fast_fresh_ihs_order Θ Ξ ρ As p ups Dc B ρa gs' gs vs s) :
    { ihs | Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs } by struct H :=
  | ρ, As, p, ups, Dc, B, ρa, nil, nil, nil, s, H => exist _ nil _
  | ρ, As, p, ups, Dc, B, ρa, ca_arg _ :: gs', ca_arg _ :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B (ρa ↦ v) gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, B, ρa, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, s, H with cache_lookup F (fc_seed F) p := {
    | exist _ (Some D) Ed
        with inspect (ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t))) := {
      (** The branch reads none of the argument's results: their types are
          not computed. *)
      | exist _ true E =>
          let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs
                               (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                                               (List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t))) s) + s) _ in
          exist _ (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                     (List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t))) s ++ ihs) _
      | exist _ false E =>
          let (as', Has) := fast_eval_ihty_impl F p ups ρ As ρa t v _ in
          let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs
                               (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s) + s) _ in
          exist _ (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s ++ ihs) _ }
    | exist _ None Ed => False_rect _ _ }
  | ρ, As, p, ups, Dc, B, ρa, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := fast_fresh_ihs_impl ρ As p ups Dc B ρa gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, B, ρa, _, _, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs (H : fast_wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs) :
    { r | ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r } by struct H :=
  | ρ, p, ups, Bks, Dc, nil, nil, nil, nil, H => exist _ nil _
  | ρ, p, ups, Bks, Dc, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, ihs, H with cache_lookup F (fc_seed F) p := {
    | exist _ (Some D) Ed =>
        let (rs, Hrs) := fast_eval_ih_impl F ρ p ups Bks t v (fc_seed F) _ in
        let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs
                         (snd (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs)) _ in
        exist _ (fst (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs) ++ r) _
    | exist _ None Ed => False_rect _ _ }
  | ρ, p, ups, Bks, Dc, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, ihs, H =>
      let (rs, Hrs) := fast_eval_ih_impl F ρ p ups Bks t v (fc_seed F) _ in
      let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs _ in
      exist _ (rs ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ :: gs', ca_arg _ :: gs, _ :: vs, ihs, H =>
      let (r, Hr) := fast_wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs _ in
      exist _ r _
  | ρ, p, ups, Bks, Dc, _, _, _, _, H => False_rect _ _.
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
  `( fast_read_la_order Θ Ξ s xs ->
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

with fast_read_la_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
| fast_read_la_order_nil :
  `( fast_read_la_order Θ Ξ s nil )
| fast_read_la_order_cons :
  `( fast_read_ne_order Θ Ξ s m ->
     fast_read_la_order Θ Ξ s xs ->
     fast_read_la_order Θ Ξ s ((k, n, m) :: xs) )

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
Hint Constructors fast_read_nf_order fast_read_ne_order fast_read_typ_order fast_read_la_order
  fast_read_ps_order fast_read_fields_order fast_read_cargs_order fast_read_shape_order fast_read_blocks_order fast_read_brs_order : mctt.

(** Every readback derivation is within its order: by the mutual induction
    on readback, the evaluations the orders quantify over being the ones
    the derivation makes ([functional_fast_eval]). *)
Lemma fast_read_order_sound : forall Θ Ξ,
    (forall s d m, Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_nf_order Θ Ξ s d) /\
    (forall s d m, Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_ne_order Θ Ξ s d) /\
    (forall s d m, Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fast_read_typ_order Θ Ξ s d) /\
    (forall s xs ys, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys -> fast_read_la_order Θ Ξ s xs) /\
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

Lemma fast_read_la_order_sound : forall Θ Ξ s xs ys, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys -> fast_read_la_order Θ Ξ s xs.
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
Hint Resolve fast_read_nf_order_sound fast_read_ne_order_sound fast_read_typ_order_sound fast_read_la_order_sound
  fast_read_ps_order_sound fast_read_cargs_order_sound fast_read_shape_order_sound fast_read_blocks_order_sound
  fast_read_brs_order_sound fast_read_fields_order_sound : mctt.

(** A constructor at a view, its arguments the last values, as many as the
    constructor takes ([fast_read_nf_con_view]). *)
Lemma fast_read_nf_con_view_last : forall Θ Ξ s p D j Mj qc k Is vm c gs as' vs Ps Args,
    ind_lookup Θ Ξ p = Some D ->
    ind_member D j = Some Mj ->
    im_head Mj = mh_view qc k Is vm ->
    ind_con Mj c = Some gs ->
    List.length as' = im_np D Mj ->
    List.length gs <= List.length vs ->
    Rpsᶠ as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
    Rcargsᶠ List.skipn (List.length vs - List.length gs) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ
      ⍮ env_args nil as' ⍮ s ↘ Args ->
    Rnfᶠ ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args).
Proof. intros; eapply fast_read_nf_con_view; try eassumption; lia. Qed.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : fast_read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : fast_read_la_order _ _ _ _ |- _ => progressive_invert H
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
Equations fast_read_nf_impl_c s d (ck : lk_cache Θ Ξ) (H : fast_read_nf_order Θ Ξ s d) : { m | Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, ⇓ 𝕌ω@i a      , ck, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ in
    exist _ A _
| s, ⇓ 𝕌@n a     , ck, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ in
    exist _ A _
| s, ⇓ (Levelᵈ@n) (lvᵈ c xs), ck, H =>
    let (ys, Hys) := fast_read_la_impl_c s xs ck _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, ⇓ (Levelᵈ@n) (⇑ a m), ck, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    exist _ (lvⁿ oz (cons (mk_level_atom 0 (dsort a) M) nil)) _
| s, ⇓ ⊤ᵈ m, ck, H => exist _ ⋆ⁿ _
| s, ⇓ ⊥ᵈ (⇑ _ m), ck, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (Πᵈ a p B) m, ck, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ in
    let (m', Hm') := fast_eval_app_impl F m ⇑! a s _ in
    let (b, Hb) := fast_eval_exp_impl F B (p ↦ ⇑! a s) _ in
    let (M, HM) := fast_read_nf_impl_c (S s) ⇓ b m' ck _ in
    exist _ (λⁿ A M) _
| s, ⇓ (⇑ a b) (⇑ c m), ck, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (d_ind p j as') v, ck, H with cache_lookup F ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_head Mj) := {
      (** At a record view, any value: the view's constructor, its
          arguments the value's projections *)
      | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
        | exist _ ((c, gs) :: nil) Ec =>
            let (ws, Hws) := fast_eval_projs_impl F fl v _ in
            let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (ind_uparams D)) as' ck _ in
            let (Args, HArgs) := fast_read_cargs_impl_c s p as' (env_args nil as') gs ws (Some (exist _ (p, D) Ed)) _ in
            exist _ (nf_con p j c (Ps ++ Args)%list) _
        | exist _ _ Ec => False_rect _ _ }
      | exist _ (mh_decl pm) Eh with v := {
        (** A constructor of a declared member: its arguments after its
            parameters *)
        | d_con _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ in
              let (Args, HArgs) := fast_read_cargs_impl_c s p (List.firstn (ind_nu D) as') (env_args nil as') gs
                                     (List.skipn (im_np D Mj) vs) (Some (exist _ (p, D) Ed)) _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | ⇑ a m =>
            let (M, HM) := fast_read_ne_impl_c s m ck _ in
            exist _ ⇑ⁿ M _
        | _ => False_rect _ _ }
      | exist _ (mh_view qv kv Iv vmv) Eh with v := {
        (** At a view: its arguments are the last values *)
        | d_con _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ in
              let (Args, HArgs) := fast_read_cargs_impl_c s p (List.firstn (ind_nu D) as') (env_args nil as') gs
                                     (List.skipn (List.length vs - List.length gs) vs) (Some (exist _ (p, D) Ed)) _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | ⇑ a m =>
            let (M, HM) := fast_read_ne_impl_c s m ck _ in
            exist _ ⇑ⁿ M _
        | _ => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, ⇓ (d_record p ns) v, ck, H with record_lookup_f F p := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (record_params R)) ns ck _ in
      let (Fs, HFs) := fast_read_fields_impl_c s (env_args nil ns) (record_fields R) v ck _ in
      exist _ (nf_tuple p Ps (List.map fst (record_fields R)) Fs) _
  | exist _ None El => False_rect _ _ }

  with fast_read_ne_impl_c s d (ck : lk_cache Θ Ξ) (H : fast_read_ne_order Θ Ξ s d) : { m | Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, ck, H => exist _ #ⁿ (s - x - 1) _
| s, d_glob p, ck, H => exist _ (ne_glob p) _
| s, m $ᵈ n, ck, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    let (N, HN) := fast_read_nf_impl_c s n ck _ in
    exist _ (M $ⁿ N) _
| s, efqᵈ m under p return B, ck, H =>
    let (b, Hb) := fast_eval_exp_impl F B (p ↦ ⇑! ⊥ᵈ s) _ in
    let (B', HB') := fast_read_typ_impl_c (S s) b ck _ in
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    exist _ (efqⁿ M return B') _
| s, d_elim ρ Bks p ups j as' m, ck, H with cache_lookup F ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_ref p j Mj) := {
      | exist _ (pc, k) Er with cache_lookup F (Some (exist _ (p, D) Ed)) pc := {
        | exist _ (Some Dq) Edq with fast_eval_mref_impl F p ups j _ := {
          | exist _ (_, _, pre) Hm =>
              let (Us, HUs) := fast_read_ps_impl_c s nil (List.rev (ind_uparams Dq)) pre ck _ in
              let (NBks, HNBks) := fast_read_blocks_impl_c s ρ p ups Bks Dq (im_sel Mj) 0 (ind_bmembers Dq) (Some (exist _ (p, D) Ed)) _ in
              let (M, HM) := fast_read_ne_impl_c s m ck _ in
              exist _ (ne_elim pc Us k NBks M) _ }
        | exist _ None Edq => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_proj f m, ck, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    exist _ (ne_proj f M) _

  with fast_read_typ_impl_c s d (ck : lk_cache Θ Ξ) (H : fast_read_typ_order Θ Ξ s d) : { m | Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, ck, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, ck, H =>
    let (W, HW) := fast_read_nf_impl_c s ⇓ Levelᵈ l ck _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, Levelᵈ@n, ck, H => exist _ (Levelⁿ@n) _
| s, ⊤ᵈ, ck, H => exist _ ⊤ⁿ _
| s, ⊥ᵈ, ck, H => exist _ ⊥ⁿ _
| s, Πᵈ a p B, ck, H =>
    let (A, HA) := fast_read_typ_impl_c s a ck _ in
    let (b, Hb) := fast_eval_exp_impl F B (p ↦ ⇑! a s) _ in
    let (B', HB') := fast_read_typ_impl_c (S s) b ck _ in
    exist _ (Πⁿ A B') _
| s, ⇑ a b, ck, H =>
    let (B, HB) := fast_read_ne_impl_c s b ck _ in
    exist _ ⇑ⁿ B _
| s, d_ind p k nil, ck, H => exist _ (nf_indty p k nil) _
| s, d_ind p k as', ck, H with cache_lookup F ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D k) := {
    | exist _ (Some Mk) Em =>
        let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (im_params D Mk)) as' ck _ in
        exist _ (nf_indty p k Ps) _
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_record p ns, ck, H with record_lookup_f F p := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fast_read_ps_impl_c s nil (List.rev (record_params R)) ns ck _ in
      exist _ (nf_record p Ps) _
  | exist _ None El => False_rect _ _ }

  with fast_read_la_impl_c s xs (ck : lk_cache Θ Ξ) (H : fast_read_la_order Θ Ξ s xs) : { ys | Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, ck, H => exist _ nil _
| s, cons (k, n, m) xs, ck, H =>
    let (M, HM) := fast_read_ne_impl_c s m ck _ in
    let (ys, Hys) := fast_read_la_impl_c s xs ck _ in
    exist _ (cons (mk_level_atom k n M) ys) _

  with fast_read_ps_impl_c s ρ T vs (ck : lk_cache Θ Ξ) (H : fast_read_ps_order Θ Ξ s ρ T vs) : { Ms | Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, ck, H => exist _ nil _
| s, ρ, ce_ass A :: T, v :: vs, ck, H =>
    let (a, Ha) := fast_eval_exp_impl F A ρ _ in
    let (V, HV) := fast_read_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fast_read_ps_impl_c s (ρ ↦ v) T vs ck _ in
    exist _ (cons V Vs) _
| s, ρ, _, _, ck, H => False_rect _ _

  with fast_read_fields_impl_c s ρ fl v (ck : lk_cache Θ Ξ) (H : fast_read_fields_order Θ Ξ s ρ fl v) :
    { Fs | Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs } by struct H :=
| s, ρ, nil, v, ck, H => exist _ nil _
| s, ρ, (f, T) :: fl, v, ck, H =>
    let (r, Hr) := fast_eval_proj_impl F f v _ in
    let (t, Ht) := fast_eval_exp_impl F T ρ _ in
    let (V, HV) := fast_read_nf_impl_c s ⇓ t r ck _ in
    let (Vs, HVs) := fast_read_fields_impl_c s (ρ ↦ r) fl v ck _ in
    exist _ (cons V Vs) _

  with fast_read_cargs_impl_c s p ups ρ gs vs (ck : lk_cache Θ Ξ) (H : fast_read_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, p, ups, ρ, nil, nil, ck, H => exist _ nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, ck, H =>
    let (a, Ha) := fast_eval_exp_impl F A ρ _ in
    let (V, HV) := fast_read_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fast_read_cargs_impl_c s p ups (ρ ↦ v) gs vs ck _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, ca_rec t :: gs, v :: vs, ck, H =>
    let (V, HV) := fast_read_shape_impl_c s p ups ρ t v ck _ in
    let (Vs, HVs) := fast_read_cargs_impl_c s p ups ρ gs vs ck _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, _, _, ck, H => False_rect _ _

  with fast_read_shape_impl_c s p ups ρ t v (ck : lk_cache Θ Ξ) (H : fast_read_shape_order Θ Ξ s p ups ρ t v) :
    { V | Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V } by struct H :=
| s, p, ups, ρ, pt_self j Ps, v, ck, H =>
    let (bs, Hbs) := fast_eval_exps_impl F Ps ρ _ in
    let (V, HV) := fast_read_nf_impl_c s ⇓ (d_ind p j (ups ++ bs)) v ck _ in
    exist _ V _
| s, p, ups, ρ, pt_pi B t, v, ck, H =>
    let (b, Hb) := fast_eval_exp_impl F B ρ _ in
    let (A, HA) := fast_read_typ_impl_c s b ck _ in
    let (r, Hr) := fast_eval_app_impl F v (⇑! b s) _ in
    let (V, HV) := fast_read_shape_impl_c (S s) p ups (ρ ↦ ⇑! b s) t r ck _ in
    exist _ (λⁿ A V) _

  with fast_read_blocks_impl_c s ρ p ups Bks Dc sel i Ms (ck : lk_cache Θ Ξ) (H : fast_read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms) :
    { NBks | Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks } by struct H :=
| s, ρ, p, ups, Bks, Dc, sel, i, nil, ck, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, sel, i, Mi :: Ms, ck, H with cache_lookup F ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D (elim_src sel i)) := {
    | exist _ (Some Mv) Em with inspect (List.nth_error Bks (elim_src sel i)) := {
      | exist _ (Some b) Eb with fast_eval_mref_impl F p ups (elim_src sel i) _ := {
        | exist _ (pk, k, pre) Hm =>
            let (ns, Hns) := fast_fresh_tele_impl F (env_args nil ups) (List.rev (im_nparams Mv)) s _ in
            let (a, Ha) := fast_eval_exp_impl F (eb_motive b)
                             (env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil)) _ in
            let (A', HA') := fast_read_typ_impl_c (S (s + im_nn Mi)) a ck _ in
            let (Bs', HBs') := fast_read_brs_impl_c s ρ p ups Bks Dc Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b) ck _ in
            let (NBks, HNBks) := fast_read_blocks_impl_c s ρ p ups Bks Dc sel (S i) Ms ck _ in
            exist _ (cons (mk_normal_block (S (im_nn Mi)) A' Bs') NBks) _ }
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }

  with fast_read_brs_impl_c s ρ p ups Bks Dc Mv A Mi r cs Bs (ck : lk_cache Θ Ξ)
         (H : fast_read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs) :
    { Bs' | Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' } by struct H :=
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, nil, nil, ck, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, (pk, k, pre), (c, gs') :: cs, (_, _, B) :: Bs, ck, H with inspect (ind_con Mv c) := {
  | exist _ (Some gs) Ec =>
      let (ns, Hns) := fast_fresh_tele_impl F (env_args nil ups) (List.rev (im_nparams Mv)) s _ in
      let (vs, Hvs) := fast_fresh_cargs_impl F p ups (env_args nil (ups ++ ns)) gs (s + im_nn Mi) _ in
      let (ihs, Hihs) := fast_fresh_ihs_impl F ρ (blocks_motives Bks) p ups Dc B (env_args nil (ups ++ ns)) gs' gs vs
                           (s + im_nn Mi + List.length gs') _ in
      let (wihs, Hw) := fast_wrap_ihs_impl F ρ p ups Bks Dc gs' gs vs ihs _ in
      let (b, Hb) := fast_eval_exp_impl F B (env_args ρ (ns ++ vs ++ wihs)) _ in
      let (t, Ht) := fast_eval_exp_impl F A (env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil)) _ in
      let (B', HB') := fast_read_nf_impl_c (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) ⇓ t b ck _ in
      let (Bs', HBs') := fast_read_brs_impl_c s ρ p ups Bks Dc Mv A Mi (pk, k, pre) cs Bs ck _ in
      exist _ (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dc gs') B') Bs') _
  | exist _ None Ec => False_rect _ _ }
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, _, _, ck, H => False_rect _ _.

(** Each hole is either a readback order of a subterm, read off the order of
    the whole by inversion, or the readback itself, by its rule. *)
(** The lookups the order records are the ones computed.  The computed
    one is replaced, in the goal, by the recorded one: the order premises
    about the recorded one are then the arguments of the recursion as they
    stand, which the structural recursion needs. *)
#[local]
Ltac rb_unify x y :=
  let Heq := fresh "Heq" in
  intro Heq;
  first [ is_var y; lazymatch goal with |- context [y] => subst y end
        | is_var x; lazymatch goal with |- context [x] => subst x end
        | subst ].

#[local]
Ltac rb_glob :=
  repeat match goal with
    | H1 : ind_lookup _ _ ?p = Some ?x, H2 : ind_lookup _ _ ?p = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; rb_unify x y
    | H1 : ind_con ?D ?c = Some ?x, H2 : ind_con ?D ?c = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; rb_unify x y
    | H1 : ind_member ?D ?k = Some ?x, H2 : ind_member ?D ?k = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; rb_unify x y
    | H1 : List.nth_error ?Bks ?j = Some ?x, H2 : List.nth_error ?Bks ?j = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; rb_unify x y
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
        rewrite H1 in H2; injection H2; clear H2; rb_unify x y
    (** The member a member stands for, at the reference the order records *)
    | Hm : fast_eval_mref _ _ ?p _ ?j (?a, ?b, _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
      Hr : im_ref ?p ?j _ = (?c, ?d) |- _ =>
        assert_fails (constr_eq a c);
        let E := fresh "Er" in
        pose proof (fast_eval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) as E;
        rewrite E in Hr; injection Hr; clear Hr; intros; subst
    end.

#[local]
Ltac rb_ord :=
  repeat impl_obl_tac1; rb_glob;
  first [ eassumption
        (** A readback under a binder: the order of the body is a premise
            quantified over the results of the evaluations above it. *)
        | solve [ eauto 2 ] ].

#[local]
Ltac rb_eqb := repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end.

#[local]
Ltac rb_run := repeat impl_obl_tac1; rb_glob; rb_eqb; econstructor; eassumption.

(** The rules of inductive types have premises the order records under
    quantifiers, and lookups the order rules out when they fail. *)
#[local]
Ltac rb_ind :=
  repeat impl_obl_tac1; rb_glob; rb_eqb;
  first [ congruence
        | solve [ eapply fast_read_nf_con_view_last; eassumption ]
        (** A neutral of a member with a block: its head is not a record
            view's *)
        | solve [ eapply fast_read_nf_ind_neut; try eassumption;
                  unfold im_is_rview; match goal with H : im_head _ = _ |- _ => rewrite H; reflexivity end ]
        | econstructor; try eassumption; eauto 3 ].

#[local]
Ltac rb_obl_auto :=
  intros; cbv beta in *;
  lazymatch goal with
  | |- fast_read_nf_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_ne_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_typ_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_la_order _ _ _ _ => first [ rb_ord | rb_run ]
  (** The parameters of a type former with arguments: read off its order
      before inversion takes the arguments apart. *)
  | |- fast_read_ps_order _ _ _ _ _ _ =>
      first [ solve [ match goal with H : fast_read_typ_order _ _ _ (d_ind _ _ (_ :: _)) |- _ =>
                        inversion H; subst; rb_glob; assumption end ]
            | rb_ord | rb_run ]
  | |- fast_read_fields_order _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_eval_proj_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_cargs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_shape_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_blocks_order _ _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_read_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_fresh_tele_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_fresh_cargs_order _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_eval_projs_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_eval_exp_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_eval_exps_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_eval_app_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fast_eval_mref_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- _ => abstract (first [ rb_ord | rb_run | eapply fast_read_typ_suniv_of_nf; eassumption | rb_ind ])
  end.

Solve All Obligations with rb_obl_auto.

(** The [fast_read_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the readback orders and the functionality
    of readback. *)

(** The entries of readback, from the declaration the command looked up
    ([fc_seed]). *)
Definition fast_read_nf_impl s d (H : fast_read_nf_order Θ Ξ s d) : { m | Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_nf_impl_c s d (fc_seed F) H.
Definition fast_read_ne_impl s d (H : fast_read_ne_order Θ Ξ s d) : { m | Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_ne_impl_c s d (fc_seed F) H.
Definition fast_read_typ_impl s d (H : fast_read_typ_order Θ Ξ s d) : { m | Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fast_read_typ_impl_c s d (fc_seed F) H.
Definition fast_read_la_impl s xs (H : fast_read_la_order Θ Ξ s xs) : { ys | Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys } :=
  fast_read_la_impl_c s xs (fc_seed F) H.

#[local]
Ltac functional_fast_read_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_fast_read_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma fast_read_nf_impl_complete : forall s d m,
    Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', fast_read_nf_impl s d H = exist _ m H'.
Proof.
  intros; functional_fast_read_complete.
Qed.

Lemma fast_read_ne_impl_complete : forall s d m,
    Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', fast_read_ne_impl s d H = exist _ m H'.
Proof.
  intros; functional_fast_read_complete.
Qed.

Lemma fast_read_typ_impl_complete : forall s d m,
    Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', fast_read_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_fast_read_complete.
Qed.

Lemma fast_read_la_impl_complete : forall s xs ys,
    Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    exists H H', fast_read_la_impl s xs H = exist _ ys H'.
Proof.
  intros; functional_fast_read_complete.
Qed.

End ReadbackImpl.

Extraction Inline fast_read_nf_impl_c_functional
  fast_read_ne_impl_c_functional
  fast_read_typ_impl_c_functional
  fast_read_la_impl_c_functional
  fast_read_ps_impl_c_functional
  fast_read_fields_impl_c_functional
  fast_read_cargs_impl_c_functional
  fast_read_shape_impl_c_functional
  fast_read_blocks_impl_c_functional
  fast_read_brs_impl_c_functional.
