From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Reference Require Import Evaluation.
From Mctt.Extraction Require Import Readback.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** * The Reference Readback

    The readback relations of [Core.Semantic.Readback] implemented
    literally, with their termination orders; see [Reference.Evaluation].
    The relations along the leaf paths of a recursive argument,
    [fresh_leaf_vars] and [wrap_leaf_vals], need no order: they are
    computed by [leaf_vars_f] and [leaf_wrap_f] ([Extraction.Readback]),
    sound at the lengths their relations have. *)

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
Hint Constructors fresh_tele_order fresh_cargs_order fresh_ihs_order wrap_ihs_order eval_entry_type_order : mctt.

Lemma fresh_tele_order_sound : forall Θ Ξ ρ T s vs, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> fresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

Lemma fresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs,
    Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> fresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

Lemma fresh_ihs_order_sound : forall Θ Ξ ρ As p ups Dc ρa gs' gs vs s ihs,
    Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs s.
Proof.
  induction 1; try solve [ econstructor; eassumption ].
  eapply fresh_ihs_order_rec_case; try eassumption; [ mauto | |];
    intros; functional_eval_rewrite_clear.
  - exact (fresh_leaf_vars_types_length _ _ _ _ H1).
  - rewrite <- (fresh_leaf_vars_f _ _ _ _ H1); assumption.
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
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac fresh_readback_obligation :=
    intros; cbv beta in *;
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
      (** The [i]-th type of the recursive results is there. *)
      | H : forall as', ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ as' -> _ < _,
        Hi : ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?l, E : List.nth_error ?l _ = None |- _ =>
          exfalso; pose proof (H _ Hi); apply List.nth_error_None in E; lia
      end;
    first [ eassumption | solve [ eauto 2 ]
          (** The leaf paths' computations, at the lengths the order
              records *)
          | solve [ eapply fresh_ihs_rec; [ eassumption | eassumption | apply leaf_vars_f_sound; eauto | eassumption ] ]
          | solve [ eapply wrap_ihs_eval_rec; [ eassumption | eassumption | | eassumption ];
                    match goal with H : forall rs, _ -> _ /\ _, Hr : eval_ih _ _ _ _ _ _ _ _ ?rs |- _ =>
                      destruct (H _ Hr); apply leaf_wrap_f_sound; assumption end ]
          | econstructor; eassumption ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_tele_impl ρ T s (H : fresh_tele_order Θ Ξ ρ T s) : { vs | Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | ρ, nil, s, H => exist _ nil _
  | ρ, ce_ass κ A :: T, s, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := fresh_tele_impl (ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ) T (S s) _ in
      exist _ (⇑! a s :: vs) _
  | ρ, _, s, H => False_rect _ _.
  Solve All Obligations with fresh_readback_obligation.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_cargs_impl p ups ρ gs s (H : fresh_cargs_order Θ Ξ p ups ρ gs s) :
    { vs | Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ nil _
  | p, ups, ρ, ca_arg r A :: gs, s, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := fresh_cargs_impl p ups (ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ) gs (S s) _ in
      exist _ (⇑! a s :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, H =>
      let (a, Ha) := eval_shape_type_impl Θ Ξ p ups ρ t _ in
      let (vs, Hvs) := fresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! a s :: vs) _.
  Solve All Obligations with fresh_readback_obligation.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs s (H : fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs s) :
    { ihs | Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs } by struct H :=
  | ρ, As, p, ups, Dc, ρa, nil, nil, nil, s, H => exist _ nil _
  | ρ, As, p, ups, Dc, ρa, ca_arg _ _ :: gs', ca_arg _ T :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := fresh_ihs_impl ρ As p ups Dc (ρa ↦ v ⦂ entry_type_closure T ρa) gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, ρa, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, s, H with inspect (ind_lookup Θ Ξ p) := {
    | exist _ (Some D) Ed =>
        let (as', Has) := eval_ihty_impl Θ Ξ p ups ρ As ρa t v _ in
        let (ihs, Hihs) := fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs
                             (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s) + s) _ in
        exist _ (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s ++ ihs) _
    | exist _ None Ed => False_rect _ _ }
  | ρ, As, p, ups, Dc, ρa, ca_arg _ _ :: gs', ca_rec t :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, ρa, _, _, _, s, H => False_rect _ _.
  Solve All Obligations with fresh_readback_obligation.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs (H : wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs) :
    { r | ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r } by struct H :=
  | ρ, p, ups, Bks, Dc, nil, nil, nil, nil, H => exist _ nil _
  | ρ, p, ups, Bks, Dc, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, ihs, H with inspect (ind_lookup Θ Ξ p) := {
    | exist _ (Some D) Ed =>
        let (rs, Hrs) := eval_ih_impl Θ Ξ ρ p ups Bks t v _ in
        let (r, Hr) := wrap_ihs_impl ρ p ups Bks Dc gs' gs vs
                         (snd (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs)) _ in
        exist _ (fst (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs) ++ r) _
    | exist _ None Ed => False_rect _ _ }
  | ρ, p, ups, Bks, Dc, ca_arg _ _ :: gs', ca_rec t :: gs, v :: vs, ihs, H =>
      let (rs, Hrs) := eval_ih_impl Θ Ξ ρ p ups Bks t v _ in
      let (r, Hr) := wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs _ in
      exist _ (rs ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ _ :: gs', ca_arg _ _ :: gs, _ :: vs, ihs, H =>
      let (r, Hr) := wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs _ in
      exist _ r _
  | ρ, p, ups, Bks, Dc, _, _, _, _, H => False_rect _ _.
  Solve All Obligations with fresh_readback_obligation.

  (** The type value of an environment's entry *)
  #[tactic="idtac"]
  Equations eval_entry_type_impl t (H : eval_entry_type_order Θ Ξ t) : { a | eval_entry_type Θ Ξ t a } :=
  | entry_type_value a, H => exist _ a _
  | entry_type_closure A ρ, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      exist _ a _
  | entry_type_shape p ups ρ t, H =>
      let (a, Ha) := eval_shape_type_impl Θ Ξ p ups ρ t _ in
      exist _ a _
  | entry_type_induction_hypothesis ρm As p ups ρ t v i, H with eval_ihty_impl Θ Ξ p ups ρm As ρ t v _ := {
    | exist _ as' Has with inspect (List.nth_error as' i) := {
      | exist _ (Some a) E => exist _ a _
      | exist _ None E => False_rect _ _ } }
  | entry_type_none, H => False_rect _ _.
  Solve All Obligations with fresh_readback_obligation.
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

(** The atoms of a level *)
with read_level_atoms_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
(** No atom *)
| read_level_atoms_order_nil :
  `( read_level_atoms_order Θ Ξ s nil )
(** The first atom's neutral, then the rest *)
| read_level_atoms_order_cons :
  `( read_ne_order Θ Ξ s m ->
     read_level_atoms_order Θ Ξ s xs ->
     read_level_atoms_order Θ Ξ s ((k, n, m) :: xs) )

(** Values at a telescope *)
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

(** The arguments of a constructor *)
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
Lemma read_nf_con_view_last : forall Θ Ξ s p D j Mj qc k Is vm c gs as' vs Ps Args,
    ind_lookup Θ Ξ p = Some D ->
    ind_member D j = Some Mj ->
    im_head Mj = mh_view qc k Is vm ->
    ind_con Mj c = Some gs ->
    List.length as' = im_np D Mj ->
    List.length gs <= List.length vs ->
    Rps as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
    Rcargs List.skipn (List.length vs - List.length gs) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ
      ⍮ env_tele nil (List.rev (im_params D Mj)) as' ⍮ s ↘ Args ->
    Rnf ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args).
Proof. intros; eapply read_nf_con_view; try eassumption; lia. Qed.

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
  (** A value at a type of a known head: by the rules at that head, or a
      proof, the lookups and the kind then excluding all but one *)
  | H : read_nf_order _ _ _ (⇓ (d_ind _ _ _) _) |- _ => inversion H; subst; clear H
  | H : read_nf_order _ _ _ (⇓ (d_pi _ _ _ _ _) _) |- _ => inversion H; subst; clear H
  | H : read_nf_order _ _ _ (⇓ (⇑ _ _) _) |- _ => inversion H; subst; clear H
  | H : read_nf_order _ _ _ (⇓ ?a _) |- _ => is_var a; inversion H; subst; clear H
  end.

Section ReadbackImpl.
Variables (Θ : gdeps) (Ξ : gstack).

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations read_nf_impl s d (H : read_nf_order Θ Ξ s d) : { m | Rnf d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
(** A value of a proposition, whatever its head: the proposition as a
    type, the proof as a term ([read_nf_proof]) *)
| s, d_dom a m, H with evaluated_kind_decide (domain_kind a) := {
  | right Hk =>
      let (P, HP) := read_typ_impl s a _ in
      let (M, HM) := read_proof_impl s m _ in
      exist _ (nf_proof P M) _
  | left Hk with a := {
    | d_univ i =>
        let (A, HA) := read_typ_impl s m _ in
        exist _ A _
    | d_suniv n =>
        let (A, HA) := read_typ_impl s m _ in
        exist _ A _
    | d_level n with m := {
      | d_lvl c xs =>
          let (ys, Hys) := read_level_atoms_impl s xs _ in
          exist _ (nf_lvl_of (lvl_canon (c, ys))) _
      | d_neut a' m' =>
          let (M, HM) := read_ne_impl s m' _ in
          exist _ (lvⁿ ordinal_zero (cons (mk_level_atom 0 (domain_level_sort a') M) nil)) _
      | _ => False_rect _ _ }
    | d_prop =>
        let (A, HA) := read_typ_impl s m _ in
        exist _ A _
    | d_level_sort =>
        let (A, HA) := read_typ_impl s m _ in
        exist _ A _
    (** A function, η-long *)
    | d_pi κd κc a' ρ B =>
        let (A, HA) := read_typ_impl s a' _ in
        let (m', Hm') := eval_app_impl Θ Ξ m (⇑! a' s) _ in
        let (b, Hb) := eval_exp_impl Θ Ξ B (ρ ↦ ⇑! a' s ⦂ entry_type_value a') _ in
        let (M, HM) := read_nf_impl (S s) ⇓ b m' _ in
        exist _ (λⁿ A M) _
    | d_neut a' b with m := {
      | d_neut c m' =>
          let (M, HM) := read_ne_impl s m' _ in
          exist _ (⇑ⁿ{domain_kind (⇑ a' b)} M) _
      | _ => False_rect _ _ }
    | d_ind p j as' with inspect (ind_lookup Θ Ξ p) := {
      | exist _ (Some D) Ed with inspect (ind_member D j) := {
        | exist _ (Some Mj) Em with inspect (im_is_rview Mj) := {
          (** At a record view, any value: the view's constructor, its
              arguments the value's projections *)
          | exist _ true Ev with inspect (im_head Mj) := {
            | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
              | exist _ ((c, gs) :: nil) Ec =>
                  let (ws, Hws) := eval_projs_impl Θ Ξ fl m _ in
                  let (Ps, HPs) := read_ps_impl s nil (List.rev (ind_uparams D)) as' _ in
                  let (Args, HArgs) := read_cargs_impl s p as' (decl_env D as') gs ws _ in
                  exist _ (nf_con p j c (Ps ++ Args)%list) _
              | exist _ _ Ec => False_rect _ _ }
            | exist _ _ Eh => False_rect _ _ }
          | exist _ false Ev with m := {
            (** A neutral of a member with a block *)
            | d_neut a' m' =>
                let (M, HM) := read_ne_impl s m' _ in
                exist _ (⇑ⁿ{domain_kind (d_ind p j as')} M) _
            | d_con _ _ c vs with inspect (im_head Mj) := {
              (** A constructor of a declared member: its arguments after
                  its parameters *)
              | exist _ (mh_decl pm) Eh with inspect (ind_con Mj c) := {
                | exist _ (Some gs) Ec =>
                    let (Ps, HPs) := read_ps_impl s nil (List.rev (im_params D Mj)) as' _ in
                    let (Args, HArgs) := read_cargs_impl s p (List.firstn (ind_nu D) as') (env_tele nil (List.rev (im_params D Mj)) as') gs
                                           (List.skipn (im_np D Mj) vs) _ in
                    exist _ (nf_con p j c (Ps ++ Args)%list) _
                | exist _ None Ec => False_rect _ _ }
              (** A constructor at a view: its arguments are the last
                  values *)
              | exist _ (mh_view qv kv Iv vmv) Eh with inspect (ind_con Mj c) := {
                | exist _ (Some gs) Ec =>
                    let (Ps, HPs) := read_ps_impl s nil (List.rev (im_params D Mj)) as' _ in
                    let (Args, HArgs) := read_cargs_impl s p (List.firstn (ind_nu D) as') (env_tele nil (List.rev (im_params D Mj)) as') gs
                                           (List.skipn (List.length vs - List.length gs) vs) _ in
                    exist _ (nf_con p j c (Ps ++ Args)%list) _
                | exist _ None Ec => False_rect _ _ }
              | exist _ (mh_record _ _ _) Eh => False_rect _ _ }
            | _ => False_rect _ _ } }
        | exist _ None Em => False_rect _ _ }
      | exist _ None Ed => False_rect _ _ }
    (** A value of a record type, η-long *)
    | d_record p ns with inspect (record_lookup Θ Ξ p) := {
      | exist _ (Some R) El =>
          let (Ps, HPs) := read_ps_impl s nil (List.rev (record_params R)) ns _ in
          let (Fs, HFs) := read_fields_impl s (env_tele nil (List.rev (record_params R)) ns) (record_fields R) m _ in
          exist _ (nf_tuple p Ps (List.map fst (record_fields R)) Fs) _
      | exist _ None El => False_rect _ _ }
    (** No other type of an evaluated kind has a readback order *)
    | _ => False_rect _ _ } }

  with read_ne_impl s d (H : read_ne_order Θ Ξ s d) : { m | Rne d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, H => exist _ #ⁿ (s - x - 1) _
| s, m $ᵈ n, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (N, HN) := read_nf_impl s n _ in
    exist _ (M $ⁿ N) _
| s, d_absurd c p, H =>
    let (C, HC) := read_typ_impl s c _ in
    let (M, HM) := read_proof_impl s p _ in
    exist _ (efqⁿ M return C) _
| s, d_glob p, H => exist _ (ne_glob p) _
| s, d_elim ρ Bks p ups j as' m, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_ref p j Mj) := {
      | exist _ (pc, k) Er with inspect (ind_lookup Θ Ξ pc) := {
        | exist _ (Some Dq) Edq with eval_mref_impl Θ Ξ p ups j _ := {
          | exist _ (_, _, pre) Hm =>
              let (Us, HUs) := read_ps_impl s nil (List.rev (ind_uparams Dq)) pre _ in
              let (NBks, HNBks) := read_blocks_impl s ρ p ups Bks Dq (im_sel Mj) 0 (ind_block_members Dq) _ in
              let (M, HM) := read_ne_impl s m _ in
              exist _ (ne_elim pc Us k NBks M) _ }
        | exist _ None Edq => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_proj f m, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ (ne_proj f M) _

  (** A proof, as a term: a neutral, or a kept proof under the definitions
      of the positions it reads *)
  with read_proof_impl s d (H : read_proof_order Θ Ξ s d) : { M | Rprf d in Θ ⍮ Ξ ⍮ s ↘ M } by struct H :=
| s, d_neut a m, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ (ne_to_exp M) _
| s, d_proof M ρ, H =>
    let (bs, Hbs) := read_lets_impl s ρ (proof_scope M ρ) _ in
    exist _ (lets_exp bs M) _
| s, _, H => False_rect _ _

  (** The definitions binding the positions [k - 1], …, [0] of [ρ],
      outermost first *)
  with read_lets_impl s ρ k (H : read_lets_order Θ Ξ s ρ k) : { bs | Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs } by struct H :=
| s, ρ, 0, H => exist _ nil _
| s, ρ, S k, H =>
    let (b, Hb) := read_entry_impl s (env_entry ρ k) _ in
    let (bs, Hbs) := read_lets_impl (S s) ρ k _ in
    exist _ (b :: bs) _

  (** The definition an entry is bound by *)
  with read_entry_impl s e (H : read_entry_order Θ Ξ s e) : { b | Rent e in Θ ⍮ Ξ ⍮ s ↘ b } by struct H :=
| s, de_term v t, H =>
    let (a, Ha) := eval_entry_type_impl Θ Ξ t _ in
    let (A, HA) := read_typ_impl s a _ in
    let (W, HW) := read_nf_impl s ⇓ a v _ in
    exist _ (b_def A W) _
| s, de_dm v t h U, H =>
    let (a, Ha) := eval_entry_type_impl Θ Ξ t _ in
    let (A, HA) := read_typ_impl s a _ in
    let (W, HW) := read_nf_impl s ⇓ a v _ in
    exist _ (b_def_mod A W U) _
| s, de_mod h U, H => exist _ (b_mod U) _

  with read_typ_impl s d (H : read_typ_order Θ Ξ s d) : { m | Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, H =>
    let (W, HW) := read_nf_impl s ⇓ Levelᵈ l _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, d_level n, H => exist _ (Levelⁿ@n) _
| s, d_level_sort, H => exist _ LevelSortⁿ _
| s, d_prop, H => exist _ Propⁿ _
| s, d_True, H => exist _ ⊤ⁿ _
| s, d_False, H => exist _ ⊥ⁿ _
| s, d_pi κd κc a ρ B, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (ρ ↦ ⇑! a s ⦂ entry_type_value a) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ (nf_pi κd κc A B') _
| s, d_and a ρ Q, H =>
    let (P', HP') := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl Θ Ξ Q (ρ ↦ ⇑! a s ⦂ entry_type_value a) _ in
    let (Q', HQ') := read_typ_impl (S s) b _ in
    exist _ (Σₚⁿ P' Q') _
| s, d_neut a b, H =>
    let (B, HB) := read_ne_impl s b _ in
    exist _ (⇑ⁿ{domain_kind (⇑ a b)} B) _
| s, d_ind p k as', H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_member D k) := {
    | exist _ (Some Mk) Em =>
        let (Ps, HPs) := read_ps_impl s nil (List.rev (im_params D Mk)) as' _ in
        exist _ (nf_indty p k Ps) _
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_record p ns, H with inspect (record_lookup Θ Ξ p) := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := read_ps_impl s nil (List.rev (record_params R)) ns _ in
      exist _ (nf_record p Ps) _
  | exist _ None El => False_rect _ _ }
(** No other value has a readback order as a type *)
| s, _, H => False_rect _ _

  with read_level_atoms_impl s xs (H : read_level_atoms_order Θ Ξ s xs) : { ys | Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, H => exist _ nil _
| s, cons (k, n, m) xs, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (ys, Hys) := read_level_atoms_impl s xs _ in
    exist _ (cons (mk_level_atom k n M) ys) _

  with read_ps_impl s ρ T vs (H : read_ps_order Θ Ξ s ρ T vs) : { Ms | Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, H => exist _ nil _
| s, ρ, ce_ass κ A :: T, v :: vs, H =>
    let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := read_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := read_ps_impl s (ρ ↦ v ⦂ entry_type_closure A ρ) T vs _ in
    exist _ (cons V Vs) _
| s, ρ, _, _, H => False_rect _ _

  with read_fields_impl s ρ fl v (H : read_fields_order Θ Ξ s ρ fl v) :
    { Fs | Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs } by struct H :=
| s, ρ, nil, v, H => exist _ nil _
| s, ρ, (f, T) :: fl, v, H =>
    let (r, Hr) := eval_proj_impl Θ Ξ f v _ in
    let (t, Ht) := eval_exp_impl Θ Ξ T ρ _ in
    let (V, HV) := read_nf_impl s ⇓ t r _ in
    let (Vs, HVs) := read_fields_impl s (ρ ↦ r ⦂ entry_type_closure T ρ) fl v _ in
    exist _ (cons V Vs) _

  with read_cargs_impl s p ups ρ gs vs (H : read_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, p, ups, ρ, nil, nil, H => exist _ nil _
| s, p, ups, ρ, ca_arg r A :: gs, v :: vs, H =>
    let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := read_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := read_cargs_impl s p ups (ρ ↦ v ⦂ entry_type_closure A ρ) gs vs _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, ca_rec t :: gs, v :: vs, H =>
    let (V, HV) := read_shape_impl s p ups ρ t v _ in
    let (Vs, HVs) := read_cargs_impl s p ups ρ gs vs _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, _, _, H => False_rect _ _

  with read_shape_impl s p ups ρ t v (H : read_shape_order Θ Ξ s p ups ρ t v) :
    { V | Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V } by struct H :=
| s, p, ups, ρ, pt_self j Ps, v, H =>
    let (bs, Hbs) := eval_exps_impl Θ Ξ Ps ρ _ in
    let (V, HV) := read_nf_impl s ⇓ (d_ind p j (ups ++ bs)) v _ in
    exist _ V _
| s, p, ups, ρ, pt_pi B t, v, H =>
    let (b, Hb) := eval_exp_impl Θ Ξ B ρ _ in
    let (A, HA) := read_typ_impl s b _ in
    let (r, Hr) := eval_app_impl Θ Ξ v (⇑! b s) _ in
    let (V, HV) := read_shape_impl (S s) p ups (ρ ↦ ⇑! b s ⦂ entry_type_closure B ρ) t r _ in
    exist _ (λⁿ A V) _

  with read_blocks_impl s ρ p ups Bks Dc sel i Ms (H : read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms) :
    { NBks | Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks } by struct H :=
| s, ρ, p, ups, Bks, Dc, sel, i, nil, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, sel, i, Mi :: Ms, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_member D (elim_src sel i)) := {
    | exist _ (Some Mv) Em with inspect (List.nth_error Bks (elim_src sel i)) := {
      | exist _ (Some b) Eb with eval_mref_impl Θ Ξ p ups (elim_src sel i) _ := {
        | exist _ (pk, k, pre) Hm =>
            let (ns, Hns) := fresh_tele_impl Θ Ξ (decl_env D ups) (List.rev (im_nparams Mv)) s _ in
            let (Z', HZ') := read_typ_impl (s + im_nn Mi) (d_ind pk k (pre ++ ns)) _ in
            let (a, Ha) := eval_exp_impl Θ Ξ (eb_motive b)
                             (env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns))
                                                    (⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat)))) _ in
            let (A', HA') := read_typ_impl (S (s + im_nn Mi)) a _ in
            let (Bs', HBs') := read_brs_impl s ρ p ups Bks Dc Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b) _ in
            let (NBks, HNBks) := read_blocks_impl s ρ p ups Bks Dc sel (S i) Ms _ in
            exist _ (cons (mk_normal_block (S (im_nn Mi)) Z' A' Bs') NBks) _ }
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }

  with read_brs_impl s ρ p ups Bks Dc Mv A Mi r cs Bs (H : read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs) :
    { Bs' | Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' } by struct H :=
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, nil, nil, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, (pk, k, pre), (c, gs') :: cs, (_, _, B) :: Bs, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_con Mv c) := {
    | exist _ (Some gs) Ec =>
        let (ns, Hns) := fresh_tele_impl Θ Ξ (decl_env D ups) (List.rev (im_nparams Mv)) s _ in
        let (vs, Hvs) := fresh_cargs_impl Θ Ξ p ups (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns) gs (s + im_nn Mi) _ in
        let (ihs, Hihs) := fresh_ihs_impl Θ Ξ ρ (blocks_motives Bks) p ups Dc (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns)
                             gs' gs vs (s + im_nn Mi + List.length gs') _ in
        let (wihs, Hw) := wrap_ihs_impl Θ Ξ ρ p ups Bks Dc gs' gs vs ihs _ in
        let (b, Hb) := eval_exp_impl Θ Ξ B (env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs)) _ in
        let (t, Ht) := eval_exp_impl Θ Ξ A (env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns))
                                                                  (d_con pk k c (pre ++ ns ++ vs)))) _ in
        let (B', HB') := read_nf_impl (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) ⇓ t b _ in
        let (Bs', HBs') := read_brs_impl s ρ p ups Bks Dc Mv A Mi (pk, k, pre) cs Bs _ in
        exist _ (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dc gs') B') Bs') _
    | exist _ None Ec => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, _, _, H => False_rect _ _.

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
    | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = None |- _ =>
        rewrite H1 in H2; discriminate H2
    | H1 : ind_con ?D ?c = Some ?x, H2 : ind_con ?D ?c = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = None |- _ =>
        rewrite H1 in H2; discriminate H2
    | H1 : ind_member ?D ?k = Some ?x, H2 : ind_member ?D ?k = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = None |- _ =>
        rewrite H1 in H2; discriminate H2
    | H1 : List.nth_error ?Bks ?j = Some ?x, H2 : List.nth_error ?Bks ?j = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = None |- _ =>
        rewrite H1 in H2; discriminate H2
    | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
        rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
    | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
        rewrite H1 in H2; injection H2; clear H2; intros; subst
    (** A record view, by its head; its one constructor *)
    | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
        exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
    | H1 : im_is_rview ?M = true, H2 : im_head ?M = mh_decl _ |- _ =>
        exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
    | H1 : im_is_rview ?M = true, H2 : im_head ?M = mh_view _ _ _ _ |- _ =>
        exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
    | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
        rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
    (** The kind of a type of a known head, computed: a proof's order at a
        type that is no proposition is ruled out *)
    | H : domain_kind _ = _ |- _ => progress cbn [domain_kind] in H; try discriminate H
    | H : evaluated_kind (domain_kind _) |- _ => progress cbn [domain_kind] in H
    | H : evaluated_kind ak_propositional |- _ => exfalso; exact (evaluated_kind_not_propositional _ H eq_refl)
    | H1 : evaluated_kind ?k, H2 : ?k = ak_propositional |- _ => exfalso; exact (evaluated_kind_not_propositional _ H1 H2)
    (** A record, looked up once *)
    | H1 : record_lookup _ _ ?p = Some ?x, H2 : record_lookup _ _ ?p = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; readback_unify x y
    | H1 : record_lookup _ _ ?p = Some _, H2 : record_lookup _ _ ?p = None |- _ =>
        rewrite H1 in H2; discriminate H2
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
  readback_glob;
  first [ eassumption
        | solve [ congruence ]
        (** A readback under a binder: the order of the body is a premise
            quantified over the results of the evaluations above it. *)
        | solve [ eauto 2 ]
        | impl_obligation_tac1; readback_order ].

#[local]
Ltac readback_eqb := repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end.

#[local]
Ltac readback_run := repeat impl_obligation_tac1; readback_glob; readback_eqb;
  econstructor; first [ eassumption | reflexivity ].

(** The rules of inductive types have premises the order records under
    quantifiers, and lookups the order rules out when they fail. *)
#[local]
Ltac readback_ind :=
  repeat impl_obligation_tac1; readback_glob; readback_eqb;
  first [ congruence
        | solve [ eapply read_nf_con_view_last; eassumption ]
        (** A neutral of a member with a block: its head is not a record
            view's *)
        | solve [ eapply read_nf_ind_neut; eassumption ]
        | econstructor; try eassumption; eauto 3 ].

#[local]
Ltac readback_obligation_auto :=
  intros; cbv beta in *;
  (** The recursive functions in scope are not needed by an obligation. *)
  repeat match goal with f : _ |- _ => lazymatch type of f with context [@sig _ _] => clear f end end;
  lazymatch goal with
  | |- read_nf_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_ne_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_proof_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_lets_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_entry_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_entry_type_order _ _ _ => first [ readback_order | readback_run ]
  | |- read_typ_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_level_atoms_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_ps_order _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_fields_order _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_proj_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_cargs_order _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_shape_order _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_blocks_order _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fresh_tele_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fresh_cargs_order _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_projs_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_exp_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_exps_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_app_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- eval_mref_order _ _ _ _ _ => first [ readback_order | readback_run ]
  | |- _ => abstract (first [ readback_order
                             (** A value of a proposition: the proposition as a type, the proof *)
                             | solve [ eapply read_nf_proof; eassumption ]
                             | readback_run | eapply read_typ_suniv_of_nf; eassumption | readback_ind ])
  end.

Solve All Obligations with readback_obligation_auto.

(** The [read_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the readback orders and the functionality
    of readback. *)

#[local]
Ltac functional_read_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_read_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma read_nf_impl_complete : forall s d m,
    Rnf d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', read_nf_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_ne_impl_complete : forall s d m,
    Rne d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', read_ne_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_typ_impl_complete : forall s d m,
    Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', read_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_level_atoms_impl_complete : forall s xs ys,
    Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    exists H H', read_level_atoms_impl s xs H = exist _ ys H'.
Proof.
  intros; functional_read_complete.
Qed.

End ReadbackImpl.
