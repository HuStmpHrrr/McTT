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

    Readback of [Core.Semantic.Readback], with its termination orders; see
    [Reference.Evaluation]. *)

Lemma read_nf_level_lvl_of_nf : forall Θ Ξ s l W,
    Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    W = nf_lvl_of (lvl_of_nf W).
Proof. inversion 1; subst; reflexivity. Qed.

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
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> fresh_tele_order Θ Ξ (ρ ↦ ⇑! a s) T (S s)) ->
     fresh_tele_order Θ Ξ ρ (ce_ass A :: T) s ).

(** The variables of the arguments of a constructor *)
Inductive fresh_cargs_order (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> Prop :=
(** No argument *)
| fresh_cargs_order_nil :
  `( fresh_cargs_order Θ Ξ p ups ρ nil s )
(** A non-recursive argument's type, then the rest *)
| fresh_cargs_order_arg :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> fresh_cargs_order Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s)) ->
     fresh_cargs_order Θ Ξ p ups ρ (ca_arg A :: gs) s )
(** A recursive argument's type, then the rest *)
| fresh_cargs_order_rec_case :
  `( eval_shty_order Θ Ξ p ups ρ t ->
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
  `( fresh_ihs_order Θ Ξ ρ As p ups Dc (ρa ↦ v) gs' gs vs s ->
     fresh_ihs_order Θ Ξ ρ As p ups Dc ρa (ca_arg T' :: gs') (ca_arg T :: gs) (v :: vs) s )
(** Recursive in both: the types of its results, one per leaf path, then
    the rest after the variables at the paths of the container's *)
| fresh_ihs_order_rec_case :
  `( ind_lookup Θ Ξ p = Some D ->
     eval_ihty_order Θ Ξ p ups ρ As ρa t v ->
     (forall as', ⟦ihty v of t at p ups under ρ As ⟧ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
        List.length as' = List.length (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))) ->
     (forall as', ⟦ihty v of t at p ups under ρ As ⟧ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
        fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs
          (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s) + s)) ->
     fresh_ihs_order Θ Ξ ρ As p ups Dc ρa (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) s )
(** Nested through: the rest *)
| fresh_ihs_order_nest :
  `( fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs s ->
     fresh_ihs_order Θ Ξ ρ As p ups Dc ρa (ca_arg T' :: gs') (ca_rec t :: gs) (v :: vs) s ).

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
        List.length rs = List.length (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) /\
        List.length (List.filter (fun b => b) (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)))
          <= List.length ihs) ->
     (forall rs, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
        wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs
          (snd (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs))) ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Nested through: the eliminator at the argument, then the rest *)
| wrap_ihs_order_nest :
  `( eval_ih_order Θ Ξ ρ p ups Bks t v ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_arg T' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Non-recursive: the rest *)
| wrap_ihs_order_arg :
  `( wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs ->
     wrap_ihs_order Θ Ξ ρ p ups Bks Dc (ca_arg T' :: gs') (ca_arg T :: gs) (v :: vs) ihs ).

#[local]
Hint Constructors fresh_tele_order fresh_cargs_order fresh_ihs_order wrap_ihs_order : mctt.

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

#[export]
Hint Resolve fresh_tele_order_sound fresh_cargs_order_sound fresh_ihs_order_sound wrap_ihs_order_sound : mctt.

Section FreshImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac fr_obl :=
    intros; cbv beta in *;
    repeat match goal with
      | H : fresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : fresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : fresh_ihs_order _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : wrap_ihs_order _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    (** The lookups the order records are the ones computed. *)
    repeat match goal with
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
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
  | ρ, ce_ass A :: T, s, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := fresh_tele_impl (ρ ↦ ⇑! a s) T (S s) _ in
      exist _ (⇑! a s :: vs) _
  | ρ, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_cargs_impl p ups ρ gs s (H : fresh_cargs_order Θ Ξ p ups ρ gs s) :
    { vs | Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ nil _
  | p, ups, ρ, ca_arg A :: gs, s, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := fresh_cargs_impl p ups (ρ ↦ ⇑! a s) gs (S s) _ in
      exist _ (⇑! a s :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, H =>
      let (a, Ha) := eval_shty_impl Θ Ξ p ups ρ t _ in
      let (vs, Hvs) := fresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! a s :: vs) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs s (H : fresh_ihs_order Θ Ξ ρ As p ups Dc ρa gs' gs vs s) :
    { ihs | Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs } by struct H :=
  | ρ, As, p, ups, Dc, ρa, nil, nil, nil, s, H => exist _ nil _
  | ρ, As, p, ups, Dc, ρa, ca_arg _ :: gs', ca_arg _ :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := fresh_ihs_impl ρ As p ups Dc (ρa ↦ v) gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, ρa, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, s, H with inspect (ind_lookup Θ Ξ p) := {
    | exist _ (Some D) Ed =>
        let (as', Has) := eval_ihty_impl Θ Ξ p ups ρ As ρa t v _ in
        let (ihs, Hihs) := fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs
                             (List.length (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s) + s) _ in
        exist _ (leaf_vars_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s ++ ihs) _
    | exist _ None Ed => False_rect _ _ }
  | ρ, As, p, ups, Dc, ρa, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := fresh_ihs_impl ρ As p ups Dc ρa gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, p, ups, Dc, ρa, _, _, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs (H : wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs) :
    { r | ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r } by struct H :=
  | ρ, p, ups, Bks, Dc, nil, nil, nil, nil, H => exist _ nil _
  | ρ, p, ups, Bks, Dc, ca_rec t' :: gs', ca_rec t :: gs, v :: vs, ihs, H with inspect (ind_lookup Θ Ξ p) := {
    | exist _ (Some D) Ed =>
        let (rs, Hrs) := eval_ih_impl Θ Ξ ρ p ups Bks t v _ in
        let (r, Hr) := wrap_ihs_impl ρ p ups Bks Dc gs' gs vs
                         (snd (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs)) _ in
        exist _ (fst (leaf_wrap_f (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs) ++ r) _
    | exist _ None Ed => False_rect _ _ }
  | ρ, p, ups, Bks, Dc, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, ihs, H =>
      let (rs, Hrs) := eval_ih_impl Θ Ξ ρ p ups Bks t v _ in
      let (r, Hr) := wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs _ in
      exist _ (rs ++ r) _
  | ρ, p, ups, Bks, Dc, ca_arg _ :: gs', ca_arg _ :: gs, _ :: vs, ihs, H =>
      let (r, Hr) := wrap_ihs_impl ρ p ups Bks Dc gs' gs vs ihs _ in
      exist _ r _
  | ρ, p, ups, Bks, Dc, _, _, _, _, H => False_rect _ _.
  Solve All Obligations with fr_obl.
End FreshImpl.

(** ** The Orders of Readback *)

Inductive read_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| read_nf_order_type :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
| read_nf_order_stype :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌@n a )
| read_nf_order_lvl :
  `( read_level_atoms_order Θ Ξ s xs ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
| read_nf_order_lvl_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
| read_nf_order_true :
  `( read_nf_order Θ Ξ s ⇓ ⊤ᵈ m )
| read_nf_order_False_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ ⊥ᵈ (⇑ a m) )
| read_nf_order_fn :
  `( read_typ_order Θ Ξ s a ->
     eval_app_order Θ Ξ m ⇑! a s ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall m' b,
         $| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_nf_order Θ Ξ (S s) ⇓ b m') ->
     read_nf_order Θ Ξ s ⇓ (Πᵈ a p B) m )
| read_nf_order_neut :
  `( read_ne_order Θ Ξ s m ->
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
     read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (im_np D Mk) vs) ->
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
     read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs
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
     (forall ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> read_cargs_order Θ Ξ s p as' (env_args nil as') gs ws) ->
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
     read_fields_order Θ Ξ s (env_args nil ns) (record_fields R) v ->
     read_nf_order Θ Ξ s ⇓ (d_record p ns) v )

with read_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
| read_ne_order_var :
  `( read_ne_order Θ Ξ s #ᵈ x )
| read_ne_order_app :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s n ->
     read_ne_order Θ Ξ s (m $ᵈ n) )
| read_ne_order_exfalso :
  `( eval_exp_order Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ⊥ᵈ s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s efqᵈ m under p return B )
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
     blocks_nm_at D None Bks ->
     rview_leaf_arity D ->
     eval_mref_order Θ Ξ p ups j ->
     (forall pre, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (pc, k, pre) -> read_ps_order Θ Ξ s nil (List.rev (ind_uparams Dq)) pre) ->
     read_blocks_order Θ Ξ s ρ p ups Bks Dq (im_sel Mj) 0 (ind_bmembers Dq) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s (d_elim ρ Bks p ups j as' m) )
(** The field of a neutral *)
| read_ne_order_proj :
  `( read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s (d_proj f m) )

with read_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| read_typ_order_univ :
  `( read_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| read_typ_order_suniv :
  `( read_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     read_typ_order Θ Ξ s 𝕌@l )
| read_typ_order_level :
  `( read_typ_order Θ Ξ s (Levelᵈ@n) )
| read_typ_order_True :
  `( read_typ_order Θ Ξ s ⊤ᵈ )
| read_typ_order_False :
  `( read_typ_order Θ Ξ s ⊥ᵈ )
| read_typ_order_pi :
  `( read_typ_order Θ Ξ s a ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_typ_order Θ Ξ s Πᵈ a p B)
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
| read_level_atoms_order_nil :
  `( read_level_atoms_order Θ Ξ s nil )
| read_level_atoms_order_cons :
  `( read_ne_order Θ Ξ s m ->
     read_level_atoms_order Θ Ξ s xs ->
     read_level_atoms_order Θ Ξ s ((k, n, m) :: xs) )

with read_ps_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> Prop :=
| read_ps_order_nil :
  `( read_ps_order Θ Ξ s ρ nil nil )
| read_ps_order_cons :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_ps_order Θ Ξ s (ρ ↦ v) T vs ->
     read_ps_order Θ Ξ s ρ (ce_ass A :: T) (v :: vs) )

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
     (forall r, eval_proj Θ Ξ f v r -> read_fields_order Θ Ξ s (ρ ↦ r) fl v) ->
     read_fields_order Θ Ξ s ρ ((f, T) :: fl) v )

with read_cargs_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> Prop :=
| read_cargs_order_nil :
  `( read_cargs_order Θ Ξ s p ups ρ nil nil )
| read_cargs_order_arg :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_cargs_order Θ Ξ s p ups (ρ ↦ v) gs vs ->
     read_cargs_order Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) )
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
        read_shape_order Θ Ξ (S s) p ups (ρ ↦ ⇑! b s) t r) ->
     read_shape_order Θ Ξ s p ups ρ (pt_pi B t) v )

(** The blocks of a stuck eliminator *)
with read_blocks_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                                 option (list nat) -> nat -> list imember -> Prop :=
(** No member left *)
| read_blocks_order_nil :
  `( read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i nil )
(** The block of the member [Mi]: its motive, its branches, then the rest *)
| read_blocks_order_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     Nat.eqb (eb_nm b) (S (im_nn Mi)) = true ->
     eval_mref_order Θ Ξ p ups (elim_src sel i) ->
     fresh_tele_order Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s ->
     (forall pk k pre ns, ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
        eval_exp_order Θ Ξ (eb_motive b) (env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil))) ->
     (forall pk k pre ns a, ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
        ⟦ eb_motive b ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil) ↘ a ->
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
     cargs_nin D Dc gs' gs = cargs_nrec Dc gs' ->
     cargs_plen D gs ->
     fresh_tele_order Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s ->
     (forall ns,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         fresh_cargs_order Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + im_nn Mi)) ->
     (forall ns vs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         fresh_ihs_order Θ Ξ ρ (blocks_motives Bks) p ups Dc (env_args nil (ups ++ ns)) gs' gs vs (s + im_nn Mi + List.length gs')) ->
     (forall ns vs ihs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         wrap_ihs_order Θ Ξ ρ p ups Bks Dc gs' gs vs ihs) ->
     (forall ns vs ihs wihs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         eval_exp_order Θ Ξ B (env_args ρ (ns ++ vs ++ wihs))) ->
     (forall ns vs,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         eval_exp_order Θ Ξ A (env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil))) ->
     (forall ns vs ihs wihs b t,
         Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ wihs) ↘ b ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil) ↘ t ->
         read_nf_order Θ Ξ (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) ⇓ t b) ->
     read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi (pk, k, pre) cs Bs ->
     read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi (pk, k, pre) ((c, gs') :: cs) ((c, n0, B) :: Bs) ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order read_level_atoms_order
  read_ps_order read_fields_order read_cargs_order read_shape_order read_blocks_order read_brs_order : mctt.

(** Every readback derivation is within its order. *)
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
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> read_fields_order Θ Ξ s ρ fl v).
Proof.
  intros Θ Ξ; apply read_mut_ind; intros;
    (** A constructor at a view: its arguments are the last values, as
        many as the constructor takes. *)
    try match goal with Hh : im_head _ = mh_view _ _ _ _, Hl : List.length ?vs = (?n + List.length ?gs)%nat
                        |- read_nf_order _ _ _ (⇓ _ (d_con _ _ _ ?vs)) =>
          replace n with (List.length vs - List.length gs) in * by lia end;
    first [ solve [ eapply read_nf_order_ind_neut; eassumption ] |
    (econstructor; try eassumption; try lia; try (apply Nat.eqb_eq; first [ assumption | subst; reflexivity ]);
     intros; functional_eval_rewrite_clear; functional_fresh_rewrite_clear;
     functional_eval_rewrite_clear; subst; mauto) ].
Qed.

Lemma read_nf_order_sound : forall Θ Ξ s d m, Rnf d in Θ ⍮ Ξ ⍮ s ↘ m -> read_nf_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (read_order_sound Θ Ξ)). Qed.

Lemma read_ne_order_sound : forall Θ Ξ s d m, Rne d in Θ ⍮ Ξ ⍮ s ↘ m -> read_ne_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (proj2 (read_order_sound Θ Ξ))). Qed.

Lemma read_typ_order_sound : forall Θ Ξ s d m, Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m -> read_typ_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (read_order_sound Θ Ξ)))). Qed.

Lemma read_level_atoms_order_sound : forall Θ Ξ s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> read_level_atoms_order Θ Ξ s xs.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (read_order_sound Θ Ξ))))). Qed.

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

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound read_level_atoms_order_sound
  read_ps_order_sound read_cargs_order_sound read_shape_order_sound read_blocks_order_sound
  read_brs_order_sound read_fields_order_sound : mctt.

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
      ⍮ env_args nil as' ⍮ s ↘ Args ->
    Rnf ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args).
Proof. intros; eapply read_nf_con_view; try eassumption; lia. Qed.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ _ _ |- _ => progressive_invert H
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
  end.

Section ReadbackImpl.
Variables (Θ : gdeps) (Ξ : gstack).

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations read_nf_impl s d (H : read_nf_order Θ Ξ s d) : { m | Rnf d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, ⇓ 𝕌ω@i a      , H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, ⇓ 𝕌@n a     , H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, ⇓ (Levelᵈ@n) (lvᵈ c xs), H =>
    let (ys, Hys) := read_level_atoms_impl s xs _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, ⇓ (Levelᵈ@n) (⇑ a m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ (lvⁿ ordinal_zero (cons (mk_level_atom 0 (domain_level_sort a) M) nil)) _
| s, ⇓ ⊤ᵈ m, H => exist _ ⋆ⁿ _
| s, ⇓ ⊥ᵈ (⇑ _ m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (Πᵈ a p B) m, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (m', Hm') := eval_app_impl Θ Ξ m ⇑! a s _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (M, HM) := read_nf_impl (S s) ⇓ b m' _ in
    exist _ (λⁿ A M) _
| s, ⇓ (⇑ a b) (⇑ c m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (d_ind p j as') v, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_head Mj) := {
      (** At a record view, any value: the view's constructor, its
          arguments the value's projections *)
      | exist _ (mh_record qr Is fl) Eh with inspect (im_cons Mj) := {
        | exist _ ((c, gs) :: nil) Ec =>
            let (ws, Hws) := eval_projs_impl Θ Ξ fl v _ in
            let (Ps, HPs) := read_ps_impl s nil (List.rev (ind_uparams D)) as' _ in
            let (Args, HArgs) := read_cargs_impl s p as' (env_args nil as') gs ws _ in
            exist _ (nf_con p j c (Ps ++ Args)%list) _
        | exist _ _ Ec => False_rect _ _ }
      | exist _ (mh_decl pm) Eh with v := {
        | d_con _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := read_ps_impl s nil (List.rev (im_params D Mj)) as' _ in
              let (Args, HArgs) := read_cargs_impl s p (List.firstn (ind_nu D) as') (env_args nil as') gs
                                     (List.skipn (im_np D Mj) vs) _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | ⇑ a m =>
            let (M, HM) := read_ne_impl s m _ in
            exist _ ⇑ⁿ M _
        | _ => False_rect _ _ }
      | exist _ (mh_view qv kv Iv vmv) Eh with v := {
        | d_con _ _ c vs with inspect (ind_con Mj c) := {
          | exist _ (Some gs) Ec =>
              let (Ps, HPs) := read_ps_impl s nil (List.rev (im_params D Mj)) as' _ in
              let (Args, HArgs) := read_cargs_impl s p (List.firstn (ind_nu D) as') (env_args nil as') gs
                                     (List.skipn (List.length vs - List.length gs) vs) _ in
              exist _ (nf_con p j c (Ps ++ Args)%list) _
          | exist _ None Ec => False_rect _ _ }
        | ⇑ a m =>
            let (M, HM) := read_ne_impl s m _ in
            exist _ ⇑ⁿ M _
        | _ => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, ⇓ (d_record p ns) v, H with inspect (record_lookup Θ Ξ p) := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := read_ps_impl s nil (List.rev (record_params R)) ns _ in
      let (Fs, HFs) := read_fields_impl s (env_args nil ns) (record_fields R) v _ in
      exist _ (nf_tuple p Ps (List.map fst (record_fields R)) Fs) _
  | exist _ None El => False_rect _ _ }

  with read_ne_impl s d (H : read_ne_order Θ Ξ s d) : { m | Rne d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, H => exist _ #ⁿ (s - x - 1) _
| s, d_glob p, H => exist _ (ne_glob p) _
| s, m $ᵈ n, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (N, HN) := read_nf_impl s n _ in
    exist _ (M $ⁿ N) _
| s, efqᵈ m under p return B, H =>
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ (efqⁿ M return B') _
| s, d_elim ρ Bks p ups j as' m, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_ref p j Mj) := {
      | exist _ (pc, k) Er with inspect (ind_lookup Θ Ξ pc) := {
        | exist _ (Some Dq) Edq with eval_mref_impl Θ Ξ p ups j _ := {
          | exist _ (_, _, pre) Hm =>
              let (Us, HUs) := read_ps_impl s nil (List.rev (ind_uparams Dq)) pre _ in
              let (NBks, HNBks) := read_blocks_impl s ρ p ups Bks Dq (im_sel Mj) 0 (ind_bmembers Dq) _ in
              let (M, HM) := read_ne_impl s m _ in
              exist _ (ne_elim pc Us k NBks M) _ }
        | exist _ None Edq => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_proj f m, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ (ne_proj f M) _

  with read_typ_impl s d (H : read_typ_order Θ Ξ s d) : { m | Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, H =>
    let (W, HW) := read_nf_impl s ⇓ Levelᵈ l _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, Levelᵈ@n, H => exist _ (Levelⁿ@n) _
| s, ⊤ᵈ, H => exist _ ⊤ⁿ _
| s, ⊥ᵈ, H => exist _ ⊥ⁿ _
| s, Πᵈ a p B, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ (Πⁿ A B') _
| s, ⇑ a b, H =>
    let (B, HB) := read_ne_impl s b _ in
    exist _ ⇑ⁿ B _
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

  with read_level_atoms_impl s xs (H : read_level_atoms_order Θ Ξ s xs) : { ys | Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, H => exist _ nil _
| s, cons (k, n, m) xs, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (ys, Hys) := read_level_atoms_impl s xs _ in
    exist _ (cons (mk_level_atom k n M) ys) _

  with read_ps_impl s ρ T vs (H : read_ps_order Θ Ξ s ρ T vs) : { Ms | Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, H => exist _ nil _
| s, ρ, ce_ass A :: T, v :: vs, H =>
    let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := read_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := read_ps_impl s (ρ ↦ v) T vs _ in
    exist _ (cons V Vs) _
| s, ρ, _, _, H => False_rect _ _

  with read_fields_impl s ρ fl v (H : read_fields_order Θ Ξ s ρ fl v) :
    { Fs | Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs } by struct H :=
| s, ρ, nil, v, H => exist _ nil _
| s, ρ, (f, T) :: fl, v, H =>
    let (r, Hr) := eval_proj_impl Θ Ξ f v _ in
    let (t, Ht) := eval_exp_impl Θ Ξ T ρ _ in
    let (V, HV) := read_nf_impl s ⇓ t r _ in
    let (Vs, HVs) := read_fields_impl s (ρ ↦ r) fl v _ in
    exist _ (cons V Vs) _

  with read_cargs_impl s p ups ρ gs vs (H : read_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, p, ups, ρ, nil, nil, H => exist _ nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, H =>
    let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := read_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := read_cargs_impl s p ups (ρ ↦ v) gs vs _ in
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
    let (V, HV) := read_shape_impl (S s) p ups (ρ ↦ ⇑! b s) t r _ in
    exist _ (λⁿ A V) _

  with read_blocks_impl s ρ p ups Bks Dc sel i Ms (H : read_blocks_order Θ Ξ s ρ p ups Bks Dc sel i Ms) :
    { NBks | Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks } by struct H :=
| s, ρ, p, ups, Bks, Dc, sel, i, nil, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, sel, i, Mi :: Ms, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_member D (elim_src sel i)) := {
    | exist _ (Some Mv) Em with inspect (List.nth_error Bks (elim_src sel i)) := {
      | exist _ (Some b) Eb with eval_mref_impl Θ Ξ p ups (elim_src sel i) _ := {
        | exist _ (pk, k, pre) Hm =>
            let (ns, Hns) := fresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s _ in
            let (a, Ha) := eval_exp_impl Θ Ξ (eb_motive b)
                             (env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil)) _ in
            let (A', HA') := read_typ_impl (S (s + im_nn Mi)) a _ in
            let (Bs', HBs') := read_brs_impl s ρ p ups Bks Dc Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b) _ in
            let (NBks, HNBks) := read_blocks_impl s ρ p ups Bks Dc sel (S i) Ms _ in
            exist _ (cons (mk_normal_block (S (im_nn Mi)) A' Bs') NBks) _ }
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }

  with read_brs_impl s ρ p ups Bks Dc Mv A Mi r cs Bs (H : read_brs_order Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs) :
    { Bs' | Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' } by struct H :=
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, nil, nil, H => exist _ nil _
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, (pk, k, pre), (c, gs') :: cs, (_, _, B) :: Bs, H with inspect (ind_con Mv c) := {
  | exist _ (Some gs) Ec =>
      let (ns, Hns) := fresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s _ in
      let (vs, Hvs) := fresh_cargs_impl Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + im_nn Mi) _ in
      let (ihs, Hihs) := fresh_ihs_impl Θ Ξ ρ (blocks_motives Bks) p ups Dc (env_args nil (ups ++ ns)) gs' gs vs
                           (s + im_nn Mi + List.length gs') _ in
      let (wihs, Hw) := wrap_ihs_impl Θ Ξ ρ p ups Bks Dc gs' gs vs ihs _ in
      let (b, Hb) := eval_exp_impl Θ Ξ B (env_args ρ (ns ++ vs ++ wihs)) _ in
      let (t, Ht) := eval_exp_impl Θ Ξ A (env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil)) _ in
      let (B', HB') := read_nf_impl (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) ⇓ t b _ in
      let (Bs', HBs') := read_brs_impl s ρ p ups Bks Dc Mv A Mi (pk, k, pre) cs Bs _ in
      exist _ (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dc gs') B') Bs') _
  | exist _ None Ec => False_rect _ _ }
| s, ρ, p, ups, Bks, Dc, Mv, A, Mi, r, _, _, H => False_rect _ _.

(** Each hole is either a readback order of a subterm, read off the order of
    the whole by inversion, or the readback itself, by its rule.  The
    lookups the order records are the ones computed. *)
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
    | Hm : eval_mref _ _ ?p _ ?j (?a, ?b, _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
      Hr : im_ref ?p ?j _ = (?c, ?d) |- _ =>
        assert_fails (constr_eq a c);
        let E := fresh "Er" in
        pose proof (eval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) as E;
        rewrite E in Hr; injection Hr; clear Hr; intros; subst
    end.

#[local]
Ltac readback_order :=
  repeat impl_obl_tac1; readback_glob;
  first [ eassumption
        | solve [ eauto 2 ] ].

#[local]
Ltac readback_eqb := repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end.

#[local]
Ltac readback_run := repeat impl_obl_tac1; readback_glob; readback_eqb; econstructor; eassumption.

#[local]
Ltac readback_ind :=
  repeat impl_obl_tac1; readback_glob; readback_eqb;
  first [ congruence
        | solve [ eapply read_nf_con_view_last; eassumption ]
        (** A neutral of a member with a block: its head is not a record
            view's *)
        | solve [ eapply read_nf_ind_neut; try eassumption;
                  unfold im_is_rview; match goal with H : im_head _ = _ |- _ => rewrite H; reflexivity end ]
        | econstructor; try eassumption; eauto 3 ].

#[local]
Ltac readback_obligation_auto :=
  intros; cbv beta in *;
  lazymatch goal with
  | |- read_nf_order _ _ _ _ => first [ readback_order | readback_run ]
  | |- read_ne_order _ _ _ _ => first [ readback_order | readback_run ]
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
  | |- _ => abstract (first [ readback_order | readback_run | eapply read_typ_suniv_of_nf; eassumption | readback_ind ])
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
