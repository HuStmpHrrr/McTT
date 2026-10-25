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
    back as [nf_lvl_of] of a canonical level ([fread_nf_level_lvl_of_nf]), so
    the default is never reached. *)
Definition lvl_of_nf (W : nf) : lvl :=
  match W with nf_lvl c xs => (c, xs) | _ => (oz, nil) end.

Lemma fread_nf_level_lvl_of_nf : forall Θ Ξ s l W,
    Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    W = nf_lvl_of (lvl_of_nf W).
Proof. inversion 1; subst; reflexivity. Qed.

Lemma fread_typ_suniv_of_nf : forall Θ Ξ s l W,
    Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    Rtypᶠ 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of (lvl_of_nf W).
Proof.
  intros * H; apply fread_typ_suniv.
  rewrite <- (fread_nf_level_lvl_of_nf _ _ _ _ _ H); exact H.
Qed.

(** ** The Fresh Variables of the Telescopes of a Group

    Their orders, and the functions that compute them. *)

(** The variables of a telescope *)
Inductive ffresh_tele_order (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> Prop :=
(** No entry *)
| ffresh_tele_order_nil :
  `( ffresh_tele_order Θ Ξ ρ nil s )
(** The first entry's type, then the rest under its variable *)
| ffresh_tele_order_cons :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> ffresh_tele_order Θ Ξ (ρ ↦ ⇑! a s) T (S s)) ->
     ffresh_tele_order Θ Ξ ρ (ce_ass A :: T) s ).

(** The variables of the arguments of a constructor *)
Inductive ffresh_cargs_order (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> Prop :=
(** No argument *)
| ffresh_cargs_order_nil :
  `( ffresh_cargs_order Θ Ξ p ups ρ nil s )
(** A non-recursive argument's type, then the rest *)
| ffresh_cargs_order_arg :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> ffresh_cargs_order Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s)) ->
     ffresh_cargs_order Θ Ξ p ups ρ (ca_arg A :: gs) s )
(** A recursive argument's type, then the rest *)
| ffresh_cargs_order_rec_case :
  `( feval_shty_order Θ Ξ p ups ρ t ->
     ffresh_cargs_order Θ Ξ p ups ρ gs (S s) ->
     ffresh_cargs_order Θ Ξ p ups ρ (ca_rec t :: gs) s ).

(** The variables of the recursive results of a branch [B] *)
Inductive ffresh_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (As : list exp) (B : exp) :
  env -> list carg -> list carg -> list domain -> nat -> Prop :=
(** No argument *)
| ffresh_ihs_order_nil :
  `( ffresh_ihs_order Θ Ξ ρ As B ρa nil nil nil s )
(** A non-recursive argument, entering the environment *)
| ffresh_ihs_order_arg :
  `( ffresh_ihs_order Θ Ξ ρ As B (ρa ↦ v) gs' gs vs s ->
     ffresh_ihs_order Θ Ξ ρ As B ρa (ca_arg T' :: gs') (ca_arg T :: gs) (v :: vs) s )
(** Recursive in both: its type when the branch reads it, then the rest *)
| ffresh_ihs_order_rec_case :
  `( (exp_freshb (cargs_nrec gs) B = false -> feval_ihty_order Θ Ξ ρ As ρa t v) ->
     ffresh_ihs_order Θ Ξ ρ As B ρa gs' gs vs (S s) ->
     ffresh_ihs_order Θ Ξ ρ As B ρa (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) s )
(** Nested through: the rest *)
| ffresh_ihs_order_nest :
  `( ffresh_ihs_order Θ Ξ ρ As B ρa gs' gs vs s ->
     ffresh_ihs_order Θ Ξ ρ As B ρa (ca_arg T' :: gs') (ca_rec t :: gs) (v :: vs) s ).

(** The recursive results a branch is read under, wrapped *)
Inductive fwrap_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (p : qname) (ups : list domain) (Bks : list eblock) :
  list carg -> list carg -> list domain -> list domain -> Prop :=
(** No argument *)
| fwrap_ihs_order_nil :
  `( fwrap_ihs_order Θ Ξ ρ p ups Bks nil nil nil nil )
(** Recursive in both: the rest *)
| fwrap_ihs_order_rec_case :
  `( fwrap_ihs_order Θ Ξ ρ p ups Bks gs' gs vs ihs ->
     fwrap_ihs_order Θ Ξ ρ p ups Bks (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) (ih :: ihs) )
(** Nested through: the eliminator at the argument, then the rest *)
| fwrap_ihs_order_nest :
  `( feval_ih_order Θ Ξ ρ p ups Bks t v ->
     fwrap_ihs_order Θ Ξ ρ p ups Bks gs' gs vs ihs ->
     fwrap_ihs_order Θ Ξ ρ p ups Bks (ca_arg T' :: gs') (ca_rec t :: gs) (v :: vs) ihs )
(** Non-recursive: the rest *)
| fwrap_ihs_order_arg :
  `( fwrap_ihs_order Θ Ξ ρ p ups Bks gs' gs vs ihs ->
     fwrap_ihs_order Θ Ξ ρ p ups Bks (ca_arg T' :: gs') (ca_arg T :: gs) (v :: vs) ihs ).

#[local]
Hint Constructors ffresh_tele_order ffresh_cargs_order ffresh_ihs_order fwrap_ihs_order : mctt.

Lemma ffresh_tele_order_sound : forall Θ Ξ ρ T s vs, Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> ffresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

Lemma ffresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs,
    Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> ffresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

Lemma ffresh_ihs_order_sound : forall Θ Ξ ρ As B ρa gs' gs vs s ihs,
    Fihsᶠ vs at gs' gs under ρ As for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> ffresh_ihs_order Θ Ξ ρ As B ρa gs' gs vs s.
Proof. induction 1; econstructor; intros; try congruence; functional_feval_rewrite_clear; mauto. Qed.

Lemma fwrap_ihs_order_sound : forall Θ Ξ ρ p ups Bks gs' gs vs ihs r,
    ⟦wihsᶠ vs of gs' gs with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r -> fwrap_ihs_order Θ Ξ ρ p ups Bks gs' gs vs ihs.
Proof.
  induction 1; econstructor; try eassumption; mauto.
Qed.

#[export]
Hint Resolve ffresh_tele_order_sound ffresh_cargs_order_sound ffresh_ihs_order_sound fwrap_ihs_order_sound : mctt.

Section FreshImpl.
  Variables (Θ : gdeps) (Ξ : gstack).
  Context {F : FCtx Θ Ξ}.

  #[local]
  Ltac fr_obl :=
    intros; cbv beta in *;
    repeat match goal with
      | H : ffresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : ffresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : ffresh_ihs_order _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : fwrap_ihs_order _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    first [ eassumption | solve [ eauto 2 ] | econstructor; eassumption
          | match goal with H : _ = false -> _ |- _ => apply H; assumption end ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_tele_impl ρ T s (H : ffresh_tele_order Θ Ξ ρ T s) : { vs | Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | ρ, nil, s, H => exist _ nil _
  | ρ, ce_ass A :: T, s, H =>
      let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := ffresh_tele_impl (ρ ↦ ⇑! a s) T (S s) _ in
      exist _ (⇑! a s :: vs) _
  | ρ, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_cargs_impl p ups ρ gs s (H : ffresh_cargs_order Θ Ξ p ups ρ gs s) :
    { vs | Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ nil _
  | p, ups, ρ, ca_arg A :: gs, s, H =>
      let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := ffresh_cargs_impl p ups (ρ ↦ ⇑! a s) gs (S s) _ in
      exist _ (⇑! a s :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, H =>
      let (a, Ha) := feval_shty_impl Θ Ξ p ups ρ t _ in
      let (vs, Hvs) := ffresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! a s :: vs) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_ihs_impl ρ As B ρa gs' gs vs s (H : ffresh_ihs_order Θ Ξ ρ As B ρa gs' gs vs s) :
    { ihs | Fihsᶠ vs at gs' gs under ρ As for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs } by struct H :=
  | ρ, As, B, ρa, nil, nil, nil, s, H => exist _ nil _
  | ρ, As, B, ρa, ca_arg _ :: gs', ca_arg _ :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := ffresh_ihs_impl ρ As B (ρa ↦ v) gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, B, ρa, ca_rec _ :: gs', ca_rec t :: gs, v :: vs, s, H with inspect (exp_freshb (cargs_nrec gs) B) := {
    | exist _ true E =>
        let (ihs, Hihs) := ffresh_ihs_impl ρ As B ρa gs' gs vs (S s) _ in
        exist _ (⇑! 𝕌ω@0 s :: ihs) _
    | exist _ false E =>
        let (a, Ha) := feval_ihty_impl Θ Ξ ρ As ρa t v _ in
        let (ihs, Hihs) := ffresh_ihs_impl ρ As B ρa gs' gs vs (S s) _ in
        exist _ (⇑! a s :: ihs) _ }
  | ρ, As, B, ρa, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := ffresh_ihs_impl ρ As B ρa gs' gs vs s _ in
      exist _ ihs _
  | ρ, As, B, ρa, _, _, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fwrap_ihs_impl ρ p ups Bks gs' gs vs ihs (H : fwrap_ihs_order Θ Ξ ρ p ups Bks gs' gs vs ihs) :
    { r | ⟦wihsᶠ vs of gs' gs with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r } by struct H :=
  | ρ, p, ups, Bks, nil, nil, nil, nil, H => exist _ nil _
  | ρ, p, ups, Bks, ca_rec _ :: gs', ca_rec _ :: gs, _ :: vs, ih :: ihs, H =>
      let (r, Hr) := fwrap_ihs_impl ρ p ups Bks gs' gs vs ihs _ in
      exist _ (ih :: r) _
  | ρ, p, ups, Bks, ca_arg _ :: gs', ca_rec t :: gs, v :: vs, ihs, H =>
      let (ih, Hih) := feval_ih_impl Θ Ξ ρ p ups Bks t v (@fc_seed Θ Ξ F) _ in
      let (r, Hr) := fwrap_ihs_impl ρ p ups Bks gs' gs vs ihs _ in
      exist _ (ih :: r) _
  | ρ, p, ups, Bks, ca_arg _ :: gs', ca_arg _ :: gs, _ :: vs, ihs, H =>
      let (r, Hr) := fwrap_ihs_impl ρ p ups Bks gs' gs vs ihs _ in
      exist _ r _
  | ρ, p, ups, Bks, _, _, _, _, H => False_rect _ _.
  Solve All Obligations with fr_obl.
End FreshImpl.

(** ** The Orders of Readback *)

Inductive fread_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| fread_nf_order_type :
  `( fread_typ_order Θ Ξ s a ->
    fread_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
| fread_nf_order_stype :
  `( fread_typ_order Θ Ξ s a ->
    fread_nf_order Θ Ξ s ⇓ 𝕌@n a )
| fread_nf_order_lvl :
  `( fread_la_order Θ Ξ s xs ->
     fread_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
| fread_nf_order_lvl_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
| fread_nf_order_true :
  `( fread_nf_order Θ Ξ s ⇓ ⊤ᵈ m )
| fread_nf_order_False_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ ⊥ᵈ (⇑ a m) )
| fread_nf_order_fn :
  `( fread_typ_order Θ Ξ s a ->
     feval_app_order Θ Ξ m ⇑! a s ->
     feval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall m' b,
         $ᶠ| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         fread_nf_order Θ Ξ (S s) ⇓ b m') ->
     fread_nf_order Θ Ξ s ⇓ (Πᵈ a p B) m )
| fread_nf_order_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ (⇑ a b) (⇑ c m) )
(** A constructor of a declared member *)
| fread_nf_order_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length as' = im_np D Mk ->
     List.length vs = (im_np D Mk + List.length gs)%nat ->
     fread_ps_order Θ Ξ s nil (List.rev (im_params D Mk)) as' ->
     fread_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (im_np D Mk) vs) ->
     fread_nf_order Θ Ξ s ⇓ (d_ind p k as') (d_con p k c vs) )
(** A constructor at a view: its arguments are the last values *)
| fread_nf_order_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_con Mj c = Some gs ->
     List.length as' = im_np D Mj ->
     List.length gs <= List.length vs ->
     fread_ps_order Θ Ξ s nil (List.rev (im_params D Mj)) as' ->
     fread_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs
       (List.skipn (List.length vs - List.length gs) vs) ->
     fread_nf_order Θ Ξ s ⇓ (d_ind p j as') (d_con qc k c vs) )
| fread_nf_order_ind_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ (d_ind p k as') (⇑ a m) )
(** A value of a record type: the type's parameters, then the fields *)
| fread_nf_order_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     fread_ps_order Θ Ξ s nil (List.rev (record_params R)) ns ->
     fread_fields_order Θ Ξ s (env_args nil ns) (record_fields R) v ->
     fread_nf_order Θ Ξ s ⇓ (d_record p ns) v )

with fread_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
| fread_ne_order_var :
  `( fread_ne_order Θ Ξ s #ᵈ x )
| fread_ne_order_app :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s n ->
     fread_ne_order Θ Ξ s (m $ᵈ n) )
| fread_ne_order_exfalso :
  `( feval_exp_order Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ⊥ᵈ s ↘ b ->
         fread_typ_order Θ Ξ (S s) b) ->
     fread_ne_order Θ Ξ s m ->
     fread_ne_order Θ Ξ s efqᵈ m under p return B )
| fread_ne_order_glob :
  `( fread_ne_order Θ Ξ s (d_glob p) )
(** A stuck eliminator: the container's uniform parameters, the blocks
    read as the container's group's, and the scrutinee *)
| fread_ne_order_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     blocks_nm_at D None Bks ->
     feval_mref_order Θ Ξ p ups j ->
     (forall pre, ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) -> fread_ps_order Θ Ξ s nil (List.rev (ind_uparams Dq)) pre) ->
     fread_blocks_order Θ Ξ s ρ p ups Bks (im_sel Mj) 0 (ind_members Dq) ->
     fread_ne_order Θ Ξ s m ->
     fread_ne_order Θ Ξ s (d_elim ρ Bks p ups j as' m) )
(** The field of a neutral *)
| fread_ne_order_proj :
  `( fread_ne_order Θ Ξ s m ->
     fread_ne_order Θ Ξ s (d_proj f m) )

with fread_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| fread_typ_order_univ :
  `( fread_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| fread_typ_order_suniv :
  `( fread_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     fread_typ_order Θ Ξ s 𝕌@l )
| fread_typ_order_level :
  `( fread_typ_order Θ Ξ s (Levelᵈ@n) )
| fread_typ_order_True :
  `( fread_typ_order Θ Ξ s ⊤ᵈ )
| fread_typ_order_False :
  `( fread_typ_order Θ Ξ s ⊥ᵈ )
| fread_typ_order_pi :
  `( fread_typ_order Θ Ξ s a ->
     feval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         fread_typ_order Θ Ξ (S s) b) ->
     fread_typ_order Θ Ξ s Πᵈ a p B)
| fread_typ_order_neut :
  `( fread_ne_order Θ Ξ s b ->
    fread_typ_order Θ Ξ s ⇑ a b )
(** A type former without arguments: no lookup *)
| fread_typ_order_indty_nil :
  `( fread_typ_order Θ Ξ s (d_ind p k nil) )
(** At one argument or more *)
| fread_typ_order_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length (a :: as') = im_np D Mk ->
     fread_ps_order Θ Ξ s nil (List.rev (im_params D Mk)) (a :: as') ->
     fread_typ_order Θ Ξ s (d_ind p k (a :: as')) )
(** A record type at all its parameters *)
| fread_typ_order_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     fread_ps_order Θ Ξ s nil (List.rev (record_params R)) ns ->
     fread_typ_order Θ Ξ s (d_record p ns) )

with fread_la_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
| fread_la_order_nil :
  `( fread_la_order Θ Ξ s nil )
| fread_la_order_cons :
  `( fread_ne_order Θ Ξ s m ->
     fread_la_order Θ Ξ s xs ->
     fread_la_order Θ Ξ s ((k, n, m) :: xs) )

with fread_ps_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> Prop :=
| fread_ps_order_nil :
  `( fread_ps_order Θ Ξ s ρ nil nil )
| fread_ps_order_cons :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fread_nf_order Θ Ξ s ⇓ a v) ->
     fread_ps_order Θ Ξ s (ρ ↦ v) T vs ->
     fread_ps_order Θ Ξ s ρ (ce_ass A :: T) (v :: vs) )

(** The fields of a record value, each its projection at its type *)
with fread_fields_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list (string * exp) -> domain -> Prop :=
(** No field left *)
| fread_fields_order_nil :
  `( fread_fields_order Θ Ξ s ρ nil v )
(** The next field: its projection, its type, its readback, then the rest
    with the projection in the environment *)
| fread_fields_order_cons :
  `( feval_proj_order Θ Ξ f v ->
     feval_exp_order Θ Ξ T ρ ->
     (forall r t, feval_proj Θ Ξ f v r -> ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ t -> fread_nf_order Θ Ξ s ⇓ t r) ->
     (forall r, feval_proj Θ Ξ f v r -> fread_fields_order Θ Ξ s (ρ ↦ r) fl v) ->
     fread_fields_order Θ Ξ s ρ ((f, T) :: fl) v )

with fread_cargs_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> Prop :=
| fread_cargs_order_nil :
  `( fread_cargs_order Θ Ξ s p ups ρ nil nil )
| fread_cargs_order_arg :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fread_nf_order Θ Ξ s ⇓ a v) ->
     fread_cargs_order Θ Ξ s p ups (ρ ↦ v) gs vs ->
     fread_cargs_order Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) )
(** A recursive argument, along its shape *)
| fread_cargs_order_rec_case :
  `( fread_shape_order Θ Ξ s p ups ρ t v ->
     fread_cargs_order Θ Ξ s p ups ρ gs vs ->
     fread_cargs_order Θ Ξ s p ups ρ (ca_rec t :: gs) (v :: vs) )

(** A recursive argument of a shape *)
with fread_shape_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> ptyp -> domain -> Prop :=
(** At the end: the parameters, then the value at the member *)
| fread_shape_order_self :
  `( feval_exps_order Θ Ξ Ps ρ ->
     (forall bs, ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs -> fread_nf_order Θ Ξ s ⇓ (d_ind p j (ups ++ bs)) v) ->
     fread_shape_order Θ Ξ s p ups ρ (pt_self j Ps) v )
(** At a domain: under a fresh variable of it *)
| fread_shape_order_pi :
  `( feval_exp_order Θ Ξ B ρ ->
     (forall b, ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b -> fread_typ_order Θ Ξ s b) ->
     (forall b, ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b -> feval_app_order Θ Ξ v (⇑! b s)) ->
     (forall b r, ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b -> $ᶠ| v & ⇑! b s | Θ ⍮ Ξ ↘ r ->
        fread_shape_order Θ Ξ (S s) p ups (ρ ↦ ⇑! b s) t r) ->
     fread_shape_order Θ Ξ s p ups ρ (pt_pi B t) v )

(** The blocks of a stuck eliminator *)
with fread_blocks_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock ->
                                                  option (list nat) -> nat -> list imember -> Prop :=
(** No member left *)
| fread_blocks_order_nil :
  `( fread_blocks_order Θ Ξ s ρ p ups Bks sel i nil )
(** The block of the member [Mi]: its motive, its branches, then the rest *)
| fread_blocks_order_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     Nat.eqb (eb_nm b) (S (im_nn Mi)) = true ->
     feval_mref_order Θ Ξ p ups (elim_src sel i) ->
     ffresh_tele_order Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s ->
     (forall pk k pre ns, ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
        feval_exp_order Θ Ξ (eb_motive b) (env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil))) ->
     (forall pk k pre ns a, ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
        ⟦ eb_motive b ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil) ↘ a ->
        fread_typ_order Θ Ξ (S (s + im_nn Mi)) a) ->
     (forall pk k pre, ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
        fread_brs_order Θ Ξ s ρ p ups Bks Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b)) ->
     fread_blocks_order Θ Ξ s ρ p ups Bks sel (S i) Ms ->
     fread_blocks_order Θ Ξ s ρ p ups Bks sel i (Mi :: Ms) )

(** The branches of a block *)
with fread_brs_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock ->
                                               imember -> exp -> imember -> (qname * nat * list domain) ->
                                               list (string * list carg) -> list (string * nat * exp) -> Prop :=
(** No constructor left *)
| fread_brs_order_nil :
  `( fread_brs_order Θ Ξ s ρ p ups Bks Mv A Mi r nil nil )
(** The branch of the next constructor, then the rest *)
| fread_brs_order_cons :
  `( ind_con Mv c = Some gs ->
     Nat.eqb n0 (im_nn Mi + List.length gs' + cargs_nrec gs)%nat = true ->
     ind_lookup Θ Ξ p = Some D ->
     cargs_plen D gs ->
     ffresh_tele_order Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s ->
     (forall ns,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         ffresh_cargs_order Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + im_nn Mi)) ->
     (forall ns vs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         ffresh_ihs_order Θ Ξ ρ (blocks_motives Bks) B (env_args nil (ups ++ ns)) gs' gs vs (s + im_nn Mi + List.length gs')) ->
     (forall ns vs ihs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihsᶠ vs at gs' gs under ρ (blocks_motives Bks) for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         fwrap_ihs_order Θ Ξ ρ p ups Bks gs' gs vs ihs) ->
     (forall ns vs ihs wihs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihsᶠ vs at gs' gs under ρ (blocks_motives Bks) for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihsᶠ vs of gs' gs with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         feval_exp_order Θ Ξ B (env_args ρ (ns ++ vs ++ wihs))) ->
     (forall ns vs,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         feval_exp_order Θ Ξ A (env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil))) ->
     (forall ns vs ihs wihs b t,
         Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
         Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
         Fihsᶠ vs at gs' gs under ρ (blocks_motives Bks) for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi + List.length gs') ↘ ihs ->
         ⟦wihsᶠ vs of gs' gs with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ wihs) ↘ b ->
         ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil) ↘ t ->
         fread_nf_order Θ Ξ (s + (im_nn Mi + List.length gs' + cargs_nrec gs')) ⇓ t b) ->
     fread_brs_order Θ Ξ s ρ p ups Bks Mv A Mi (pk, k, pre) cs Bs ->
     fread_brs_order Θ Ξ s ρ p ups Bks Mv A Mi (pk, k, pre) ((c, gs') :: cs) ((c, n0, B) :: Bs) ).

#[local]
Hint Constructors fread_nf_order fread_ne_order fread_typ_order fread_la_order
  fread_ps_order fread_fields_order fread_cargs_order fread_shape_order fread_blocks_order fread_brs_order : mctt.

(** Every readback derivation is within its order: by the mutual induction
    on readback, the evaluations the orders quantify over being the ones
    the derivation makes ([functional_feval]). *)
Lemma fread_order_sound : forall Θ Ξ,
    (forall s d m, Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fread_nf_order Θ Ξ s d) /\
    (forall s d m, Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fread_ne_order Θ Ξ s d) /\
    (forall s d m, Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fread_typ_order Θ Ξ s d) /\
    (forall s xs ys, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys -> fread_la_order Θ Ξ s xs) /\
    (forall s ρ T vs Ms, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fread_ps_order Θ Ξ s ρ T vs) /\
    (forall s p ups ρ gs vs Ms, Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fread_cargs_order Θ Ξ s p ups ρ gs vs) /\
    (forall s p ups ρ t v V, Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> fread_shape_order Θ Ξ s p ups ρ t v) /\
    (forall s ρ p ups Bks sel i Ms NBks, Rblksᶠ i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       fread_blocks_order Θ Ξ s ρ p ups Bks sel i Ms) /\
    (forall s ρ p ups Bks Mv A Mi r cs Bs Bs', Rbrsᶠ Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       fread_brs_order Θ Ξ s ρ p ups Bks Mv A Mi r cs Bs) /\
    (forall s ρ fl v Fs, Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> fread_fields_order Θ Ξ s ρ fl v).
Proof.
  intros Θ Ξ; apply fread_mut_ind; intros;
    (** A constructor at a view: its arguments are the last values, as
        many as the constructor takes. *)
    try match goal with Hh : im_head _ = mh_view _ _ _ _, Hl : List.length ?vs = (?n + List.length ?gs)%nat
                        |- fread_nf_order _ _ _ (⇓ _ (d_con _ _ _ ?vs)) =>
          replace n with (List.length vs - List.length gs) in * by lia end;
    (econstructor; try eassumption; try lia; try (apply Nat.eqb_eq; first [ assumption | subst; reflexivity ]);
     intros; functional_feval_rewrite_clear; functional_ffresh_rewrite_clear;
     functional_feval_rewrite_clear; subst; mauto).
Qed.

Lemma fread_nf_order_sound : forall Θ Ξ s d m, Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fread_nf_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (fread_order_sound Θ Ξ)). Qed.

Lemma fread_ne_order_sound : forall Θ Ξ s d m, Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fread_ne_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (proj2 (fread_order_sound Θ Ξ))). Qed.

Lemma fread_typ_order_sound : forall Θ Ξ s d m, Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m -> fread_typ_order Θ Ξ s d.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (fread_order_sound Θ Ξ)))). Qed.

Lemma fread_la_order_sound : forall Θ Ξ s xs ys, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys -> fread_la_order Θ Ξ s xs.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (fread_order_sound Θ Ξ))))). Qed.

Lemma fread_ps_order_sound : forall Θ Ξ s ρ T vs Ms, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fread_ps_order Θ Ξ s ρ T vs.
Proof. intros Θ Ξ; pose proof (fread_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fread_cargs_order_sound : forall Θ Ξ s p ups ρ gs vs Ms,
    Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> fread_cargs_order Θ Ξ s p ups ρ gs vs.
Proof. intros Θ Ξ; pose proof (fread_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fread_shape_order_sound : forall Θ Ξ s p ups ρ t v V,
    Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> fread_shape_order Θ Ξ s p ups ρ t v.
Proof. intros Θ Ξ; pose proof (fread_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fread_blocks_order_sound : forall Θ Ξ s ρ p ups Bks sel i Ms NBks,
    Rblksᶠ i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks -> fread_blocks_order Θ Ξ s ρ p ups Bks sel i Ms.
Proof. intros Θ Ξ; pose proof (fread_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fread_brs_order_sound : forall Θ Ξ s ρ p ups Bks Mv A Mi r cs Bs Bs',
    Rbrsᶠ Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' -> fread_brs_order Θ Ξ s ρ p ups Bks Mv A Mi r cs Bs.
Proof. intros Θ Ξ; pose proof (fread_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma fread_fields_order_sound : forall Θ Ξ s ρ fl v Fs,
    Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> fread_fields_order Θ Ξ s ρ fl v.
Proof. intros Θ Ξ; pose proof (fread_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve fread_nf_order_sound fread_ne_order_sound fread_typ_order_sound fread_la_order_sound
  fread_ps_order_sound fread_cargs_order_sound fread_shape_order_sound fread_blocks_order_sound
  fread_brs_order_sound fread_fields_order_sound : mctt.

(** A constructor at a view, its arguments the last values, as many as the
    constructor takes ([fread_nf_con_view]). *)
Lemma fread_nf_con_view_last : forall Θ Ξ s p D j Mj qc k Is vm c gs as' vs Ps Args,
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
Proof. intros; eapply fread_nf_con_view; try eassumption; lia. Qed.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : fread_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_la_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_ps_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_fields_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_cargs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_shape_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_blocks_order _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  (** A constructor, at a declared member or at a view: both cases, the
      lookups then excluding one *)
  | H : fread_nf_order _ _ _ (⇓ (d_ind _ _ _) (d_con _ _ _ _)) |- _ => inversion H; subst; clear H
  end.

Section ReadbackImpl.
Variables (Θ : gdeps) (Ξ : gstack).
Context {F : FCtx Θ Ξ}.

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations fread_nf_impl_c s d (ck : lk_cache Θ Ξ) (H : fread_nf_order Θ Ξ s d) : { m | Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, ⇓ 𝕌ω@i a      , ck, H =>
    let (A, HA) := fread_typ_impl_c s a ck _ in
    exist _ A _
| s, ⇓ 𝕌@n a     , ck, H =>
    let (A, HA) := fread_typ_impl_c s a ck _ in
    exist _ A _
| s, ⇓ (Levelᵈ@n) (lvᵈ c xs), ck, H =>
    let (ys, Hys) := fread_la_impl_c s xs ck _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, ⇓ (Levelᵈ@n) (⇑ a m), ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ (lvⁿ oz (cons (mk_level_atom 0 (dsort a) M) nil)) _
| s, ⇓ ⊤ᵈ m, ck, H => exist _ ⋆ⁿ _
| s, ⇓ ⊥ᵈ (⇑ _ m), ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (Πᵈ a p B) m, ck, H =>
    let (A, HA) := fread_typ_impl_c s a ck _ in
    let (m', Hm') := feval_app_impl Θ Ξ m ⇑! a s _ in
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (M, HM) := fread_nf_impl_c (S s) ⇓ b m' ck _ in
    exist _ (λⁿ A M) _
| s, ⇓ (⇑ a b) (⇑ c m), ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (d_ind p j as') (d_con _ _ c vs), ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (ind_con Mj c) := {
      | exist _ (Some gs) Ec with inspect (im_head Mj) := {
        (** A constructor of a declared member: its arguments after its
            parameters *)
        | exist _ (mh_decl _) Eh =>
            let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ in
            let (Args, HArgs) := fread_cargs_impl_c s p (List.firstn (ind_nu D) as') (env_args nil as') gs
                                   (List.skipn (im_np D Mj) vs) (Some (exist _ (p, D) Ed)) _ in
            exist _ (nf_con p j c (Ps ++ Args)%list) _
        (** At a view: its arguments are the last values *)
        | exist _ (mh_view _ _ _ _) Eh =>
            let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (im_params D Mj)) as' ck _ in
            let (Args, HArgs) := fread_cargs_impl_c s p (List.firstn (ind_nu D) as') (env_args nil as') gs
                                   (List.skipn (List.length vs - List.length gs) vs) (Some (exist _ (p, D) Ed)) _ in
            exist _ (nf_con p j c (Ps ++ Args)%list) _ }
      | exist _ None Ec => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, ⇓ (d_ind p k as') (⇑ a m), ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (d_record p ns) v, ck, H with inspect (record_lookup Θ Ξ p) := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (record_params R)) ns ck _ in
      let (Fs, HFs) := fread_fields_impl_c s (env_args nil ns) (record_fields R) v ck _ in
      exist _ (nf_tuple p Ps (List.map fst (record_fields R)) Fs) _
  | exist _ None El => False_rect _ _ }

  with fread_ne_impl_c s d (ck : lk_cache Θ Ξ) (H : fread_ne_order Θ Ξ s d) : { m | Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, ck, H => exist _ #ⁿ (s - x - 1) _
| s, d_glob p, ck, H => exist _ (ne_glob p) _
| s, m $ᵈ n, ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    let (N, HN) := fread_nf_impl_c s n ck _ in
    exist _ (M $ⁿ N) _
| s, efqᵈ m under p return B, ck, H =>
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) _ in
    let (B', HB') := fread_typ_impl_c (S s) b ck _ in
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ (efqⁿ M return B') _
| s, d_elim ρ Bks p ups j as' m, ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D j) := {
    | exist _ (Some Mj) Em with inspect (im_ref p j Mj) := {
      | exist _ (pc, k) Er with cache_lookup Θ Ξ (Some (exist _ (p, D) Ed)) pc := {
        | exist _ (Some Dq) Edq with feval_mref_impl Θ Ξ p ups j _ := {
          | exist _ (_, _, pre) Hm =>
              let (Us, HUs) := fread_ps_impl_c s nil (List.rev (ind_uparams Dq)) pre ck _ in
              let (NBks, HNBks) := fread_blocks_impl_c s ρ p ups Bks (im_sel Mj) 0 (ind_members Dq) (Some (exist _ (p, D) Ed)) _ in
              let (M, HM) := fread_ne_impl_c s m ck _ in
              exist _ (ne_elim pc Us k NBks M) _ }
        | exist _ None Edq => False_rect _ _ } }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_proj f m, ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ (ne_proj f M) _

  with fread_typ_impl_c s d (ck : lk_cache Θ Ξ) (H : fread_typ_order Θ Ξ s d) : { m | Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, ck, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, ck, H =>
    let (W, HW) := fread_nf_impl_c s ⇓ Levelᵈ l ck _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, Levelᵈ@n, ck, H => exist _ (Levelⁿ@n) _
| s, ⊤ᵈ, ck, H => exist _ ⊤ⁿ _
| s, ⊥ᵈ, ck, H => exist _ ⊥ⁿ _
| s, Πᵈ a p B, ck, H =>
    let (A, HA) := fread_typ_impl_c s a ck _ in
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (B', HB') := fread_typ_impl_c (S s) b ck _ in
    exist _ (Πⁿ A B') _
| s, ⇑ a b, ck, H =>
    let (B, HB) := fread_ne_impl_c s b ck _ in
    exist _ ⇑ⁿ B _
| s, d_ind p k nil, ck, H => exist _ (nf_indty p k nil) _
| s, d_ind p k as', ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D k) := {
    | exist _ (Some Mk) Em =>
        let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (im_params D Mk)) as' ck _ in
        exist _ (nf_indty p k Ps) _
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, d_record p ns, ck, H with inspect (record_lookup Θ Ξ p) := {
  | exist _ (Some R) El =>
      let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (record_params R)) ns ck _ in
      exist _ (nf_record p Ps) _
  | exist _ None El => False_rect _ _ }

  with fread_la_impl_c s xs (ck : lk_cache Θ Ξ) (H : fread_la_order Θ Ξ s xs) : { ys | Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, ck, H => exist _ nil _
| s, cons (k, n, m) xs, ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    let (ys, Hys) := fread_la_impl_c s xs ck _ in
    exist _ (cons (mk_level_atom k n M) ys) _

  with fread_ps_impl_c s ρ T vs (ck : lk_cache Θ Ξ) (H : fread_ps_order Θ Ξ s ρ T vs) : { Ms | Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, ck, H => exist _ nil _
| s, ρ, ce_ass A :: T, v :: vs, ck, H =>
    let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := fread_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fread_ps_impl_c s (ρ ↦ v) T vs ck _ in
    exist _ (cons V Vs) _
| s, ρ, _, _, ck, H => False_rect _ _

  with fread_fields_impl_c s ρ fl v (ck : lk_cache Θ Ξ) (H : fread_fields_order Θ Ξ s ρ fl v) :
    { Fs | Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs } by struct H :=
| s, ρ, nil, v, ck, H => exist _ nil _
| s, ρ, (f, T) :: fl, v, ck, H =>
    let (r, Hr) := feval_proj_impl Θ Ξ f v _ in
    let (t, Ht) := feval_exp_impl Θ Ξ T ρ _ in
    let (V, HV) := fread_nf_impl_c s ⇓ t r ck _ in
    let (Vs, HVs) := fread_fields_impl_c s (ρ ↦ r) fl v ck _ in
    exist _ (cons V Vs) _

  with fread_cargs_impl_c s p ups ρ gs vs (ck : lk_cache Θ Ξ) (H : fread_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, p, ups, ρ, nil, nil, ck, H => exist _ nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, ck, H =>
    let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := fread_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fread_cargs_impl_c s p ups (ρ ↦ v) gs vs ck _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, ca_rec t :: gs, v :: vs, ck, H =>
    let (V, HV) := fread_shape_impl_c s p ups ρ t v ck _ in
    let (Vs, HVs) := fread_cargs_impl_c s p ups ρ gs vs ck _ in
    exist _ (cons V Vs) _
| s, p, ups, ρ, _, _, ck, H => False_rect _ _

  with fread_shape_impl_c s p ups ρ t v (ck : lk_cache Θ Ξ) (H : fread_shape_order Θ Ξ s p ups ρ t v) :
    { V | Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V } by struct H :=
| s, p, ups, ρ, pt_self j Ps, v, ck, H =>
    let (bs, Hbs) := feval_exps_impl Θ Ξ Ps ρ _ in
    let (V, HV) := fread_nf_impl_c s ⇓ (d_ind p j (ups ++ bs)) v ck _ in
    exist _ V _
| s, p, ups, ρ, pt_pi B t, v, ck, H =>
    let (b, Hb) := feval_exp_impl Θ Ξ B ρ _ in
    let (A, HA) := fread_typ_impl_c s b ck _ in
    let (r, Hr) := feval_app_impl Θ Ξ v (⇑! b s) _ in
    let (V, HV) := fread_shape_impl_c (S s) p ups (ρ ↦ ⇑! b s) t r ck _ in
    exist _ (λⁿ A V) _

  with fread_blocks_impl_c s ρ p ups Bks sel i Ms (ck : lk_cache Θ Ξ) (H : fread_blocks_order Θ Ξ s ρ p ups Bks sel i Ms) :
    { NBks | Rblksᶠ i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks } by struct H :=
| s, ρ, p, ups, Bks, sel, i, nil, ck, H => exist _ nil _
| s, ρ, p, ups, Bks, sel, i, Mi :: Ms, ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed with inspect (ind_member D (elim_src sel i)) := {
    | exist _ (Some Mv) Em with inspect (List.nth_error Bks (elim_src sel i)) := {
      | exist _ (Some b) Eb with feval_mref_impl Θ Ξ p ups (elim_src sel i) _ := {
        | exist _ (pk, k, pre) Hm =>
            let (ns, Hns) := ffresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s _ in
            let (a, Ha) := feval_exp_impl Θ Ξ (eb_motive b)
                             (env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil)) _ in
            let (A', HA') := fread_typ_impl_c (S (s + im_nn Mi)) a ck _ in
            let (Bs', HBs') := fread_brs_impl_c s ρ p ups Bks Mv (eb_motive b) Mi (pk, k, pre) (im_cons Mi) (eb_brs b) ck _ in
            let (NBks, HNBks) := fread_blocks_impl_c s ρ p ups Bks sel (S i) Ms ck _ in
            exist _ (cons (mk_normal_block (S (im_nn Mi)) A' Bs') NBks) _ }
      | exist _ None Eb => False_rect _ _ }
    | exist _ None Em => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }

  with fread_brs_impl_c s ρ p ups Bks Mv A Mi r cs Bs (ck : lk_cache Θ Ξ)
         (H : fread_brs_order Θ Ξ s ρ p ups Bks Mv A Mi r cs Bs) :
    { Bs' | Rbrsᶠ Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' } by struct H :=
| s, ρ, p, ups, Bks, Mv, A, Mi, r, nil, nil, ck, H => exist _ nil _
| s, ρ, p, ups, Bks, Mv, A, Mi, (pk, k, pre), (c, gs') :: cs, (_, _, B) :: Bs, ck, H with inspect (ind_con Mv c) := {
  | exist _ (Some gs) Ec =>
      let (ns, Hns) := ffresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (im_nparams Mv)) s _ in
      let (vs, Hvs) := ffresh_cargs_impl Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + im_nn Mi) _ in
      let (ihs, Hihs) := ffresh_ihs_impl Θ Ξ ρ (blocks_motives Bks) B (env_args nil (ups ++ ns)) gs' gs vs
                           (s + im_nn Mi + List.length gs') _ in
      let (wihs, Hw) := fwrap_ihs_impl Θ Ξ ρ p ups Bks gs' gs vs ihs _ in
      let (b, Hb) := feval_exp_impl Θ Ξ B (env_args ρ (ns ++ vs ++ wihs)) _ in
      let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil)) _ in
      let (B', HB') := fread_nf_impl_c (s + (im_nn Mi + List.length gs' + cargs_nrec gs')) ⇓ t b ck _ in
      let (Bs', HBs') := fread_brs_impl_c s ρ p ups Bks Mv A Mi (pk, k, pre) cs Bs ck _ in
      exist _ (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec gs') B') Bs') _
  | exist _ None Ec => False_rect _ _ }
| s, ρ, p, ups, Bks, Mv, A, Mi, r, _, _, ck, H => False_rect _ _.

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
    (** A record, looked up once *)
    | H1 : record_lookup _ _ ?p = Some ?x, H2 : record_lookup _ _ ?p = Some ?y |- _ =>
        assert_fails (constr_eq x y);
        rewrite H1 in H2; injection H2; clear H2; rb_unify x y
    (** The member a member stands for, at the reference the order records *)
    | Hm : feval_mref _ _ ?p _ ?j (?a, ?b, _), Hl : ind_lookup _ _ ?p = Some _, Hj : ind_member _ ?j = Some _,
      Hr : im_ref ?p ?j _ = (?c, ?d) |- _ =>
        assert_fails (constr_eq a c);
        let E := fresh "Er" in
        pose proof (feval_mref_im_ref _ _ _ _ _ _ _ _ _ _ Hm Hl Hj) as E;
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
        | solve [ eapply fread_nf_con_view_last; eassumption ]
        | econstructor; try eassumption; eauto 3 ].

#[local]
Ltac rb_obl_auto :=
  intros; cbv beta in *;
  lazymatch goal with
  | |- fread_nf_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_ne_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_typ_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_la_order _ _ _ _ => first [ rb_ord | rb_run ]
  (** The parameters of a type former with arguments: read off its order
      before inversion takes the arguments apart. *)
  | |- fread_ps_order _ _ _ _ _ _ =>
      first [ solve [ match goal with H : fread_typ_order _ _ _ (d_ind _ _ (_ :: _)) |- _ =>
                        inversion H; subst; rb_glob; assumption end ]
            | rb_ord | rb_run ]
  | |- fread_fields_order _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_proj_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_cargs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_shape_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_blocks_order _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_brs_order _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_tele_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_cargs_order _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_ihs_order _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fwrap_ihs_order _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_exp_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_exps_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_app_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_mref_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- _ => abstract (first [ rb_ord | rb_run | eapply fread_typ_suniv_of_nf; eassumption | rb_ind ])
  end.

Solve All Obligations with rb_obl_auto.

(** The [fread_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the readback orders and the functionality
    of readback. *)

(** The entries of readback, from the declaration the command looked up
    ([fc_seed]). *)
Definition fread_nf_impl s d (H : fread_nf_order Θ Ξ s d) : { m | Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fread_nf_impl_c s d (@fc_seed Θ Ξ F) H.
Definition fread_ne_impl s d (H : fread_ne_order Θ Ξ s d) : { m | Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fread_ne_impl_c s d (@fc_seed Θ Ξ F) H.
Definition fread_typ_impl s d (H : fread_typ_order Θ Ξ s d) : { m | Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } :=
  fread_typ_impl_c s d (@fc_seed Θ Ξ F) H.
Definition fread_la_impl s xs (H : fread_la_order Θ Ξ s xs) : { ys | Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys } :=
  fread_la_impl_c s xs (@fc_seed Θ Ξ F) H.

#[local]
Ltac functional_fread_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_fread_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma fread_nf_impl_complete : forall s d m,
    Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', fread_nf_impl s d H = exist _ m H'.
Proof.
  intros; functional_fread_complete.
Qed.

Lemma fread_ne_impl_complete : forall s d m,
    Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', fread_ne_impl s d H = exist _ m H'.
Proof.
  intros; functional_fread_complete.
Qed.

Lemma fread_typ_impl_complete : forall s d m,
    Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', fread_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_fread_complete.
Qed.

Lemma fread_la_impl_complete : forall s xs ys,
    Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    exists H H', fread_la_impl s xs H = exist _ ys H'.
Proof.
  intros; functional_fread_complete.
Qed.

End ReadbackImpl.

Extraction Inline fread_nf_impl_c_functional
  fread_ne_impl_c_functional
  fread_typ_impl_c_functional
  fread_la_impl_c_functional
  fread_ps_impl_c_functional
  fread_fields_impl_c_functional
  fread_cargs_impl_c_functional
  fread_shape_impl_c_functional
  fread_blocks_impl_c_functional
  fread_brs_impl_c_functional.
