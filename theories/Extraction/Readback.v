From Equations Require Import Equations.
From Stdlib Require Import List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members Inductives.
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
  match W with nf_lvl c xs => (c, xs) | _ => (oz, la_nil) end.

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

(** ** The Fresh Variables of the Telescopes of an Inductive Type

    Their orders, and the functions that compute them. *)

Inductive ffresh_tele_order (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> Prop :=
| fftelo_nil :
  `( ffresh_tele_order Θ Ξ ρ nil s )
| fftelo_cons :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> ffresh_tele_order Θ Ξ (ρ ↦ ⇑! a s) T (S s)) ->
     ffresh_tele_order Θ Ξ ρ (ce_ass A :: T) s ).

Inductive ffresh_cargs_order (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> Prop :=
| ffcargo_nil :
  `( ffresh_cargs_order Θ Ξ p ups ρ nil s )
| ffcargo_arg :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> ffresh_cargs_order Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s)) ->
     ffresh_cargs_order Θ Ξ p ups ρ (ca_arg A :: gs) s )
| ffcargo_rec :
  `( feval_shty_order Θ Ξ p ups ρ t ->
     ffresh_cargs_order Θ Ξ p ups ρ gs (S s) ->
     ffresh_cargs_order Θ Ξ p ups ρ (ca_rec t :: gs) s ).

Inductive ffresh_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (A : exp) (B : exp) :
  env -> list carg -> list domain -> nat -> Prop :=
| ffihso_nil :
  `( ffresh_ihs_order Θ Ξ ρ A B ρa nil nil s )
| ffihso_arg :
  `( ffresh_ihs_order Θ Ξ ρ A B (ρa ↦ v) gs vs s ->
     ffresh_ihs_order Θ Ξ ρ A B ρa (ca_arg T :: gs) (v :: vs) s )
| ffihso_rec :
  `( (exp_freshb (cargs_nrec gs) B = false -> feval_ihty_order Θ Ξ ρ A ρa t v) ->
     ffresh_ihs_order Θ Ξ ρ A B ρa gs vs (S s) ->
     ffresh_ihs_order Θ Ξ ρ A B ρa (ca_rec t :: gs) (v :: vs) s ).

#[local]
Hint Constructors ffresh_tele_order ffresh_cargs_order ffresh_ihs_order : mctt.

Lemma ffresh_tele_order_sound : forall Θ Ξ ρ T s vs, ffresh_tele Θ Ξ ρ T s vs -> ffresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

Lemma ffresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs,
    ffresh_cargs Θ Ξ p ups ρ gs s vs -> ffresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

Lemma ffresh_ihs_order_sound : forall Θ Ξ ρ A B ρa gs vs s ihs,
    ffresh_ihs Θ Ξ ρ A B ρa gs vs s ihs -> ffresh_ihs_order Θ Ξ ρ A B ρa gs vs s.
Proof. induction 1; econstructor; intros; try congruence; functional_feval_rewrite_clear; mauto. Qed.

#[export]
Hint Resolve ffresh_tele_order_sound ffresh_cargs_order_sound ffresh_ihs_order_sound : mctt.

Section FreshImpl.
  Variables (Θ : gdeps) (Ξ : gstack).
  Context {F : FCtx Θ Ξ}.

  #[local]
  Ltac fr_obl :=
    intros; cbv beta in *;
    repeat match goal with
      | H : ffresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : ffresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : ffresh_ihs_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    first [ eassumption | solve [ eauto 2 ] | econstructor; eassumption
          | match goal with H : _ = false -> _ |- _ => apply H; assumption end ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_tele_impl ρ T s (H : ffresh_tele_order Θ Ξ ρ T s) : { vs | ffresh_tele Θ Ξ ρ T s vs } by struct H :=
  | ρ, nil, s, H => exist _ nil _
  | ρ, ce_ass A :: T, s, H =>
      let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := ffresh_tele_impl (ρ ↦ ⇑! a s) T (S s) _ in
      exist _ (⇑! a s :: vs) _
  | ρ, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_cargs_impl p ups ρ gs s (H : ffresh_cargs_order Θ Ξ p ups ρ gs s) :
    { vs | ffresh_cargs Θ Ξ p ups ρ gs s vs } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ nil _
  | p, ups, ρ, ca_arg A :: gs, s, H =>
      let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := ffresh_cargs_impl p ups (ρ ↦ ⇑! a s) gs (S s) _ in
      exist _ (⇑! a s :: vs) _
  | p, ups, ρ, ca_rec t :: gs, s, H =>
      let (a, Ha) := feval_shty_fast Θ Ξ p ups ρ t _ in
      let (vs, Hvs) := ffresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! a s :: vs) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_ihs_impl ρ A B ρa gs vs s (H : ffresh_ihs_order Θ Ξ ρ A B ρa gs vs s) :
    { ihs | ffresh_ihs Θ Ξ ρ A B ρa gs vs s ihs } by struct H :=
  | ρ, A, B, ρa, nil, nil, s, H => exist _ nil _
  | ρ, A, B, ρa, ca_arg T :: gs, v :: vs, s, H =>
      let (ihs, Hihs) := ffresh_ihs_impl ρ A B (ρa ↦ v) gs vs s _ in
      exist _ ihs _
  | ρ, A, B, ρa, ca_rec t :: gs, v :: vs, s, H with inspect (exp_freshb (cargs_nrec gs) B) := {
    | exist _ true E =>
        let (ihs, Hihs) := ffresh_ihs_impl ρ A B ρa gs vs (S s) _ in
        exist _ (⇑! 𝕌ω@0 s :: ihs) _
    | exist _ false E =>
        let (a, Ha) := feval_ihty_fast Θ Ξ ρ A ρa t v _ in
        let (ihs, Hihs) := ffresh_ihs_impl ρ A B ρa gs vs (S s) _ in
        exist _ (⇑! a s :: ihs) _ }
  | ρ, A, B, ρa, _, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.
End FreshImpl.

(** ** The Orders of Readback *)

Inductive fread_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| frnf_type :
  `( fread_typ_order Θ Ξ s a ->
    fread_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
| frnf_stype :
  `( fread_typ_order Θ Ξ s a ->
    fread_nf_order Θ Ξ s ⇓ 𝕌@n a )
| frnf_lvl :
  `( fread_la_order Θ Ξ s xs ->
     fread_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
| frnf_lvl_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
| frnf_true :
  `( fread_nf_order Θ Ξ s ⇓ ⊤ᵈ m )
| frnf_False_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ ⊥ᵈ (⇑ a m) )
| frnf_fn :
  `( fread_typ_order Θ Ξ s a ->
     feval_app_order Θ Ξ m ⇑! a s ->
     feval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall m' b,
         $ᶠ| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         fread_nf_order Θ Ξ (S s) ⇓ b m') ->
     fread_nf_order Θ Ξ s ⇓ (Πᵈ a p B) m )
| frnf_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ (⇑ a b) (⇑ c m) )
| frnf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length as' = ind_np D ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     fread_ps_order Θ Ξ s nil (List.rev (ind_params D)) as' ->
     fread_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) ->
     fread_nf_order Θ Ξ s ⇓ (d_ind p as') (d_con p c vs) )
| frnf_ind_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ (d_ind p as') (⇑ a m) )

with fread_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
| frne_var :
  `( fread_ne_order Θ Ξ s #ᵈ x )
| frne_app :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s n ->
     fread_ne_order Θ Ξ s (m $ᵈ n) )
| frne_exfalso :
  `( feval_exp_order Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ⊥ᵈ s ↘ b ->
         fread_typ_order Θ Ξ (S s) b) ->
     fread_ne_order Θ Ξ s m ->
     fread_ne_order Θ Ξ s efqᵈ m under p return B )
| frne_glob :
  `( fread_ne_order Θ Ξ s (d_glob p) )
| frne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     Nat.eqb nm (S (ind_nn D)) = true ->
     ffresh_tele_order Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ->
     (forall ns,
         ffresh_tele Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         feval_exp_order Θ Ξ A (env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil))) ->
     (forall ns a,
         ffresh_tele Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil) ↘ a ->
         fread_typ_order Θ Ξ (S (s + ind_nn D)) a) ->
     fread_brs_order Θ Ξ s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs ->
     fread_ne_order Θ Ξ s m ->
     fread_ne_order Θ Ξ s (d_elim ρ nm A Bs p as' m) )

with fread_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| frtyp_univ :
  `( fread_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| frtyp_suniv :
  `( fread_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     fread_typ_order Θ Ξ s 𝕌@l )
| frtyp_level :
  `( fread_typ_order Θ Ξ s (Levelᵈ@n) )
| frtyp_True :
  `( fread_typ_order Θ Ξ s ⊤ᵈ )
| frtyp_False :
  `( fread_typ_order Θ Ξ s ⊥ᵈ )
| frtyp_pi :
  `( fread_typ_order Θ Ξ s a ->
     feval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         fread_typ_order Θ Ξ (S s) b) ->
     fread_typ_order Θ Ξ s Πᵈ a p B)
| frtyp_neut :
  `( fread_ne_order Θ Ξ s b ->
    fread_typ_order Θ Ξ s ⇑ a b )
| frtyp_indty_nil :
  `( fread_typ_order Θ Ξ s (d_ind p nil) )
| frtyp_indty :
  `( as' <> nil ->
     ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     fread_ps_order Θ Ξ s nil (List.rev (ind_params D)) as' ->
     fread_typ_order Θ Ξ s (d_ind p as') )

with fread_la_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
| frla_nil :
  `( fread_la_order Θ Ξ s nil )
| frla_cons :
  `( fread_ne_order Θ Ξ s m ->
     fread_la_order Θ Ξ s xs ->
     fread_la_order Θ Ξ s ((k, n, m) :: xs) )

with fread_ps_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> Prop :=
| frps_nil :
  `( fread_ps_order Θ Ξ s ρ nil nil )
| frps_cons :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fread_nf_order Θ Ξ s ⇓ a v) ->
     fread_ps_order Θ Ξ s (ρ ↦ v) T vs ->
     fread_ps_order Θ Ξ s ρ (ce_ass A :: T) (v :: vs) )

with fread_cargs_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> Prop :=
| frcargs_nil :
  `( fread_cargs_order Θ Ξ s p ups ρ nil nil )
| frcargs_arg :
  `( feval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a -> fread_nf_order Θ Ξ s ⇓ a v) ->
     fread_cargs_order Θ Ξ s p ups (ρ ↦ v) gs vs ->
     fread_cargs_order Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) )
| frcargs_rec :
  `( feval_shty_order Θ Ξ p ups ρ t ->
     (forall a, feval_shty Θ Ξ p ups ρ t a -> fread_nf_order Θ Ξ s ⇓ a v) ->
     fread_cargs_order Θ Ξ s p ups ρ gs vs ->
     fread_cargs_order Θ Ξ s p ups ρ (ca_rec t :: gs) (v :: vs) )

with fread_brs_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> exp -> qname -> ind_decl -> list domain ->
                                            list (string * list carg) -> list (string * nat * exp) -> Prop :=
| frbrs_nil :
  `( fread_brs_order Θ Ξ s ρ A p D ups nil nil )
| frbrs_cons :
  `( Nat.eqb n (ind_nn D + List.length gs + cargs_nrec gs)%nat = true ->
     cargs_plen (ind_nn D) gs ->
     ffresh_tele_order Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ->
     (forall ns,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs_order Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D)) ->
     (forall ns vs,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs ->
         ffresh_ihs_order Θ Ξ ρ A B (env_args nil (ups ++ ns)) gs vs (s + ind_nn D + List.length gs)) ->
     (forall ns vs,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs ->
         feval_exp_order Θ Ξ A (env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil))) ->
     (forall ns vs ihs,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs ->
         ffresh_ihs Θ Ξ ρ A B (env_args nil (ups ++ ns)) gs vs (s + ind_nn D + List.length gs) ihs ->
         feval_exp_order Θ Ξ B (env_args ρ (ns ++ vs ++ ihs))) ->
     (forall ns vs ihs b t,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs ->
         ffresh_ihs Θ Ξ ρ A B (env_args nil (ups ++ ns)) gs vs (s + ind_nn D + List.length gs) ihs ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ ihs) ↘ b ->
         ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil) ↘ t ->
         fread_nf_order Θ Ξ (s + n) ⇓ t b) ->
     fread_brs_order Θ Ξ s ρ A p D ups cs Bs ->
     fread_brs_order Θ Ξ s ρ A p D ups ((c, gs) :: cs) ((c, n, B) :: Bs) ).

#[local]
Hint Constructors fread_nf_order fread_ne_order fread_typ_order fread_la_order
  fread_ps_order fread_cargs_order fread_brs_order : mctt.

Lemma fread_nf_order_sound : forall Θ Ξ s d m,
    Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    fread_nf_order Θ Ξ s d
with fread_ne_order_sound : forall Θ Ξ s d m,
    Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    fread_ne_order Θ Ξ s d
with fread_typ_order_sound : forall Θ Ξ s d m,
    Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m ->
    fread_typ_order Θ Ξ s d
with fread_la_order_sound : forall Θ Ξ s xs ys,
    Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    fread_la_order Θ Ξ s xs
with fread_ps_order_sound : forall Θ Ξ s ρ T vs Ms,
    Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
    fread_ps_order Θ Ξ s ρ T vs
with fread_cargs_order_sound : forall Θ Ξ s p ups ρ gs vs Ms,
    fread_cargs Θ Ξ s p ups ρ gs vs Ms ->
    fread_cargs_order Θ Ξ s p ups ρ gs vs
with fread_brs_order_sound : forall Θ Ξ s ρ A p D ups cs Bs Bs',
    fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
    fread_brs_order Θ Ξ s ρ A p D ups cs Bs.
Proof.
  all: [> clear fread_nf_order_sound | clear fread_ne_order_sound | clear fread_typ_order_sound
       | clear fread_la_order_sound | clear fread_ps_order_sound | clear fread_cargs_order_sound
       | clear fread_brs_order_sound ];
    induction 1;
    (econstructor; try eassumption; try (apply Nat.eqb_eq; assumption);
     intros; functional_feval_rewrite_clear; functional_ffresh_rewrite_clear;
     functional_feval_rewrite_clear; mauto).
Qed.

#[export]
Hint Resolve fread_nf_order_sound fread_ne_order_sound fread_typ_order_sound fread_la_order_sound
  fread_ps_order_sound fread_cargs_order_sound fread_brs_order_sound : mctt.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : fread_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_la_order _ _ _ _ |- _ => progressive_invert H
  | H : fread_ps_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_cargs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : fread_brs_order _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

#[local]
Hint Resolve feval_shty_self_nil : mctt.

(** The readback of the constructors of the shape of [zero] and [succ]. *)
Lemma fread_nf_con_zero : forall Θ Ξ s p D c,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some nil -> ind_params D = nil -> ind_nu D = 0 ->
    Rnfᶠ ⇓ (d_ind p nil) (d_con p c nil) in Θ ⍮ Ξ ⍮ s ↘ nf_con p c nfs_nil.
Proof.
  intros * Hl Hc Hp Hu.
  change nfs_nil with (nfs_app nfs_nil nfs_nil).
  assert (ind_np D = 0) by (unfold ind_np; rewrite Hp; reflexivity).
  econstructor; try eassumption; try (rewrite Hp; constructor);
    rewrite ?H, ?Hu; cbn; try constructor; reflexivity.
Qed.

Lemma fread_nf_con_succ : forall Θ Ξ s p D c k v V,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some (ca_rec (pt_self k nil) :: nil) -> ind_params D = nil -> ind_nu D = 0 ->
    Rnfᶠ ⇓ (d_ind p nil) v in Θ ⍮ Ξ ⍮ s ↘ V ->
    Rnfᶠ ⇓ (d_ind p nil) (d_con p c (v :: nil)) in Θ ⍮ Ξ ⍮ s ↘ nf_con p c (nfs_cons V nfs_nil).
Proof.
  intros * Hl Hc Hp Hu HV.
  change (nfs_cons V nfs_nil) with (nfs_app nfs_nil (nfs_cons V nfs_nil)).
  assert (ind_np D = 0) by (unfold ind_np; rewrite Hp; reflexivity).
  econstructor; try eassumption; try (rewrite Hp; constructor); rewrite ?H, ?Hu; cbn; try reflexivity.
  econstructor; [ apply feval_shty_self_nil | exact HV | constructor ].
Qed.

#[local]
Hint Resolve fread_nf_con_zero fread_nf_con_succ : mctt.

(** The readback of the branches of the constructors of the shape of [zero]
    and [succ], at the environments [fread_brs] gives them. *)
Lemma fread_brs_nat_zero : forall Θ Ξ s ρ A p D ups c n B cs Bs b t B' Bs',
    ind_params D = nil ->
    n = (ind_nn D + 0 + 0)%nat ->
    cargs_plen (ind_nn D) nil ->
    ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ nil ++ nil) ↘ b ->
    ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ d_con p c (ups ++ nil ++ nil) :: nil) ↘ t ->
    Rnfᶠ ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
    fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
    fread_brs Θ Ξ s ρ A p D ups ((c, nil) :: cs) ((c, n, B) :: Bs) (nbrs_cons c n B' Bs').
Proof.
  intros * Hp Hn Hl Hb Ht HB HBs.
  econstructor; try eassumption; [ | constructor | constructor ].
  rewrite Hp, firstn_nil; constructor.
Qed.

Lemma fread_brs_nat_skip : forall Θ Ξ s ρ A p D ups c k n B cs Bs b t B' Bs',
    ind_params D = nil ->
    n = (ind_nn D + 1 + 1)%nat ->
    cargs_plen (ind_nn D) (ca_rec (pt_self k nil) :: nil) ->
    exp_freshb 0 B = true ->
    ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ (⇑! (d_ind p ups) (s + ind_nn D) :: nil) ++ ⇑! 𝕌ω@0 (s + ind_nn D + 1) :: nil) ↘ b ->
    ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ d_con p c (ups ++ nil ++ ⇑! (d_ind p ups) (s + ind_nn D) :: nil) :: nil) ↘ t ->
    Rnfᶠ ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
    fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
    fread_brs Θ Ξ s ρ A p D ups ((c, ca_rec (pt_self k nil) :: nil) :: cs) ((c, n, B) :: Bs) (nbrs_cons c n B' Bs').
Proof.
  intros * Hp Hn Hl Hf Hb Ht HB HBs.
  eapply fread_brs_cons with (ns := nil) (vs := _ :: nil) (ihs := _ :: nil); try eassumption.
  - rewrite Hp, firstn_nil; constructor.
  - econstructor; [ apply feval_shty_self_nil | constructor ].
  - eapply ffresh_ihs_skip; [ exact Hf | constructor ].
Qed.

Lemma fread_brs_nat_rec : forall Θ Ξ s ρ A p D ups c k n B cs Bs a b t B' Bs',
    ind_params D = nil ->
    n = (ind_nn D + 1 + 1)%nat ->
    cargs_plen (ind_nn D) (ca_rec (pt_self k nil) :: nil) ->
    exp_freshb 0 B = false ->
    ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ ⇑! (d_ind p ups) (s + ind_nn D) :: nil) ↘ a ->
    ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ (⇑! (d_ind p ups) (s + ind_nn D) :: nil) ++ ⇑! a (s + ind_nn D + 1) :: nil) ↘ b ->
    ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (nil ++ d_con p c (ups ++ nil ++ ⇑! (d_ind p ups) (s + ind_nn D) :: nil) :: nil) ↘ t ->
    Rnfᶠ ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
    fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
    fread_brs Θ Ξ s ρ A p D ups ((c, ca_rec (pt_self k nil) :: nil) :: cs) ((c, n, B) :: Bs) (nbrs_cons c n B' Bs').
Proof.
  intros * Hp Hn Hl Hf Ha Hb Ht HB HBs.
  eapply fread_brs_cons with (ns := nil) (vs := _ :: nil) (ihs := _ :: nil); try eassumption.
  - rewrite Hp, firstn_nil; constructor.
  - econstructor; [ apply feval_shty_self_nil | constructor ].
  - eapply ffresh_ihs_rec; [ exact Hf | econstructor; [ constructor | exact Ha ] | constructor ].
Qed.

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
    exist _ (lvⁿ oz (la_cons 0 (dsort a) M la_nil)) _
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
| s, ⇓ (d_ind p as') (d_con p' c vs), ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed with inspect (con_view D c vs) := {
    (** Of the shape of [zero] or [succ v] ([con_view]): no parameter, and
        [v] at the type itself. *)
    | exist _ (Some None) Ev => exist _ (nf_con p c nfs_nil) _
    | exist _ (Some (Some v)) Ev =>
        let (V, HV) := fread_nf_impl_c s ⇓ (d_ind p nil) v (Some (exist _ (p, D) Ed)) _ in
        exist _ (nf_con p c (nfs_cons V nfs_nil)) _
    | exist _ None Ev with inspect (ind_con D c) := {
      | exist _ (Some gs) Ec =>
          let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (ind_params D)) as' ck _ in
          let (Args, HArgs) := fread_cargs_impl_c s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) (Some (exist _ (p, D) Ed)) _ in
          exist _ (nf_con p c (nfs_app Ps Args)) _
      | exist _ None Ec => False_rect _ _ } }
  | exist _ None Ed => False_rect _ _ }
| s, ⇓ (d_ind p as') (⇑ a m), ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    exist _ ⇑ⁿ M _

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
| s, d_elim ρ nm A Bs p as' m, ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed =>
      let (ns, Hns) := ffresh_tele_impl Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s _ in
      let (a, Ha) := feval_exp_impl Θ Ξ A (env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil)) _ in
      let (A', HA') := fread_typ_impl_c (S (s + ind_nn D)) a ck _ in
      let (Bs', HBs') := fread_brs_impl_c s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs (Some (exist _ (p, D) Ed)) _ in
      let (M, HM) := fread_ne_impl_c s m ck _ in
      exist _ (ne_elim nm A' Bs' M) _
  | exist _ None Ed => False_rect _ _ }

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
| s, d_ind p nil, ck, H => exist _ (nf_indty p nfs_nil) _
| s, d_ind p as', ck, H with cache_lookup Θ Ξ ck p := {
  | exist _ (Some D) Ed =>
      let (Ps, HPs) := fread_ps_impl_c s nil (List.rev (ind_params D)) as' ck _ in
      exist _ (nf_indty p Ps) _
  | exist _ None Ed => False_rect _ _ }

  with fread_la_impl_c s xs (ck : lk_cache Θ Ξ) (H : fread_la_order Θ Ξ s xs) : { ys | Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, ck, H => exist _ la_nil _
| s, cons (k, n, m) xs, ck, H =>
    let (M, HM) := fread_ne_impl_c s m ck _ in
    let (ys, Hys) := fread_la_impl_c s xs ck _ in
    exist _ (la_cons k n M ys) _

  with fread_ps_impl_c s ρ T vs (ck : lk_cache Θ Ξ) (H : fread_ps_order Θ Ξ s ρ T vs) : { Ms | Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, ck, H => exist _ nfs_nil _
| s, ρ, ce_ass A :: T, v :: vs, ck, H =>
    let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := fread_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fread_ps_impl_c s (ρ ↦ v) T vs ck _ in
    exist _ (nfs_cons V Vs) _
| s, ρ, _, _, ck, H => False_rect _ _

  with fread_cargs_impl_c s p ups ρ gs vs (ck : lk_cache Θ Ξ) (H : fread_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | fread_cargs Θ Ξ s p ups ρ gs vs Ms } by struct H :=
| s, p, ups, ρ, nil, nil, ck, H => exist _ nfs_nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, ck, H =>
    let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := fread_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fread_cargs_impl_c s p ups (ρ ↦ v) gs vs ck _ in
    exist _ (nfs_cons V Vs) _
| s, p, ups, ρ, ca_rec t :: gs, v :: vs, ck, H =>
    let (a, Ha) := feval_shty_fast Θ Ξ p ups ρ t _ in
    let (V, HV) := fread_nf_impl_c s ⇓ a v ck _ in
    let (Vs, HVs) := fread_cargs_impl_c s p ups ρ gs vs ck _ in
    exist _ (nfs_cons V Vs) _
| s, p, ups, ρ, _, _, ck, H => False_rect _ _

  with fread_brs_impl_c s ρ A p D ups cs Bs (ck : lk_cache Θ Ξ) (H : fread_brs_order Θ Ξ s ρ A p D ups cs Bs) :
    { Bs' | fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' } by struct H :=
| s, ρ, A, p, D, ups, nil, nil, ck, H => exist _ nbrs_nil _
| s, ρ, A, p, D, ups, (c, gs) :: cs, (c', n, B) :: Bs, ck, H with inspect (nat_cargs D gs) := {
  (** The branch of a constructor of the shape of [zero] ([nat_cargs]):
      it binds nothing. *)
  | exist _ (Some false) Eg =>
      let (b, Hb) := feval_exp_impl Θ Ξ B (env_args ρ (nil ++ nil ++ nil)) _ in
      let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (nil ++ d_con p c (ups ++ nil ++ nil) :: nil)) _ in
      let (B', HB') := fread_nf_impl_c (s + n) ⇓ t b ck _ in
      let (Bs', HBs') := fread_brs_impl_c s ρ A p D ups cs Bs ck _ in
      exist _ (nbrs_cons c n B' Bs') _
  (** Of the shape of [succ]: the argument, a variable of the type itself,
      and its recursive result, of the type the motive gives the argument
      unless the branch does not read it. *)
  | exist _ (Some true) Eg with inspect (exp_freshb 0 B) := {
    | exist _ true Ef =>
        let v := ⇑! (d_ind p ups) (s + ind_nn D) in
        let (b, Hb) := feval_exp_impl Θ Ξ B (env_args ρ (nil ++ (v :: nil) ++ ⇑! 𝕌ω@0 (s + ind_nn D + 1) :: nil)) _ in
        let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (nil ++ d_con p c (ups ++ nil ++ v :: nil) :: nil)) _ in
        let (B', HB') := fread_nf_impl_c (s + n) ⇓ t b ck _ in
        let (Bs', HBs') := fread_brs_impl_c s ρ A p D ups cs Bs ck _ in
        exist _ (nbrs_cons c n B' Bs') _
    | exist _ false Ef =>
        let v := ⇑! (d_ind p ups) (s + ind_nn D) in
        let (a, Ha) := feval_exp_impl Θ Ξ A (env_args ρ (nil ++ v :: nil)) _ in
        let (b, Hb) := feval_exp_impl Θ Ξ B (env_args ρ (nil ++ (v :: nil) ++ ⇑! a (s + ind_nn D + 1) :: nil)) _ in
        let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (nil ++ d_con p c (ups ++ nil ++ v :: nil) :: nil)) _ in
        let (B', HB') := fread_nf_impl_c (s + n) ⇓ t b ck _ in
        let (Bs', HBs') := fread_brs_impl_c s ρ A p D ups cs Bs ck _ in
        exist _ (nbrs_cons c n B' Bs') _ }
  | exist _ None Eg =>
    let (ns, Hns) := ffresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s _ in
    let (vs, Hvs) := ffresh_cargs_impl Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) _ in
    let (ihs, Hihs) := ffresh_ihs_impl Θ Ξ ρ A B (env_args nil (ups ++ ns)) gs vs (s + ind_nn D + List.length gs) _ in
    let (b, Hb) := feval_exp_impl Θ Ξ B (env_args ρ (ns ++ vs ++ ihs)) _ in
    let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil)) _ in
    let (B', HB') := fread_nf_impl_c (s + n) ⇓ t b ck _ in
    let (Bs', HBs') := fread_brs_impl_c s ρ A p D ups cs Bs ck _ in
    exist _ (nbrs_cons c n B' Bs') _ }
| s, ρ, A, p, D, ups, _, _, ck, H => False_rect _ _.

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
Ltac rb_ind := repeat impl_obl_tac1; rb_glob; rb_eqb; first [ congruence | econstructor; try eassumption; eauto 3 ].

(** The constructors of the shape of the natural numbers ([con_view],
    [nat_cargs]): the general rules at no parameter, and at the lists the
    view fixes. *)
#[local]
Ltac rb_nat :=
  match goal with
  | Ev : con_view _ _ _ = Some None |- _ => destruct (con_view_zero _ _ _ Ev) as (? & ? & ? & ? & ?); subst
  | Ev : con_view _ _ _ = Some (Some _) |- _ => destruct (con_view_succ _ _ _ _ Ev) as (? & ? & ? & ? & ? & ?); subst
  | Eg : nat_cargs _ _ = Some false |- _ => destruct (nat_cargs_zero _ _ Eg) as (? & ? & ?); subst
  | Eg : nat_cargs _ _ = Some true |- _ => destruct (nat_cargs_succ _ _ Eg) as (? & ? & ? & ?); subst
  end;
  repeat impl_obl_tac1; rb_glob; rb_eqb;
  first [ solve [ eapply fread_brs_nat_zero; eassumption ]
        | solve [ eapply fread_brs_nat_skip; eassumption ]
        | solve [ eapply fread_brs_nat_rec; eassumption ]
        | idtac ];
  match goal with Hp : ind_params ?D = nil, Hu : ind_nu ?D = 0 |- _ =>
    let Hnp := fresh "Hnp" in let Hnn := fresh "Hnn" in
    assert (Hnp : ind_np D = 0) by (unfold ind_np; rewrite Hp; reflexivity);
    assert (Hnn : ind_nn D = 0) by (unfold ind_nn; rewrite Hnp, Hu; reflexivity);
    rewrite ?Hnn, ?Hnp, ?Hu in *; rewrite ?Hp in *;
    cbn [skipn firstn rev app env_args fold_left extend_env cargs_nrec List.length] in * |-;
    repeat impl_obl_tac1; rb_glob; rb_eqb;
    try match goal with Hl : List.length ?l = 0 |- _ => destruct l; [| discriminate ] end;
    repeat impl_obl_tac1;
    first [ eassumption
          | solve [ eauto 8 with mctt ]
          | match goal with Hb : forall _, _ |- _ =>
              first [ solve [ eapply (Hb nil nil nil); eauto 8 with mctt ]
                    | solve [ eapply (Hb nil (_ :: nil) (_ :: nil)); eauto 8 with mctt ]
                    | solve [ eapply (Hb nil nil); eauto 8 with mctt ]
                    | solve [ eapply (Hb nil (_ :: nil)); eauto 8 with mctt ]
                    | solve [ eapply Hb; eauto 8 with mctt ] ] end
          (** The type of the recursive result: the order of the motive
              under the order of the recursive results. *)
          | match goal with Ho : forall ns vs, _ -> _ -> ffresh_ihs_order _ _ _ _ _ _ _ _ _ |- feval_exp_order _ _ _ _ =>
              let Hi := fresh "Hi" in
              pose proof (Ho nil (_ :: nil) ltac:(eauto 8 with mctt) ltac:(eauto 8 with mctt)) as Hi;
              dependent destruction Hi; cbn [cargs_nrec] in * |-; try congruence;
              match goal with Hf : ?P -> feval_ihty_order _ _ _ _ _ _ _, Ef : ?P |- _ => specialize (Hf Ef) end;
              match goal with Ht : feval_ihty_order _ _ _ _ _ _ _ |- _ => progressive_invert Ht end;
              match goal with Hq : forall bs, _ -> feval_exp_order _ _ _ _ |- _ => solve [ eapply (Hq nil); eauto 8 with mctt ] end
            end
          | solve [ econstructor; rewrite ?Hnn, ?Hnp, ?Hu, ?Hp; cbn; eauto 8 with mctt ] ]
  end.

#[local]
Ltac rb_obl_auto :=
  intros; cbv beta in *;
  first [ lazymatch goal with
          | E : con_view _ _ _ = Some _ |- _ => solve [ rb_nat ]
          | E : nat_cargs _ _ = Some _ |- _ => solve [ rb_nat ]
          end
        | idtac ];
  lazymatch goal with
  | |- fread_nf_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_ne_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_typ_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_la_order _ _ _ _ => first [ rb_ord | rb_run ]
  (** The parameters of a type former with arguments: read off its order
      before inversion takes the arguments apart. *)
  | |- fread_ps_order _ _ _ _ _ _ =>
      first [ solve [ match goal with H : fread_typ_order _ _ _ (d_ind _ (_ :: _)) |- _ =>
                        inversion H; subst; rb_glob; assumption end ]
            | rb_ord | rb_run ]
  | |- fread_cargs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_brs_order _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_tele_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_cargs_order _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_ihs_order _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_exp_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_exps_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_app_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_shty_order _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_ihty_order _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- _ => abstract (first [ rb_ord | rb_run | eapply fread_typ_suniv_of_nf; eassumption | rb_ind ])
  end.

Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.
Next Obligation. rb_obl_auto. Defined.


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
  fread_cargs_impl_c_functional
  fread_brs_impl_c_functional.
