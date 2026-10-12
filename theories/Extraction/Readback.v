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
  `( feval_exps_order Θ Ξ (ptyp_ps Ps) ρ ->
     ffresh_cargs_order Θ Ξ p ups ρ gs (S s) ->
     ffresh_cargs_order Θ Ξ p ups ρ (ca_rec Ps :: gs) s ).

Inductive ffresh_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (A : exp) :
  list carg -> list domain -> list (list domain) -> nat -> Prop :=
| ffihso_nil :
  `( ffresh_ihs_order Θ Ξ ρ A nil nil nil s )
| ffihso_arg :
  `( ffresh_ihs_order Θ Ξ ρ A gs vs bss s ->
     ffresh_ihs_order Θ Ξ ρ A (ca_arg T :: gs) (v :: vs) bss s )
| ffihso_rec :
  `( feval_exp_order Θ Ξ A (env_args ρ (bs ++ v :: nil)) ->
     ffresh_ihs_order Θ Ξ ρ A gs vs bss (S s) ->
     ffresh_ihs_order Θ Ξ ρ A (ca_rec Ps :: gs) (v :: vs) (bs :: bss) s ).

#[local]
Hint Constructors ffresh_tele_order ffresh_cargs_order ffresh_ihs_order : mctt.

Lemma ffresh_tele_order_sound : forall Θ Ξ ρ T s vs, ffresh_tele Θ Ξ ρ T s vs -> ffresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

Lemma ffresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs bss,
    ffresh_cargs Θ Ξ p ups ρ gs s vs bss -> ffresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

Lemma ffresh_ihs_order_sound : forall Θ Ξ ρ A gs vs bss s ihs,
    ffresh_ihs Θ Ξ ρ A gs vs bss s ihs -> ffresh_ihs_order Θ Ξ ρ A gs vs bss s.
Proof. induction 1; econstructor; intros; functional_feval_rewrite_clear; mauto. Qed.

#[export]
Hint Resolve ffresh_tele_order_sound ffresh_cargs_order_sound ffresh_ihs_order_sound : mctt.

Section FreshImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac fr_obl :=
    intros; cbv beta in *;
    repeat match goal with
      | H : ffresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : ffresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : ffresh_ihs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    first [ eassumption | solve [ eauto 2 ] | econstructor; eassumption ].

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
    { r | ffresh_cargs Θ Ξ p ups ρ gs s (fst r) (snd r) } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ (nil, nil) _
  | p, ups, ρ, ca_arg A :: gs, s, H =>
      let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
      let (r, Hr) := ffresh_cargs_impl p ups (ρ ↦ ⇑! a s) gs (S s) _ in
      exist _ (⇑! a s :: fst r, snd r) _
  | p, ups, ρ, ca_rec Ps :: gs, s, H =>
      let (bs, Hbs) := feval_exps_impl Θ Ξ (ptyp_ps Ps) ρ _ in
      let (r, Hr) := ffresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! (d_ind p (ups ++ bs)) s :: fst r, bs :: snd r) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations ffresh_ihs_impl ρ A gs vs bss s (H : ffresh_ihs_order Θ Ξ ρ A gs vs bss s) :
    { ihs | ffresh_ihs Θ Ξ ρ A gs vs bss s ihs } by struct H :=
  | ρ, A, nil, nil, nil, s, H => exist _ nil _
  | ρ, A, ca_arg T :: gs, v :: vs, bss, s, H =>
      let (ihs, Hihs) := ffresh_ihs_impl ρ A gs vs bss s _ in
      exist _ ihs _
  | ρ, A, ca_rec Ps :: gs, v :: vs, bs :: bss, s, H =>
      let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (bs ++ v :: nil)) _ in
      let (ihs, Hihs) := ffresh_ihs_impl ρ A gs vs bss (S s) _ in
      exist _ (⇑! t s :: ihs) _
  | ρ, A, _, _, _, s, H => False_rect _ _.
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
| frnf_zero :
  `( fread_nf_order Θ Ξ s ⇓ ℕᵈ zeroᵈ )
| frnf_succ :
  `( fread_nf_order Θ Ξ s ⇓ ℕᵈ m ->
     fread_nf_order Θ Ξ s ⇓ ℕᵈ (succᵈ m) )
| frnf_nat_neut :
  `( fread_ne_order Θ Ξ s m ->
     fread_nf_order Θ Ξ s ⇓ ℕᵈ (⇑ a m) )
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
| frne_natrec :
  `( feval_exp_order Θ Ξ B (p ↦ ⇑! ℕᵈ s) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         fread_typ_order Θ Ξ (S s) b) ->
     feval_exp_order Θ Ξ B (p ↦ zeroᵈ) ->
     (forall bz,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ zeroᵈ ↘ bz ->
         fread_nf_order Θ Ξ s ⇓ bz mz) ->
     feval_exp_order Θ Ξ B (p ↦ succᵈ (⇑! ℕᵈ s)) ->
     (forall b,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         feval_exp_order Θ Ξ MS (p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s))) ->
     (forall b bs ms,
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
         ⟦ MS ⟧ᶠ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
         fread_nf_order Θ Ξ (S (S s)) ⇓ bs ms) ->
     fread_ne_order Θ Ξ s m ->
     fread_ne_order Θ Ξ s recᵈ m under p return B | zero -> mz | succ -> MS end )
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
| frtyp_nat :
  `( fread_typ_order Θ Ξ s ℕᵈ )
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
| frtyp_indty :
  `( ind_lookup Θ Ξ p = Some D ->
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
  `( feval_exps_order Θ Ξ (ptyp_ps Ps) ρ ->
     (forall bs, ⟦ (ptyp_ps Ps) ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs -> fread_nf_order Θ Ξ s ⇓ (d_ind p (ups ++ bs)) v) ->
     fread_cargs_order Θ Ξ s p ups ρ gs vs ->
     fread_cargs_order Θ Ξ s p ups ρ (ca_rec Ps :: gs) (v :: vs) )

with fread_brs_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> exp -> qname -> ind_decl -> list domain ->
                                            list (string * list carg) -> list (string * nat * exp) -> Prop :=
| frbrs_nil :
  `( fread_brs_order Θ Ξ s ρ A p D ups nil nil )
| frbrs_cons :
  `( Nat.eqb n (ind_nn D + List.length gs + cargs_nrec gs)%nat = true ->
     ffresh_tele_order Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ->
     (forall ns,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs_order Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D)) ->
     (forall ns vs bss,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         List.Forall (fun bs => List.length bs = ind_nn D) bss) ->
     (forall ns vs bss,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         ffresh_ihs_order Θ Ξ ρ A gs vs bss (s + ind_nn D + List.length gs)) ->
     (forall ns vs bss,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         feval_exp_order Θ Ξ A (env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil))) ->
     (forall ns vs bss ihs,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         ffresh_ihs Θ Ξ ρ A gs vs bss (s + ind_nn D + List.length gs) ihs ->
         feval_exp_order Θ Ξ B (env_args ρ (ns ++ vs ++ ihs))) ->
     (forall ns vs bss ihs b t,
         ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         ffresh_ihs Θ Ξ ρ A gs vs bss (s + ind_nn D + List.length gs) ihs ->
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

Section ReadbackImpl.
Variables (Θ : gdeps) (Ξ : gstack).

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations fread_nf_impl s d (H : fread_nf_order Θ Ξ s d) : { m | Rnfᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, ⇓ 𝕌ω@i a      , H =>
    let (A, HA) := fread_typ_impl s a _ in
    exist _ A _
| s, ⇓ 𝕌@n a     , H =>
    let (A, HA) := fread_typ_impl s a _ in
    exist _ A _
| s, ⇓ (Levelᵈ@n) (lvᵈ c xs), H =>
    let (ys, Hys) := fread_la_impl s xs _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, ⇓ (Levelᵈ@n) (⇑ a m), H =>
    let (M, HM) := fread_ne_impl s m _ in
    exist _ (lvⁿ oz (la_cons 0 (dsort a) M la_nil)) _
| s, ⇓ ℕᵈ zeroᵈ, H => exist _ zeroⁿ _
| s, ⇓ ℕᵈ (succᵈ m) , H =>
    let (M, HM) := fread_nf_impl s ⇓ ℕᵈ m _ in
    exist _ succⁿ M _
| s, ⇓ ℕᵈ (⇑ _ m)  , H =>
    let (M, HM) := fread_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ ⊤ᵈ m, H => exist _ ⋆ⁿ _
| s, ⇓ ⊥ᵈ (⇑ _ m), H =>
    let (M, HM) := fread_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (Πᵈ a p B) m, H =>
    let (A, HA) := fread_typ_impl s a _ in
    let (m', Hm') := feval_app_impl Θ Ξ m ⇑! a s _ in
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (M, HM) := fread_nf_impl (S s) ⇓ b m' _ in
    exist _ (λⁿ A M) _
| s, ⇓ (⇑ a b) (⇑ c m), H =>
    let (M, HM) := fread_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (d_ind p as') (d_con p' c vs), H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_con D c) := {
    | exist _ (Some gs) Ec =>
        let (Ps, HPs) := fread_ps_impl s nil (List.rev (ind_params D)) as' _ in
        let (Args, HArgs) := fread_cargs_impl s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) _ in
        exist _ (nf_con p c (nfs_app Ps Args)) _
    | exist _ None Ec => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, ⇓ (d_ind p as') (⇑ a m), H =>
    let (M, HM) := fread_ne_impl s m _ in
    exist _ ⇑ⁿ M _

  with fread_ne_impl s d (H : fread_ne_order Θ Ξ s d) : { m | Rneᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, H => exist _ #ⁿ (s - x - 1) _
| s, d_glob p, H => exist _ (ne_glob p) _
| s, m $ᵈ n, H =>
    let (M, HM) := fread_ne_impl s m _ in
    let (N, HN) := fread_nf_impl s n _ in
    exist _ (M $ⁿ N) _
| s, recᵈ m under p return B | zero -> mz | succ -> MS end, H =>
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! ℕᵈ s) _ in
    let (B', HB') := fread_typ_impl (S s) b _ in
    let (bz, Hbz) := feval_exp_impl Θ Ξ B (p ↦ zeroᵈ) _ in
    let (MZ, HMZ) := fread_nf_impl s ⇓ bz mz _ in
    let (bs, Hbs) := feval_exp_impl Θ Ξ B (p ↦ succᵈ (⇑! ℕᵈ s)) _ in
    let (ms, Hms) := feval_exp_impl Θ Ξ MS (p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s)) _ in
    let (MS', HMS') := fread_nf_impl (S (S s)) ⇓ bs ms _ in
    let (M, HM) := fread_ne_impl s m _ in
    exist _ recⁿ M return B' | zero -> MZ | succ -> MS' end _
| s, efqᵈ m under p return B, H =>
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) _ in
    let (B', HB') := fread_typ_impl (S s) b _ in
    let (M, HM) := fread_ne_impl s m _ in
    exist _ (efqⁿ M return B') _
| s, d_elim ρ nm A Bs p as' m, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed =>
      let (ns, Hns) := ffresh_tele_impl Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s _ in
      let (a, Ha) := feval_exp_impl Θ Ξ A (env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil)) _ in
      let (A', HA') := fread_typ_impl (S (s + ind_nn D)) a _ in
      let (Bs', HBs') := fread_brs_impl s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs _ in
      let (M, HM) := fread_ne_impl s m _ in
      exist _ (ne_elim nm A' Bs' M) _
  | exist _ None Ed => False_rect _ _ }

      with fread_typ_impl s d (H : fread_typ_order Θ Ξ s d) : { m | Rtypᶠ d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, H =>
    let (W, HW) := fread_nf_impl s ⇓ Levelᵈ l _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, Levelᵈ@n, H => exist _ (Levelⁿ@n) _
| s, ℕᵈ, H => exist _ ℕⁿ _
| s, ⊤ᵈ, H => exist _ ⊤ⁿ _
| s, ⊥ᵈ, H => exist _ ⊥ⁿ _
| s, Πᵈ a p B, H =>
    let (A, HA) := fread_typ_impl s a _ in
    let (b, Hb) := feval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (B', HB') := fread_typ_impl (S s) b _ in
    exist _ (Πⁿ A B') _
| s, ⇑ a b, H =>
    let (B, HB) := fread_ne_impl s b _ in
    exist _ ⇑ⁿ B _
| s, d_ind p as', H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed =>
      let (Ps, HPs) := fread_ps_impl s nil (List.rev (ind_params D)) as' _ in
      exist _ (nf_indty p Ps) _
  | exist _ None Ed => False_rect _ _ }

  with fread_la_impl s xs (H : fread_la_order Θ Ξ s xs) : { ys | Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, H => exist _ la_nil _
| s, cons (k, n, m) xs, H =>
    let (M, HM) := fread_ne_impl s m _ in
    let (ys, Hys) := fread_la_impl s xs _ in
    exist _ (la_cons k n M ys) _

  with fread_ps_impl s ρ T vs (H : fread_ps_order Θ Ξ s ρ T vs) : { Ms | Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, H => exist _ nfs_nil _
| s, ρ, ce_ass A :: T, v :: vs, H =>
    let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := fread_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := fread_ps_impl s (ρ ↦ v) T vs _ in
    exist _ (nfs_cons V Vs) _
| s, ρ, _, _, H => False_rect _ _

  with fread_cargs_impl s p ups ρ gs vs (H : fread_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | fread_cargs Θ Ξ s p ups ρ gs vs Ms } by struct H :=
| s, p, ups, ρ, nil, nil, H => exist _ nfs_nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, H =>
    let (a, Ha) := feval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := fread_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := fread_cargs_impl s p ups (ρ ↦ v) gs vs _ in
    exist _ (nfs_cons V Vs) _
| s, p, ups, ρ, ca_rec Ps :: gs, v :: vs, H =>
    let (bs, Hbs) := feval_exps_impl Θ Ξ (ptyp_ps Ps) ρ _ in
    let (V, HV) := fread_nf_impl s ⇓ (d_ind p (ups ++ bs)) v _ in
    let (Vs, HVs) := fread_cargs_impl s p ups ρ gs vs _ in
    exist _ (nfs_cons V Vs) _
| s, p, ups, ρ, _, _, H => False_rect _ _

  with fread_brs_impl s ρ A p D ups cs Bs (H : fread_brs_order Θ Ξ s ρ A p D ups cs Bs) :
    { Bs' | fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' } by struct H :=
| s, ρ, A, p, D, ups, nil, nil, H => exist _ nbrs_nil _
| s, ρ, A, p, D, ups, (c, gs) :: cs, (c', n, B) :: Bs, H =>
    let (ns, Hns) := ffresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s _ in
    let (r, Hr) := ffresh_cargs_impl Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) _ in
    let (ihs, Hihs) := ffresh_ihs_impl Θ Ξ ρ A gs (fst r) (snd r) (s + ind_nn D + List.length gs) _ in
    let (b, Hb) := feval_exp_impl Θ Ξ B (env_args ρ (ns ++ fst r ++ ihs)) _ in
    let (t, Ht) := feval_exp_impl Θ Ξ A (env_args ρ (ns ++ d_con p c (ups ++ ns ++ fst r) :: nil)) _ in
    let (B', HB') := fread_nf_impl (s + n) ⇓ t b _ in
    let (Bs', HBs') := fread_brs_impl s ρ A p D ups cs Bs _ in
    exist _ (nbrs_cons c n B' Bs') _
| s, ρ, A, p, D, ups, _, _, H => False_rect _ _.

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

#[local]
Ltac rb_obl_auto :=
  intros; cbv beta in *;
  lazymatch goal with
  | |- fread_nf_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_ne_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_typ_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_la_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_ps_order _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_cargs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fread_brs_order _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_tele_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_cargs_order _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- ffresh_ihs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_exp_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_exps_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- feval_app_order _ _ _ _ => first [ rb_ord | rb_run ]
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


(** The [fread_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the readback orders and the functionality
    of readback. *)

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

Extraction Inline fread_nf_impl_functional
  fread_ne_impl_functional
  fread_typ_impl_functional
  fread_la_impl_functional
  fread_ps_impl_functional
  fread_cargs_impl_functional
  fread_brs_impl_functional.
