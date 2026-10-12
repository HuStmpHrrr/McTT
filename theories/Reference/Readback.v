From Equations Require Import Equations.
From Stdlib Require Import List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members Inductives.
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

(** ** The Fresh Variables of the Telescopes of an Inductive Type

    Their orders, and the functions that compute them. *)

Inductive fresh_tele_order (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> Prop :=
| telo_nil :
  `( fresh_tele_order Θ Ξ ρ nil s )
| telo_cons :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> fresh_tele_order Θ Ξ (ρ ↦ ⇑! a s) T (S s)) ->
     fresh_tele_order Θ Ξ ρ (ce_ass A :: T) s ).

Inductive fresh_cargs_order (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> Prop :=
| cargo_nil :
  `( fresh_cargs_order Θ Ξ p ups ρ nil s )
| cargo_arg :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> fresh_cargs_order Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s)) ->
     fresh_cargs_order Θ Ξ p ups ρ (ca_arg A :: gs) s )
| cargo_rec :
  `( eval_exps_order Θ Ξ Ps ρ ->
     fresh_cargs_order Θ Ξ p ups ρ gs (S s) ->
     fresh_cargs_order Θ Ξ p ups ρ (ca_rec Ps :: gs) s ).

Inductive fresh_ihs_order (Θ : gdeps) (Ξ : gstack) (ρ : env) (A : exp) :
  list carg -> list domain -> list (list domain) -> nat -> Prop :=
| ihso_nil :
  `( fresh_ihs_order Θ Ξ ρ A nil nil nil s )
| ihso_arg :
  `( fresh_ihs_order Θ Ξ ρ A gs vs bss s ->
     fresh_ihs_order Θ Ξ ρ A (ca_arg T :: gs) (v :: vs) bss s )
| ihso_rec :
  `( eval_exp_order Θ Ξ A (env_args ρ (bs ++ v :: nil)) ->
     fresh_ihs_order Θ Ξ ρ A gs vs bss (S s) ->
     fresh_ihs_order Θ Ξ ρ A (ca_rec Ps :: gs) (v :: vs) (bs :: bss) s ).

#[local]
Hint Constructors fresh_tele_order fresh_cargs_order fresh_ihs_order : mctt.

Lemma fresh_tele_order_sound : forall Θ Ξ ρ T s vs, fresh_tele Θ Ξ ρ T s vs -> fresh_tele_order Θ Ξ ρ T s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

Lemma fresh_cargs_order_sound : forall Θ Ξ p ups ρ gs s vs bss,
    fresh_cargs Θ Ξ p ups ρ gs s vs bss -> fresh_cargs_order Θ Ξ p ups ρ gs s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

Lemma fresh_ihs_order_sound : forall Θ Ξ ρ A gs vs bss s ihs,
    fresh_ihs Θ Ξ ρ A gs vs bss s ihs -> fresh_ihs_order Θ Ξ ρ A gs vs bss s.
Proof. induction 1; econstructor; intros; functional_eval_rewrite_clear; mauto. Qed.

#[export]
Hint Resolve fresh_tele_order_sound fresh_cargs_order_sound fresh_ihs_order_sound : mctt.

Section FreshImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac fr_obl :=
    intros; cbv beta in *;
    repeat match goal with
      | H : fresh_tele_order _ _ _ _ _ |- _ => progressive_invert H
      | H : fresh_cargs_order _ _ _ _ _ _ _ |- _ => progressive_invert H
      | H : fresh_ihs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    first [ eassumption | solve [ eauto 2 ] | econstructor; eassumption ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_tele_impl ρ T s (H : fresh_tele_order Θ Ξ ρ T s) : { vs | fresh_tele Θ Ξ ρ T s vs } by struct H :=
  | ρ, nil, s, H => exist _ nil _
  | ρ, ce_ass A :: T, s, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      let (vs, Hvs) := fresh_tele_impl (ρ ↦ ⇑! a s) T (S s) _ in
      exist _ (⇑! a s :: vs) _
  | ρ, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_cargs_impl p ups ρ gs s (H : fresh_cargs_order Θ Ξ p ups ρ gs s) :
    { r | fresh_cargs Θ Ξ p ups ρ gs s (fst r) (snd r) } by struct H :=
  | p, ups, ρ, nil, s, H => exist _ (nil, nil) _
  | p, ups, ρ, ca_arg A :: gs, s, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
      let (r, Hr) := fresh_cargs_impl p ups (ρ ↦ ⇑! a s) gs (S s) _ in
      exist _ (⇑! a s :: fst r, snd r) _
  | p, ups, ρ, ca_rec Ps :: gs, s, H =>
      let (bs, Hbs) := eval_exps_impl Θ Ξ Ps ρ _ in
      let (r, Hr) := fresh_cargs_impl p ups ρ gs (S s) _ in
      exist _ (⇑! (d_ind p (ups ++ bs)) s :: fst r, bs :: snd r) _.
  Solve All Obligations with fr_obl.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations fresh_ihs_impl ρ A gs vs bss s (H : fresh_ihs_order Θ Ξ ρ A gs vs bss s) :
    { ihs | fresh_ihs Θ Ξ ρ A gs vs bss s ihs } by struct H :=
  | ρ, A, nil, nil, nil, s, H => exist _ nil _
  | ρ, A, ca_arg T :: gs, v :: vs, bss, s, H =>
      let (ihs, Hihs) := fresh_ihs_impl ρ A gs vs bss s _ in
      exist _ ihs _
  | ρ, A, ca_rec Ps :: gs, v :: vs, bs :: bss, s, H =>
      let (t, Ht) := eval_exp_impl Θ Ξ A (env_args ρ (bs ++ v :: nil)) _ in
      let (ihs, Hihs) := fresh_ihs_impl ρ A gs vs bss (S s) _ in
      exist _ (⇑! t s :: ihs) _
  | ρ, A, _, _, _, s, H => False_rect _ _.
  Solve All Obligations with fr_obl.
End FreshImpl.

(** ** The Orders of Readback *)

Inductive read_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| rnf_type :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
| rnf_stype :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌@n a )
| rnf_lvl :
  `( read_la_order Θ Ξ s xs ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
| rnf_lvl_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
| rnf_zero :
  `( read_nf_order Θ Ξ s ⇓ ℕᵈ zeroᵈ )
| rnf_succ :
  `( read_nf_order Θ Ξ s ⇓ ℕᵈ m ->
     read_nf_order Θ Ξ s ⇓ ℕᵈ (succᵈ m) )
| rnf_nat_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ ℕᵈ (⇑ a m) )
| rnf_true :
  `( read_nf_order Θ Ξ s ⇓ ⊤ᵈ m )
| rnf_False_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ ⊥ᵈ (⇑ a m) )
| rnf_fn :
  `( read_typ_order Θ Ξ s a ->
     eval_app_order Θ Ξ m ⇑! a s ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall m' b,
         $| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_nf_order Θ Ξ (S s) ⇓ b m') ->
     read_nf_order Θ Ξ s ⇓ (Πᵈ a p B) m )
| rnf_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (⇑ a b) (⇑ c m) )
| rnf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length as' = ind_np D ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     read_ps_order Θ Ξ s nil (List.rev (ind_params D)) as' ->
     read_cargs_order Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) ->
     read_nf_order Θ Ξ s ⇓ (d_ind p as') (d_con p c vs) )
| rnf_ind_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (d_ind p as') (⇑ a m) )

with read_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
| rne_var :
  `( read_ne_order Θ Ξ s #ᵈ x )
| rne_app :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s n ->
     read_ne_order Θ Ξ s (m $ᵈ n) )
| rne_natrec :
  `( eval_exp_order Θ Ξ B (p ↦ ⇑! ℕᵈ s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     eval_exp_order Θ Ξ B (p ↦ zeroᵈ) ->
     (forall bz,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ zeroᵈ ↘ bz ->
         read_nf_order Θ Ξ s ⇓ bz mz) ->
     eval_exp_order Θ Ξ B (p ↦ succᵈ (⇑! ℕᵈ s)) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         eval_exp_order Θ Ξ MS (p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s))) ->
     (forall b bs ms,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
         ⟦ MS ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
         read_nf_order Θ Ξ (S (S s)) ⇓ bs ms) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s recᵈ m under p return B | zero -> mz | succ -> MS end )
| rne_exfalso :
  `( eval_exp_order Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ⊥ᵈ s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s efqᵈ m under p return B )
| rne_glob :
  `( read_ne_order Θ Ξ s (d_glob p) )
| rne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     Nat.eqb nm (S (ind_nn D)) = true ->
     fresh_tele_order Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ->
     (forall ns,
         fresh_tele Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         eval_exp_order Θ Ξ A (env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil))) ->
     (forall ns a,
         fresh_tele Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil) ↘ a ->
         read_typ_order Θ Ξ (S (s + ind_nn D)) a) ->
     read_brs_order Θ Ξ s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s (d_elim ρ nm A Bs p as' m) )

with read_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| rtyp_univ :
  `( read_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| rtyp_suniv :
  `( read_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     read_typ_order Θ Ξ s 𝕌@l )
| rtyp_level :
  `( read_typ_order Θ Ξ s (Levelᵈ@n) )
| rtyp_nat :
  `( read_typ_order Θ Ξ s ℕᵈ )
| rtyp_True :
  `( read_typ_order Θ Ξ s ⊤ᵈ )
| rtyp_False :
  `( read_typ_order Θ Ξ s ⊥ᵈ )
| rtyp_pi :
  `( read_typ_order Θ Ξ s a ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_typ_order Θ Ξ s Πᵈ a p B)
| rtyp_neut :
  `( read_ne_order Θ Ξ s b ->
    read_typ_order Θ Ξ s ⇑ a b )
| rtyp_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     read_ps_order Θ Ξ s nil (List.rev (ind_params D)) as' ->
     read_typ_order Θ Ξ s (d_ind p as') )

with read_la_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> Prop :=
| rla_nil :
  `( read_la_order Θ Ξ s nil )
| rla_cons :
  `( read_ne_order Θ Ξ s m ->
     read_la_order Θ Ξ s xs ->
     read_la_order Θ Ξ s ((k, n, m) :: xs) )

with read_ps_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> Prop :=
| rps_nil :
  `( read_ps_order Θ Ξ s ρ nil nil )
| rps_cons :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_ps_order Θ Ξ s (ρ ↦ v) T vs ->
     read_ps_order Θ Ξ s ρ (ce_ass A :: T) (v :: vs) )

with read_cargs_order (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> Prop :=
| rcargs_nil :
  `( read_cargs_order Θ Ξ s p ups ρ nil nil )
| rcargs_arg :
  `( eval_exp_order Θ Ξ A ρ ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> read_nf_order Θ Ξ s ⇓ a v) ->
     read_cargs_order Θ Ξ s p ups (ρ ↦ v) gs vs ->
     read_cargs_order Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) )
| rcargs_rec :
  `( eval_exps_order Θ Ξ Ps ρ ->
     (forall bs, ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs -> read_nf_order Θ Ξ s ⇓ (d_ind p (ups ++ bs)) v) ->
     read_cargs_order Θ Ξ s p ups ρ gs vs ->
     read_cargs_order Θ Ξ s p ups ρ (ca_rec Ps :: gs) (v :: vs) )

with read_brs_order (Θ : gdeps) (Ξ : gstack) : nat -> env -> exp -> qname -> ind_decl -> list domain ->
                                            list (string * list carg) -> list (string * nat * exp) -> Prop :=
| rbrs_nil :
  `( read_brs_order Θ Ξ s ρ A p D ups nil nil )
| rbrs_cons :
  `( Nat.eqb n (ind_nn D + List.length gs + cargs_nrec gs)%nat = true ->
     fresh_tele_order Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ->
     (forall ns,
         fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         fresh_cargs_order Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D)) ->
     (forall ns vs bss,
         fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         fresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         List.Forall (fun bs => List.length bs = ind_nn D) bss) ->
     (forall ns vs bss,
         fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         fresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         fresh_ihs_order Θ Ξ ρ A gs vs bss (s + ind_nn D + List.length gs)) ->
     (forall ns vs bss,
         fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         fresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         eval_exp_order Θ Ξ A (env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil))) ->
     (forall ns vs bss ihs,
         fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         fresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         fresh_ihs Θ Ξ ρ A gs vs bss (s + ind_nn D + List.length gs) ihs ->
         eval_exp_order Θ Ξ B (env_args ρ (ns ++ vs ++ ihs))) ->
     (forall ns vs bss ihs b t,
         fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
         fresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) vs bss ->
         fresh_ihs Θ Ξ ρ A gs vs bss (s + ind_nn D + List.length gs) ihs ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ ihs) ↘ b ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil) ↘ t ->
         read_nf_order Θ Ξ (s + n) ⇓ t b) ->
     read_brs_order Θ Ξ s ρ A p D ups cs Bs ->
     read_brs_order Θ Ξ s ρ A p D ups ((c, gs) :: cs) ((c, n, B) :: Bs) ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order read_la_order
  read_ps_order read_cargs_order read_brs_order : mctt.

Lemma read_nf_order_sound : forall Θ Ξ s d m,
    Rnf d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_nf_order Θ Ξ s d
with read_ne_order_sound : forall Θ Ξ s d m,
    Rne d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_ne_order Θ Ξ s d
with read_typ_order_sound : forall Θ Ξ s d m,
    Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_typ_order Θ Ξ s d
with read_la_order_sound : forall Θ Ξ s xs ys,
    Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    read_la_order Θ Ξ s xs
with read_ps_order_sound : forall Θ Ξ s ρ T vs Ms,
    Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
    read_ps_order Θ Ξ s ρ T vs
with read_cargs_order_sound : forall Θ Ξ s p ups ρ gs vs Ms,
    read_cargs Θ Ξ s p ups ρ gs vs Ms ->
    read_cargs_order Θ Ξ s p ups ρ gs vs
with read_brs_order_sound : forall Θ Ξ s ρ A p D ups cs Bs Bs',
    read_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
    read_brs_order Θ Ξ s ρ A p D ups cs Bs.
Proof.
  all: [> clear read_nf_order_sound | clear read_ne_order_sound | clear read_typ_order_sound
       | clear read_la_order_sound | clear read_ps_order_sound | clear read_cargs_order_sound
       | clear read_brs_order_sound ];
    induction 1;
    (econstructor; try eassumption; try (apply Nat.eqb_eq; assumption);
     intros; functional_eval_rewrite_clear; functional_fresh_rewrite_clear;
     functional_eval_rewrite_clear; mauto).
Qed.

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound read_la_order_sound
  read_ps_order_sound read_cargs_order_sound read_brs_order_sound : mctt.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : read_la_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ps_order _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_cargs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  | H : read_brs_order _ _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

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
    let (ys, Hys) := read_la_impl s xs _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, ⇓ (Levelᵈ@n) (⇑ a m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ (lvⁿ oz (la_cons 0 (dsort a) M la_nil)) _
| s, ⇓ ℕᵈ zeroᵈ, H => exist _ zeroⁿ _
| s, ⇓ ℕᵈ (succᵈ m) , H =>
    let (M, HM) := read_nf_impl s ⇓ ℕᵈ m _ in
    exist _ succⁿ M _
| s, ⇓ ℕᵈ (⇑ _ m)  , H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _
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
| s, ⇓ (d_ind p as') (d_con p' c vs), H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed with inspect (ind_con D c) := {
    | exist _ (Some gs) Ec =>
        let (Ps, HPs) := read_ps_impl s nil (List.rev (ind_params D)) as' _ in
        let (Args, HArgs) := read_cargs_impl s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) _ in
        exist _ (nf_con p c (nfs_app Ps Args)) _
    | exist _ None Ec => False_rect _ _ }
  | exist _ None Ed => False_rect _ _ }
| s, ⇓ (d_ind p as') (⇑ a m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _

  with read_ne_impl s d (H : read_ne_order Θ Ξ s d) : { m | Rne d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, H => exist _ #ⁿ (s - x - 1) _
| s, d_glob p, H => exist _ (ne_glob p) _
| s, m $ᵈ n, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (N, HN) := read_nf_impl s n _ in
    exist _ (M $ⁿ N) _
| s, recᵈ m under p return B | zero -> mz | succ -> MS end, H =>
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! ℕᵈ s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (bz, Hbz) := eval_exp_impl Θ Ξ B (p ↦ zeroᵈ) _ in
    let (MZ, HMZ) := read_nf_impl s ⇓ bz mz _ in
    let (bs, Hbs) := eval_exp_impl Θ Ξ B (p ↦ succᵈ (⇑! ℕᵈ s)) _ in
    let (ms, Hms) := eval_exp_impl Θ Ξ MS (p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s)) _ in
    let (MS', HMS') := read_nf_impl (S (S s)) ⇓ bs ms _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ recⁿ M return B' | zero -> MZ | succ -> MS' end _
| s, efqᵈ m under p return B, H =>
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ (efqⁿ M return B') _
| s, d_elim ρ nm A Bs p as' m, H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed =>
      let (ns, Hns) := fresh_tele_impl Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s _ in
      let (a, Ha) := eval_exp_impl Θ Ξ A (env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil)) _ in
      let (A', HA') := read_typ_impl (S (s + ind_nn D)) a _ in
      let (Bs', HBs') := read_brs_impl s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs _ in
      let (M, HM) := read_ne_impl s m _ in
      exist _ (ne_elim nm A' Bs' M) _
  | exist _ None Ed => False_rect _ _ }

      with read_typ_impl s d (H : read_typ_order Θ Ξ s d) : { m | Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, H =>
    let (W, HW) := read_nf_impl s ⇓ Levelᵈ l _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, Levelᵈ@n, H => exist _ (Levelⁿ@n) _
| s, ℕᵈ, H => exist _ ℕⁿ _
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
| s, d_ind p as', H with inspect (ind_lookup Θ Ξ p) := {
  | exist _ (Some D) Ed =>
      let (Ps, HPs) := read_ps_impl s nil (List.rev (ind_params D)) as' _ in
      exist _ (nf_indty p Ps) _
  | exist _ None Ed => False_rect _ _ }

  with read_la_impl s xs (H : read_la_order Θ Ξ s xs) : { ys | Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, H => exist _ la_nil _
| s, cons (k, n, m) xs, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (ys, Hys) := read_la_impl s xs _ in
    exist _ (la_cons k n M ys) _

  with read_ps_impl s ρ T vs (H : read_ps_order Θ Ξ s ρ T vs) : { Ms | Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms } by struct H :=
| s, ρ, nil, nil, H => exist _ nfs_nil _
| s, ρ, ce_ass A :: T, v :: vs, H =>
    let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := read_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := read_ps_impl s (ρ ↦ v) T vs _ in
    exist _ (nfs_cons V Vs) _
| s, ρ, _, _, H => False_rect _ _

  with read_cargs_impl s p ups ρ gs vs (H : read_cargs_order Θ Ξ s p ups ρ gs vs) :
    { Ms | read_cargs Θ Ξ s p ups ρ gs vs Ms } by struct H :=
| s, p, ups, ρ, nil, nil, H => exist _ nfs_nil _
| s, p, ups, ρ, ca_arg A :: gs, v :: vs, H =>
    let (a, Ha) := eval_exp_impl Θ Ξ A ρ _ in
    let (V, HV) := read_nf_impl s ⇓ a v _ in
    let (Vs, HVs) := read_cargs_impl s p ups (ρ ↦ v) gs vs _ in
    exist _ (nfs_cons V Vs) _
| s, p, ups, ρ, ca_rec Ps :: gs, v :: vs, H =>
    let (bs, Hbs) := eval_exps_impl Θ Ξ Ps ρ _ in
    let (V, HV) := read_nf_impl s ⇓ (d_ind p (ups ++ bs)) v _ in
    let (Vs, HVs) := read_cargs_impl s p ups ρ gs vs _ in
    exist _ (nfs_cons V Vs) _
| s, p, ups, ρ, _, _, H => False_rect _ _

  with read_brs_impl s ρ A p D ups cs Bs (H : read_brs_order Θ Ξ s ρ A p D ups cs Bs) :
    { Bs' | read_brs Θ Ξ s ρ A p D ups cs Bs Bs' } by struct H :=
| s, ρ, A, p, D, ups, nil, nil, H => exist _ nbrs_nil _
| s, ρ, A, p, D, ups, (c, gs) :: cs, (c', n, B) :: Bs, H =>
    let (ns, Hns) := fresh_tele_impl Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s _ in
    let (r, Hr) := fresh_cargs_impl Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D) _ in
    let (ihs, Hihs) := fresh_ihs_impl Θ Ξ ρ A gs (fst r) (snd r) (s + ind_nn D + List.length gs) _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (env_args ρ (ns ++ fst r ++ ihs)) _ in
    let (t, Ht) := eval_exp_impl Θ Ξ A (env_args ρ (ns ++ d_con p c (ups ++ ns ++ fst r) :: nil)) _ in
    let (B', HB') := read_nf_impl (s + n) ⇓ t b _ in
    let (Bs', HBs') := read_brs_impl s ρ A p D ups cs Bs _ in
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
  | |- read_nf_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- read_ne_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- read_typ_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- read_la_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- read_ps_order _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- read_cargs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- read_brs_order _ _ _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fresh_tele_order _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fresh_cargs_order _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- fresh_ihs_order _ _ _ _ _ _ _ _ => first [ rb_ord | rb_run ]
  | |- eval_exp_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- eval_exps_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- eval_app_order _ _ _ _ => first [ rb_ord | rb_run ]
  | |- _ => abstract (first [ rb_ord | rb_run | eapply read_typ_suniv_of_nf; eassumption | rb_ind ])
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

Lemma read_la_impl_complete : forall s xs ys,
    Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    exists H H', read_la_impl s xs H = exist _ ys H'.
Proof.
  intros; functional_read_complete.
Qed.

End ReadbackImpl.
