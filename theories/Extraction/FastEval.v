(** * The Evaluation the Extracted Checker Runs

    A copy of the evaluation relations ([Core.Semantic.Evaluation]) and of
    readback ([Core.Semantic.Readback]) with one rule changed: the
    eliminator of an inductive type at a constructor computes the recursive
    result of a recursive argument only when the branch reads it, that is,
    when its variable is not fresh in the branch ([exp_freshb]); an unused
    entry is [𝕌ω@0] ([feval_ihs_skip]).

    The decision is syntactic and builds nothing.  Readback is copied
    because it evaluates closures.

    The values of the two evaluations agree except in the entries of
    environments that nothing reads: [Extraction.Simulation] makes this
    precise and proves that both read back to the same normal forms, so the
    normalizer built on this evaluation ([Extraction.NbE]) meets the
    specification [nbe] of the reference one. *)
From Stdlib Require Import Lia List Morphisms PeanoNat Relations String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Fresh Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Open Scope bool_scope.

(** ** Deciding Freshness *)

(** Freshness of a term is decided by a boolean function with the same
    clauses as [exp_fresh]: evaluation consults it, to skip a value that the
    term it evaluates next never reads. *)
Fixpoint exp_freshb (k : nat) (M : exp) {struct M} : bool :=
  match M with
  | a_typ _ | a_level _ | a_llit _
  | a_True | a_true | a_False => true
  | a_univ M | a_succl M => exp_freshb k M
  | a_maxl M N | a_app M N => exp_freshb k M && exp_freshb k N
  | a_exfalso A M => exp_freshb (S k) A && exp_freshb k M
  | a_ind _ | a_con _ _ | a_nlit _ | a_ntok => true
  | a_elim nm A Bs M =>
      exp_freshb (nm + k) A &&
      (fix brs_freshb (Bs : list (string * nat * exp)) : bool :=
         match Bs with
         | nil => true
         | cons b Bs' => exp_freshb (snd (fst b) + k) (snd b) && brs_freshb Bs'
         end) Bs &&
      exp_freshb k M
  | a_pi A B | a_fn A B => exp_freshb k A && exp_freshb (S k) B
  | a_var x => negb (Nat.eqb x k)
  | a_let b B => bnd_freshb k b && exp_freshb (S k) B
  | a_mem H _ => modexp_freshb k H
  end
with modexp_freshb (k : nat) (H : modexp) {struct H} : bool :=
  match H with
  | me_unit _ => true
  | me_var x => negb (Nat.eqb x k)
  | me_mem H _ => modexp_freshb k H
  | me_app H N => modexp_freshb k H && exp_freshb k N
  | me_lit U => gunit_freshb k U
  end
with bnd_freshb (k : nat) (b : bnd) {struct b} : bool :=
  match b with
  | b_def oA M => match oA with Some A => exp_freshb k A | None => true end && exp_freshb k M
  | b_mod U => gunit_freshb k U
  end
with gunit_freshb (k : nat) (U : gunit) {struct U} : bool :=
  match U with
  | gu_mk Δ D =>
      (fix tele_freshb (Δ : list centry) : bool :=
         match Δ with
         | nil => true
         | cons e Δ' => centry_freshb (List.length Δ' + k) e && tele_freshb Δ'
         end) Δ
      && moddef_freshb (List.length Δ + k) D
  end
with moddef_freshb (k : nat) (D : moddef) {struct D} : bool :=
  match D with
  | md_body Φ => gmod_freshb k Φ
  | md_alias E => modexp_freshb k E
  end
with gmod_freshb (k : nat) (Φ : gmod) {struct Φ} : bool :=
  match Φ with
  | gm_nil => true
  | gm_ext Φ _ E => gmod_freshb k Φ && gentry_freshb (gm_binders Φ + k) E
  | gm_open Φ H _ => gmod_freshb k Φ && modexp_freshb (gm_binders Φ + k) H
  end
with gentry_freshb (k : nat) (E : gentry) {struct E} : bool :=
  match E with
  | ge_def _ _ A B => exp_freshb k A && match B with Some M => exp_freshb k M | None => true end
  | ge_mod _ U => gunit_freshb k U
  | ge_ind _ D Φ => gmod_freshb (ind_nu D + k) Φ
  | ge_ind_alias _ _ _ _ => true
  end
with centry_freshb (k : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass A => exp_freshb k A
  | ce_def A M => exp_freshb k A && exp_freshb k M
  | ce_mod U => gunit_freshb k U
  end.

Lemma freshb_sound :
  (forall M k, exp_freshb k M = true -> exp_fresh k M) /\
  (forall H k, modexp_freshb k H = true -> modexp_fresh k H) /\
  (forall b k, bnd_freshb k b = true -> bnd_fresh k b) /\
  (forall U k, gunit_freshb k U = true -> gunit_fresh k U) /\
  (forall D k, moddef_freshb k D = true -> moddef_fresh k D) /\
  (forall Φ k, gmod_freshb k Φ = true -> gmod_fresh k Φ) /\
  (forall E k, gentry_freshb k E = true -> gentry_fresh k E) /\
  (forall e k, centry_freshb k e = true -> centry_fresh k e).
Proof.
  apply (syn_mut_ind
           (fun M => forall k, exp_freshb k M = true -> exp_fresh k M)
           (fun H => forall k, modexp_freshb k H = true -> modexp_fresh k H)
           (fun b => forall k, bnd_freshb k b = true -> bnd_fresh k b)
           (fun U => forall k, gunit_freshb k U = true -> gunit_fresh k U)
           (fun D => forall k, moddef_freshb k D = true -> moddef_fresh k D)
           (fun Φ => forall k, gmod_freshb k Φ = true -> gmod_fresh k Φ)
           (fun E => forall k, gentry_freshb k E = true -> gentry_fresh k E)
           (fun e => forall k, centry_freshb k e = true -> centry_fresh k e));
    intros; cbn in *; repeat rewrite Bool.andb_true_iff in *; destruct_conjs;
    try solve [ auto | split; auto | repeat split; auto
              | apply Bool.negb_true_iff, Nat.eqb_neq in H; assumption
              | apply Bool.negb_true_iff, Nat.eqb_neq in H0; assumption ].
  - (* an eliminator: its branches, one by one *)
    apply (proj2 (exp_fresh_elim k nm A Bs M)); split; [ auto | split; [| auto ] ].
    match goal with HF : List.Forall _ Bs, Hb : _ Bs = true |- _ =>
      clear - HF Hb; induction HF as [| b Bs Hb' HF IH]; cbn in *; [ constructor |];
      apply Bool.andb_true_iff in Hb as [Hb1 Hb2]; constructor; [ apply Hb'; exact Hb1 | apply IH; exact Hb2 ] end.
  - (* a binding *) destruct oA; split; eauto.
  - (* a unit: its telescope, entry by entry *)
    split; [| auto ].
    clear H2 H0; induction H as [| e Δ' He HΔ' IHΔ]; cbn in *; [ exact I |].
    apply Bool.andb_true_iff in H1 as [H1 H1']; split; [ apply He; exact H1 | apply IHΔ; exact H1' ].
  - (* a global entry *) destruct B; split; eauto.
Qed.

Lemma exp_freshb_sound : forall M k, exp_freshb k M = true -> exp_fresh k M.
Proof. exact (proj1 freshb_sound). Qed.

(** ** The Relations *)

Reserved Notation "'⟦' M '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$ᶠ|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦elimᶠ' m 'under' nm A Bs '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, nm at level 0, A at level 0, Bs at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihsᶠ' vs 'of' gs 'under' nm A Bs 'for' B '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, nm at level 0, A at level 0, Bs at level 0, B at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).

Reserved Notation "'⟦' H '⟧ᵐᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, H at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦' Ms '⟧*ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ms" (at level 70, Ms at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ms at level 69).
Reserved Notation "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" (at level 70, Φ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρ' at level 69).
Reserved Notation "'$*ᶠ|' m '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐᶠ|' h '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₜᶠ' x Θ '⍮' Ξ '↘' r" (at level 70, x at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘᶠ' y Θ '⍮' Ξ '↘' r" (at level 70, y at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₜ*ᶠ' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘ*ᶠ' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).

Generalizable All Variables.

(** The rules of [Core.Semantic.Evaluation], one for one, but for the two
    rules of the eliminator at a successor and the two rules of a recursive
    argument's result. *)
Inductive feval_exp (Θ : gdeps) (Ξ : gstack) : exp -> env -> domain -> Prop :=
(** A universe is its own value. *)
| feval_exp_typ :
  `( ⟦ Typeω@i ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌ω@i )
(** A small universe evaluates its level. *)
| feval_exp_univ :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ l ->
     ⟦ Type⟨M⟩ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌@l )
(** [Level] is a value. *)
| feval_exp_level :
  `( ⟦ Level@n ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Levelᵈ@n )
(** A level literal is the flat level with that constant and no atom. *)
| feval_exp_llit :
  `( ⟦ 𝕃ᵒ o ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ dlvl_lit o )
(** The level operations only flatten: they add to the offsets, or join the
    constants and concatenate the atoms.  Canonicalisation is readback's. *)
| feval_exp_succl :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succl M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ dlvl_suc m )
| feval_exp_maxl :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     ⟦ maxl M N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ dlvl_max m n )
(** A variable is read off the environment. *)
| feval_exp_var :
  `( ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ x )
(** [⊤] is a value. *)
| feval_exp_True :
  `( ⟦ ⊤ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⊤ᵈ )
(** So is [⋆]. *)
| feval_exp_true :
  `( ⟦ ⋆ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** [⊥] is a value. *)
| feval_exp_False :
  `( ⟦ ⊥ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⊥ᵈ )
(** [⊥] has no canonical values, so the eliminator only meets a neutral. *)
| feval_exp_exfalso :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ b m ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦ efq M return A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (efqᵈ m under ρ return A) )
(** The type former and a constructor of an inductive type are values,
    with no argument yet. *)
| feval_exp_indty :
  `( ⟦ a_ind p ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_ind p nil )
| feval_exp_con :
  `( ⟦ a_con p c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con p c nil )
(** The eliminator evaluates its scrutinee, then eliminates the value. *)
| feval_exp_elim :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ a_elim nm A Bs M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A [Π] evaluates its domain and closes over its codomain. *)
| feval_exp_pi :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ a ρ B )
(** A function closes over its body. *)
| feval_exp_fn :
  `( ⟦ λ A M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ ρ M )
(** An application applies the value of the function to that of the argument. *)
| feval_exp_app :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $ᶠ| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local definition extends the environment by the value of its body;
    nothing is substituted. *)
| feval_exp_let :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ m ↘ r ->
     ⟦ a_let (b_def oA M) B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local module extends it by the unit's closure. *)
| feval_exp_let_mod :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ᵐ dm_local ρ U nil ↘ r ->
     ⟦ ℓₘ U in B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A member is read off the root of its module expression, then applied to
    the module's arguments: arguments commute with selection.  Without
    arguments this is selection from the module's value. *)
| feval_exp_mem :
  `( modexp_spine H = (R, args, pre) ->
     ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₜ*ᶠ (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
     ⟦ args ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ns ->
     $*ᶠ| f & ns | Θ ⍮ Ξ ↘ r ->
     ⟦ a_mem H x ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' e '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_exp Θ Ξ e ρ r)
(** The eliminator of an inductive type, as in [Core.Semantic.Evaluation]. *)
with feval_elim (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> domain -> domain -> Prop :=
| feval_elim_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     brs_lookup Bs c = Some (n, B) ->
     n = (ind_nn D + List.length gs + cargs_nrec gs)%nat ->
     ⟦ihsᶠ skipn (ind_np D) vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs) ↘ r ->
     ⟦elimᶠ d_con p c vs under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
| feval_elim_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     nm = S (ind_nn D) ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu D) as' ++ ⇑ (d_ind p as') m :: nil) ↘ a ->
     ⟦elimᶠ ⇑ (d_ind p as') m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_elim ρ nm A Bs p as' m) )
where "'⟦elimᶠ' m 'under' nm A Bs '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_elim Θ Ξ ρ nm A Bs m r)
(** The recursive results of the arguments [vs] of a constructor, for the
    branch [B]: the entry of a recursive argument is computed only when [B]
    reads it.  The entry of the recursive argument at the head of
    [ca_rec t :: gs] is the variable [cargs_nrec gs] of [B], since the
    results of the recursive arguments after it come after it in [B]'s
    environment. *)
with feval_ihs (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> exp -> list carg -> list domain -> list domain -> Prop :=
| feval_ihs_nil :
  `( ⟦ihsᶠ nil of nil under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
| feval_ihs_arg :
  `( ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_arg T :: gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs )
(** The branch reads the recursive result: it is computed. *)
| feval_ihs_rec :
  `( exp_freshb (cargs_nrec gs) B = false ->
     feval_ih Θ Ξ ρ nm A Bs t v ih ->
     ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_rec t :: gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ih :: ihs )
(** It does not: the entry is [𝕌ω@0], which nothing reads. *)
| feval_ihs_skip :
  `( exp_freshb (cargs_nrec gs) B = true ->
     ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_rec t :: gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌ω@0 :: ihs )
where "'⟦ihsᶠ' vs 'of' gs 'under' nm A Bs 'for' B '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_ihs Θ Ξ ρ nm A Bs B gs vs r)
(** The recursive result of an argument of a shape, the type of an argument
    of a shape and the type of its recursive result, as in
    [Core.Semantic.Evaluation]. *)
with feval_ih (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> ptyp -> domain -> domain -> Prop :=
| feval_ih_self :
  `( ⟦elimᶠ v under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     feval_ih Θ Ξ ρ nm A Bs (pt_self k Ps) v r )
| feval_ih_pi :
  `( feval_ih Θ Ξ ρ nm A Bs (pt_pi B t) v (d_ihfn ρ nm A Bs t v) )
with feval_shty (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> domain -> Prop :=
| feval_shty_self :
  `( ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     feval_shty Θ Ξ p ups ρ (pt_self k Ps) (d_ind p (ups ++ bs)) )
| feval_shty_pi :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     feval_shty Θ Ξ p ups ρ (pt_pi B t) (Πᵈ b (nil ↦ d_shfam p ups ρ t) fam_cod) )
with feval_ihty (Θ : gdeps) (Ξ : gstack) : env -> exp -> env -> ptyp -> domain -> domain -> Prop :=
| feval_ihty_self :
  `( ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρm (bs ++ v :: nil) ↘ a ->
     feval_ihty Θ Ξ ρm A ρ (pt_self k Ps) v a )
| feval_ihty_pi :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     feval_ihty Θ Ξ ρm A ρ (pt_pi B t) v (Πᵈ b (nil ↦ d_ihfam ρm A ρ t v) fam_cod) )
with feval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
(** A function's body, at the argument. *)
| feval_app_fn :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $ᶠ| λᵈ ρ M & n | Θ ⍮ Ξ ↘ m )
(** A neutral applied, at the codomain's instance. *)
| feval_app_neut :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $ᶠ| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** The type former takes a parameter it still lacks. *)
| feval_app_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' < ind_np D ->
     $ᶠ| d_ind p as' & n | Θ ⍮ Ξ ↘ d_ind p (as' ++ n :: nil) )
(** So does a constructor, a parameter or an argument. *)
| feval_app_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length vs < (ind_np D + List.length gs)%nat ->
     $ᶠ| d_con p c vs & n | Θ ⍮ Ξ ↘ d_con p c (vs ++ n :: nil) )
(** The recursive result of a function shape, and the families of the types
    of an argument of a function shape and of its recursive result. *)
| feval_app_ihfn :
  `( $ᶠ| f & n | Θ ⍮ Ξ ↘ fn ->
     feval_ih Θ Ξ ρ nm A Bs t fn r ->
     $ᶠ| d_ihfn ρ nm A Bs t f & n | Θ ⍮ Ξ ↘ r )
| feval_app_shfam :
  `( feval_shty Θ Ξ p ups (ρ ↦ n) t a ->
     $ᶠ| d_shfam p ups ρ t & n | Θ ⍮ Ξ ↘ a )
| feval_app_ihfam :
  `( $ᶠ| f & n | Θ ⍮ Ξ ↘ fn ->
     feval_ihty Θ Ξ ρm A (ρ ↦ n) t fn a ->
     $ᶠ| d_ihfam ρm A ρ t f & n | Θ ⍮ Ξ ↘ a )
(** A member closure takes the next argument of its module, and selects again. *)
| feval_app_member :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     $ᶠ| d_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$ᶠ|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (feval_app Θ Ξ m n r)
with feval_exps (Θ : gdeps) (Ξ : gstack) : list exp -> env -> list domain -> Prop :=
(** No terms. *)
| feval_exps_nil :
  `( ⟦ nil ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A term, then the rest. *)
| feval_exps_cons :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms ->
     ⟦ M :: Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m :: ms )
where "'⟦' Ms '⟧*ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ms" := (feval_exps Θ Ξ Ms ρ ms)
with feval_apps (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> domain -> Prop :=
(** No arguments. *)
| feval_apps_nil :
  `( $*ᶠ| m & nil | Θ ⍮ Ξ ↘ m )
(** The first argument, then the rest. *)
| feval_apps_cons :
  `( $ᶠ| m & n | Θ ⍮ Ξ ↘ m1 ->
     $*ᶠ| m1 & args | Θ ⍮ Ξ ↘ r ->
     $*ᶠ| m & n :: args | Θ ⍮ Ξ ↘ r )
where "'$*ᶠ|' m '&' ns '|' Θ '⍮' Ξ '↘' r" := (feval_apps Θ Ξ m ns r)
with feval_modexp (Θ : gdeps) (Ξ : gstack) : modexp -> env -> dmod -> Prop :=
(** A module slot is read off the environment. *)
| feval_me_var :
  `( ⟦ me_var x ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ env_mod ρ x )
(** A unit is a global body module, with no argument yet.  Its submodules
    are selected from it ([feval_selm_global]). *)
| feval_me_unit :
  `( ⟦ me_unit fp ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_global (q_abs fp nil) nil )
(** A literal unit is its closure, with no argument yet. *)
| feval_me_lit :
  `( ⟦ me_lit U ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_local ρ U nil )
(** A submodule is selected from the module's value. *)
| feval_me_mem :
  `( ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₘᶠ y Θ ⍮ Ξ ↘ r ->
     ⟦ me_mem H y ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An application adds the argument's value to the module's. *)
| feval_me_app :
  `( ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r ->
     ⟦ me_app H N ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' H '⟧ᵐᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_modexp Θ Ξ H ρ r)
(** Applying a module value to one more argument, which it must still lack.
    A saturated alias is its target. *)
with feval_appm (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> dmod -> Prop :=
(** A global module records the argument. *)
| feval_appm_global :
  `( $ᵐᶠ| dm_global p args & n | Θ ⍮ Ξ ↘ dm_global p (args ++ n :: nil) )
(** A body unit lacking arguments records it. *)
| feval_appm_body :
  `( List.length args < List.length Δ ->
     $ᵐᶠ| dm_local ρ (gu_mk Δ (md_body Φ)) args & n | Θ ⍮ Ξ ↘ dm_local ρ (gu_mk Δ (md_body Φ)) (args ++ n :: nil) )
(** So does an alias unit lacking arguments. *)
| feval_appm_alias_unsat :
  `( List.length args < List.length Δ ->
     $ᵐᶠ| dm_local ρ (gu_mk Δ (md_alias E)) args & n | Θ ⍮ Ξ ↘
       dm_local ρ (gu_mk Δ (md_alias E)) (args ++ n :: nil) )
(** A saturated alias passes it to its target. *)
| feval_appm_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ h ->
     $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r ->
     $ᵐᶠ| dm_local ρ (gu_mk Δ (md_alias E)) args & n | Θ ⍮ Ξ ↘ r )
(** A submodule of an unsaturated module passes it to the module, then selects again. *)
| feval_appm_member :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     $ᵐᶠ| dm_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$ᵐᶠ|' h '&' n '|' Θ '⍮' Ξ '↘' r" := (feval_appm Θ Ξ h n r)
(** Selecting a term member.  A member of a global module is stored closed,
    over the module's parameters: δ evaluates a transparent one's body in the
    empty environment, and an opaque one or an axiom is a neutral at its
    (closed) type.  Either is then applied to the module's arguments. *)
with feval_sel (Θ : gdeps) (Ξ : gstack) : dmod -> string -> domain -> Prop :=
(** A transparent definition of a global module: its body, applied to the module's arguments. *)
| feval_sel_global :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def true pv A (Some M)) ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f ->
     $*ᶠ| f & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** An opaque definition or an axiom of a global module: a neutral, applied to the module's arguments. *)
| feval_sel_global_neut :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ a ->
     $*ᶠ| ⇑ a (d_glob (qname_app p (x :: nil))) & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** The module of an inductive type, as a term: the type former, applied to
    the module's arguments. *)
| feval_sel_global_ind :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_lookup Θ Ξ (qname_app p (x :: nil)) = Some D ->
     $*ᶠ| d_ind (qname_app p (x :: nil)) nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
| feval_sel_global_ind_alias :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_alias_lookup Θ Ξ (qname_app p (x :: nil)) = Some (Δ, pt, Ns) ->
     ⟦ ctx_fn Δ (apps (a_ind pt) Ns) ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f ->
     $*ᶠ| f & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A member of an unsaturated module is a member closure. *)
| feval_sel_unsat :
  `( List.length args < List.length (gu_params U) ->
     dm_local ρ U args ·ₜᶠ x Θ ⍮ Ξ ↘ d_member (dm_local ρ U args) (x :: nil) )
(** A definition of a saturated body: its body, in the environment of the body before it. *)
| feval_sel_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ ρ' ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local ρ (gu_mk Δ (md_body Φ)) args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A definition a local open of a saturated body declares: the member it
    names in the open's target, read in the environment of the body before
    the open. *)
| feval_sel_item :
  `( List.length args = List.length Δ ->
     gm_item_upto Φ x = Some (Φ0, H, its1, (Some n, d, pv)) ->
     ⟦ Φ0 ⟧ᵇᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ ρ0 ->
     ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ0 ↘ h ->
     h ·ₜᶠ n Θ ⍮ Ξ ↘ r ->
     dm_local ρ (gu_mk Δ (md_body Φ)) args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A member of a saturated alias is selected from its target. *)
| feval_sel_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ h ->
     h ·ₜᶠ x Θ ⍮ Ξ ↘ r ->
     dm_local ρ (gu_mk Δ (md_alias E)) args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A member of a submodule closure extends the chain. *)
| feval_sel_member :
  `( dm_member h ch ·ₜᶠ x Θ ⍮ Ξ ↘ d_member h (ch ++ x :: nil) )
where "h '·ₜᶠ' x Θ '⍮' Ξ '↘' r" := (feval_sel Θ Ξ h x r)
(** Selecting a submodule. *)
with feval_selm (Θ : gdeps) (Ξ : gstack) : dmod -> string -> dmod -> Prop :=
(** A body submodule of a global module is a global module, with the same arguments. *)
| feval_selm_global :
  `( (forall U r, gc_module Θ Ξ (qname_app p (y :: nil)) <> Some (mr_alias U r)) ->
     dm_global p args ·ₘᶠ y Θ ⍮ Ξ ↘ dm_global (qname_app p (y :: nil)) args )
(** An alias submodule of a global module is selected from the alias's closure. *)
| feval_selm_global_alias :
  `( gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U ch) ->
     dm_local nil U args ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₘᶠ y Θ ⍮ Ξ ↘ r )
(** A submodule of an unsaturated module is a submodule closure. *)
| feval_selm_unsat :
  `( List.length args < List.length (gu_params U) ->
     dm_local ρ U args ·ₘᶠ y Θ ⍮ Ξ ↘ dm_member (dm_local ρ U args) (y :: nil) )
(** A submodule of a saturated body is its unit's closure, in the environment of the body before it. *)
| feval_selm_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ ρ' ->
     dm_local ρ (gu_mk Δ (md_body Φ)) args ·ₘᶠ y Θ ⍮ Ξ ↘ dm_local ρ' Uy nil )
(** A module a local open of a saturated body declares: the target, or its
    member the item names. *)
| feval_selm_item :
  `( List.length args = List.length Δ ->
     gm_item_upto Φ y = Some (Φ0, H, its1, it) ->
     ⟦ Φ0 ⟧ᵇᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ ρ0 ->
     ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ0 ↘ h ->
     h ·ₘ*ᶠ (item_ch it nil) Θ ⍮ Ξ ↘ r ->
     dm_local ρ (gu_mk Δ (md_body Φ)) args ·ₘᶠ y Θ ⍮ Ξ ↘ r )
(** A submodule of a saturated alias is selected from its target. *)
| feval_selm_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ env_args ρ args ↘ h ->
     h ·ₘᶠ y Θ ⍮ Ξ ↘ r ->
     dm_local ρ (gu_mk Δ (md_alias E)) args ·ₘᶠ y Θ ⍮ Ξ ↘ r )
(** A submodule of a submodule closure extends the chain. *)
| feval_selm_member :
  `( dm_member h ch ·ₘᶠ y Θ ⍮ Ξ ↘ dm_member h (ch ++ y :: nil) )
where "h '·ₘᶠ' y Θ '⍮' Ξ '↘' r" := (feval_selm Θ Ξ h y r)
(** Selecting along a chain: submodules, then a term member. *)
with feval_selc (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> domain -> Prop :=
(** The last selection is a term member. *)
| feval_selc_one :
  `( h ·ₜᶠ x Θ ⍮ Ξ ↘ r ->
     h ·ₜ*ᶠ (x :: nil) Θ ⍮ Ξ ↘ r )
(** The ones before it are submodules. *)
| feval_selc_cons :
  `( h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 ->
     h1 ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     h ·ₜ*ᶠ (y :: ch) Θ ⍮ Ξ ↘ r )
where "h '·ₜ*ᶠ' ch Θ '⍮' Ξ '↘' r" := (feval_selc Θ Ξ h ch r)
with feval_selmc (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> dmod -> Prop :=
(** The empty chain is the module itself. *)
| feval_selmc_nil :
  `( h ·ₘ*ᶠ nil Θ ⍮ Ξ ↘ h )
(** A submodule, then the rest of the chain. *)
| feval_selmc_cons :
  `( h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 ->
     h1 ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     h ·ₘ*ᶠ (y :: ch) Θ ⍮ Ξ ↘ r )
where "h '·ₘ*ᶠ' ch Θ '⍮' Ξ '↘' r" := (feval_selmc Θ Ξ h ch r)
(** The environment the members of a body see after its entries [Φ]: each
    definition adds its value and each module its closure. *)
with feval_benv (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
(** The empty body adds nothing. *)
| feval_benv_nil :
  `( ⟦ gm_nil ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ )
(** A definition adds its value. *)
| feval_benv_def :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ gm_ext Φ y (ge_def b pv A (Some M)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ m )
(** A submodule adds its unit's closure. *)
| feval_benv_mod :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ gm_ext Φ y (ge_mod pm Uy) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵐ dm_local ρ1 Uy nil )
(** A local open adds the entries it generates, by the kinds of the members
    its items name. *)
| feval_benv_open :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     kgens Θ Ξ ρ1 H its gs ->
     ⟦ gens_append gm_nil 0 gs ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ ρ2 ->
     ⟦ gm_open Φ H its ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 )
where "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" := (feval_benv Θ Ξ ρ Φ ρ').

Scheme feval_exp_mut_ind := Induction for feval_exp Sort Prop
with feval_app_mut_ind := Induction for feval_app Sort Prop
with feval_exps_mut_ind := Induction for feval_exps Sort Prop
with feval_apps_mut_ind := Induction for feval_apps Sort Prop
with feval_modexp_mut_ind := Induction for feval_modexp Sort Prop
with feval_appm_mut_ind := Induction for feval_appm Sort Prop
with feval_sel_mut_ind := Induction for feval_sel Sort Prop
with feval_selm_mut_ind := Induction for feval_selm Sort Prop
with feval_selc_mut_ind := Induction for feval_selc Sort Prop
with feval_selmc_mut_ind := Induction for feval_selmc Sort Prop
with feval_benv_mut_ind := Induction for feval_benv Sort Prop
with feval_elim_mut_ind := Induction for feval_elim Sort Prop
with feval_ihs_mut_ind := Induction for feval_ihs Sort Prop
with feval_ih_mut_ind := Induction for feval_ih Sort Prop
with feval_shty_mut_ind := Induction for feval_shty Sort Prop
with feval_ihty_mut_ind := Induction for feval_ihty Sort Prop.
Combined Scheme feval_mut_ind from
  feval_exp_mut_ind,
  feval_app_mut_ind,
  feval_exps_mut_ind,
  feval_apps_mut_ind,
  feval_modexp_mut_ind,
  feval_appm_mut_ind,
  feval_sel_mut_ind,
  feval_selm_mut_ind,
  feval_selc_mut_ind,
  feval_selmc_mut_ind,
  feval_benv_mut_ind,
  feval_elim_mut_ind,
  feval_ihs_mut_ind,
  feval_ih_mut_ind,
  feval_shty_mut_ind,
  feval_ihty_mut_ind.

#[export]
Hint Constructors feval_exp feval_elim feval_ihs feval_ih feval_shty feval_ihty feval_app feval_exps feval_apps feval_modexp feval_appm feval_sel feval_selm
  feval_selc feval_selmc feval_benv : mctt.

(** [feval_exp_var] with the value as a premise.  The value [ρ x] is a flexible
    application, so unifying against it directly can pick the wrong [ρ] and
    [x]. *)
Proposition feval_exp_var_eq : forall {Θ Ξ} x (ρ : env) m,
    ρ x = m ->
    ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m.
Proof. intros * <-; apply feval_exp_var. Qed.


(** ** Determinism *)

  Lemma functional_feval : forall {Θ Ξ},
    (forall M ρ m1,
        ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
      (forall m n r1,
          $ᶠ| m & n | Θ ⍮ Ξ ↘ r1 ->
          forall r2,
            $ᶠ| m & n | Θ ⍮ Ξ ↘ r2 ->
            r1 = r2) /\
      (forall Ms ρ ms1, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> forall ms2, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2) /\
      (forall m args r1, $*ᶠ| m & args | Θ ⍮ Ξ ↘ r1 -> forall r2, $*ᶠ| m & args | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall H ρ h1, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall h n r1, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h x r1, h ·ₜᶠ x Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜᶠ x Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h y r1, h ·ₘᶠ y Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘᶠ y Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2) /\
      (forall ρ nm A Bs m r1,
          ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ nm A Bs B gs vs r1,
          ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ nm A Bs t v r1, feval_ih Θ Ξ ρ nm A Bs t v r1 -> forall r2, feval_ih Θ Ξ ρ nm A Bs t v r2 -> r1 = r2) /\
      (forall p ups ρ t a1, feval_shty Θ Ξ p ups ρ t a1 -> forall a2, feval_shty Θ Ξ p ups ρ t a2 -> a1 = a2) /\
      (forall ρm A ρ t v a1, feval_ihty Θ Ξ ρm A ρ t v a1 -> forall a2, feval_ihty Θ Ξ ρm A ρ t v a2 -> a1 = a2).
  Proof.
    intros Θ Ξ; apply feval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         two resolutions of a global or a module agree, and two neutral
         scrutinees of [efq] that are equal have equal parts; an induction
         hypothesis is never spent on the premise it is about *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : Members.gc_resolve Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_alias_lookup Θ Ξ ?p = Some _, H2 : ind_alias_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_alias_lookup Θ Ξ ?p = Some _ |- _ =>
            exfalso; destruct (ind_lookup_entry _ _ _ _ H1) as (? & ? & He1); rewrite ind_alias_lookup_entry, He1 in H2; discriminate H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _ _),
          H2 : forall U r, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U r) |- _ =>
            exfalso; exact (H2 _ _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
        | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : kgens Θ Ξ ?ρ ?H ?its ?g1, H2 : kgens Θ Ξ ?ρ ?H ?its ?g2 |- _ =>
            assert_fails (constr_eq g1 g2); pose proof (functional_kgens _ _ _ _ _ H1 H2); subst g2
        | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        | H : d_neut _ _ = d_neut _ _ |- _ => injection H; intros; subst; clear H
        | H : feval_selc _ _ _ nil _ |- _ => inversion H
        end;
      cbn [gu_params] in *; try congruence; try lia; intuition (try congruence; try lia).
  Qed.

  Corollary functional_feval_exp : forall {Θ Ξ} M ρ m1 m2,
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ); firstorder.
  Qed.

  Corollary functional_feval_app : forall {Θ Ξ} m n r1 r2,
      $ᶠ| m & n | Θ ⍮ Ξ ↘ r1 ->
      $ᶠ| m & n | Θ ⍮ Ξ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ); intuition.
  Qed.

  Corollary functional_feval_modexp : forall {Θ Ξ} H ρ h1 h2,
      ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h1 ->
      ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h2 ->
      h1 = h2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ); intuition.
  Qed.

  Corollary functional_feval_elim : forall {Θ Ξ} ρ nm A Bs m r1 r2,
      ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_feval_ihs : forall {Θ Ξ} ρ nm A Bs B gs vs r1 r2,
      ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_feval_ih : forall {Θ Ξ} ρ nm A Bs t v r1 r2,
      feval_ih Θ Ξ ρ nm A Bs t v r1 -> feval_ih Θ Ξ ρ nm A Bs t v r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_shty : forall {Θ Ξ} p ups ρ t a1 a2,
      feval_shty Θ Ξ p ups ρ t a1 -> feval_shty Θ Ξ p ups ρ t a2 -> a1 = a2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_ihty : forall {Θ Ξ} ρm A ρ t v a1 a2,
      feval_ihty Θ Ξ ρm A ρ t v a1 -> feval_ihty Θ Ξ ρm A ρ t v a2 -> a1 = a2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_exps : forall {Θ Ξ} Ms ρ ms1 ms2,
      ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); firstorder. Qed.

  Corollary functional_feval_benv : forall {Θ Ξ} ρ Φ ρ1 ρ2,
      ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
      ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 ->
      ρ1 = ρ2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto.
  Qed.

#[export]
Hint Resolve functional_feval_exp functional_feval_elim functional_feval_ihs functional_feval_ih
  functional_feval_shty functional_feval_ihty functional_feval_app functional_feval_modexp : mctt.



Ltac functional_feval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_feval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦elimᶠ ?m under ?nm ?A ?Bs ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦elimᶠ ?m under ?nm ?A ?Bs ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦ihsᶠ ?vs of ?gs under ?nm ?A ?Bs for ?B ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦ihsᶠ ?vs of ?gs under ?nm ?A ?Bs for ?B ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : feval_ih ?T ?X ?ρ ?nm ?A ?Bs ?t ?v ?r1, H2 : feval_ih ?T ?X ?ρ ?nm ?A ?Bs ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_ih; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_shty; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r1, H2 : feval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_ihty; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : (⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_exps; eassumption] | tactic_error r2 r1]; clear H2
  end.
(** There is no [feval_sub] case: [functional_feval_sub] gives only pointwise
    equality, so there is nothing to [replace]. *)
Ltac functional_feval_rewrite_clear := repeat functional_feval_rewrite_clear1.

(** ** Readback *)

Reserved Notation "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).
Reserved Notation "'Rpsᶠ' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).

Generalizable All Variables.

(** The fresh variables of the telescopes of an inductive type, as in
    [Core.Semantic.Readback]. *)
Inductive ffresh_tele (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> list domain -> Prop :=
| ffresh_tele_nil :
  `( ffresh_tele Θ Ξ ρ nil s nil )
| ffresh_tele_cons :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ffresh_tele Θ Ξ (ρ ↦ ⇑! a s) T (S s) vs ->
     ffresh_tele Θ Ξ ρ (ce_ass A :: T) s (⇑! a s :: vs) ).

Inductive ffresh_cargs (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> list domain -> Prop :=
| ffresh_cargs_nil :
  `( ffresh_cargs Θ Ξ p ups ρ nil s nil )
| ffresh_cargs_arg :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ffresh_cargs Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s) vs ->
     ffresh_cargs Θ Ξ p ups ρ (ca_arg A :: gs) s (⇑! a s :: vs) )
| ffresh_cargs_rec :
  `( feval_shty Θ Ξ p ups ρ t a ->
     ffresh_cargs Θ Ξ p ups ρ gs (S s) vs ->
     ffresh_cargs Θ Ξ p ups ρ (ca_rec t :: gs) s (⇑! a s :: vs) ).

(** The recursive results of a branch [B] of a stuck eliminator, as fresh
    variables: the type of one the branch does not read, the variable
    [cargs_nrec gs] of [B] for the argument heading [ca_rec t :: gs], is not
    computed; the variable gets [𝕌ω@0]. *)
Inductive ffresh_ihs (Θ : gdeps) (Ξ : gstack) (ρ : env) (A : exp) (B : exp) :
  env -> list carg -> list domain -> nat -> list domain -> Prop :=
| ffresh_ihs_nil :
  `( ffresh_ihs Θ Ξ ρ A B ρa nil nil s nil )
| ffresh_ihs_arg :
  `( ffresh_ihs Θ Ξ ρ A B (ρa ↦ v) gs vs s ihs ->
     ffresh_ihs Θ Ξ ρ A B ρa (ca_arg T :: gs) (v :: vs) s ihs )
| ffresh_ihs_rec :
  `( exp_freshb (cargs_nrec gs) B = false ->
     feval_ihty Θ Ξ ρ A ρa t v a ->
     ffresh_ihs Θ Ξ ρ A B ρa gs vs (S s) ihs ->
     ffresh_ihs Θ Ξ ρ A B ρa (ca_rec t :: gs) (v :: vs) s (⇑! a s :: ihs) )
| ffresh_ihs_skip :
  `( exp_freshb (cargs_nrec gs) B = true ->
     ffresh_ihs Θ Ξ ρ A B ρa gs vs (S s) ihs ->
     ffresh_ihs Θ Ξ ρ A B ρa (ca_rec t :: gs) (v :: vs) s (⇑! 𝕌ω@0 s :: ihs) ).

#[export]
Hint Constructors ffresh_tele ffresh_cargs ffresh_ihs : mctt.

(** Readback of values into normal and neutral forms in a context with [s]
    variables.  The global context is needed to evaluate closures. *)
Inductive fread_nf (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> nf -> Prop :=
| fread_nf_type :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ 𝕌ω@i a in Θ ⍮ Ξ ⍮ s ↘ A )
| fread_nf_stype :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ 𝕌@n a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A level reads back canonically: its atoms are read, then sorted and
    merged, and a dominated constant is dropped ([lvl_canon]).  Evaluation
    flattens only, so this is where levels equal by the level equations become
    the same normal form.  A neutral level is the single atom at offset [0],
    of the sort of its type ([dsort]), which is already canonical: the sort
    is read off the neutral's type, not off the type it is read back at. *)
| fread_nf_lvl :
  `( Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rnfᶠ ⇓ (Levelᵈ@n) (lvᵈ c xs) in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of (lvl_canon (c, ys)) )
| fread_nf_lvl_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (Levelᵈ@n) (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ lvⁿ oz (la_cons 0 (dsort a) M la_nil) )
(** η for [⊤]: every value of type [⊤] reads back as [⋆]. *)
| fread_nf_true :
  `( Rnfᶠ ⇓ ⊤ᵈ m in Θ ⍮ Ξ ⍮ s ↘ ⋆ⁿ )
| fread_nf_False_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ ⊥ᵈ (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
| fread_nf_fn :
  `( (** The normal form of the argument type. *)
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     (** The normal form of the η-expanded body. *)
     $ᶠ| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rnfᶠ ⇓ b m' in Θ ⍮ Ξ ⍮ S s ↘ M ->

     Rnfᶠ ⇓ (Πᵈ a ρ B) m in Θ ⍮ Ξ ⍮ s ↘ λⁿ A M )
| fread_nf_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (⇑ a b) (⇑ c m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
| fread_nf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length as' = ind_np D ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     Rpsᶠ as' at List.rev (ind_params D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     fread_cargs Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) Args ->
     Rnfᶠ ⇓ (d_ind p as') (d_con p c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p c (nfs_app Ps Args) )
| fread_nf_ind_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (d_ind p as') (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
where "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_nf Θ Ξ s m M) : type_scope
with fread_ne (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> ne -> Prop :=
| fread_ne_var :
  `( Rneᶠ #ᵈ x in Θ ⍮ Ξ ⍮ s ↘ #ⁿ (s - x - 1) )
| fread_ne_app :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ n in Θ ⍮ Ξ ⍮ s ↘ N ->
     Rneᶠ m $ᵈ n in Θ ⍮ Ξ ⍮ s ↘ M $ⁿ N )
| fread_ne_exfalso :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ⊥ᵈ s ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     (** The neutral form of the scrutinee. *)
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->

     Rneᶠ efqᵈ m under ρ return B in Θ ⍮ Ξ ⍮ s ↘ efqⁿ M return B' )
| fread_ne_glob :
  `( Rneᶠ d_glob p in Θ ⍮ Ξ ⍮ s ↘ ne_glob p )
| fread_ne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     nm = S (ind_nn D) ->
     ffresh_tele Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil) ↘ a ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ S (s + ind_nn D)%nat ↘ A' ->
     fread_brs Θ Ξ s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs Bs' ->
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rneᶠ d_elim ρ nm A Bs p as' m in Θ ⍮ Ξ ⍮ s ↘ ne_elim nm A' Bs' M )
where "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_ne Θ Ξ s m M) : type_scope
with fread_typ (Θ : gdeps) (Ξ : gstack) : nat -> domain -> nf -> Prop :=
| fread_typ_univ :
  `( Rtypᶠ 𝕌ω@i in Θ ⍮ Ξ ⍮ s ↘ Typeωⁿ@i )
(** A small universe reads back as the universe at the canonical form its
    level reads back as: that readback is always of the shape [nf_lvl_of L]
    (see [Core.Semantic.Levels.dlvl_canon_of_read]), and the universe takes
    the same canonical level. *)
| fread_typ_suniv :
  `( Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of L ->
     Rtypᶠ 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of L )
| fread_typ_level :
  `( Rtypᶠ Levelᵈ@n in Θ ⍮ Ξ ⍮ s ↘ Levelⁿ@n )
| fread_typ_True :
  `( Rtypᶠ ⊤ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊤ⁿ )
| fread_typ_False :
  `( Rtypᶠ ⊥ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊥ⁿ )
| fread_typ_pi :
  `( (** The normal form of the argument type. *)
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->

     (** The normal form of the return type. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     Rtypᶠ Πᵈ a ρ B in Θ ⍮ Ξ ⍮ s ↘ Πⁿ A B')
| fread_typ_neut :
  `( Rneᶠ b in Θ ⍮ Ξ ⍮ s ↘ B ->
     Rtypᶠ ⇑ a b in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ B)
(** A type former without arguments reads back without its declaration:
    it has no parameter to read. *)
| fread_typ_indty_nil :
  `( Rtypᶠ d_ind p nil in Θ ⍮ Ξ ⍮ s ↘ nf_indty p nfs_nil )
| fread_typ_indty :
  `( as' <> nil ->
     ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     Rpsᶠ as' at List.rev (ind_params D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtypᶠ d_ind p as' in Θ ⍮ Ξ ⍮ s ↘ nf_indty p Ps )
where "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_typ Θ Ξ s m M) : type_scope
(** The atoms of a level, read one by one. *)
with fread_la (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> lvl_atoms -> Prop :=
| fread_la_nil :
  `( Rlaᶠ nil in Θ ⍮ Ξ ⍮ s ↘ la_nil )
| fread_la_cons :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rlaᶠ (k, n, m) :: xs in Θ ⍮ Ξ ⍮ s ↘ la_cons k n M ys )
where "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" := (fread_la Θ Ξ s xs ys) : type_scope
with fread_ps (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> nfs -> Prop :=
| fread_ps_nil :
  `( Rpsᶠ nil at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nfs_nil )
| fread_ps_cons :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ↦ v ⍮ s ↘ Vs ->
     Rpsᶠ v :: vs at ce_ass A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nfs_cons V Vs )
where "'Rpsᶠ' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (fread_ps Θ Ξ s ρ T vs Ms) : type_scope
with fread_cargs (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> nfs -> Prop :=
| fread_cargs_nil :
  `( fread_cargs Θ Ξ s p ups ρ nil nil nfs_nil )
| fread_cargs_arg :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     fread_cargs Θ Ξ s p ups (ρ ↦ v) gs vs Vs ->
     fread_cargs Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) (nfs_cons V Vs) )
| fread_cargs_rec :
  `( feval_shty Θ Ξ p ups ρ t a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     fread_cargs Θ Ξ s p ups ρ gs vs Vs ->
     fread_cargs Θ Ξ s p ups ρ (ca_rec t :: gs) (v :: vs) (nfs_cons V Vs) )
with fread_brs (Θ : gdeps) (Ξ : gstack) : nat -> env -> exp -> qname -> ind_decl -> list domain ->
                                    list (string * list carg) -> list (string * nat * exp) -> nbrs -> Prop :=
| fread_brs_nil :
  `( fread_brs Θ Ξ s ρ A p D ups nil nil nbrs_nil )
| fread_brs_cons :
  `( n = (ind_nn D + List.length gs + cargs_nrec gs)%nat ->
     cargs_plen (ind_nn D) gs ->
     ffresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
     ffresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D)%nat vs ->
     ffresh_ihs Θ Ξ ρ A B (env_args nil (ups ++ ns)) gs vs (s + ind_nn D + List.length gs)%nat ihs ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ ihs) ↘ b ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil) ↘ t ->
     Rnfᶠ ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
     fread_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
     fread_brs Θ Ξ s ρ A p D ups ((c, gs) :: cs) ((c, n, B) :: Bs) (nbrs_cons c n B' Bs') )
.

Scheme fread_nf_mut_ind := Induction for fread_nf Sort Prop
with fread_ne_mut_ind := Induction for fread_ne Sort Prop
with fread_typ_mut_ind := Induction for fread_typ Sort Prop
with fread_la_mut_ind := Induction for fread_la Sort Prop
with fread_ps_mut_ind := Induction for fread_ps Sort Prop
with fread_cargs_mut_ind := Induction for fread_cargs Sort Prop
with fread_brs_mut_ind := Induction for fread_brs Sort Prop.
Combined Scheme fread_mut_ind from
  fread_nf_mut_ind,
  fread_ne_mut_ind,
  fread_typ_mut_ind,
  fread_la_mut_ind,
  fread_ps_mut_ind,
  fread_cargs_mut_ind,
  fread_brs_mut_ind.

#[export]
Hint Constructors fread_nf fread_ne fread_typ fread_la fread_ps fread_cargs fread_brs : mctt.

  Lemma functional_ffresh_tele : forall {Θ Ξ} ρ T s vs1, ffresh_tele Θ Ξ ρ T s vs1 ->
      forall vs2, ffresh_tele Θ Ξ ρ T s vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ reflexivity |].
    functional_feval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_ffresh_cargs : forall {Θ Ξ} p ups ρ gs s vs1, ffresh_cargs Θ Ξ p ups ρ gs s vs1 ->
      forall vs2, ffresh_cargs Θ Ξ p ups ρ gs s vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ auto | |];
      functional_feval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_ffresh_ihs : forall {Θ Ξ} ρ A B ρa gs vs s ihs1, ffresh_ihs Θ Ξ ρ A B ρa gs vs s ihs1 ->
      forall ihs2, ffresh_ihs Θ Ξ ρ A B ρa gs vs s ihs2 -> ihs1 = ihs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; auto; try congruence.
    all: functional_feval_rewrite_clear; f_equal; auto.
  Qed.

  Ltac functional_ffresh_rewrite_clear :=
    repeat match goal with
      | H1 : ffresh_tele ?T ?X ?ρ ?L ?s ?v1, H2 : ffresh_tele ?T ?X ?ρ ?L ?s ?v2 |- _ =>
          pose proof (functional_ffresh_tele _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : ffresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v1, H2 : ffresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v2 |- _ =>
          pose proof (functional_ffresh_cargs _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : ffresh_ihs ?T ?X ?ρ ?A ?B ?ρa ?gs ?vs ?s ?i1, H2 : ffresh_ihs ?T ?X ?ρ ?A ?B ?ρa ?gs ?vs ?s ?i2 |- _ =>
          pose proof (functional_ffresh_ihs _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : ind_lookup ?T ?X ?p = Some _, H2 : ind_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      end.
  Lemma functional_fread : forall {Θ Ξ},
    (forall s m M1,
        Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
        forall M2,
          Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
          M1 = M2) /\
      (forall s m M1,
          Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
          forall M2,
            Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
            M1 = M2) /\
      (forall s m M1,
          Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
          forall M2,
            Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
            M1 = M2) /\
      (forall s xs ys1,
          Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys1 ->
          forall ys2,
            Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys2 ->
            ys1 = ys2) /\
      (forall s ρ T vs Vs1, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs1 -> forall Vs2, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs2 -> Vs1 = Vs2) /\
      (forall s p ups ρ gs vs Vs1, fread_cargs Θ Ξ s p ups ρ gs vs Vs1 ->
         forall Vs2, fread_cargs Θ Ξ s p ups ρ gs vs Vs2 -> Vs1 = Vs2) /\
      (forall s ρ A p D ups cs Bs Bs1, fread_brs Θ Ξ s ρ A p D ups cs Bs Bs1 ->
         forall Bs2, fread_brs Θ Ξ s ρ A p D ups cs Bs Bs2 -> Bs1 = Bs2).
  Proof.
    intros Θ Ξ; apply fread_mut_ind; intros; progressive_inversion; functional_feval_rewrite_clear;
      functional_ffresh_rewrite_clear; functional_feval_rewrite_clear;
      (** The two rules of a type former exclude each other. *)
      try contradiction.
    all: try (first
        [ (** A small universe takes the canonical level that its level reads
              back as, so its case is that equality under [nf_univ_of]. *)
          solve [ apply nf_univ_of_cong; eauto ]
          (** The other level cases read back a canonical form, so the equality
              is under [nf_lvl_of (lvl_canon …)]: [repeat f_equal] reaches the
              atoms. *)
        | repeat f_equal; solve [eauto] ]).
    (** A type former: its other derivation, by either rule. *)
    all: match goal with H : Rtypᶠ d_ind _ _ in _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H end;
      functional_ffresh_rewrite_clear; try contradiction; try reflexivity; f_equal; eauto.
  Qed.

  Corollary functional_fread_nf : forall {Θ Ξ} s m M1 M2,
      Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fread Θ Ξ); firstorder.
  Qed.

  Lemma functional_fread_la : forall {Θ Ξ} s xs ys1 ys2,
      Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys1 ->
      Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys2 ->
      ys1 = ys2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fread Θ Ξ); firstorder.
  Qed.

  Lemma functional_fread_ne : forall {Θ Ξ} s m M1 M2,
      Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fread Θ Ξ); firstorder.
  Qed.

  Lemma functional_fread_typ : forall {Θ Ξ} s m M1 M2,
      Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fread Θ Ξ); firstorder.
  Qed.

#[export]
Hint Resolve functional_fread_nf functional_fread_ne functional_fread_typ functional_fread_la : mctt.

Ltac functional_fread_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_fread equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (Rnfᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rnfᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rneᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rneᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rtypᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rtypᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rlaᶠ ?xs in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rlaᶠ ?xs in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  end.
Ltac functional_fread_rewrite_clear := repeat functional_fread_rewrite_clear1.
