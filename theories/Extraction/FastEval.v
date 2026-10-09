(** * The Evaluation the Extracted Checker Runs

    A copy of the evaluation relations ([Core.Semantic.Evaluation]) and of
    readback ([Core.Semantic.Readback]) with one rule changed: the
    [ℕ]-eliminator at a successor does not compute the recursive result
    when the successor case does not read it, that is, when [#0] is fresh
    in [MS] ([exp_freshb]); the unused entry of the environment is then
    [zeroᵈ] ([feval_natrec_skip]).  The decision is syntactic and builds
    nothing.  Readback is copied because it evaluates closures.

    The values of the two evaluations agree except in the entries of
    environments that nothing reads: [Extraction.Simulation] makes this
    precise and proves that both read back to the same normal forms, so the
    normalizer built on this evaluation ([Extraction.NbE]) meets the
    specification [nbe] of the reference one. *)
From Stdlib Require Import Lia List Morphisms PeanoNat Relations String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Fresh.
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
  | a_typ _ | a_level _ | a_llit _ | a_nat | a_zero
  | a_True | a_true | a_False => true
  | a_univ M | a_succl M | a_succ M => exp_freshb k M
  | a_maxl M N | a_app M N => exp_freshb k M && exp_freshb k N
  | a_natrec A MZ MS M =>
      exp_freshb (S k) A && exp_freshb k MZ && exp_freshb (S (S k)) MS && exp_freshb k M
  | a_exfalso A M => exp_freshb (S k) A && exp_freshb k M
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
Reserved Notation "'⟦recᶠ' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$ᶠ|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).

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
    rules of the eliminator at a successor. *)
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
(** [ℕ] is a value. *)
| feval_exp_nat :
  `( ⟦ ℕ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ℕᵈ )
(** So is [zero]. *)
| feval_exp_zero :
  `( ⟦ zero ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ zeroᵈ )
(** [succ] of the value of its argument. *)
| feval_exp_succ :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ succᵈ m )
(** The eliminator evaluates its scrutinee, then recurses on the value. *)
| feval_exp_natrec :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
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
with feval_natrec (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
(** At [zero], the base case. *)
| feval_natrec_zero :
  `( ⟦ MZ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦recᶠ zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ mz )
(** At a successor, the step case on the predecessor and the recursive
    result, when the step case reads the recursive result. *)
| feval_natrec_succ :
  `( exp_freshb 0 MS = false ->
     ⟦recᶠ b return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ MS ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ b ↦ r ↘ ms ->
     ⟦recᶠ succᵈ b return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms )
(** When it does not, the recursive result is not computed: its entry of the
    environment is [zeroᵈ], which nothing reads. *)
| feval_natrec_skip :
  `( exp_freshb 0 MS = true ->
     ⟦ MS ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ b ↦ zeroᵈ ↘ ms ->
     ⟦recᶠ succᵈ b return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms )
(** At a neutral, a neutral at the motive's instance. *)
| feval_natrec_neut :
  `( ⟦ MZ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦recᶠ ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a recᵈ m under ρ return A | zero -> mz | succ -> MS end )
where "'⟦recᶠ' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_natrec Θ Ξ A MZ MS m ρ r)
with feval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
(** A function's body, at the argument. *)
| feval_app_fn :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $ᶠ| λᵈ ρ M & n | Θ ⍮ Ξ ↘ m )
(** A neutral applied, at the codomain's instance. *)
| feval_app_neut :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $ᶠ| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
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
     $ᵐᶠ| dm_local ρ (gu_body Δ Φ) args & n | Θ ⍮ Ξ ↘ dm_local ρ (gu_body Δ Φ) (args ++ n :: nil) )
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
     dm_local ρ (gu_body Δ Φ) args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
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
     dm_local ρ (gu_body Δ Φ) args ·ₘᶠ y Θ ⍮ Ξ ↘ dm_local ρ' Uy nil )
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
where "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" := (feval_benv Θ Ξ ρ Φ ρ').

Scheme feval_exp_mut_ind := Induction for feval_exp Sort Prop
with feval_natrec_mut_ind := Induction for feval_natrec Sort Prop
with feval_app_mut_ind := Induction for feval_app Sort Prop
with feval_exps_mut_ind := Induction for feval_exps Sort Prop
with feval_apps_mut_ind := Induction for feval_apps Sort Prop
with feval_modexp_mut_ind := Induction for feval_modexp Sort Prop
with feval_appm_mut_ind := Induction for feval_appm Sort Prop
with feval_sel_mut_ind := Induction for feval_sel Sort Prop
with feval_selm_mut_ind := Induction for feval_selm Sort Prop
with feval_selc_mut_ind := Induction for feval_selc Sort Prop
with feval_selmc_mut_ind := Induction for feval_selmc Sort Prop
with feval_benv_mut_ind := Induction for feval_benv Sort Prop.
Combined Scheme feval_mut_ind from
  feval_exp_mut_ind,
  feval_natrec_mut_ind,
  feval_app_mut_ind,
  feval_exps_mut_ind,
  feval_apps_mut_ind,
  feval_modexp_mut_ind,
  feval_appm_mut_ind,
  feval_sel_mut_ind,
  feval_selm_mut_ind,
  feval_selc_mut_ind,
  feval_selmc_mut_ind,
  feval_benv_mut_ind.

#[export]
Hint Constructors feval_exp feval_natrec feval_app feval_exps feval_apps feval_modexp feval_appm feval_sel feval_selm
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
      (forall A MZ MS m ρ r1,
          ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2,
            ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
            r1 = r2) /\
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
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2).
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
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _ _),
          H2 : forall U r, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U r) |- _ =>
            exfalso; exact (H2 _ _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
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

  Corollary functional_feval_natrec : forall {Θ Ξ} A MZ MS m ρ r1 r2,
      ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ); intuition.
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

  Corollary functional_feval_benv : forall {Θ Ξ} ρ Φ ρ1 ρ2,
      ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
      ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 ->
      ρ1 = ρ2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto.
  Qed.

#[export]
Hint Resolve functional_feval_exp functional_feval_natrec functional_feval_app functional_feval_modexp : mctt.



Ltac functional_feval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_feval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦recᶠ ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦recᶠ ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  end.
(** There is no [feval_sub] case: [functional_feval_sub] gives only pointwise
    equality, so there is nothing to [replace]. *)
Ltac functional_feval_rewrite_clear := repeat functional_feval_rewrite_clear1.

(** ** Readback *)

Reserved Notation "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).

Generalizable All Variables.

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
| fread_nf_zero :
  `( Rnfᶠ ⇓ ℕᵈ zeroᵈ in Θ ⍮ Ξ ⍮ s ↘ zeroⁿ )
| fread_nf_succ :
  `( Rnfᶠ ⇓ ℕᵈ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ ℕᵈ (succᵈ m) in Θ ⍮ Ξ ⍮ s ↘ succⁿ M )
| fread_nf_nat_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ ℕᵈ (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
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
where "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_nf Θ Ξ s m M) : type_scope
with fread_ne (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> ne -> Prop :=
| fread_ne_var :
  `( Rneᶠ #ᵈ x in Θ ⍮ Ξ ⍮ s ↘ #ⁿ (s - x - 1) )
| fread_ne_app :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ n in Θ ⍮ Ξ ⍮ s ↘ N ->
     Rneᶠ m $ᵈ n in Θ ⍮ Ξ ⍮ s ↘ M $ⁿ N )
| fread_ne_natrec :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ℕᵈ s ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     (** The normal form of the zero case. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ zeroᵈ ↘ bz ->
     Rnfᶠ ⇓ bz mz in Θ ⍮ Ξ ⍮ s ↘ MZ ->

     (** The normal form of the successor case. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
     ⟦ MS ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
     Rnfᶠ ⇓ bs ms in Θ ⍮ Ξ ⍮ S (S s) ↘ MS' ->

     (** The neutral form of the scrutinee. *)
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->

     Rneᶠ recᵈ m under ρ return B | zero -> mz | succ -> MS end in Θ ⍮ Ξ ⍮ s ↘ recⁿ M return B' | zero -> MZ | succ -> MS' end )
| fread_ne_exfalso :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ⊥ᵈ s ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     (** The neutral form of the scrutinee. *)
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->

     Rneᶠ efqᵈ m under ρ return B in Θ ⍮ Ξ ⍮ s ↘ efqⁿ M return B' )
| fread_ne_glob :
  `( Rneᶠ d_glob p in Θ ⍮ Ξ ⍮ s ↘ ne_glob p )
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
| fread_typ_nat :
  `( Rtypᶠ ℕᵈ in Θ ⍮ Ξ ⍮ s ↘ ℕⁿ )
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
.

Scheme fread_nf_mut_ind := Induction for fread_nf Sort Prop
with fread_ne_mut_ind := Induction for fread_ne Sort Prop
with fread_typ_mut_ind := Induction for fread_typ Sort Prop
with fread_la_mut_ind := Induction for fread_la Sort Prop.
Combined Scheme fread_mut_ind from
  fread_nf_mut_ind,
  fread_ne_mut_ind,
  fread_typ_mut_ind,
  fread_la_mut_ind.

#[export]
Hint Constructors fread_nf fread_ne fread_typ fread_la : mctt.
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
            ys1 = ys2).
  Proof.
    intros Θ Ξ; apply fread_mut_ind; intros; progressive_inversion; functional_feval_rewrite_clear;
      first
        [ (** A small universe takes the canonical level that its level reads
              back as, so its case is that equality under [nf_univ_of]. *)
          solve [ apply nf_univ_of_cong; eauto ]
          (** The other level cases read back a canonical form, so the equality
              is under [nf_lvl_of (lvl_canon …)]: [repeat f_equal] reaches the
              atoms. *)
        | repeat f_equal; solve [eauto] ].
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
