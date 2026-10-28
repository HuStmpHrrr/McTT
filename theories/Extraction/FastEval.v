(** * The Evaluation the Extracted Checker Runs

    A copy of the evaluation relations ([Core.Semantic.Evaluation]) and of
    readback ([Core.Semantic.Readback]) with one rule changed: the
    eliminator of a group of inductive types at a constructor computes the
    recursive result of a recursive argument only when the branch reads it,
    that is, when its variable is not fresh in the branch ([exp_freshb]);
    an unused entry is [𝕌ω@0] ([feval_ihs_skip]).  Readback of a stuck
    eliminator's branch gives such a recursive result the type [𝕌ω@0]
    ([fast_fresh_ihs_skip]).

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
From Mctt.Core.Syntactic Require Import Substitution Members Records Fresh.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Open Scope bool_scope.

(** ** Deciding Freshness *)

(** The boolean counterparts of [all_list], [opt_all], [all_brs] and
    [all_blocks]: structural recursions on the lists, so that a recursive
    function on terms may use them on an eliminator's parts. *)
Fixpoint all_listb {A : Set} (f : A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | x :: l' => f x && all_listb f l'
  end.

(** An annotation, when there is one. *)
Definition opt_allb {A : Set} (f : A -> bool) (o : option A) : bool :=
  match o with Some a => f a | None => true end.

(** Every branch, under its binders. *)
Fixpoint all_brsb {A : Type} (f : nat -> A -> bool) (Bs : list (string * nat * A)) : bool :=
  match Bs with
  | nil => true
  | b :: Bs' => f (snd (fst b)) (snd b) && all_brsb f Bs'
  end.

(** Every block: its binder count, annotation, motive and branches. *)
Fixpoint all_blocksb {A : Set} (f : nat -> option A -> A -> list (string * nat * A) -> bool)
    (Bks : list (eblock_g A)) : bool :=
  match Bks with
  | nil => true
  | eb_mk nm oZ M Bs :: Bks' => f nm oZ M Bs && all_blocksb f Bks'
  end.

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
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => true
  | a_elim _ Us _ Bks M =>
      all_listb (exp_freshb k) Us &&
      all_blocksb (fun nm oZ A Bs => opt_allb (exp_freshb (nm - 1 + k)) oZ && exp_freshb (nm + k) A &&
                                     all_brsb (fun n B => exp_freshb (n + k) B) Bs) Bks &&
      exp_freshb k M
  | a_pi A B | a_fn A B => exp_freshb k A && exp_freshb (S k) B
  | a_var x => negb (Nat.eqb x k)
  | a_let b B => bnd_freshb k b && exp_freshb (S k) B
  | a_mem H _ => modexp_freshb k H
  | a_record _ => true
  | a_tuple T fs => exp_freshb k T && all_listb (fun f => exp_freshb k (snd f)) fs
  | a_proj _ M => exp_freshb k M
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
  | md_body sm Φ => gmod_freshb k Φ
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
  | ge_ind _ _ _ D Φ => gmod_freshb (ind_nu D + k) Φ
  | ge_def_mod _ A M U => exp_freshb k A && exp_freshb k M && gunit_freshb k U
  | ge_record _ _ R Φ => gmod_freshb (S (List.length (record_params R)) + k) Φ
  end
with centry_freshb (k : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass A => exp_freshb k A
  | ce_def A M => exp_freshb k A && exp_freshb k M
  | ce_mod U => gunit_freshb k U
  | ce_dm A M U => exp_freshb k A && exp_freshb k M && gunit_freshb k U
  end.

(** The boolean list functions decide their counterparts, element by
    element. *)
Lemma all_listb_sound : forall {A : Set} (f : A -> bool) (P : A -> Prop) l,
    List.Forall (fun x => f x = true -> P x) l -> all_listb f l = true -> all_list P l.
Proof.
  induction 1 as [| x l Hx Hl IH]; cbn; [ trivial |].
  intros Hb; apply Bool.andb_true_iff in Hb as [H1 H2]; split; auto.
Qed.

Lemma all_brsb_sound : forall {A : Type} (f : nat -> A -> bool) (P : nat -> A -> Prop) Bs,
    List.Forall (fun b => f (snd (fst b)) (snd b) = true -> P (snd (fst b)) (snd b)) Bs ->
    all_brsb f Bs = true -> all_brs P Bs.
Proof.
  induction 1 as [| b Bs Hb HBs IH]; cbn; [ trivial |].
  intros H; apply Bool.andb_true_iff in H as [H1 H2]; split; auto.
Qed.

Lemma all_blocksb_sound : forall {A : Set} (f : nat -> option A -> A -> list (string * nat * A) -> bool)
    (P : nat -> option A -> A -> list (string * nat * A) -> Prop) Bks,
    List.Forall (fun b => f (eb_nm b) (eb_ann b) (eb_motive b) (eb_brs b) = true ->
                          P (eb_nm b) (eb_ann b) (eb_motive b) (eb_brs b)) Bks ->
    all_blocksb f Bks = true -> all_blocks P Bks.
Proof.
  induction 1 as [| [nm oZ M Bs] Bks Hb HBks IH]; cbn; [ trivial |].
  intros H; apply Bool.andb_true_iff in H as [H1 H2]; split; auto.
Qed.

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
           (fun e => forall k, centry_freshb k e = true -> centry_fresh k e)).
  (** An eliminator: its uniform parameters, then its blocks, part by
      part, then its scrutinee. *)
  15: { intros oq Us m Bks M HUs HBks HM k Hb; cbn [exp_freshb] in Hb.
        apply Bool.andb_true_iff in Hb as [Hb HbM]; apply Bool.andb_true_iff in Hb as [HbU HbB].
        apply (proj2 (exp_fresh_elim k oq Us m Bks M)); split; [| split; [| auto ] ].
        - eapply all_listb_sound; [| exact HbU ].
          eapply List.Forall_impl; [| exact HUs ]; cbv beta; intros U HU; apply HU.
        - eapply all_blocksb_sound; [| exact HbB ].
          eapply List.Forall_impl; [| exact HBks ]; cbv beta.
          intros [nm oZ A Bs] (HZ & HA & HBs) Hbk; cbn [eb_nm eb_ann eb_motive eb_brs] in *.
          apply Bool.andb_true_iff in Hbk as [Hbk Hbr]; apply Bool.andb_true_iff in Hbk as [HbZ HbA].
          split; [| split ].
          + destruct oZ as [Z |]; cbn in *; [ apply (HZ Z eq_refl); exact HbZ | exact I ].
          + apply HA; exact HbA.
          + eapply all_brsb_sound; [| exact Hbr ].
            eapply List.Forall_impl; [| exact HBs ]; cbv beta; intros br Hbr' Hbt; apply Hbr'; exact Hbt. }
  (** A record element: its type, then its fields. *)
  all: try match goal with |- forall T fs, _ -> _ -> forall k, exp_freshb k (a_tuple T fs) = true -> _ =>
         intros T fs HT Hfs k Hb; cbn [exp_freshb exp_fresh] in *; apply Bool.andb_true_iff in Hb as [HbT Hbf];
         split; [ auto
                | eapply all_listb_sound; [| exact Hbf ];
                  eapply List.Forall_impl; [| exact Hfs ]; cbv beta; intros f Hf; apply Hf ] end.
  all: intros; cbn in *; repeat rewrite Bool.andb_true_iff in *; destruct_conjs;
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

(** Whether a branch [B] reads none of the [k] recursive results of one
    argument, the entries [base] to [base + k - 1] of its environment.
    [None] stands for a computation every result of which is read: the
    recursive results of a record view's fields, which become those of the
    argument the view is at. *)
Definition ihs_skipb (oB : option exp) (base k : nat) : bool :=
  match oB with
  | Some B => List.forallb (fun i => exp_freshb (base + i) B) (List.seq 0 k)
  | None => false
  end.

(** A skipped argument's results are each unread. *)
Lemma ihs_skipb_sound : forall oB base k, ihs_skipb oB base k = true ->
    exists B, oB = Some B /\ forall i, i < k -> exp_fresh (base + i) B.
Proof.
  intros [B |] * H; cbn in H; [| discriminate ].
  exists B; split; [ reflexivity |]; intros i Hi.
  apply exp_freshb_sound; apply (proj1 (List.forallb_forall _ _) H), List.in_seq; lia.
Qed.

(** ** The Relations *)

Reserved Notation "'⟦' M '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$ᶠ|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦elimᶠ' m 'at' j 'of' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, j at level 0, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihsᶠ' vs 'of' gs 'under' p ups Bks 'for' B '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, Bks at level 0, B at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihᶠ' v 'of' t 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦mrefᶠ' j 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '↘' r" (at level 70, j at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦shtyᶠ' t 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, t at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihtyᶠ' v 'of' t 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, ρm at level 0, As at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihtysᶠ' vs 'of' gs 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, ρm at level 0, As at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦projsᶠ' fl 'of' v '⟧ᶠ' Θ '⍮' Ξ '↘' ws" (at level 70, fl at level 69, v at level 69, Θ at level 69, Ξ at level 69, ws at level 69).
Reserved Notation "'⟦' H '⟧ᵐᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, H at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦' Ms '⟧*ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ms" (at level 70, Ms at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ms at level 69).
Reserved Notation "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" (at level 70, Φ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρ' at level 69).
Reserved Notation "'$*ᶠ|' m '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐᶠ|' h '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐ*ᶠ|' h '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' Δ '⊢' D '⟧ᶜᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, Δ at level 69, D at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "h '·ₜᶠ' x Θ '⍮' Ξ '↘' r" (at level 70, x at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘᶠ' y Θ '⍮' Ξ '↘' r" (at level 70, y at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₜ*ᶠ' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘ*ᶠ' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).

Generalizable All Variables.

(** The rules of [Core.Semantic.Evaluation], one for one, but for the rules
    of a recursive argument's result: the recursive results of a
    constructor's arguments are computed for the branch that reads them. *)
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
(** The join of two levels: the flat join of their values. *)
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
(** The type former of a member of a group of inductive types is a value,
    with no argument yet. *)
| feval_exp_indty :
  `( ⟦ a_ind p k ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_ind p k nil )
(** A constructor, with no argument yet, when it is a value of its own
    before any argument ([im_starts]). *)
| feval_exp_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_starts D Mk = true ->
     ⟦ a_con p k c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con p k c nil )
(** A constructor of a view of a group with no uniform parameters is at
    once the container's, at the view's arguments. *)
| feval_exp_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_nu D = 0 ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ env_args nil nil ↘ cups ->
     ⟦ a_con p j c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con qc k c cups )
(** The constructor of a record view of a group with no uniform
    parameters, of a record with fields: a value of its own *)
| feval_exp_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ind_nu D = 0 ->
     0 < List.length fl ->
     ⟦ a_con p j c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con p j c nil )
(** Of a record without fields: the empty tuple *)
| feval_exp_con_rview_empty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is nil ->
     ind_nu D = 0 ->
     ⟦ a_con p j c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_tuple nil )
(** The eliminator evaluates its uniform parameters and its scrutinee, then
    eliminates the value by the blocks of its group: the one written, or
    the group of the value. *)
| feval_exp_elim :
  `( ⟦ Us ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ups ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     elim_grp_of oq m = Some p ->
     ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ a_elim oq Us j Bks M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
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
  `( ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ᵐ h ↘ r ->
     ⟦ ℓₘ (gu_mk Δ D) in B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
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
(** A record's type former is a value, with no argument yet. *)
| feval_exp_record :
  `( ⟦ a_record p ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_record p nil )
(** A record element is the tuple of its fields' values, by name. *)
| feval_exp_tuple :
  `( ⟦ List.map snd fs ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ vs ->
     ⟦ a_tuple T fs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_tuple (List.combine (List.map fst fs) vs) )
(** A field: the field of the value. *)
| feval_exp_proj :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     feval_proj Θ Ξ f m r ->
     ⟦ a_proj f M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' e '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_exp Θ Ξ e ρ r)
(** The field [f] of a value, as in [Core.Semantic.Evaluation]. *)
with feval_proj (Θ : gdeps) (Ξ : gstack) : string -> domain -> domain -> Prop :=
(** A tuple: its field *)
| feval_proj_tuple :
  `( field_lookup vs f = Some r ->
     feval_proj Θ Ξ f (d_tuple vs) r )
(** A neutral: its projection, at the field's type *)
| feval_proj_neut :
  `( record_lookup Θ Ξ p = Some R ->
     field_index (record_fields R) f = Some k ->
     feval_nflds Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil rs ->
     List.nth_error rs k = Some r ->
     feval_proj Θ Ξ f (⇑ (d_record p ns) m) r )
(** The neutral projections of [m] at the fields [fl], as in
    [Core.Semantic.Evaluation]. *)
with feval_nflds (Θ : gdeps) (Ξ : gstack) : list domain -> domain_ne -> list (string * exp) -> list domain -> list domain -> Prop :=
(** No field left *)
| feval_nflds_nil :
  `( feval_nflds Θ Ξ ns m nil pre nil )
(** The next field's projection, at its type, then the rest after it *)
| feval_nflds_cons :
  `( ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ env_args nil (ns ++ pre) ↘ a ->
     feval_nflds Θ Ξ ns m fl (pre ++ ⇑ a (d_proj g m) :: nil) rs ->
     feval_nflds Θ Ξ ns m ((g, T) :: fl) pre (⇑ a (d_proj g m) :: rs) )
(** The eliminator of the group at [p] at its member [j], on a value, as in
    [Core.Semantic.Evaluation]; the recursive results are computed for the
    branch. *)
with feval_elim (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> domain -> Prop :=
(** On a saturated constructor: its branch, at the non-uniform parameters,
    the arguments and the recursive results the branch reads *)
| feval_elim_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     ind_con Mj c = Some gs ->
     List.length vs = (im_np Dq Mk + List.length gs)%nat ->
     List.nth_error Bks j = Some b ->
     brs_lookup (eb_brs b) c = Some (n, B) ->
     n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat ->
     leaves_coherent D ->
     ⟦ihsᶠ skipn (im_np Dq Mk) vs of gs under p ups Bks for (Some B) ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs) ++ skipn (im_np Dq Mk) vs ++ ihs) ↘ r ->
     ⟦elimᶠ d_con pc k c vs at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** On a neutral: a stuck eliminator, at the motive's instance *)
| feval_elim_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_nm b = S (im_nn Mk) ->
     ⟦ eb_motive b ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil) ↘ a ->
     ⟦elimᶠ ⇑ (d_ind pc k as') m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_elim ρ Bks p ups j as' m) )
where "'⟦elimᶠ' m 'at' j 'of' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_elim Θ Ξ ρ p ups Bks j m r)
(** The recursive results of the arguments [vs] of a constructor, for the
    branch [B] ([Some B]): those of a recursive argument, one per leaf
    path of its shape, are computed only when [B] reads one of them.  The
    results of the recursive argument at the head of [ca_rec t :: gs] are
    the variables [cargs_nrec D gs] on of [B], since the results of the
    recursive arguments after it come after it in [B]'s environment.
    [None] computes them all. *)
with feval_ihs (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> option exp -> list carg -> list domain -> list domain -> Prop :=
(** No argument, no result *)
| feval_ihs_nil :
  `( ⟦ihsᶠ nil of nil under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A non-recursive argument has none *)
| feval_ihs_arg :
  `( ⟦ihsᶠ vs of gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_arg T :: gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs )
(** The branch reads one of the recursive results: they are computed. *)
| feval_ihs_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = false ->
     ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs1 ->
     ⟦ihsᶠ vs of gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_rec t :: gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs1 ++ ihs )
(** It reads none: each entry is [𝕌ω@0], which nothing reads. *)
| feval_ihs_skip :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = true ->
     ⟦ihsᶠ vs of gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_rec t :: gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ
       ↘ List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t)) ++ ihs )
where "'⟦ihsᶠ' vs 'of' gs 'under' p ups Bks 'for' oB '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_ihs Θ Ξ ρ p ups Bks oB gs vs r)
(** The recursive results of an argument [v] of shape [t], one per leaf
    path, as in [Core.Semantic.Evaluation]. *)
with feval_ih (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> list domain -> Prop :=
(** At the end of a shape, at a member with a block: the eliminator at the
    member [j] *)
| feval_ih_self :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     ⟦elimᶠ v at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ihᶠ v of pt_self j Ps under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r :: nil )
(** At a record view: the recursive results of its fields at the
    projections of [v], all computed *)
| feval_ih_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     ⟦ihsᶠ ws of gs under p ups Bks for None ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦ihᶠ v of pt_self j Ps under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a function shape: the family of each recursive result of the rest
    at [v]'s values *)
| feval_ih_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ihᶠ v of pt_pi B t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => d_ihfn ρ Bks p ups t i v) (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t))) )
where "'⟦ihᶠ' v 'of' t 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_ih Θ Ξ ρ p ups Bks t v r)
(** The projections of a value at the fields [fl], as in
    [Core.Semantic.Evaluation]. *)
with feval_projs (Θ : gdeps) (Ξ : gstack) : list string -> domain -> list domain -> Prop :=
(** No field *)
| feval_projs_nil :
  `( ⟦projsᶠ nil of v ⟧ᶠ Θ ⍮ Ξ ↘ nil )
(** The first field's projection, then the rest *)
| feval_projs_cons :
  `( feval_proj Θ Ξ f v w ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     ⟦projsᶠ f :: fl of v ⟧ᶠ Θ ⍮ Ξ ↘ w :: ws )
where "'⟦projsᶠ' fl 'of' v '⟧ᶠ' Θ '⍮' Ξ '↘' ws" := (feval_projs Θ Ξ fl v ws)
(** The member [j] of the group at [p] at the uniform parameters [ups], as
    in [Core.Semantic.Evaluation]. *)
with feval_mref (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> nat -> (qname * nat * list domain) -> Prop :=
(** A declared member: itself, at [ups] *)
| feval_mref_decl :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_decl pm ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (p, j, ups) )
(** A view: the container's member, at the view's arguments at [ups] *)
| feval_mref_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ env_args nil ups ↘ cups ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (qc, k, cups) )
where "'⟦mrefᶠ' j 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '↘' r" := (feval_mref Θ Ξ p ups j r)
(** The type of an argument of shape [t], as in [Core.Semantic.Evaluation]. *)
with feval_shty (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> domain -> Prop :=
(** At the end: the member's type former at the shape's parameters *)
| feval_shty_self :
  `( ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) ->
     ⟦shtyᶠ pt_self j Ps of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_ind pc k (pre ++ bs) )
(** At the end, at a record view: the record type at the view's instance *)
| feval_shty_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ env_args nil ups ↘ cups ->
     ⟦shtyᶠ pt_self j Ps of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_record qr cups )
(** At a domain: a [Π] over it, of the shape family *)
| feval_shty_pi :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦shtyᶠ pt_pi B t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ b (nil ↦ d_shfam p ups ρ t) fam_cod )
where "'⟦shtyᶠ' t 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_shty Θ Ξ p ups ρ t r)
(** The types of the recursive results of an argument of shape [t], one
    per leaf path, as in [Core.Semantic.Evaluation]. *)
with feval_ihty (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> ptyp -> domain -> list domain -> Prop :=
(** At the end, at a member with a block: the member's motive at the
    shape's parameters and [v] *)
| feval_ihty_self :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦ List.nth j As a_True ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρm (bs ++ v :: nil) ↘ a ->
     ⟦ihtyᶠ v of pt_self j Ps at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a :: nil )
(** At a record view: those of its fields at [v]'s projections *)
| feval_ihty_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     ⟦ihtysᶠ ws of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ env_args nil ups ↘ rs ->
     ⟦ihtyᶠ v of pt_self j Ps at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a domain: a [Π] over it, of each recursive result's family *)
| feval_ihty_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦ihtyᶠ v of pt_pi B t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => Πᵈ b (nil ↦ d_ihfam ρm As p ups ρ t i v) fam_cod)
           (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t))) )
where "'⟦ihtyᶠ' v 'of' t 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_ihty Θ Ξ p ups ρm As ρ t v r)
(** The types of the recursive results of a record view's fields, as in
    [Core.Semantic.Evaluation]. *)
with feval_ihtys (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> list carg -> list domain -> list domain -> Prop :=
(** No field, no result *)
| feval_ihtys_nil :
  `( ⟦ihtysᶠ nil of nil at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A non-recursive field: none, the field entering the environment *)
| feval_ihtys_arg :
  `( ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ v ↘ rs ->
     ⟦ihtysᶠ v :: vs of ca_arg T :: gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** A recursive field: those of its shape *)
| feval_ihtys_rec :
  `( ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs1 ->
     ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦ihtysᶠ v :: vs of ca_rec t :: gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs1 ++ rs )
where "'⟦ihtysᶠ' vs 'of' gs 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_ihtys Θ Ξ p ups ρm As ρ gs vs r)
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
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     $ᶠ| d_ind p k as' & n | Θ ⍮ Ξ ↘ d_ind p k (as' ++ n :: nil) )
(** So does a constructor of a declared member, a parameter or an argument. *)
| feval_app_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length vs < (im_np D Mk + List.length gs)%nat ->
     $ᶠ| d_con p k c vs & n | Θ ⍮ Ξ ↘ d_con p k c (vs ++ n :: nil) )
(** A constructor of a view takes the group's uniform parameters *)
| feval_app_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) < ind_nu D ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con p j c (vs ++ n :: nil) )
(** At the last uniform parameter, the container's constructor at the
    view's arguments *)
| feval_app_con_view_ups :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) = ind_nu D ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ env_args nil (vs ++ n :: nil) ↘ cups ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con qc k c cups )
(** The constructor of a record view, before its last argument *)
| feval_app_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) < ind_nu D + List.length fl ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con p j c (vs ++ n :: nil) )
(** At its last: the tuple of the fields *)
| feval_app_con_rview_full :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) = ind_nu D + List.length fl ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_tuple (List.combine fl (List.skipn (ind_nu D) (vs ++ n :: nil))) )
(** The [i]-th recursive result of a function shape, at the argument's
    value: the [i]-th of the rest's at the function's value there. *)
| feval_app_ihfn :
  `( $ᶠ| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ihᶠ fn of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     List.nth_error rs i = Some r ->
     $ᶠ| d_ihfn ρ Bks p ups t i f & n | Θ ⍮ Ξ ↘ r )
(** The family of the type of an argument of a function shape *)
| feval_app_shfam :
  `( ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ a ->
     $ᶠ| d_shfam p ups ρ t & n | Θ ⍮ Ξ ↘ a )
(** The [i]-th recursive result's family, at the argument's value *)
| feval_app_ihfam :
  `( $ᶠ| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ihtyᶠ fn of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ as' ->
     List.nth_error as' i = Some a ->
     $ᶠ| d_ihfam ρm As p ups ρ t i f & n | Θ ⍮ Ξ ↘ a )
(** A member closure takes the next argument of its module, and selects again. *)
| feval_app_member :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     $ᶠ| d_member h ch & n | Θ ⍮ Ξ ↘ r )
(** A record's type former takes a parameter it still lacks. *)
| feval_app_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns < List.length (record_params R) ->
     $ᶠ| d_record p ns & n | Θ ⍮ Ξ ↘ d_record p (ns ++ n :: nil) )
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
(** A literal unit is its closure. *)
| feval_me_lit :
  `( ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ me_lit (gu_mk Δ D) ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h )
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
(** The closure of a unit's definition lacking the parameters [Δ]: a body,
    or an alias still lacking a parameter, is its closure; an alias lacking
    none is its target's value. *)
with feval_close (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> dmod -> Prop :=
(** A body: its closure *)
| feval_close_body :
  `( ⟦ Δ ⊢ md_body sm Φ ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_body sm Φ) ρ )
(** An alias still lacking a parameter: its closure *)
| feval_close_alias :
  `( 0 < List.length Δ ->
     ⟦ Δ ⊢ md_alias E ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_alias E) ρ )
(** An alias lacking none: its target's value *)
| feval_close_alias0 :
  `( ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ nil ⊢ md_alias E ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h )
where "'⟦' Δ '⊢' D '⟧ᶜᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (feval_close Θ Ξ Δ D ρ r)
(** Applying a module value to one more argument, which it must still lack. *)
with feval_appm (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> dmod -> Prop :=
(** A global module records the argument. *)
| feval_appm_global :
  `( $ᵐᶠ| dm_global p args & n | Θ ⍮ Ξ ↘ dm_global p (args ++ n :: nil) )
(** A closure takes it as its outermost missing parameter, in its
    environment. *)
| feval_appm_local :
  `( ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ r ->
     $ᵐᶠ| dm_local (Δ ++ ce_ass A :: nil) D ρ & n | Θ ⍮ Ξ ↘ r )
(** A submodule of an unsaturated module passes it to the module, then selects again. *)
| feval_appm_member :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     $ᵐᶠ| dm_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$ᵐᶠ|' h '&' n '|' Θ '⍮' Ξ '↘' r" := (feval_appm Θ Ξ h n r)
(** Applying a module value to arguments, outermost first. *)
with feval_appms (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> dmod -> Prop :=
(** No argument *)
| feval_appms_nil :
  `( $ᵐ*ᶠ| h & nil | Θ ⍮ Ξ ↘ h )
(** The first argument, then the rest *)
| feval_appms_cons :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h1 ->
     $ᵐ*ᶠ| h1 & ns | Θ ⍮ Ξ ↘ r ->
     $ᵐ*ᶠ| h & n :: ns | Θ ⍮ Ξ ↘ r )
where "'$ᵐ*ᶠ|' h '&' ns '|' Θ '⍮' Ξ '↘' r" := (feval_appms Θ Ξ h ns r)
(** Selecting a term member.  A member of a global module is stored closed,
    over the module's parameters: δ evaluates a transparent one's body in the
    empty environment, and an opaque one or an axiom is a neutral at its
    (closed) type.  Either is then applied to the module's arguments. *)
with feval_sel (Θ : gdeps) (Ξ : gstack) : dmod -> string -> domain -> Prop :=
(** A term part of a global module, a transparent definition's body or a
    definition with a module part's term ([gc_term]): it, applied to the
    module's arguments. *)
| feval_sel_global :
  `( gc_term Θ Ξ (qname_app p (x :: nil)) = Some M ->
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
(** The module of a member of a group of inductive types, as a term: the
    member's type former, applied to the module's arguments. *)
| feval_sel_global_ind :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app p (x :: nil)) = Some (pq, k, D) ->
     $*ᶠ| d_ind pq k nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A member of a closure lacking a parameter is a member closure. *)
| feval_sel_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₜᶠ x Θ ⍮ Ξ ↘ d_member (dm_local Δ D ρ) (x :: nil) )
(** A term part of a saturated body ([entry_tm]: a definition's body or a
    definition with a module part's term), found in the body read through
    the entries its local opens generate: it, in the environment of the
    body before it. *)
| feval_sel_body :
  `( kbody Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A member of a submodule closure extends the chain. *)
| feval_sel_member :
  `( dm_member h ch ·ₜᶠ x Θ ⍮ Ξ ↘ d_member h (ch ++ x :: nil) )
(** A record type of a global module, stored or with its module's frame
    open, as a term: its type former, applied to the module's arguments. *)
| feval_sel_global_record :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     record_lookup Θ Ξ (qname_app p (x :: nil)) = Some R ->
     $*ᶠ| d_record (qname_app p (x :: nil)) nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
where "h '·ₜᶠ' x Θ '⍮' Ξ '↘' r" := (feval_sel Θ Ξ h x r)
(** Selecting a submodule. *)
with feval_selm (Θ : gdeps) (Ξ : gstack) : dmod -> string -> dmod -> Prop :=
(** A body submodule, an open frame or the module of an inductive type in a
    global module is a global module, with the same arguments. *)
| feval_selm_global :
  `( gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ ->
     dm_global p args ·ₘᶠ y Θ ⍮ Ξ ↘ dm_global (qname_app p (y :: nil)) args )
(** An alias submodule of a global module is the closure of the alias,
    stored closed over the module's parameters, given the module's
    arguments. *)
| feval_selm_global_alias :
  `( gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ nil ↘ h ->
     $ᵐ*ᶠ| h & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₘᶠ y Θ ⍮ Ξ ↘ r )
(** A submodule of a closure lacking a parameter is a submodule closure. *)
| feval_selm_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₘᶠ y Θ ⍮ Ξ ↘ dm_member (dm_local Δ D ρ) (y :: nil) )
(** A module part of a saturated body ([entry_unit]: a submodule, or a
    definition with a module part's), found in the body read through the
    entries its local opens generate: its unit's closure, in the
    environment of the body before it. *)
| feval_selm_body :
  `( kbody Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ Δy ⊢ Dy ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₘᶠ y Θ ⍮ Ξ ↘ r )
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
     ⟦ Δy ⊢ Dy ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_mod pm (gu_mk Δy Dy)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵐ h )
(** A definition with a module part adds its term's value and its unit's
    closure. *)
| feval_benv_dm :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ Δy ⊢ Dy ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵈ m ‖ h )
where "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" := (feval_benv Θ Ξ ρ Φ ρ').

Scheme feval_exp_mut_ind := Induction for feval_exp Sort Prop
with feval_app_mut_ind := Induction for feval_app Sort Prop
with feval_exps_mut_ind := Induction for feval_exps Sort Prop
with feval_apps_mut_ind := Induction for feval_apps Sort Prop
with feval_modexp_mut_ind := Induction for feval_modexp Sort Prop
with feval_close_mut_ind := Induction for feval_close Sort Prop
with feval_appm_mut_ind := Induction for feval_appm Sort Prop
with feval_appms_mut_ind := Induction for feval_appms Sort Prop
with feval_sel_mut_ind := Induction for feval_sel Sort Prop
with feval_selm_mut_ind := Induction for feval_selm Sort Prop
with feval_selc_mut_ind := Induction for feval_selc Sort Prop
with feval_selmc_mut_ind := Induction for feval_selmc Sort Prop
with feval_benv_mut_ind := Induction for feval_benv Sort Prop
with feval_elim_mut_ind := Induction for feval_elim Sort Prop
with feval_ihs_mut_ind := Induction for feval_ihs Sort Prop
with feval_ih_mut_ind := Induction for feval_ih Sort Prop
with feval_mref_mut_ind := Induction for feval_mref Sort Prop
with feval_shty_mut_ind := Induction for feval_shty Sort Prop
with feval_ihty_mut_ind := Induction for feval_ihty Sort Prop
with feval_proj_mut_ind := Induction for feval_proj Sort Prop
with feval_nflds_mut_ind := Induction for feval_nflds Sort Prop
with feval_projs_mut_ind := Induction for feval_projs Sort Prop
with feval_ihtys_mut_ind := Induction for feval_ihtys Sort Prop.
Combined Scheme feval_mut_ind from
  feval_exp_mut_ind,
  feval_app_mut_ind,
  feval_exps_mut_ind,
  feval_apps_mut_ind,
  feval_modexp_mut_ind,
  feval_close_mut_ind,
  feval_appm_mut_ind,
  feval_appms_mut_ind,
  feval_sel_mut_ind,
  feval_selm_mut_ind,
  feval_selc_mut_ind,
  feval_selmc_mut_ind,
  feval_benv_mut_ind,
  feval_elim_mut_ind,
  feval_ihs_mut_ind,
  feval_ih_mut_ind,
  feval_mref_mut_ind,
  feval_shty_mut_ind,
  feval_ihty_mut_ind,
  feval_proj_mut_ind,
  feval_nflds_mut_ind,
  feval_projs_mut_ind,
  feval_ihtys_mut_ind.

#[export]
Hint Constructors feval_exp feval_proj feval_nflds feval_projs feval_elim feval_ihs feval_ih feval_mref feval_shty feval_ihty feval_ihtys feval_app feval_exps feval_apps
  feval_modexp feval_close feval_appm feval_appms feval_sel feval_selm feval_selc feval_selmc feval_benv : mctt.

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
      (forall Δ D ρ h1, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall h n r1, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ns r1, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h x r1, h ·ₜᶠ x Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜᶠ x Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h y r1, h ·ₘᶠ y Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘᶠ y Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2) /\
      (forall ρ p ups Bks j m r1,
          ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ p ups Bks B gs vs r1,
          ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ p ups Bks t v r1,
          ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> forall r2, ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall p ups j r1, ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r1 -> forall r2, ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall p ups ρ t a1, ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> forall a2, ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2) /\
      (forall p ups ρm As ρ t v a1, ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 ->
          forall a2, ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2) /\
      (forall f m r1, feval_proj Θ Ξ f m r1 -> forall r2, feval_proj Θ Ξ f m r2 -> r1 = r2) /\
      (forall ns m fl pre rs1, feval_nflds Θ Ξ ns m fl pre rs1 -> forall rs2, feval_nflds Θ Ξ ns m fl pre rs2 -> rs1 = rs2) /\
      (forall fl v ws1, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws1 -> forall ws2, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws2 -> ws1 = ws2) /\
      (forall p ups ρm As ρ gs vs r1, ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2).
  Proof.
    intros Θ Ξ; apply feval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         two resolutions of a global or a module agree, and two neutral
         scrutinees of [efq] that are equal have equal parts; an induction
         hypothesis is never spent on the premise it is about *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H : gc_term Θ Ξ ?p = Some _ |- _ =>
            destruct (gc_term_inv _ _ _ _ H) as [(? & ? & ?) | (? & ? & ? & ?)]; clear H
        | H1 : entry_tm ?E = Some _, H2 : entry_tm ?E = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : entry_unit ?E = Some _, H2 : entry_unit ?E = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_resolve Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : gc_entry Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _), H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            exfalso; rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H1) in H2; discriminate H2
        | H1 : ind_mlookup Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
            exfalso; exact (ind_mlookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
        | H1 : ind_mlookup Θ Ξ ?p = Some _, H2 : ind_mlookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : record_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : ind_mlookup Θ Ξ ?p = Some _ |- _ =>
            exfalso; rewrite (record_lookup_not_ind _ _ _ _ H1) in H2; discriminate H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
            exfalso; exact (record_lookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
        | H1 : field_index ?fl ?f = Some _, H2 : field_index ?fl ?f = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : field_lookup ?fl ?f = Some _, H2 : field_lookup ?fl ?f = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_view _ _ _ _ |- _ =>
            unfold im_starts, im_is_decl in H1; rewrite H2 in H1; cbn [orb] in H1; apply Nat.ltb_lt in H1
        | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_record _ _ _ |- _ =>
            unfold im_starts, im_is_decl in H1; rewrite H2 in H1; cbn [orb] in H1; apply Nat.ltb_lt in H1
        | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
            exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
        | H : 0 < List.length nil |- _ => exfalso; cbn in H; lia
        | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : feval_mref Θ Ξ ?p _ ?j _, H2 : ind_member _ ?j = Some ?M, H3 : im_head ?M = mh_record _ _ _ |- _ =>
            inversion H1; subst; clear H1
        | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : elim_grp_of ?oq ?m = Some _, H2 : elim_grp_of ?oq ?m = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _),
          H2 : forall U, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U) |- _ =>
            exfalso; exact (H2 _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : kgens Θ Ξ ?ρ ?H ?its ?g1, H2 : kgens Θ Ξ ?ρ ?H ?its ?g2 |- _ =>
            assert_fails (constr_eq g1 g2); pose proof (functional_kgens _ _ _ _ _ H1 H2); subst g2
        | H1 : kbody Θ Ξ ?ρ ?Φ ?Φ1, H2 : kbody Θ Ξ ?ρ ?Φ ?Φ2 |- _ =>
            assert_fails (constr_eq Φ1 Φ2); pose proof (functional_kbody _ _ _ _ H1 H2); subst Φ2
        | H1 : Members.gc_loc Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _) |- _ =>
            exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
        | H : _ ++ ce_ass _ :: nil = _ ++ ce_ass _ :: nil |- _ =>
            apply List.app_inj_tail in H as [? [= ?]]; subst
        | H : 0 < List.length (_ ++ _ :: nil) -> False |- _ =>
            exfalso; apply H; rewrite List.length_app; cbn; lia
        | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        | H : d_neut _ _ = d_neut _ _ |- _ => injection H; intros; subst; clear H
        | H : feval_selc _ _ _ nil _ |- _ => inversion H
        end;
      cbn [gu_params List.length] in *; try congruence; try lia; intuition (try congruence; try lia).
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

  Corollary functional_feval_elim : forall {Θ Ξ} ρ p ups Bks j m r1 r2,
      ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_feval_ihs : forall {Θ Ξ} ρ p ups Bks B gs vs r1 r2,
      ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_feval_ih : forall {Θ Ξ} ρ p ups Bks t v r1 r2,
      ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_mref : forall {Θ Ξ} p ups j r1 r2,
      ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r1 -> ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_shty : forall {Θ Ξ} p ups ρ t a1 a2,
      ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_ihty : forall {Θ Ξ} p ups ρm As ρ t v a1 a2,
      ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_ihtys : forall {Θ Ξ} p ups ρm As ρ gs vs r1 r2,
      ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_feval_projs : forall {Θ Ξ} fl v ws1 ws2,
      ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws1 -> ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws2 -> ws1 = ws2.
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

  (** A field of a value is one value. *)
  Corollary functional_feval_proj : forall {Θ Ξ} f m r1 r2,
      feval_proj Θ Ξ f m r1 -> feval_proj Θ Ξ f m r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto. Qed.

  (** So are the neutral projections of the fields of a neutral. *)
  Corollary functional_feval_nflds : forall {Θ Ξ} ns m fl pre rs1 rs2,
      feval_nflds Θ Ξ ns m fl pre rs1 -> feval_nflds Θ Ξ ns m fl pre rs2 -> rs1 = rs2.
  Proof. intros Θ Ξ; pose proof (@functional_feval Θ Ξ) as H; destruct_all; eauto. Qed.

#[export]
Hint Resolve functional_feval_exp functional_feval_elim functional_feval_ihs functional_feval_ih functional_feval_mref
  functional_feval_shty functional_feval_ihty functional_feval_ihtys functional_feval_projs functional_feval_app
  functional_feval_modexp functional_feval_proj functional_feval_nflds : mctt.

Ltac functional_feval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_feval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : feval_elim ?T ?X ?ρ ?p ?o ?Bks ?j ?m ?r1, H2 : feval_elim ?T ?X ?ρ ?p ?o ?Bks ?j ?m ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : feval_ihs ?T ?X ?ρ ?p ?o ?Bks ?B ?gs ?vs ?r1, H2 : feval_ihs ?T ?X ?ρ ?p ?o ?Bks ?B ?gs ?vs ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : feval_ih ?T ?X ?ρ ?p ?o ?Bks ?t ?v ?r1, H2 : feval_ih ?T ?X ?ρ ?p ?o ?Bks ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_ih; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_mref ?T ?X ?p ?ups ?j ?r1, H2 : feval_mref ?T ?X ?p ?ups ?j ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_mref; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_shty; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_ihty ?T ?X ?p ?u ?ρm ?As ?ρ ?t ?v ?r1, H2 : feval_ihty ?T ?X ?p ?u ?ρm ?As ?ρ ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_ihty; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_ihtys ?T ?X ?p ?u ?ρm ?As ?ρ ?gs ?vs ?r1, H2 : feval_ihtys ?T ?X ?p ?u ?ρm ?As ?ρ ?gs ?vs ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_ihtys; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_projs ?T ?X ?fl ?v ?r1, H2 : feval_projs ?T ?X ?fl ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_projs; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : (⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_exps; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_proj ?T ?X ?f ?m ?r1, H2 : feval_proj ?T ?X ?f ?m ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_proj; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : feval_nflds ?T ?X ?ns ?m ?fl ?pre ?r1, H2 : feval_nflds ?T ?X ?ns ?m ?fl ?pre ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_feval_nflds; eassumption] | tactic_error r2 r1]; clear H2
  end.
(** There is no [feval_sub] case: there is no fast evaluation of
    substitutions. *)
Ltac functional_feval_rewrite_clear := repeat functional_feval_rewrite_clear1.

(** ** Readback *)

Reserved Notation "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).
Reserved Notation "'Rfldsᶠ' v 'at' fl 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Fs" (at level 70, v at level 69, fl at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Fs at level 69).
Reserved Notation "'Rpsᶠ' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).
Reserved Notation "'Rcargsᶠ' vs 'at' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).
Reserved Notation "'Rshᶠ' v 'at' t 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ V" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, V at level 69).
Reserved Notation "'Rbrsᶠ' Bs 'at' cs 'of' Mi r 'of' Dc 'from' p ups Bks Mv A 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Bs'" (at level 70, Bs at level 69, cs at level 69, Mi at level 0, r at level 0, Dc at level 0, p at level 0, ups at level 0, Bks at level 0, Mv at level 0, A at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Bs' at level 69).
Reserved Notation "'Rblksᶠ' i Ms 'of' Dc 'from' p ups Bks sel 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ NBks" (at level 70, i at level 0, Ms at level 0, Dc at level 0, p at level 0, ups at level 0, Bks at level 0, sel at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, NBks at level 69).

Reserved Notation "'Fteleᶠ' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" (at level 70, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, vs at level 69).
Reserved Notation "'Fcargsᶠ' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" (at level 70, gs at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, vs at level 69).
Reserved Notation "'Fihsᶠ' vs 'at' gs' gs 'of' Dc 'under' ρm As 'at' p ups 'for' B 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ ihs" (at level 70, vs at level 69, gs' at level 0, gs at level 0, Dc at level 0, ρm at level 0, As at level 0, p at level 0, ups at level 0, B at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, ihs at level 69).
Reserved Notation "'⟦wihsᶠ' vs 'of' gs' gs 'of' Dc 'with' ihs 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs' at level 0, gs at level 0, Dc at level 0, ihs at level 0, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).

Generalizable All Variables.

(** The fresh variables of the telescopes of a group of inductive types,
    as in [Core.Semantic.Readback]. *)
Inductive fast_fresh_tele (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> list domain -> Prop :=
(** No entry, no variable *)
| fast_fresh_tele_nil :
  `( Fteleᶠ nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A variable of the first entry's type, then the rest under it *)
| fast_fresh_tele_cons :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⍮ S s ↘ vs ->
     Fteleᶠ ce_ass A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
where "'Fteleᶠ' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" := (fast_fresh_tele Θ Ξ ρ T s vs) : type_scope.

(** The arguments of a constructor, as in [Core.Semantic.Readback]. *)
Inductive fast_fresh_cargs (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> list domain -> Prop :=
(** No argument *)
| fast_fresh_cargs_nil :
  `( Fcargsᶠ nil of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A non-recursive argument, of its declared type *)
| fast_fresh_cargs_arg :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⍮ S s ↘ vs ->
     Fcargsᶠ ca_arg A :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
(** A recursive argument, of the type of its shape *)
| fast_fresh_cargs_rec :
  `( ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ S s ↘ vs ->
     Fcargsᶠ ca_rec t :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
where "'Fcargsᶠ' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" := (fast_fresh_cargs Θ Ξ p ups ρ gs s vs) : type_scope.

(** The recursive results of a branch [B] of a stuck eliminator, as fresh
    variables, as in [Core.Semantic.Readback]: the types of an argument's
    results the branch reads none of are not computed, and each of its
    variables gets [𝕌ω@0].  The results of the argument heading
    [ca_rec t :: gs], [gs] the kinds the branch's group has, are the
    variables [cargs_nrec D gs] on of [B] ([ihs_skipb]). *)
Inductive fast_fresh_ihs (Θ : gdeps) (Ξ : gstack) (ρ : env) (As : list exp) (p : qname) (ups : list domain) (Dc : ind_decl) (B : exp) :
  env -> list carg -> list carg -> list domain -> nat -> list domain -> Prop :=
(** No argument, no result *)
| fast_fresh_ihs_nil :
  `( Fihsᶠ nil at nil nil of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ nil )
(** A non-recursive argument: none, the argument entering [ρa] *)
| fast_fresh_ihs_arg :
  `( Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ↦ v ⍮ s ↘ ihs ->
     Fihsᶠ v :: vs at (ca_arg T' :: gs') (ca_arg T :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs )
(** An argument recursive in both, one of whose results the branch reads:
    a fresh variable at each recursive result's type along the paths of
    the container's *)
| fast_fresh_ihs_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = false ->
     ⟦ihtyᶠ v of t at p ups under ρ As ⟧ᶠ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
     fresh_leaf_vars (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) as' s ihs1 ->
     Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ (List.length ihs1 + s) ↘ ihs ->
     Fihsᶠ v :: vs at (ca_rec t' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ++ ihs )
(** One the branch reads none of the results of: each variable at
    [𝕌ω@0] *)
| fast_fresh_ihs_skip :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t)) = true ->
     fresh_leaf_vars (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
       (List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t))) s ihs1 ->
     Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ (List.length ihs1 + s) ↘ ihs ->
     Fihsᶠ v :: vs at (ca_rec t' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ++ ihs )
(** An argument recursive in [gs] only (nested through): no variable *)
| fast_fresh_ihs_nest :
  `( Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
     Fihsᶠ v :: vs at (ca_arg T' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs )
where "'Fihsᶠ' vs 'at' gs' gs 'of' Dc 'under' ρm As 'at' p ups 'for' B 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ ihs" :=
  (fast_fresh_ihs Θ Ξ ρm As p ups Dc B ρ gs' gs vs s ihs) : type_scope.

(** The recursive results a branch of a block is read under, as in
    [Core.Semantic.Readback]. *)
Inductive fast_wrap_ihs_eval (Θ : gdeps) (Ξ : gstack) (ρ : env) (p : qname) (ups : list domain) (Bks : list eblock) (Dc : ind_decl) :
  list carg -> list carg -> list domain -> list domain -> list domain -> Prop :=
(** No argument, no result *)
| fast_wrap_ihs_eval_nil :
  `( ⟦wihsᶠ nil of nil nil of Dc with nil under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** Recursive in both: along each path, the next of [ihs] at a path of
    the container's, the eliminator at one nested through *)
| fast_wrap_ihs_eval_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     wrap_leaf_vals (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) rs ihs ihs' r1 ->
     ⟦wihsᶠ vs of gs' gs of Dc with ihs' under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihsᶠ v :: vs of (ca_rec t' :: gs') (ca_rec t :: gs) of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ++ r )
(** Recursive for the branch's group only: the eliminator at the
    argument, along each path *)
| fast_wrap_ihs_eval_nest :
  `( ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihsᶠ v :: vs of (ca_arg T' :: gs') (ca_rec t :: gs) of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ++ r )
(** Non-recursive: no result *)
| fast_wrap_ihs_eval_arg :
  `( ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihsᶠ v :: vs of (ca_arg T' :: gs') (ca_arg T :: gs) of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦wihsᶠ' vs 'of' gs' gs 'of' Dc 'with' ihs 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" :=
  (fast_wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r) : type_scope.

#[export]
Hint Constructors fast_fresh_tele fast_fresh_cargs fast_fresh_ihs fast_wrap_ihs_eval : mctt.

(** Readback of values into normal and neutral forms in a context with [s]
    variables, as in [Core.Semantic.Readback]. *)
Inductive fread_nf (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> nf -> Prop :=
(** A type in a large universe: as a type *)
| fread_nf_type :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ 𝕌ω@i a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A type in a small universe: as a type *)
| fread_nf_stype :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ 𝕌@n a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A level reads back canonically: its atoms are read, then sorted and
    merged, and a dominated constant is dropped ([lvl_canon]). *)
| fread_nf_lvl :
  `( Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rnfᶠ ⇓ (Levelᵈ@n) (lvᵈ c xs) in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of (lvl_canon (c, ys)) )
(** A neutral level is the single atom at offset [0], of the sort of its
    type ([dsort]) *)
| fread_nf_lvl_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (Levelᵈ@n) (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ lvⁿ oz (mk_level_atom 0 (dsort a) M :: nil) )
(** η for [⊤]: every value of type [⊤] reads back as [⋆]. *)
| fread_nf_true :
  `( Rnfᶠ ⇓ ⊤ᵈ m in Θ ⍮ Ξ ⍮ s ↘ ⋆ⁿ )
(** A neutral of [⊥] *)
| fread_nf_False_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ ⊥ᵈ (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
(** A function, η-expanded *)
| fread_nf_fn :
  `( (** The normal form of the argument type. *)
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     (** The normal form of the η-expanded body. *)
     $ᶠ| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rnfᶠ ⇓ b m' in Θ ⍮ Ξ ⍮ S s ↘ M ->

     Rnfᶠ ⇓ (Πᵈ a ρ B) m in Θ ⍮ Ξ ⍮ s ↘ λⁿ A M )
(** A neutral at a neutral type *)
| fread_nf_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (⇑ a b) (⇑ c m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
(** A constructor of a declared member at all its parameters and
    arguments *)
| fread_nf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length as' = im_np D Mk ->
     List.length vs = (im_np D Mk + List.length gs)%nat ->
     Rpsᶠ as' at List.rev (im_params D Mk) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargsᶠ List.skipn (im_np D Mk) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ ⍮ env_args nil as' ⍮ s ↘ Args ->
     Rnfᶠ ⇓ (d_ind p k as') (d_con p k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p k c (Ps ++ Args) )
(** A constructor at a view, read as the view's constructor *)
| fread_nf_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_con Mj c = Some gs ->
     List.length as' = im_np D Mj ->
     List.length vs = (n + List.length gs)%nat ->
     Rpsᶠ as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargsᶠ List.skipn n vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ ⍮ env_args nil as' ⍮ s ↘ Args ->
     Rnfᶠ ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args) )
(** Any value at a record view, η-long, as in [Core.Semantic.Readback]:
    its constructor at the uniform parameters and the projections along
    the view's path *)
| fread_nf_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     List.length as' = ind_nu D ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     Rpsᶠ as' at List.rev (ind_uparams D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargsᶠ ws at gs of p as' in Θ ⍮ Ξ ⍮ env_args nil as' ⍮ s ↘ Args ->
     Rnfᶠ ⇓ (d_ind p j as') v in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args) )
(** A neutral of a member of a group with a block *)
| fread_nf_ind_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_is_rview Mk = false ->
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (d_ind p k as') (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
(** Any value of a record type, η-long, as in [Core.Semantic.Readback] *)
| fread_nf_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     Rpsᶠ ns at List.rev (record_params R) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rfldsᶠ v at record_fields R in Θ ⍮ Ξ ⍮ env_args nil ns ⍮ s ↘ Fs ->
     Rnfᶠ ⇓ (d_record p ns) v in Θ ⍮ Ξ ⍮ s ↘ nf_tuple p Ps (List.map fst (record_fields R)) Fs )
where "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_nf Θ Ξ s m M) : type_scope
with fread_ne (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> ne -> Prop :=
(** A variable, as a de Bruijn index *)
| fread_ne_var :
  `( Rneᶠ #ᵈ x in Θ ⍮ Ξ ⍮ s ↘ #ⁿ (s - x - 1) )
(** An application *)
| fread_ne_app :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ n in Θ ⍮ Ξ ⍮ s ↘ N ->
     Rneᶠ m $ᵈ n in Θ ⍮ Ξ ⍮ s ↘ M $ⁿ N )
(** The eliminator of [⊥] *)
| fread_ne_exfalso :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ⊥ᵈ s ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     (** The neutral form of the scrutinee. *)
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->

     Rneᶠ efqᵈ m under ρ return B in Θ ⍮ Ξ ⍮ s ↘ efqⁿ M return B' )
(** A global *)
| fread_ne_glob :
  `( Rneᶠ d_glob p in Θ ⍮ Ξ ⍮ s ↘ ne_glob p )
(** A stuck eliminator, as in [Core.Semantic.Readback] *)
| fread_ne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     blocks_nm_at D None Bks ->
     rview_leaf_arity D ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) ->
     Rpsᶠ pre at List.rev (ind_uparams Dq) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Us ->
     Rblksᶠ 0 (ind_bmembers Dq) of Dq from p ups Bks (im_sel Mj) in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rneᶠ d_elim ρ Bks p ups j as' m in Θ ⍮ Ξ ⍮ s ↘ ne_elim pc Us k NBks M )
(** The field of a neutral *)
| fread_ne_proj :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rneᶠ d_proj f m in Θ ⍮ Ξ ⍮ s ↘ ne_proj f M )
where "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_ne Θ Ξ s m M) : type_scope
with fread_typ (Θ : gdeps) (Ξ : gstack) : nat -> domain -> nf -> Prop :=
(** A large universe *)
| fread_typ_univ :
  `( Rtypᶠ 𝕌ω@i in Θ ⍮ Ξ ⍮ s ↘ Typeωⁿ@i )
(** A small universe reads back as the universe at the canonical form its
    level reads back as. *)
| fread_typ_suniv :
  `( Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of L ->
     Rtypᶠ 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of L )
(** The type of levels *)
| fread_typ_level :
  `( Rtypᶠ Levelᵈ@n in Θ ⍮ Ξ ⍮ s ↘ Levelⁿ@n )
(** [⊤] *)
| fread_typ_True :
  `( Rtypᶠ ⊤ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊤ⁿ )
(** [⊥] *)
| fread_typ_False :
  `( Rtypᶠ ⊥ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊥ⁿ )
(** A [Π] *)
| fread_typ_pi :
  `( (** The normal form of the argument type. *)
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->

     (** The normal form of the return type. *)
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     Rtypᶠ Πᵈ a ρ B in Θ ⍮ Ξ ⍮ s ↘ Πⁿ A B')
(** A neutral type *)
| fread_typ_neut :
  `( Rneᶠ b in Θ ⍮ Ξ ⍮ s ↘ B ->
     Rtypᶠ ⇑ a b in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ B)
(** A type former without arguments reads back without its declaration:
    it has no parameter to read. *)
| fread_typ_indty_nil :
  `( Rtypᶠ d_ind p k nil in Θ ⍮ Ξ ⍮ s ↘ nf_indty p k nil )
(** At one argument or more, each read at its type. *)
| fread_typ_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length (a :: as') = im_np D Mk ->
     Rpsᶠ (a :: as') at List.rev (im_params D Mk) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtypᶠ d_ind p k (a :: as') in Θ ⍮ Ξ ⍮ s ↘ nf_indty p k Ps )
(** A record type at all its parameters, each read at its type. *)
| fread_typ_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     Rpsᶠ ns at List.rev (record_params R) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtypᶠ d_record p ns in Θ ⍮ Ξ ⍮ s ↘ nf_record p Ps )
where "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fread_typ Θ Ξ s m M) : type_scope
(** The atoms of a level, read one by one. *)
with fread_la (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> list level_atom -> Prop :=
(** No atom *)
| fread_la_nil :
  `( Rlaᶠ nil in Θ ⍮ Ξ ⍮ s ↘ nil )
(** The first atom's neutral, then the rest *)
| fread_la_cons :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rlaᶠ (k, n, m) :: xs in Θ ⍮ Ξ ⍮ s ↘ mk_level_atom k n M :: ys )
where "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" := (fread_la Θ Ξ s xs ys) : type_scope
(** Values at a telescope, outermost first. *)
with fread_ps (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> list nf -> Prop :=
(** No value *)
| fread_ps_nil :
  `( Rpsᶠ nil at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The first value at its type, then the rest with it in the
    environment *)
| fread_ps_cons :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ↦ v ⍮ s ↘ Vs ->
     Rpsᶠ v :: vs at ce_ass A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
where "'Rpsᶠ' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (fread_ps Θ Ξ s ρ T vs Ms) : type_scope
(** The fields of a record value, each at its type, as in
    [Core.Semantic.Readback]. *)
with fread_fields (Θ : gdeps) (Ξ : gstack) : nat -> env -> list (string * exp) -> domain -> list nf -> Prop :=
(** No field left *)
| fread_fields_nil :
  `( Rfldsᶠ v at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The next field's projection at its type, then the rest with it in the
    environment *)
| fread_fields_cons :
  `( feval_proj Θ Ξ f v r ->
     ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ t ->
     Rnfᶠ ⇓ t r in Θ ⍮ Ξ ⍮ s ↘ F ->
     Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ↦ r ⍮ s ↘ Fs ->
     Rfldsᶠ v at (f, T) :: fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ F :: Fs )
where "'Rfldsᶠ' v 'at' fl 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Fs" := (fread_fields Θ Ξ s ρ fl v Fs) : type_scope
(** The arguments of a constructor, each at its type. *)
with fread_cargs (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> list nf -> Prop :=
(** No argument *)
| fread_cargs_nil :
  `( Rcargsᶠ nil at nil of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A non-recursive argument, at its declared type *)
| fread_cargs_arg :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ↦ v ⍮ s ↘ Vs ->
     Rcargsᶠ v :: vs at ca_arg A :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
(** A recursive argument, along its shape *)
| fread_cargs_rec :
  `( Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V ->
     Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs ->
     Rcargsᶠ v :: vs at ca_rec t :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
where "'Rcargsᶠ' vs 'at' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (fread_cargs Θ Ξ s p ups ρ gs vs Ms) : type_scope
(** A recursive argument of shape [t], as in [Core.Semantic.Readback]. *)
with fread_shape (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> ptyp -> domain -> nf -> Prop :=
(** At the end: at the group's own member at the shape's parameters *)
| fread_shape_self :
  `( ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     Rnfᶠ ⇓ (d_ind p j (ups ++ bs)) v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rshᶠ v at pt_self j Ps of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V )
(** At a domain: a λ, the rest read under a fresh variable of it *)
| fread_shape_pi :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ s ↘ A ->
     $ᶠ| v & ⇑! b s | Θ ⍮ Ξ ↘ r ->
     Rshᶠ r at t of p ups in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! b s ⍮ S s ↘ V ->
     Rshᶠ v at pt_pi B t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ λⁿ A V )
where "'Rshᶠ' v 'at' t 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ V" := (fread_shape Θ Ξ s p ups ρ t v V) : type_scope
(** The blocks of a stuck eliminator, as in [Core.Semantic.Readback]. *)
with fread_blocks (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                       option (list nat) -> nat -> list imember -> list normal_block -> Prop :=
(** No member left *)
| fread_blocks_nil :
  `( Rblksᶠ i nil of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The block for the member [Mi]: the motive, then the branches, then
    the rest *)
| fread_blocks_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     eb_nm b = S (im_nn Mi) ->
     ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
     Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
     ⟦ eb_motive b ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat) :: nil) ↘ a ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ S (s + im_nn Mi)%nat ↘ A' ->
     Rbrsᶠ eb_brs b at im_cons Mi of Mi (pk, k, pre) of Dc from p ups Bks Mv (eb_motive b) in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
     Rblksᶠ (S i) Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
     Rblksᶠ i (Mi :: Ms) of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ mk_normal_block (S (im_nn Mi)) A' Bs' :: NBks )
where "'Rblksᶠ' i Ms 'of' Dc 'from' p ups Bks sel 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ NBks" := (fread_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks) : type_scope
(** The branches of a block, as in [Core.Semantic.Readback]; the results
    of an argument the branch reads none of get the type [𝕌ω@0]
    ([fast_fresh_ihs_skip]). *)
with fread_brs (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                    imember -> exp -> imember -> (qname * nat * list domain) ->
                                    list (string * list carg) -> list (string * nat * exp) -> list normal_branch -> Prop :=
(** No constructor left *)
| fread_brs_nil :
  `( Rbrsᶠ nil at nil of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The branch of the next constructor, under its fresh variables, at
    the motive's instance, then the rest; the fresh recursive results are
    as many as the branch read binds, the gate of [read_brs_cons] *)
| fread_brs_cons :
  `( ind_con Mv c = Some gs ->
     ind_lookup Θ Ξ p = Some D ->
     n0 = (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat ->
     n = (im_nn Mi + List.length gs' + cargs_nrec Dc gs')%nat ->
     cargs_nin D Dc gs' gs = cargs_nrec Dc gs' ->
     cargs_plen D gs ->
     Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
     Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi)%nat ↘ vs ->
     Fihsᶠ vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups for B in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns)
       ⍮ (s + im_nn Mi + List.length gs')%nat ↘ ihs ->
     ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ wihs) ↘ b ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con pk k c (pre ++ ns ++ vs) :: nil) ↘ t ->
     Rnfᶠ ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
     Rbrsᶠ Bs at cs of Mi (pk, k, pre) of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
     Rbrsᶠ (c, n0, B) :: Bs at (c, gs') :: cs of Mi (pk, k, pre) of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s
       ↘ mk_normal_branch c n B' :: Bs' )
where "'Rbrsᶠ' Bs 'at' cs 'of' Mi r 'of' Dc 'from' p ups Bks Mv A 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Bs'" :=
  (fread_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs') : type_scope
.

Scheme fread_nf_mut_ind := Induction for fread_nf Sort Prop
with fread_ne_mut_ind := Induction for fread_ne Sort Prop
with fread_typ_mut_ind := Induction for fread_typ Sort Prop
with fread_la_mut_ind := Induction for fread_la Sort Prop
with fread_ps_mut_ind := Induction for fread_ps Sort Prop
with fread_cargs_mut_ind := Induction for fread_cargs Sort Prop
with fread_shape_mut_ind := Induction for fread_shape Sort Prop
with fread_blocks_mut_ind := Induction for fread_blocks Sort Prop
with fread_brs_mut_ind := Induction for fread_brs Sort Prop
with fread_fields_mut_ind := Induction for fread_fields Sort Prop.
Combined Scheme fread_mut_ind from
  fread_nf_mut_ind,
  fread_ne_mut_ind,
  fread_typ_mut_ind,
  fread_la_mut_ind,
  fread_ps_mut_ind,
  fread_cargs_mut_ind,
  fread_shape_mut_ind,
  fread_blocks_mut_ind,
  fread_brs_mut_ind,
  fread_fields_mut_ind.

#[export]
Hint Constructors fread_nf fread_ne fread_typ fread_la fread_ps fread_fields fread_cargs fread_shape fread_blocks fread_brs : mctt.

  Lemma functional_fast_fresh_tele : forall {Θ Ξ} ρ T s vs1, Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs1 ->
      forall vs2, Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ reflexivity |].
    functional_feval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_fast_fresh_cargs : forall {Θ Ξ} p ups ρ gs s vs1, Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs1 ->
      forall vs2, Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ auto | |];
      functional_feval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_fast_fresh_ihs : forall {Θ Ξ} ρ As p ups Dc B ρa gs' gs vs s ihs1,
      Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ->
      forall ihs2, Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs2 -> ihs1 = ihs2.
  Proof.
    induction 1; intros * Hother; inversion Hother; subst; auto.
    all: repeat match goal with
           | H1 : ind_lookup ?T ?X ?p = Some _, H3 : ind_lookup ?T ?X ?p = Some _ |- _ =>
               rewrite H1 in H3; injection H3 as ?; subst
           end; try congruence.
    all: functional_feval_rewrite_clear.
    all: match goal with H1 : fresh_leaf_vars ?b ?a ?s ?v1, H3 : fresh_leaf_vars ?b ?a ?s ?v2 |- _ =>
           pose proof (functional_fresh_leaf_vars _ _ _ _ H1 _ H3); subst end.
    all: f_equal; auto.
  Qed.

  Lemma functional_fast_wrap_ihs_eval : forall {Θ Ξ} ρ p ups Bks Dc gs' gs vs ihs r1,
      ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      forall r2, ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof.
    induction 1; intros * Hother; inversion Hother; subst; auto.
    all: repeat match goal with
           | H1 : ind_lookup ?T ?X ?p = Some _, H3 : ind_lookup ?T ?X ?p = Some _ |- _ =>
               rewrite H1 in H3; injection H3 as ?; subst
           end.
    all: functional_feval_rewrite_clear.
    all: try match goal with H1 : wrap_leaf_vals ?b ?r ?i _ _, H3 : wrap_leaf_vals ?b ?r ?i _ _ |- _ =>
           destruct (functional_wrap_leaf_vals _ _ _ _ _ H1 _ _ H3); subst end.
    all: f_equal; auto.
  Qed.

  Ltac functional_fast_fresh_rewrite_clear :=
    repeat match goal with
      | H1 : fast_fresh_tele ?T ?X ?ρ ?L ?s ?v1, H2 : fast_fresh_tele ?T ?X ?ρ ?L ?s ?v2 |- _ =>
          pose proof (functional_fast_fresh_tele _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : fast_fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v1, H2 : fast_fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v2 |- _ =>
          pose proof (functional_fast_fresh_cargs _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : fast_fresh_ihs ?T ?X ?ρ ?A ?p ?u ?Dc ?B ?ρa ?gs' ?gs ?vs ?s ?i1, H2 : fast_fresh_ihs ?T ?X ?ρ ?A ?p ?u ?Dc ?B ?ρa ?gs' ?gs ?vs ?s ?i2 |- _ =>
          pose proof (functional_fast_fresh_ihs _ _ _ _ _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : fast_wrap_ihs_eval ?T ?X ?ρ ?p ?o ?Bks ?Dc ?g' ?g ?vs ?ih ?r1, H2 : fast_wrap_ihs_eval ?T ?X ?ρ ?p ?o ?Bks ?Dc ?g' ?g ?vs ?ih ?r2 |- _ =>
          pose proof (functional_fast_wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : feval_projs ?T ?X ?fl ?v ?w1, H2 : feval_projs ?T ?X ?fl ?v ?w2 |- _ =>
          pose proof (functional_feval_projs _ _ _ _ H1 H2); subst; clear H2
      | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
          rewrite H1 in H2; injection H2; intros; subst; clear H2
      | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
          exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
      | H1 : ⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?b1, H2 : ⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?b2 |- _ =>
          pose proof (functional_feval_exps _ _ _ _ H1 H2); subst; clear H2
      | H1 : feval_mref ?T ?X ?p ?ups ?j ?r1, H2 : feval_mref ?T ?X ?p ?ups ?j ?r2 |- _ =>
          let E := fresh "E" in
          pose proof (functional_feval_mref _ _ _ _ _ H1 H2) as E; injection E; intros; subst; clear H2
      | H : (_, _) = (_, _) |- _ => injection H; intros; subst; clear H
      | H1 : ind_lookup ?T ?X ?p = Some _, H2 : ind_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : record_lookup ?T ?X ?p = Some _, H2 : record_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
          rewrite H1 in H2; injection H2; intros; subst; clear H2
      | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
          rewrite H1 in H2; injection H2; intros; subst; clear H2
      | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
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
      (forall s p ups ρ gs vs Vs1, Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs1 ->
         forall Vs2, Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs2 -> Vs1 = Vs2) /\
      (forall s p ups ρ t v V1, Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V1 ->
         forall V2, Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V2 -> V1 = V2) /\
      (forall s ρ p ups Bks Dc sel i Ms NBks1, Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks1 ->
         forall NBks2, Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks2 -> NBks1 = NBks2) /\
      (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs1, Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs1 ->
         forall Bs2, Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs2 -> Bs1 = Bs2) /\
      (forall s ρ fl v Fs1, Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs1 -> forall Fs2, Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs2 -> Fs1 = Fs2).
  Proof.
    intros Θ Ξ; apply fread_mut_ind; intros; progressive_inversion; functional_feval_rewrite_clear;
      functional_fast_fresh_rewrite_clear; functional_feval_rewrite_clear;
      (** The two rules of a type former exclude each other. *)
      try contradiction.
    all: try solve [ apply nf_univ_of_cong; eauto | f_equal; solve [eauto] | repeat f_equal; solve [eauto] ].
    (** A constructor at an inductive type, read by one of two rules (a
        declared member, or a view): the other side is inverted here, the
        rules excluding each other by the member's head. *)
    all: match goal with
         | H : fread_nf _ _ _ _ _ |- _ = _ => inversion H; subst; clear H
         | H : fread_ne _ _ _ _ _ |- _ = _ => inversion H; subst; clear H
         end;
      functional_fast_fresh_rewrite_clear; functional_feval_rewrite_clear; try congruence;
      repeat match goal with
        | H1 : List.length ?v = (?a + ?g)%nat, H2 : List.length ?v = (?b + ?g)%nat |- _ =>
            assert_fails (constr_eq a b); assert (a = b) by lia; subst b
        end;
      repeat f_equal; solve [eauto].
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

(** One fresh variable per member of a telescope, per argument, and per
    recursive argument of the eliminated group. *)
Lemma fast_fresh_tele_length : forall {Θ Ξ} ρ T s vs,
    Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

Lemma fast_fresh_cargs_length : forall {Θ Ξ} p ups ρ gs s vs,
    Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> List.length vs = List.length gs.
Proof. induction 1; cbn; congruence. Qed.

Lemma fast_fresh_ihs_length : forall {Θ Ξ} ρ As p ups Dc B ρa gs' gs vs s ihs D, ind_lookup Θ Ξ p = Some D ->
    Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> List.length ihs = cargs_nin D Dc gs' gs.
Proof.
  intros * HD H; induction H; cbn; try congruence.
  all: match goal with H1 : ind_lookup _ _ _ = Some _, H2 : ind_lookup _ _ _ = Some _ |- _ =>
         rewrite H1 in H2; injection H2 as <- end.
  all: match goal with Hf : fresh_leaf_vars _ _ _ _ |- _ => rewrite List.length_app, (fresh_leaf_vars_length _ _ _ _ Hf) end.
  all: rewrite IHfast_fresh_ihs by assumption.
  all: unfold leaves_in_count; f_equal.
  all: clear; induction (shape_leaves (rv_leaves D) 0 t); cbn; [ reflexivity |].
  all: destruct (leaf_in Dc t' a); cbn; congruence.
Qed.
