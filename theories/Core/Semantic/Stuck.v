(** * Stuck Globals in Normal Forms

    At any global context, a global reaches a normal form only as the head of
    a neutral, and only when it does not unfold: it resolves to an opaque
    definition or to an axiom ([gstuck]).  This is the invariant of
    [Core.Semantic.Transparency] with the stuck globals allowed instead of
    ruled out; at a transparent context there are none, which is
    [nbe_clean]. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Normal Forms Whose Global Heads Satisfy [G] *)

(** [nf_stuck G W]: every global heading a neutral in [W] satisfies [G];
    mutually, in the neutral [M]. *)
Fixpoint nf_stuck (G : qname -> Prop) (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_True | nf_true | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_stuck G (atom_level a)) xs
  | nf_pi A B | nf_fn A B => nf_stuck G A /\ nf_stuck G B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list (nf_stuck G) Ms
  | nf_neut M => ne_stuck G M
  | nf_record _ Ms => all_list (nf_stuck G) Ms
  | nf_tuple _ Ms _ Ns => all_list (nf_stuck G) Ms /\ all_list (nf_stuck G) Ns
  end
with ne_stuck (G : qname -> Prop) (M : ne) : Prop :=
  match M with
  | ne_exfalso A M => nf_stuck G A /\ ne_stuck G M
  | ne_elim _ Us _ Bks M =>
      all_list (nf_stuck G) Us /\
      all_list (fun b => nf_stuck G (block_motive b) /\ all_list (fun br => nf_stuck G (branch_body br)) (block_branches b)) Bks /\
      ne_stuck G M
  | ne_app M N => ne_stuck G M /\ nf_stuck G N
  | ne_var _ => True
  | ne_glob p => G p
  | ne_proj _ M => ne_stuck G M
  end.

Lemma la_stuck_sort : forall G xs, all_list (fun a => ne_stuck G (atom_level a)) xs ->
    all_list (fun a => ne_stuck G (atom_level a)) (la_sort xs).
Proof. intros * H; apply la_all_all_list, la_all_sort, la_all_all_list; assumption. Qed.

(** A global that does not unfold: an opaque definition or an axiom. *)
#[warnings="-cannot-define-projection"]
Record gstuck (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop := mk_gstuck
  { gst_transparent : bool
  ; gst_private : bool
  ; gst_typ : typ
  ; gst_body : option exp
  ; gst_resolve : gc_resolve Θ Ξ p = Some (ge_def gst_transparent gst_private gst_typ gst_body)
  ; gst_opaque : gst_transparent = false \/ gst_body = None }.

Section Stuck.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma gstuck_intro : forall p b pv A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv A B) -> b = false \/ B = None -> gstuck Θ Ξ p.
  Proof. intros * Hr Ho; exact (mk_gstuck _ _ _ _ _ _ _ Hr Ho). Qed.
  #[local] Hint Resolve gstuck_intro : mctt.

(** ** Values Whose Global Neutrals Are Stuck *)

(** [dstuck d]: every global neutral in the value [d], its closures'
    environments included, is stuck ([gstuck]); mutually, for the other
    sorts of values. *)
Inductive dstuck : domain -> Prop :=
(** A [Π]: its domain and its closure's environment *)
| dstuck_pi : forall a (ρ : env) B, dstuck a -> (forall x, destuck (env_entry ρ x)) -> dstuck (Πᵈ a ρ B)
(** A large universe *)
| dstuck_univ : forall i, dstuck 𝕌ω@i
(** A small universe: its level *)
| dstuck_suniv : forall l, dstuck l -> dstuck 𝕌@l
(** A type of levels *)
| dstuck_level : forall n, dstuck (Levelᵈ@n)
(** A level: its atoms *)
| dstuck_lvl : forall c xs, dstuck_la xs -> dstuck (lvᵈ c xs)
(** The unit type *)
| dstuck_True : dstuck ⊤ᵈ
(** The unit's element *)
| dstuck_true : dstuck ⋆ᵈ
(** The empty type *)
| dstuck_False : dstuck ⊥ᵈ
(** A λ: its closure's environment *)
| dstuck_fn : forall (ρ : env) M, (forall x, destuck (env_entry ρ x)) -> dstuck (λᵈ ρ M)
(** A neutral: its type and itself *)
| dstuck_neut : forall a m, dstuck a -> dstuck_ne m -> dstuck (⇑ a m)
(** A member of a module value: the module value *)
| dstuck_member : forall h ch, dmstuck h -> dstuck (d_member h ch)
(** A type former: its arguments *)
| dstuck_indty : forall p k args, (forall a, In a args -> dstuck a) -> dstuck (d_ind p k args)
(** A constructor: its arguments *)
| dstuck_con : forall p k c args, (forall a, In a args -> dstuck a) -> dstuck (d_con p k c args)
(** A recursive result at a function shape: the eliminator's environment,
    its uniform parameters and the argument *)
| dstuck_ihfn : forall (ρ : env) Bks p ups t f, (forall x, destuck (env_entry ρ x)) ->
    (forall a, In a ups -> dstuck a) -> dstuck f -> dstuck (d_ihfn ρ Bks p ups t f)
(** A shape family: its uniform parameters and its environment *)
| dstuck_shfam : forall p ups (ρ : env) t, (forall a, In a ups -> dstuck a) -> (forall x, destuck (env_entry ρ x)) ->
    dstuck (d_shfam p ups ρ t)
(** A recursive result's family: the motive's and the shape's
    environments, and the argument *)
| dstuck_ihfam : forall (ρm : env) As (ρ : env) t f, (forall x, destuck (env_entry ρm x)) -> (forall x, destuck (env_entry ρ x)) ->
    dstuck f -> dstuck (d_ihfam ρm As ρ t f)
(** A record type former: its arguments *)
| dstuck_record : forall p args, (forall a, In a args -> dstuck a) -> dstuck (d_record p args)
(** A record value: its fields *)
| dstuck_tuple : forall vs, (forall f a, In (f, a) vs -> dstuck a) -> dstuck (d_tuple vs)
with dstuck_ne : domain_ne -> Prop :=
(** A variable *)
| dstuck_var : forall x, dstuck_ne (#ᵈ x)
(** A global, only if it is stuck *)
| dstuck_glob : forall p, gstuck Θ Ξ p -> dstuck_ne (d_glob p)
(** An application: its head and its argument *)
| dstuck_app : forall m n, dstuck_ne m -> dstuck_nf n -> dstuck_ne (m $ᵈ n)
(** A stuck [efq]: its environment and its scrutinee *)
| dstuck_exfalso : forall (ρ : env) A m,
    (forall x, destuck (env_entry ρ x)) -> dstuck_ne m ->
    dstuck_ne (efqᵈ m under ρ return A)
(** A stuck eliminator: its environment, its uniform parameters, its
    parameters and its scrutinee *)
| dstuck_elim : forall (ρ : env) Bks p ups j args m,
    (forall x, destuck (env_entry ρ x)) -> (forall a, In a ups -> dstuck a) ->
    (forall a, In a args -> dstuck a) -> dstuck_ne m ->
    dstuck_ne (d_elim ρ Bks p ups j args m)
(** The field of a neutral: the neutral *)
| dstuck_proj : forall f m, dstuck_ne m -> dstuck_ne (d_proj f m)
with dstuck_nf : domain_nf -> Prop :=
| dstuck_dom : forall a m, dstuck a -> dstuck m -> dstuck_nf (⇓ a m)
with dmstuck : dmod -> Prop :=
| dmstuck_global : forall p args, (forall a, In a args -> dstuck a) -> dmstuck (dm_global p args)
| dmstuck_local : forall Δ D (ρ : env),
    (forall x, destuck (env_entry ρ x)) -> dmstuck (dm_local Δ D ρ)
| dmstuck_member : forall h ch, dmstuck h -> dmstuck (dm_member h ch)
with dstuck_la : list (nat * nat * domain_ne) -> Prop :=
| dstuck_la_nil : dstuck_la nil
| dstuck_la_cons : forall k n m xs, dstuck_ne m -> dstuck_la xs -> dstuck_la ((k, n, m) :: xs)
with destuck : dentry -> Prop :=
| destuck_term : forall d, dstuck d -> destuck (de_term d)
| destuck_mod : forall h, dmstuck h -> destuck (de_mod h).

Definition env_stuck (ρ : env) : Prop := forall x, destuck (env_entry ρ x).

(** The uniform parameters an eliminator carries, stuck.  A definition, so
    that the search does not use it as a lemma about every value. *)
Definition ups_stuck (ups : list domain) : Prop := forall a, In a ups -> dstuck a.

#[local] Hint Constructors dstuck dstuck_ne dstuck_nf dstuck_la dmstuck destuck : mctt.

(** [dstuck_lvl] is not a hint: its premise is a quantified statement about the
    atoms, which the search would try to prove of an unknown level.  The
    level operations are reached through the three lemmas below instead. *)
#[local] Remove Hints dstuck_lvl : mctt.

(** Nor are the rules of inductive types, whose premises are about all the
    members of a list: [all_in_with] reaches them instead. *)
#[local] Remove Hints dstuck_indty dstuck_con dstuck_elim dstuck_shfam dstuck_ihfn dstuck_ihfam : mctt.
(** Nor are those of records, for the same reason. *)
#[local] Remove Hints dstuck_record dstuck_tuple : mctt.
#[local] Hint Unfold env_stuck : mctt.

Lemma env_stuck_nil : env_stuck nil.
Proof. intros x; induction x; cbn; auto with mctt. Qed.

Lemma env_stuck_extend : forall ρ d, env_stuck ρ -> dstuck d -> env_stuck (ρ ↦ d).
Proof. intros * Hρ Hd [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_extend_mod : forall ρ h, env_stuck ρ -> dmstuck h -> env_stuck (ρ ↦ᵐ h).
Proof. intros * Hρ Hh [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_var : forall ρ x, env_stuck ρ -> dstuck (ρ x).
Proof. intros * H; unfold env_var; destruct (H x); auto with mctt. Qed.

Lemma env_stuck_mod : forall ρ x, env_stuck ρ -> dmstuck (env_mod ρ x).
Proof. intros * H; unfold env_mod; destruct (H x); auto with mctt; constructor; intros ? []. Qed.

Lemma env_stuck_args : forall args ρ, env_stuck ρ -> (forall a, In a args -> dstuck a) -> env_stuck (env_args ρ args).
Proof.
  induction args; intros * Hρ Ha; cbn; [ assumption |].
  apply IHargs; [ apply env_stuck_extend; auto with datatypes | intros; apply Ha; right; assumption ].
Qed.

Lemma stuck_app_snoc : forall (args : list domain) n,
    (forall a, In a args -> dstuck a) -> dstuck n -> forall a, In a (args ++ n :: nil) -> dstuck a.
Proof. intros * H Hn a Ha; apply in_app_or in Ha as [Ha | [<- | []]]; auto. Qed.

Lemma stuck_app : forall (l1 l2 : list domain),
    (forall a, In a l1 -> dstuck a) -> (forall a, In a l2 -> dstuck a) -> forall a, In a (l1 ++ l2) -> dstuck a.
Proof. intros * H1 H2 a Ha; apply in_app_or in Ha as [Ha | Ha]; auto. Qed.

(** The neutral projections of the fields of a neutral of a record type,
    one more: the next one at its type, then the rest after it. *)
Lemma nflds_cons_stuck : forall t m g rs pre ns,
    dstuck t -> (forall x, In x ns -> dstuck x) -> dstuck_ne m -> (forall x, In x pre -> dstuck x) ->
    ((forall x, In x ns -> dstuck x) -> dstuck_ne m ->
       (forall y, In y (pre ++ ⇑ t (d_proj g m) :: nil) -> dstuck y) -> forall z, In z rs -> dstuck z) ->
    forall d, In d (⇑ t (d_proj g m) :: rs) -> dstuck d.
Proof.
  intros * Ht Hns Hm Hpre IH d [<- | Hd]; [ constructor; [ exact Ht | constructor; exact Hm ] |].
  apply (IH Hns Hm); [| exact Hd ].
  apply stuck_app_snoc; [ exact Hpre | constructor; [ exact Ht | constructor; exact Hm ] ].
Qed.

Lemma env_stuck_entry : forall ρ x, env_stuck ρ -> destuck (env_entry ρ x).
Proof. intros * H; exact (H x). Qed.


Lemma dmstuck_global_nil : forall p, dmstuck (dm_global p nil).
Proof. intros; constructor; intros ? []. Qed.

(** The atoms a level value is built of.  The flat view of a neutral is the
    single atom [(0, m)], so the level operations preserve the property. *)
Lemma dstuck_la_view : forall d, dstuck d -> dstuck_la (dlvl_atoms d).
Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

Lemma dstuck_la_suc : forall xs, dstuck_la xs -> dstuck_la (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
Proof. induction 1; cbn; repeat constructor; assumption. Qed.

Lemma dstuck_la_app : forall xs ys, dstuck_la xs -> dstuck_la ys -> dstuck_la (xs ++ ys).
Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

Lemma dstuck_lvl_lit : forall n, dstuck (dlvl_lit n).
Proof. intros; repeat constructor. Qed.

Lemma dstuck_lvl_suc : forall d, dstuck d -> dstuck (dlvl_suc d).
Proof. intros; unfold dlvl_suc; constructor; apply dstuck_la_suc, dstuck_la_view; assumption. Qed.

Lemma dstuck_lvl_max : forall d e, dstuck d -> dstuck e -> dstuck (dlvl_max d e).
Proof. intros; unfold dlvl_max; constructor; apply dstuck_la_app; apply dstuck_la_view; assumption. Qed.

#[local] Hint Resolve env_stuck_nil env_stuck_extend env_stuck_extend_mod env_stuck_var env_stuck_mod
  env_stuck_args stuck_app_snoc dmstuck_global_nil env_stuck_entry : mctt.

(** The level lemmas are [Hint Extern], keyed on the operation in the goal: as
    [Hint Resolve] their conclusions would match a goal about an unknown
    value, since [dlvl_suc] and [dlvl_max] unfold to a flat level. *)
#[local] Hint Extern 1 (dstuck (dlvl_lit _)) => apply dstuck_lvl_lit : mctt.
#[local] Hint Extern 1 (dstuck (dlvl_suc _)) => apply dstuck_lvl_suc : mctt.
#[local] Hint Extern 1 (dstuck (dlvl_max _ _)) => apply dstuck_lvl_max : mctt.


  Lemma eval_stuck :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_stuck ρ -> dstuck m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dstuck m -> dstuck n -> dstuck r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> env_stuck ρ -> forall a, In a ms -> dstuck a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> dstuck m -> (forall a, In a args -> dstuck a) -> dstuck r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmstuck h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmstuck h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmstuck h -> dstuck n -> dmstuck r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> dmstuck h -> (forall a, In a ns -> dstuck a) -> dmstuck r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmstuck h -> dstuck r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmstuck h -> dmstuck r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmstuck h -> dstuck r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmstuck h -> dmstuck r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> env_stuck ρ -> env_stuck ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_stuck ρ ->
       ups_stuck ups -> dstuck m -> dstuck r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       env_stuck ρ -> ups_stuck ups -> (forall a, In a vs -> dstuck a) -> forall a, In a ihs -> dstuck a) /\
    (forall ρ p ups Bks t v r, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_stuck ρ ->
       ups_stuck ups -> dstuck v -> dstuck r) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> (forall u, In u ups -> dstuck u) -> forall a, In a (snd r) -> dstuck a) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> (forall u, In u ups -> dstuck u) -> env_stuck ρ -> dstuck a) /\
    (forall ρm As ρ t v a, ⟦ihty v of t under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> env_stuck ρm -> env_stuck ρ -> dstuck v -> dstuck a) /\
    (forall f m r, eval_proj Θ Ξ f m r -> dstuck m -> dstuck r) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs -> (forall a, In a ns -> dstuck a) -> dstuck_ne m ->
       (forall a, In a pre -> dstuck a) -> forall a, In a rs -> dstuck a).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_stuck ρ -> dstuck m)
             (fun m n r _ => dstuck m -> dstuck n -> dstuck r)
             (fun Ms ρ ms _ => env_stuck ρ -> forall a, In a ms -> dstuck a)
             (fun m args r _ => dstuck m -> (forall a, In a args -> dstuck a) -> dstuck r)
             (fun H ρ h _ => env_stuck ρ -> dmstuck h)
             (fun Δ D ρ h _ => env_stuck ρ -> dmstuck h)
             (fun h n r _ => dmstuck h -> dstuck n -> dmstuck r)
             (fun h ns r _ => dmstuck h -> (forall a, In a ns -> dstuck a) -> dmstuck r)
             (fun h x r _ => dmstuck h -> dstuck r)
             (fun h y r _ => dmstuck h -> dmstuck r)
             (fun h ch r _ => dmstuck h -> dstuck r)
             (fun h ch r _ => dmstuck h -> dmstuck r)
             (fun ρ Φ ρ' _ => env_stuck ρ -> env_stuck ρ')
             (fun ρ p ups Bks j m r _ => env_stuck ρ -> ups_stuck ups -> dstuck m -> dstuck r)
             (fun ρ p ups Bks gs vs ihs _ => env_stuck ρ -> ups_stuck ups ->
                (forall a, In a vs -> dstuck a) -> forall a, In a ihs -> dstuck a)
             (fun ρ p ups Bks t v r _ => env_stuck ρ -> ups_stuck ups -> dstuck v -> dstuck r)
             (fun p ups j r _ => (forall u, In u ups -> dstuck u) -> forall a, In a (snd r) -> dstuck a)
             (fun p ups ρ t a _ => (forall u, In u ups -> dstuck u) -> env_stuck ρ -> dstuck a)
             (fun ρm As ρ t v a _ => env_stuck ρm -> env_stuck ρ -> dstuck v -> dstuck a)
             (fun f m r _ => dstuck m -> dstuck r)
             (fun ns m fl pre rs _ => (forall a, In a ns -> dstuck a) -> dstuck_ne m ->
                (forall a, In a pre -> dstuck a) -> forall a, In a rs -> dstuck a));
      intros; cbn [snd] in *.
    (* records: a type former's arguments, a tuple's fields, and the
       projections of a neutral at their types *)
    all: try solve [ apply dstuck_record; intros ? [] ].
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> forall x, In x ?vs -> dstuck x, Hρ : env_stuck ?ρ |- dstuck (d_tuple (List.combine _ ?vs)) =>
          apply dstuck_tuple; intros f a Hin; apply (IH Hρ), (List.in_combine_r _ _ _ _ Hin)
      end ].
    all: try solve [ match goal with
      | IHp : dstuck ?m -> dstuck ?r, IHM : env_stuck ?ρ -> dstuck ?m, Hρ : env_stuck ?ρ |- dstuck ?r =>
          exact (IHp (IHM Hρ))
      end ].
    all: try solve [ match goal with
      | H : dstuck (d_record _ _) |- dstuck (d_record _ (_ ++ _ :: nil)) =>
          inversion_clear H; apply dstuck_record, stuck_app_snoc; assumption
      end ].
    all: try solve [ match goal with
      | H : dstuck (d_tuple ?vs), Hl : field_lookup ?vs _ = Some ?r |- dstuck ?r =>
          inversion H; subst; eauto using field_lookup_In
      end ].
    all: try solve [ match goal with
      | H : dstuck (⇑ (d_record _ ?ns) ?m), Hk : List.nth_error ?rs _ = Some ?r,
        IH : (forall x, In x ?ns -> dstuck x) -> dstuck_ne ?m -> (forall y, In y nil -> dstuck y) -> forall z, In z ?rs -> dstuck z
        |- dstuck ?r =>
          inversion H; subst;
          match goal with Hrec : dstuck (d_record _ _), Hm : dstuck_ne _ |- _ =>
            inversion Hrec; subst;
            eapply IH; [ eassumption | exact Hm | intros ? [] | eapply List.nth_error_In; exact Hk ] end
      end ].
    all: try solve [ match goal with Hin : In _ nil |- _ => destruct Hin end ].
    all: try solve [ match goal with
      | IHT : env_stuck (env_args nil (?ns ++ ?pre)) -> dstuck ?t, Hin : In ?d (⇑ ?t (d_proj _ ?m) :: ?rs) |- dstuck ?d =>
          eapply (nflds_cons_stuck t m _ rs pre ns);
            [ apply IHT, env_stuck_args; [ exact env_stuck_nil | apply stuck_app; eassumption ] | eassumption .. ]
      end ].
    all: repeat match goal with
           | H : dstuck (d_ind _ _ _) |- _ => inversion_clear H
           | H : dstuck (d_con _ _ _ _) |- _ => inversion_clear H
           | H : dstuck (_ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _ _) |- _ => inversion_clear H
           end.
    (* a member's head and uniform parameters: the group's own, or a view's
       evaluated in them *)
    all: try solve [ match goal with
           | IH : env_stuck (env_args nil ?ups) -> forall a, In a ?cups -> dstuck a,
             Hu : forall u, In u ?ups -> dstuck u |- forall a, In a ?cups -> dstuck a =>
               apply IH, env_stuck_args; [ apply env_stuck_nil | exact Hu ]
           end ].
    (* the recursive results of function shapes and the families of their
       types: closures over stuck environments *)
    all: try solve [ lazymatch goal with |- dstuck (d_ihfn _ _ _ _ _ _) => constructor; assumption end ].
    all: try solve [ lazymatch goal with |- dstuck (d_ind _ _ (?pre ++ ?bs)) =>
           match goal with IH : env_stuck ?ρ -> forall a, In a bs -> dstuck a, Hρ : env_stuck ?ρ |- _ =>
             pose proof (IH Hρ) end;
           match goal with IHm : (forall u, In u ?ups -> dstuck u) -> forall a, In a pre -> dstuck a,
                           Hu : forall u, In u ?ups -> dstuck u |- _ => pose proof (IHm Hu) end;
           constructor; all_in_with assumption end ].
    all: try solve [ lazymatch goal with |- dstuck (Πᵈ _ (_ ↦ d_shfam _ _ _ _) _) =>
           match goal with IH : env_stuck ?ρ -> dstuck ?b, Hρ : env_stuck ?ρ |- dstuck (Πᵈ ?b _ _) =>
             constructor; [ exact (IH Hρ) | apply env_stuck_extend; [ apply env_stuck_nil | constructor; assumption ] ] end end ].
    all: try solve [ lazymatch goal with |- dstuck (Πᵈ _ (_ ↦ d_ihfam _ _ _ _ _) _) =>
           match goal with IH : env_stuck ?ρ -> dstuck ?b, Hρ : env_stuck ?ρ |- dstuck (Πᵈ ?b _ _) =>
             constructor; [ exact (IH Hρ) | apply env_stuck_extend; [ apply env_stuck_nil | constructor; assumption ] ] end end ].
    all: try solve [ match goal with
           | IH : env_stuck (env_args ?ρm (?bs ++ ?v :: nil)) -> dstuck ?a,
             IHb : env_stuck ?ρ -> forall x, In x ?bs -> dstuck x, Hρ : env_stuck ?ρ, Hρm : env_stuck ?ρm,
             Hv : dstuck ?v |- dstuck ?a =>
               apply IH, env_stuck_args; [ exact Hρm | apply stuck_app_snoc; [ exact (IHb Hρ) | exact Hv ] ]
           end ].
    all: try solve [ match goal with
           | IH : (forall u, In u ?ups -> dstuck u) -> env_stuck (?ρ ↦ ?n) -> dstuck ?a |- dstuck ?a =>
               apply IH; [ assumption | apply env_stuck_extend; assumption ]
           | IH2 : env_stuck ?ρm -> env_stuck (?ρ ↦ ?n) -> dstuck ?fn -> dstuck ?a,
             IH1 : dstuck ?f -> dstuck ?n -> dstuck ?fn |- dstuck ?a =>
               apply IH2; [ assumption | apply env_stuck_extend; assumption | apply IH1; assumption ]
           | IH2 : env_stuck ?ρ -> ups_stuck ?o -> dstuck ?fn -> dstuck ?r,
             IH1 : dstuck ?f -> dstuck ?n -> dstuck ?fn |- dstuck ?r =>
               apply IH2; [ assumption | assumption | apply IH1; assumption ]
           end ].
    (* the eliminator: its uniform parameters, evaluated in a stuck
       environment *)
    all: try solve [ match goal with
           | IH : env_stuck ?ρ -> ups_stuck ?u -> dstuck ?m -> dstuck ?r,
             IHu : env_stuck ?ρ -> forall a, In a ?u -> dstuck a, IHm : env_stuck ?ρ -> dstuck ?m,
             Hρ : env_stuck ?ρ |- dstuck ?r =>
               exact (IH Hρ (IHu Hρ) (IHm Hρ))
           end ].
    (* inductive types: the values are lists, of which evaluation takes
       segments *)
    all: try solve [ lazymatch goal with |- dstuck (d_ind _ _ _) => idtac | |- dstuck (d_con _ _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    (* the branch of a constructor, in the environment of its parameters,
       arguments and recursive results *)
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> ups_stuck ?o -> (forall x1, In x1 ?vs -> dstuck x1) -> forall x2, In x2 ?ihs -> dstuck x2,
        Hρ : env_stuck ?ρ, Ho : ups_stuck ?o, IHB : env_stuck (env_args ?ρ _) -> dstuck ?r |- dstuck ?r =>
          pose proof (IH Hρ Ho ltac:(all_in_with assumption));
          apply IHB, env_stuck_args; [ exact Hρ | all_in_with assumption ]
      end ].
    (* the eliminator on a neutral *)
    all: try solve [ match goal with
      | IH : env_stuck (env_args ?ρ _) -> dstuck ?t, Hρ : env_stuck ?ρ |- dstuck (⇑ ?t (d_elim _ _ _ _ _ _ _)) =>
          constructor;
            [ apply IH, env_stuck_args;
                [ exact Hρ | all_in_with ltac:(constructor; [ constructor; assumption | assumption ]) ]
            | constructor; assumption ]
      end ].
    (* the recursive results *)
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> ups_stuck ?o -> (forall x1, In x1 ?vs -> dstuck x1) -> forall x2, In x2 ?ihs -> dstuck x2,
        Hρ : env_stuck ?ρ, Ho : ups_stuck ?o, Hv : forall x3, In x3 (_ :: ?vs) -> dstuck x3, Ha : In ?d ?ihs |- dstuck ?d =>
          exact (IH Hρ Ho (all_in_tail _ _ _ Hv) _ Ha)
      | IH : env_stuck ?ρ -> ups_stuck ?o -> (forall x1, In x1 ?vs -> dstuck x1) -> forall x2, In x2 ?ihs -> dstuck x2,
        IHv : env_stuck ?ρ -> ups_stuck ?o -> dstuck ?v -> dstuck ?ih,
        Hρ : env_stuck ?ρ, Ho : ups_stuck ?o, Hv : forall x3, In x3 (?v :: ?vs) -> dstuck x3, Ha : In ?d (?ih :: ?ihs) |- dstuck ?d =>
          destruct Ha as [<- | Ha];
            [ exact (IHv Hρ Ho (all_in_head _ _ _ Hv)) | exact (IH Hρ Ho (all_in_tail _ _ _ Hv) _ Ha) ]
      end ].
    all: try solve [ eauto 4 with mctt ].
    (* the [⊥]-eliminator, whose scrutinee is stuck *)
    all: try solve [ match goal with H : env_stuck ?ρ -> dstuck (⇑ _ _), Hρ : env_stuck ?ρ |- _ =>
        specialize (H Hρ); inversion_clear H end; eauto 7 with mctt ].
    (* the [ℕ]-eliminator on a neutral *)
    all: try solve [ match goal with IHA : env_stuck (?ρ ↦ ⇑ ?b ?m) -> dstuck ?a, IHZ : env_stuck ?ρ -> dstuck ?mz,
                      Hρ : env_stuck ?ρ |- _ =>
        apply dstuck_neut; [ apply IHA; apply env_stuck_extend; auto with mctt | constructor; auto with mctt ] end ].
    (* arguments, one at a time *)
    all: try solve [ match goal with IH : dstuck ?m1 -> _ -> dstuck ?r, IH1 : dstuck ?m -> dstuck ?n -> dstuck ?m1,
                      Ha : forall a, In a (cons ?n _) -> dstuck a |- dstuck ?r =>
        apply IH; [ apply IH1; [ assumption | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ] end ].
    (* a member: the root is stuck, and so are the arguments *)
    all: try solve [ match goal with
      | IHa : dstuck ?f -> (forall a, In a ?ns -> dstuck a) -> dstuck ?r,
        IHs : dmstuck ?h -> dstuck ?f, IHh : env_stuck ?ρ -> dmstuck ?h,
        IHe : env_stuck ?ρ -> forall a, In a ?ns -> dstuck a, Hρ : env_stuck ?ρ |- dstuck ?r =>
          apply IHa; [ apply IHs, IHh, Hρ | apply IHe, Hρ ] end ].
    (* a list of terms *)
    all: try solve [ match goal with
      | Hin : In ?a (cons _ _) |- _ => destruct Hin as [<- | Hin]; eauto with mctt end ].
    all: try solve [ eauto 6 with mctt ].
    (* the module of an inductive type, a record type: the type former, applied *)
    all: try solve [ match goal with
                     | IH : dstuck (d_ind _ _ nil) -> _ -> dstuck ?r |- dstuck ?r =>
                         apply IH; [ first [ constructor; intros ? [] | repeat constructor ] | assumption ]
                     | IH : dstuck (d_record _ nil) -> _ -> dstuck ?r |- dstuck ?r =>
                         apply IH; [ constructor; intros ? [] | assumption ] end ].
    (* a local open, and a name it declares: the entry its open makes *)
    all: try solve [ match goal with
      | IH2 : env_stuck ?ρ1 -> env_stuck ?ρ2, IH1 : env_stuck ?ρ -> env_stuck ?ρ1, Hρ : env_stuck ?ρ |- env_stuck ?ρ2 =>
          exact (IH2 (IH1 Hρ)) end ].
    all: try solve [ match goal with
      | IH : env_stuck _ -> env_stuck ?ρ', He : env_entry ?ρ' 0 = _ |- _ =>
          let Hs := fresh "Hs" in
          assert (Hs : env_stuck ρ') by (apply IH; apply env_stuck_args; assumption);
          specialize (Hs 0); rewrite He in Hs; inversion Hs; assumption end ].
    all: try match goal with Hin : In _ nil |- _ => destruct Hin end.
    (* a constructor of a view at the uniform parameters: the container's at
       the view's arguments, evaluated in an environment of stuck values *)
    all: try solve [ apply dstuck_con;
      match goal with H : env_stuck (env_args nil _) -> forall a, In a _ -> dstuck a |- _ =>
        apply H; apply env_stuck_args;
          [ exact env_stuck_nil
          | first [ intros ? [] | intros a Ha; apply List.in_app_or in Ha as [Ha | [<- | []]]; auto ] ] end ].
    (* the type of a recursive argument: the member at the shape's
       parameters after the uniform ones *)
    all: try solve [ apply dstuck_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha]; auto ].
    (* module arguments, one at a time *)
    all: match goal with IH : dmstuck ?h1 -> _ -> dmstuck ?r, IH1 : dmstuck ?h -> dstuck ?n -> dmstuck ?h1,
                      Ha : forall a, In a (cons ?n _) -> dstuck a |- dmstuck ?r =>
        apply IH; [ apply IH1; [ assumption | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ] end.
  Qed.

  (** A value built of stuck ones, and an environment of stuck values: by
      the hypotheses, the rules, and [all_in_with] for the lists. *)
  Ltac stuck_val :=
    first [ assumption
          | solve [ eapply all_in_head; eassumption ]
          | solve [ constructor; [ stuck_val | constructor ] ]
          | solve [ constructor; [ stuck_val | assumption ] ]
          | solve [ constructor; all_in_with stuck_val ] ].

  Ltac stuck_env :=
    solve [ repeat first [ assumption
                         | apply env_stuck_nil
                         | apply env_stuck_extend; [| stuck_val ]
                         | apply env_stuck_args; [| solve [ all_in_with stuck_val ] ] ] ].

  (** The fresh variables of the telescopes of a declaration are stuck. *)
  Lemma fresh_tele_stuck : forall ρ T s vs,
      Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_stuck ρ -> forall a, In a vs -> dstuck a.
  Proof.
    destruct eval_stuck as (He & _).
    induction 1; intros Hρ; [ apply all_in_nil |].
    assert (dstuck a) by (eapply He; eassumption).
    apply all_in_cons; [ stuck_val | apply IHfresh_tele; stuck_env ].
  Qed.

  Lemma fresh_cargs_stuck : forall p ups ρ gs s vs,
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_stuck ρ -> (forall a, In a ups -> dstuck a) ->
      forall a, In a vs -> dstuck a.
  Proof.
    destruct eval_stuck as (He & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
    induction 1; intros Hρ Hu; [ apply all_in_nil | |].
    - assert (dstuck a) by (eapply He; eassumption).
      apply all_in_cons; [ stuck_val | apply IHfresh_cargs; [ stuck_env | assumption ] ].
    - assert (dstuck a) by (eapply Hsh; eassumption).
      apply all_in_cons; [ stuck_val | apply IHfresh_cargs; assumption ].
  Qed.

  Lemma fresh_ihs_stuck : forall ρ A ρa gs' gs vs s ihs,
      Fihs vs at gs' gs under ρ A in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> env_stuck ρ -> env_stuck ρa -> (forall a, In a vs -> dstuck a) ->
      forall a, In a ihs -> dstuck a.
  Proof.
    destruct eval_stuck as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hit & _).
    induction 1; intros Hρ Hρa Hv; [ apply all_in_nil | apply IHfresh_ihs; [ assumption | stuck_env | all_in_with assumption ] | |].
    - assert (dstuck a) by (eapply Hit; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ]).
      apply all_in_cons; [ stuck_val | apply IHfresh_ihs; [ assumption | assumption | all_in_with assumption ] ].
    - apply IHfresh_ihs; [ assumption | assumption | all_in_with assumption ].
  Qed.

  Lemma wrap_ihs_eval_stuck : forall ρ p ups Bks gs' gs vs ihs r,
      ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_stuck ρ -> ups_stuck ups ->
      (forall a, In a vs -> dstuck a) -> (forall a, In a ihs -> dstuck a) -> forall a, In a r -> dstuck a.
  Proof.
    destruct eval_stuck as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hih & _).
    induction 1; intros Hρ Ho Hv Hi; [ apply all_in_nil | | |].
    - apply all_in_cons; [ apply Hi; left; reflexivity | apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | all_in_with assumption ] ].
    - apply all_in_cons; [ eapply Hih; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ] |].
      apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | assumption ].
    - apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | assumption ].
  Qed.

  (** Forward reasoning on the premises of the readback of an inductive
      type: what each evaluation or telescope of fresh variables gives. *)
  Ltac stuck_fwd He Hes Hsh Hm :=
    repeat match goal with
      | H : eval_mref _ _ _ ?ups _ (_, _, ?pre) |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x pre -> dstuck x) by (exact (Hm _ _ _ _ H ltac:(solve [ all_in_with stuck_val ])));
          clear H
      | H : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ ?r |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x r -> dstuck x)
            by (eapply wrap_ihs_eval_stuck; [ exact H | stuck_env | assumption | solve [ all_in_with stuck_val ] | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : fresh_tele _ _ ?ρ _ _ ?ns |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ns -> dstuck x) by (eapply fresh_tele_stuck; [ exact H | stuck_env ]);
          clear H
      | H : fresh_cargs _ _ _ _ _ _ _ ?vs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x vs -> dstuck x)
            by (eapply fresh_cargs_stuck; [ exact H | stuck_env | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : fresh_ihs _ _ _ _ _ _ _ _ _ ?ihs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ihs -> dstuck x)
            by (eapply fresh_ihs_stuck; [ exact H | stuck_env | stuck_env | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : dstuck a) by (eapply He; [ exact H | stuck_env ]); clear H
      | H : eval_exps _ _ _ _ ?bs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x bs -> dstuck x) by (eapply Hes; [ exact H | stuck_env ]); clear H
      | H : eval_shty _ _ _ _ _ _ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : dstuck a) by (eapply Hsh; [ exact H | solve [ all_in_with stuck_val ] | stuck_env ]); clear H
      end.

  Lemma read_stuck :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> dstuck_nf m -> nf_stuck (gstuck Θ Ξ) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> dstuck_ne m -> ne_stuck (gstuck Θ Ξ) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> dstuck a -> nf_stuck (gstuck Θ Ξ) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       dstuck_la xs -> all_list (fun a => ne_stuck (gstuck Θ Ξ) (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a vs -> dstuck a) -> all_list (nf_stuck (gstuck Θ Ξ)) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a ups -> dstuck a) -> (forall a, In a vs -> dstuck a) ->
       all_list (nf_stuck (gstuck Θ Ξ)) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       env_stuck ρ -> (forall a, In a ups -> dstuck a) -> dstuck x -> nf_stuck (gstuck Θ Ξ) X) /\
    (forall s ρ p ups Bks sel i Ms NBks, Rblks i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       env_stuck ρ -> ups_stuck ups ->
       all_list (fun b => nf_stuck (gstuck Θ Ξ) (block_motive b) /\
                          all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) (block_branches b)) NBks) /\
    (forall s ρ p ups Bks Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       env_stuck ρ -> ups_stuck ups -> (forall a, In a (snd r) -> dstuck a) ->
       all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) Bs') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       env_stuck ρ -> dstuck v -> all_list (nf_stuck (gstuck Θ Ξ)) Fs).
  Proof.
    destruct eval_stuck as (He & Ha & Hes & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & Hsh & _ & Hpj & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dstuck_nf m -> nf_stuck (gstuck Θ Ξ) W)
             (fun s m M _ => dstuck_ne m -> ne_stuck (gstuck Θ Ξ) M)
             (fun s a A _ => dstuck a -> nf_stuck (gstuck Θ Ξ) A)
             (fun s xs ys _ => dstuck_la xs -> all_list (fun a => ne_stuck (gstuck Θ Ξ) (atom_level a)) ys)
             (fun s ρ T vs Ms _ => env_stuck ρ -> (forall a, In a vs -> dstuck a) -> all_list (nf_stuck (gstuck Θ Ξ)) Ms)
             (fun s p ups ρ gs vs Ms _ => env_stuck ρ -> (forall a, In a ups -> dstuck a) ->
                                        (forall a, In a vs -> dstuck a) -> all_list (nf_stuck (gstuck Θ Ξ)) Ms)
             (fun s p ups ρ t x X _ => env_stuck ρ -> (forall a, In a ups -> dstuck a) -> dstuck x ->
                                     nf_stuck (gstuck Θ Ξ) X)
             (fun s ρ p ups Bks sel i Ms NBks _ =>
                env_stuck ρ -> ups_stuck ups ->
                all_list (fun b => nf_stuck (gstuck Θ Ξ) (block_motive b) /\
                                   all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) (block_branches b)) NBks)
             (fun s ρ p ups Bks Mv A Mi r cs Bs Bs' _ =>
                env_stuck ρ -> ups_stuck ups -> (forall a, In a (snd r) -> dstuck a) ->
                all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) Bs')
             (fun s ρ fl v Fs _ => env_stuck ρ -> dstuck v -> all_list (nf_stuck (gstuck Θ Ξ)) Fs));
      intros; cbn [snd] in *; cbn;
      (* a field of a value: stuck as the value is *)
      repeat match goal with
        | H : eval_proj _ _ _ ?v ?r, Hv : dstuck ?v |- _ =>
            let h := fresh "Hs" in assert (h : dstuck r) by exact (Hpj _ _ _ H Hv); clear H
        end;
      repeat match goal with
        | H : dstuck (_ _) |- _ => inversion_clear H
        | H : dstuck (_ _ _) |- _ => inversion_clear H
        | H : dstuck (_ _ _ _) |- _ => inversion_clear H
        | H : dstuck_nf (_ _ _) |- _ => inversion_clear H
        | H : dstuck_la (_ :: _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    (** Inductive types: each component is read back at a type, in an
        environment, of stuck values. *)
    all: try solve [
      stuck_fwd He Hes Hsh Hm;
      try apply all_list_app;
      match goal with
      | IH : context [ nf_stuck _ ?W ] |- nf_stuck _ ?W => apply IH
      | IH : context [ ne_stuck _ ?W ] |- ne_stuck _ ?W => apply IH
      | IH : context [ all_list _ ?W ] |- all_list _ ?W => apply IH
      end;
      first [ stuck_env | solve [ all_in_with stuck_val ] | stuck_val | solve [ constructor; stuck_val ] ] ].
    (** A level reads back canonically, so its atoms are sorted and merged;
        [la_all_keep] and [la_all_sort] move the property of all the atoms
        across. *)
    all: try solve [ apply la_all_all_list, la_all_keep, la_all_sort, la_all_all_list; eauto 3 with mctt
                   | apply la_stuck_sort; eauto 3 with mctt ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try match goal with
         | IH : _ -> nf_stuck (gstuck Θ Ξ) (nf_lvl_of _) |- all_list _ _ =>
             apply IH; repeat constructor; assumption
         end.
    (* a recursive argument of a function shape, under a fresh variable *)
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b, e0 : $| ?x & ⇑! ?b ?s | _ ⍮ _ ↘ ?r, Hρ : env_stuck ?ρ, Hx : dstuck ?x,
        Hu : forall a, In a ?ups -> dstuck a,
        IH : env_stuck (?ρ ↦ _) -> (forall a, In a ?ups -> dstuck a) -> dstuck ?r -> nf_stuck (gstuck Θ Ξ) ?V
        |- nf_stuck (gstuck Θ Ξ) ?V =>
          let Hb := fresh "Hb" in
          assert (Hb : dstuck b) by (eapply He; eassumption);
          apply IH; [ apply env_stuck_extend; [ exact Hρ | repeat constructor; assumption ] | exact Hu
                    | eapply Ha; [ exact e0 | exact Hx | repeat constructor; assumption ] ]
      end ].
    (* each component is read back from a value built of stuck ones *)
    all: match goal with
         | IH : _ -> nf_stuck (gstuck Θ Ξ) ?W |- nf_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : _ -> ne_stuck (gstuck Θ Ξ) ?W |- ne_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : _ -> all_list _ ?W |- all_list _ ?W => apply IH
         end.
    all: repeat first [ eassumption | constructor | apply env_stuck_extend
                      | eapply He; [ eassumption |] | eapply Ha; [ eassumption | |] | eapply Hsh; [ eassumption | |] ].
  Qed.

  Lemma initial_env_stuck : forall Γ ρ, initial_env Θ Ξ Γ ρ -> env_stuck ρ.
  Proof.
    destruct eval_stuck as (He & _ & _ & _ & Hm & _).
    induction 1; eauto with mctt.
  Qed.

  Theorem nbe_stuck : forall Γ M A W, nbe Θ Ξ Γ M A W -> nf_stuck (gstuck Θ Ξ) W.
  Proof.
    destruct eval_stuck as (He & _); destruct read_stuck as (Hr & _).
    intros * Hn; inversion Hn; subst.
    match goal with Hρ : initial_env _ _ _ _ |- _ => pose proof (initial_env_stuck _ _ Hρ) end.
    eapply Hr; eauto with mctt.
  Qed.
End Stuck.
