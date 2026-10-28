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

Lemma level_atoms_stuck_sort : forall G xs, all_list (fun a => ne_stuck G (atom_level a)) xs ->
    all_list (fun a => ne_stuck G (atom_level a)) (level_atoms_sort xs).
Proof. intros * H; apply level_atoms_all_all_list, level_atoms_all_sort, level_atoms_all_all_list; assumption. Qed.

(** A global that does not unfold: an opaque definition or an axiom. *)
#[warnings="-cannot-define-projection"]
Record gstuck (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop := mk_gstuck
  { gstuck_transparent : bool
  ; gstuck_private : bool
  ; gstuck_typ : typ
  ; gstuck_body : option exp
  ; gstuck_resolve : gc_resolve Θ Ξ p = Some (ge_def gstuck_transparent gstuck_private gstuck_typ gstuck_body)
  ; gstuck_opaque : gstuck_transparent = false \/ gstuck_body = None }.

Section Stuck.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma gstuck_intro : forall p b pv A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv A B) -> b = false \/ B = None -> gstuck Θ Ξ p.
  Proof. intros * Hr Ho; exact (mk_gstuck _ _ _ _ _ _ _ Hr Ho). Qed.
  #[local] Hint Resolve gstuck_intro : mctt.

(** ** Values Whose Global Neutrals Are Stuck *)

(** [domain_stuck d]: every global neutral in the value [d], its closures'
    environments included, is stuck ([gstuck]); mutually, for the other
    sorts of values. *)
Inductive domain_stuck : domain -> Prop :=
(** A [Π]: its domain and its closure's environment *)
| domain_stuck_pi : forall a (ρ : env) B, domain_stuck a -> (forall x, destuck (env_entry ρ x)) -> domain_stuck (Πᵈ a ρ B)
(** A large universe *)
| domain_stuck_univ : forall i, domain_stuck 𝕌ω@i
(** A small universe: its level *)
| domain_stuck_suniv : forall l, domain_stuck l -> domain_stuck 𝕌@l
(** A type of levels *)
| domain_stuck_level : forall n, domain_stuck (Levelᵈ@n)
(** A level: its atoms *)
| domain_stuck_lvl : forall c xs, level_atoms_stuck xs -> domain_stuck (lvᵈ c xs)
(** The unit type *)
| domain_stuck_True : domain_stuck ⊤ᵈ
(** The unit's element *)
| domain_stuck_true : domain_stuck ⋆ᵈ
(** The empty type *)
| domain_stuck_False : domain_stuck ⊥ᵈ
(** A λ: its closure's environment *)
| domain_stuck_fn : forall (ρ : env) M, (forall x, destuck (env_entry ρ x)) -> domain_stuck (λᵈ ρ M)
(** A neutral: its type and itself *)
| domain_stuck_neut : forall a m, domain_stuck a -> domain_ne_stuck m -> domain_stuck (⇑ a m)
(** A member of a module value: the module value *)
| domain_stuck_member : forall h ch, dmstuck h -> domain_stuck (d_member h ch)
(** A type former: its arguments *)
| domain_stuck_indty : forall p k args, (forall a, In a args -> domain_stuck a) -> domain_stuck (d_ind p k args)
(** A constructor: its arguments *)
| domain_stuck_con : forall p k c args, (forall a, In a args -> domain_stuck a) -> domain_stuck (d_con p k c args)
(** A recursive result at a function shape: the eliminator's environment,
    its uniform parameters and the argument *)
| domain_stuck_ihfn : forall (ρ : env) Bks p ups t i f, (forall x, destuck (env_entry ρ x)) ->
    (forall a, In a ups -> domain_stuck a) -> domain_stuck f -> domain_stuck (d_ihfn ρ Bks p ups t i f)
(** A shape family: its uniform parameters and its environment *)
| domain_stuck_shfam : forall p ups (ρ : env) t, (forall a, In a ups -> domain_stuck a) -> (forall x, destuck (env_entry ρ x)) ->
    domain_stuck (d_shfam p ups ρ t)
(** A recursive result's family: the motive's and the shape's
    environments, the group's uniform parameters and the argument *)
| domain_stuck_ihfam : forall (ρm : env) As p ups (ρ : env) t i f, (forall x, destuck (env_entry ρm x)) ->
    (forall a, In a ups -> domain_stuck a) -> (forall x, destuck (env_entry ρ x)) ->
    domain_stuck f -> domain_stuck (d_ihfam ρm As p ups ρ t i f)
(** A record type former: its arguments *)
| domain_stuck_record : forall p args, (forall a, In a args -> domain_stuck a) -> domain_stuck (d_record p args)
(** A record value: its fields *)
| domain_stuck_tuple : forall vs, (forall f a, In (f, a) vs -> domain_stuck a) -> domain_stuck (d_tuple vs)
with domain_ne_stuck : domain_ne -> Prop :=
(** A variable *)
| domain_stuck_var : forall x, domain_ne_stuck (#ᵈ x)
(** A global, only if it is stuck *)
| domain_stuck_glob : forall p, gstuck Θ Ξ p -> domain_ne_stuck (d_glob p)
(** An application: its head and its argument *)
| domain_stuck_app : forall m n, domain_ne_stuck m -> domain_nf_stuck n -> domain_ne_stuck (m $ᵈ n)
(** A stuck [efq]: its environment and its scrutinee *)
| domain_stuck_exfalso : forall (ρ : env) A m,
    (forall x, destuck (env_entry ρ x)) -> domain_ne_stuck m ->
    domain_ne_stuck (efqᵈ m under ρ return A)
(** A stuck eliminator: its environment, its uniform parameters, its
    parameters and its scrutinee *)
| domain_stuck_elim : forall (ρ : env) Bks p ups j args m,
    (forall x, destuck (env_entry ρ x)) -> (forall a, In a ups -> domain_stuck a) ->
    (forall a, In a args -> domain_stuck a) -> domain_ne_stuck m ->
    domain_ne_stuck (d_elim ρ Bks p ups j args m)
(** The field of a neutral: the neutral *)
| domain_stuck_proj : forall f m, domain_ne_stuck m -> domain_ne_stuck (d_proj f m)
with domain_nf_stuck : domain_nf -> Prop :=
| domain_stuck_dom : forall a m, domain_stuck a -> domain_stuck m -> domain_nf_stuck (⇓ a m)
with dmstuck : dmod -> Prop :=
| dmstuck_global : forall p args, (forall a, In a args -> domain_stuck a) -> dmstuck (dm_global p args)
| dmstuck_local : forall Δ D (ρ : env),
    (forall x, destuck (env_entry ρ x)) -> dmstuck (dm_local Δ D ρ)
| dmstuck_member : forall h ch, dmstuck h -> dmstuck (dm_member h ch)
with level_atoms_stuck : list (nat * nat * domain_ne) -> Prop :=
| level_atoms_stuck_nil : level_atoms_stuck nil
| level_atoms_stuck_cons : forall k n m xs, domain_ne_stuck m -> level_atoms_stuck xs -> level_atoms_stuck ((k, n, m) :: xs)
with destuck : dentry -> Prop :=
| destuck_term : forall d, domain_stuck d -> destuck (de_term d)
| destuck_mod : forall h, dmstuck h -> destuck (de_mod h)
(** A term with a module part: both *)
| destuck_dm : forall d h, domain_stuck d -> dmstuck h -> destuck (de_dm d h).

Definition env_stuck (ρ : env) : Prop := forall x, destuck (env_entry ρ x).

(** The uniform parameters an eliminator carries, stuck.  A definition, so
    that the search does not use it as a lemma about every value. *)
Definition ups_stuck (ups : list domain) : Prop := forall a, In a ups -> domain_stuck a.

#[local] Hint Constructors domain_stuck domain_ne_stuck domain_nf_stuck level_atoms_stuck dmstuck destuck : mctt.

(** [domain_stuck_lvl] is not a hint: its premise is a quantified statement about the
    atoms, which the search would try to prove of an unknown level.  The
    level operations are reached through the three lemmas below instead. *)
#[local] Remove Hints domain_stuck_lvl : mctt.

(** Nor are the rules of inductive types, whose premises are about all the
    members of a list: [all_in_with] reaches them instead. *)
#[local] Remove Hints domain_stuck_indty domain_stuck_con domain_stuck_elim domain_stuck_shfam domain_stuck_ihfn domain_stuck_ihfam : mctt.
(** Nor are those of records, for the same reason. *)
#[local] Remove Hints domain_stuck_record domain_stuck_tuple : mctt.
#[local] Hint Unfold env_stuck : mctt.

Lemma env_stuck_nil : env_stuck nil.
Proof. intros x; induction x; cbn; auto with mctt. Qed.

Lemma env_stuck_extend : forall ρ d, env_stuck ρ -> domain_stuck d -> env_stuck (ρ ↦ d).
Proof. intros * Hρ Hd [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_extend_mod : forall ρ h, env_stuck ρ -> dmstuck h -> env_stuck (ρ ↦ᵐ h).
Proof. intros * Hρ Hh [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_extend_dm : forall ρ d h, env_stuck ρ -> domain_stuck d -> dmstuck h -> env_stuck (ρ ↦ᵈ d ‖ h).
Proof. intros * Hρ Hd Hh [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_var : forall ρ x, env_stuck ρ -> domain_stuck (ρ x).
Proof. intros * H; unfold env_var; destruct (H x); auto with mctt. Qed.

Lemma env_stuck_mod : forall ρ x, env_stuck ρ -> dmstuck (env_mod ρ x).
Proof. intros * H; unfold env_mod; destruct (H x); auto with mctt; constructor; intros ? []. Qed.

Lemma env_stuck_args : forall args ρ, env_stuck ρ -> (forall a, In a args -> domain_stuck a) -> env_stuck (env_args ρ args).
Proof.
  induction args; intros * Hρ Ha; cbn; [ assumption |].
  apply IHargs; [ apply env_stuck_extend; auto with datatypes | intros; apply Ha; right; assumption ].
Qed.

Lemma stuck_app_snoc : forall (args : list domain) n,
    (forall a, In a args -> domain_stuck a) -> domain_stuck n -> forall a, In a (args ++ n :: nil) -> domain_stuck a.
Proof. intros * H Hn a Ha; apply in_app_or in Ha as [Ha | [<- | []]]; auto. Qed.

Lemma stuck_app : forall (l1 l2 : list domain),
    (forall a, In a l1 -> domain_stuck a) -> (forall a, In a l2 -> domain_stuck a) -> forall a, In a (l1 ++ l2) -> domain_stuck a.
Proof. intros * H1 H2 a Ha; apply in_app_or in Ha as [Ha | Ha]; auto. Qed.

(** The neutral projections of the fields of a neutral of a record type,
    one more: the next one at its type, then the rest after it. *)
Lemma nflds_cons_stuck : forall t m g rs pre ns,
    domain_stuck t -> (forall x, In x ns -> domain_stuck x) -> domain_ne_stuck m -> (forall x, In x pre -> domain_stuck x) ->
    ((forall x, In x ns -> domain_stuck x) -> domain_ne_stuck m ->
       (forall y, In y (pre ++ ⇑ t (d_proj g m) :: nil) -> domain_stuck y) -> forall z, In z rs -> domain_stuck z) ->
    forall d, In d (⇑ t (d_proj g m) :: rs) -> domain_stuck d.
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
Lemma level_atoms_stuck_view : forall d, domain_stuck d -> level_atoms_stuck (dlvl_atoms d).
Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

Lemma level_atoms_stuck_suc : forall xs, level_atoms_stuck xs -> level_atoms_stuck (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
Proof. induction 1; cbn; repeat constructor; assumption. Qed.

Lemma level_atoms_stuck_app : forall xs ys, level_atoms_stuck xs -> level_atoms_stuck ys -> level_atoms_stuck (xs ++ ys).
Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

Lemma domain_stuck_lvl_lit : forall n, domain_stuck (dlvl_lit n).
Proof. intros; repeat constructor. Qed.

Lemma domain_stuck_lvl_suc : forall d, domain_stuck d -> domain_stuck (dlvl_suc d).
Proof. intros; unfold dlvl_suc; constructor; apply level_atoms_stuck_suc, level_atoms_stuck_view; assumption. Qed.

Lemma domain_stuck_lvl_max : forall d e, domain_stuck d -> domain_stuck e -> domain_stuck (dlvl_max d e).
Proof. intros; unfold dlvl_max; constructor; apply level_atoms_stuck_app; apply level_atoms_stuck_view; assumption. Qed.

#[local] Hint Resolve env_stuck_nil env_stuck_extend env_stuck_extend_mod env_stuck_extend_dm env_stuck_var env_stuck_mod
  env_stuck_args stuck_app_snoc dmstuck_global_nil env_stuck_entry : mctt.

(** The level lemmas are [Hint Extern], keyed on the operation in the goal: as
    [Hint Resolve] their conclusions would match a goal about an unknown
    value, since [dlvl_suc] and [dlvl_max] unfold to a flat level. *)
#[local] Hint Extern 1 (domain_stuck (dlvl_lit _)) => apply domain_stuck_lvl_lit : mctt.
#[local] Hint Extern 1 (domain_stuck (dlvl_suc _)) => apply domain_stuck_lvl_suc : mctt.
#[local] Hint Extern 1 (domain_stuck (dlvl_max _ _)) => apply domain_stuck_lvl_max : mctt.

(** A member of a suffix is a member of the list. *)
Lemma in_skipn_in : forall {A : Type} n (l : list A) x, In x (List.skipn n l) -> In x l.
Proof. intros A n; induction n as [| n IH]; intros [| y l] x H; cbn in H; auto; right; exact (IH _ _ H). Qed.

(** The premises of a stuck value built of stuck ones ([stuck_prem]), and
    the members of a list of stuck values ([stuck_in]): along the list's
    structure, then by the hypothesis about the list. *)
Ltac stuck_prem :=
  first [ assumption
        | apply env_stuck_nil
        | solve [ apply env_stuck_extend; stuck_prem ]
        | solve [ apply env_stuck_args; [ stuck_prem | intros ? ?; stuck_in ] ]
        | match goal with H : forall a, In a (?x :: _) -> domain_stuck a |- domain_stuck ?x => apply H; left; reflexivity end
        | match goal with H : forall a, In a (_ :: ?l) -> domain_stuck a |- forall a, In a ?l -> domain_stuck a =>
            exact (all_in_tail _ _ _ H) end
        | match goal with H : context [ forall a, In a ?l -> domain_stuck a ] |- forall a, In a ?l -> domain_stuck a =>
            solve [ apply H; stuck_prem ] end
        | match goal with
          | H : _ -> domain_stuck ?r |- domain_stuck ?r => solve [ apply H; stuck_prem ]
          | H : _ -> _ -> domain_stuck ?r |- domain_stuck ?r => solve [ apply H; stuck_prem ]
          | H : _ -> _ -> _ -> domain_stuck ?r |- domain_stuck ?r => solve [ apply H; stuck_prem ]
          end
        | match goal with |- domain_stuck ?x => tryif is_var x then fail else solve [ constructor; stuck_prem ] end ]
with stuck_in :=
  match goal with
  | Ha : In ?a (?l1 ++ ?l2) |- domain_stuck ?a => apply List.in_app_or in Ha as [Ha | Ha]; stuck_in
  | Ha : In ?a (_ :: _) |- domain_stuck ?a => destruct Ha as [<- | Ha]; [ stuck_one | stuck_in ]
  | Ha : In _ nil |- _ => destruct Ha
  | Ha : In ?a ?l, Hu : ups_stuck ?l |- domain_stuck ?a => exact (Hu _ Ha)
  | Ha : In ?a (List.map _ _) |- domain_stuck ?a => apply List.in_map_iff in Ha as (? & <- & _); stuck_one
  | Hn : List.nth_error ?l _ = Some ?a, IH : context [ forall b, In b ?l -> domain_stuck b ] |- domain_stuck ?a =>
      eapply IH; [ .. | eapply List.nth_error_In; exact Hn ]; stuck_prem
  | Ha : In ?a ?l, IH : context [ forall b, In b ?l -> domain_stuck b ] |- domain_stuck ?a => eapply IH; [ .. | exact Ha ]; stuck_prem
  end
with stuck_one := first [ stuck_prem | solve [ constructor; stuck_prem ] ].


  Lemma eval_stuck :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_stuck ρ -> domain_stuck m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> domain_stuck m -> domain_stuck n -> domain_stuck r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> env_stuck ρ -> forall a, In a ms -> domain_stuck a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> domain_stuck m -> (forall a, In a args -> domain_stuck a) -> domain_stuck r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmstuck h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmstuck h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmstuck h -> domain_stuck n -> dmstuck r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> dmstuck h -> (forall a, In a ns -> domain_stuck a) -> dmstuck r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmstuck h -> domain_stuck r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmstuck h -> dmstuck r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmstuck h -> domain_stuck r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmstuck h -> dmstuck r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> env_stuck ρ -> env_stuck ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_stuck ρ ->
       ups_stuck ups -> domain_stuck m -> domain_stuck r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       env_stuck ρ -> ups_stuck ups -> (forall a, In a vs -> domain_stuck a) -> forall a, In a ihs -> domain_stuck a) /\
    (forall ρ p ups Bks t v rs, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs -> env_stuck ρ ->
       ups_stuck ups -> domain_stuck v -> forall a, In a rs -> domain_stuck a) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> (forall u, In u ups -> domain_stuck u) -> forall a, In a (snd r) -> domain_stuck a) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> (forall u, In u ups -> domain_stuck u) -> env_stuck ρ -> domain_stuck a) /\
    (forall p ups ρm As ρ t v as', ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' -> ups_stuck ups -> env_stuck ρm ->
       env_stuck ρ -> domain_stuck v -> forall a, In a as' -> domain_stuck a) /\
    (forall f m r, eval_proj Θ Ξ f m r -> domain_stuck m -> domain_stuck r) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs -> (forall a, In a ns -> domain_stuck a) -> domain_ne_stuck m ->
       (forall a, In a pre -> domain_stuck a) -> forall a, In a rs -> domain_stuck a) /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> domain_stuck v -> forall a, In a ws -> domain_stuck a) /\
    (forall p ups ρm As ρ gs vs as', ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' -> ups_stuck ups ->
       env_stuck ρm -> env_stuck ρ -> (forall a, In a vs -> domain_stuck a) -> forall a, In a as' -> domain_stuck a).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_stuck ρ -> domain_stuck m)
             (fun m n r _ => domain_stuck m -> domain_stuck n -> domain_stuck r)
             (fun Ms ρ ms _ => env_stuck ρ -> forall a, In a ms -> domain_stuck a)
             (fun m args r _ => domain_stuck m -> (forall a, In a args -> domain_stuck a) -> domain_stuck r)
             (fun H ρ h _ => env_stuck ρ -> dmstuck h)
             (fun Δ D ρ h _ => env_stuck ρ -> dmstuck h)
             (fun h n r _ => dmstuck h -> domain_stuck n -> dmstuck r)
             (fun h ns r _ => dmstuck h -> (forall a, In a ns -> domain_stuck a) -> dmstuck r)
             (fun h x r _ => dmstuck h -> domain_stuck r)
             (fun h y r _ => dmstuck h -> dmstuck r)
             (fun h ch r _ => dmstuck h -> domain_stuck r)
             (fun h ch r _ => dmstuck h -> dmstuck r)
             (fun ρ Φ ρ' _ => env_stuck ρ -> env_stuck ρ')
             (fun ρ p ups Bks j m r _ => env_stuck ρ -> ups_stuck ups -> domain_stuck m -> domain_stuck r)
             (fun ρ p ups Bks gs vs ihs _ => env_stuck ρ -> ups_stuck ups ->
                (forall a, In a vs -> domain_stuck a) -> forall a, In a ihs -> domain_stuck a)
             (fun ρ p ups Bks t v rs _ => env_stuck ρ -> ups_stuck ups -> domain_stuck v -> forall a, In a rs -> domain_stuck a)
             (fun p ups j r _ => (forall u, In u ups -> domain_stuck u) -> forall a, In a (snd r) -> domain_stuck a)
             (fun p ups ρ t a _ => (forall u, In u ups -> domain_stuck u) -> env_stuck ρ -> domain_stuck a)
             (fun p ups ρm As ρ t v as' _ => ups_stuck ups -> env_stuck ρm -> env_stuck ρ -> domain_stuck v ->
                forall a, In a as' -> domain_stuck a)
             (fun f m r _ => domain_stuck m -> domain_stuck r)
             (fun ns m fl pre rs _ => (forall a, In a ns -> domain_stuck a) -> domain_ne_stuck m ->
                (forall a, In a pre -> domain_stuck a) -> forall a, In a rs -> domain_stuck a)
             (fun fl v ws _ => domain_stuck v -> forall a, In a ws -> domain_stuck a)
             (fun p ups ρm As ρ gs vs as' _ => ups_stuck ups -> env_stuck ρm -> env_stuck ρ ->
                (forall a, In a vs -> domain_stuck a) -> forall a, In a as' -> domain_stuck a));
      intros; cbn [snd] in *.
    (* records: a type former's arguments, a tuple's fields, and the
       projections of a neutral at their types *)
    all: try solve [ apply domain_stuck_record; intros ? [] ].
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> forall x, In x ?vs -> domain_stuck x, Hρ : env_stuck ?ρ |- domain_stuck (d_tuple (List.combine _ ?vs)) =>
          apply domain_stuck_tuple; intros f a Hin; apply (IH Hρ), (List.in_combine_r _ _ _ _ Hin)
      end ].
    all: try solve [ match goal with
      | IHp : domain_stuck ?m -> domain_stuck ?r, IHM : env_stuck ?ρ -> domain_stuck ?m, Hρ : env_stuck ?ρ |- domain_stuck ?r =>
          exact (IHp (IHM Hρ))
      end ].
    all: try solve [ match goal with
      | H : domain_stuck (d_record _ _) |- domain_stuck (d_record _ (_ ++ _ :: nil)) =>
          inversion_clear H; apply domain_stuck_record, stuck_app_snoc; assumption
      end ].
    all: try solve [ match goal with
      | H : domain_stuck (d_tuple ?vs), Hl : field_lookup ?vs _ = Some ?r |- domain_stuck ?r =>
          inversion H; subst; eauto using field_lookup_In
      end ].
    all: try solve [ match goal with
      | H : domain_stuck (⇑ (d_record _ ?ns) ?m), Hk : List.nth_error ?rs _ = Some ?r,
        IH : (forall x, In x ?ns -> domain_stuck x) -> domain_ne_stuck ?m -> (forall y, In y nil -> domain_stuck y) -> forall z, In z ?rs -> domain_stuck z
        |- domain_stuck ?r =>
          inversion H; subst;
          match goal with Hrec : domain_stuck (d_record _ _), Hm : domain_ne_stuck _ |- _ =>
            inversion Hrec; subst;
            eapply IH; [ eassumption | exact Hm | intros ? [] | eapply List.nth_error_In; exact Hk ] end
      end ].
    all: try solve [ match goal with Hin : In _ nil |- _ => destruct Hin end ].
    all: try solve [ match goal with
      | IHT : env_stuck (env_args nil (?ns ++ ?pre)) -> domain_stuck ?t, Hin : In ?d (⇑ ?t (d_proj _ ?m) :: ?rs) |- domain_stuck ?d =>
          eapply (nflds_cons_stuck t m _ rs pre ns);
            [ apply IHT, env_stuck_args; [ exact env_stuck_nil | apply stuck_app; eassumption ] | eassumption .. ]
      end ].
    all: repeat match goal with
           | H : domain_stuck (d_ind _ _ _) |- _ => inversion_clear H
           | H : domain_stuck (d_con _ _ _ _) |- _ => inversion_clear H
           | H : domain_stuck (_ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _ _) |- _ => inversion_clear H
           end.
    (* a member's head and uniform parameters: the group's own, or a view's
       evaluated in them *)
    all: try solve [ match goal with
           | IH : env_stuck (env_args nil ?ups) -> forall a, In a ?cups -> domain_stuck a,
             Hu : forall u, In u ?ups -> domain_stuck u |- forall a, In a ?cups -> domain_stuck a =>
               apply IH, env_stuck_args; [ apply env_stuck_nil | exact Hu ]
           end ].
    (* the recursive results of function shapes and the families of their
       types: closures over stuck environments *)
    all: try solve [ lazymatch goal with |- domain_stuck (d_ihfn _ _ _ _ _ _) => constructor; assumption end ].
    all: try solve [ lazymatch goal with |- domain_stuck (d_ind _ _ (?pre ++ ?bs)) =>
           match goal with IH : env_stuck ?ρ -> forall a, In a bs -> domain_stuck a, Hρ : env_stuck ?ρ |- _ =>
             pose proof (IH Hρ) end;
           match goal with IHm : (forall u, In u ?ups -> domain_stuck u) -> forall a, In a pre -> domain_stuck a,
                           Hu : forall u, In u ?ups -> domain_stuck u |- _ => pose proof (IHm Hu) end;
           constructor; all_in_with assumption end ].
    all: try solve [ lazymatch goal with |- domain_stuck (Πᵈ _ (_ ↦ d_shfam _ _ _ _) _) =>
           match goal with IH : env_stuck ?ρ -> domain_stuck ?b, Hρ : env_stuck ?ρ |- domain_stuck (Πᵈ ?b _ _) =>
             constructor; [ exact (IH Hρ) | apply env_stuck_extend; [ apply env_stuck_nil | constructor; assumption ] ] end end ].
    all: try solve [ lazymatch goal with |- domain_stuck (Πᵈ _ (_ ↦ d_ihfam _ _ _ _ _) _) =>
           match goal with IH : env_stuck ?ρ -> domain_stuck ?b, Hρ : env_stuck ?ρ |- domain_stuck (Πᵈ ?b _ _) =>
             constructor; [ exact (IH Hρ) | apply env_stuck_extend; [ apply env_stuck_nil | constructor; assumption ] ] end end ].
    all: try solve [ match goal with
           | IH : env_stuck (env_args ?ρm (?bs ++ ?v :: nil)) -> domain_stuck ?a,
             IHb : env_stuck ?ρ -> forall x, In x ?bs -> domain_stuck x, Hρ : env_stuck ?ρ, Hρm : env_stuck ?ρm,
             Hv : domain_stuck ?v |- domain_stuck ?a =>
               apply IH, env_stuck_args; [ exact Hρm | apply stuck_app_snoc; [ exact (IHb Hρ) | exact Hv ] ]
           end ].
    all: try solve [ match goal with
           | IH : (forall u, In u ?ups -> domain_stuck u) -> env_stuck (?ρ ↦ ?n) -> domain_stuck ?a |- domain_stuck ?a =>
               apply IH; [ assumption | apply env_stuck_extend; assumption ]
           | IH2 : env_stuck ?ρm -> env_stuck (?ρ ↦ ?n) -> domain_stuck ?fn -> domain_stuck ?a,
             IH1 : domain_stuck ?f -> domain_stuck ?n -> domain_stuck ?fn |- domain_stuck ?a =>
               apply IH2; [ assumption | apply env_stuck_extend; assumption | apply IH1; assumption ]
           | IH2 : env_stuck ?ρ -> ups_stuck ?o -> domain_stuck ?fn -> domain_stuck ?r,
             IH1 : domain_stuck ?f -> domain_stuck ?n -> domain_stuck ?fn |- domain_stuck ?r =>
               apply IH2; [ assumption | assumption | apply IH1; assumption ]
           end ].
    (* the eliminator: its uniform parameters, evaluated in a stuck
       environment *)
    all: try solve [ match goal with
           | IH : env_stuck ?ρ -> ups_stuck ?u -> domain_stuck ?m -> domain_stuck ?r,
             IHu : env_stuck ?ρ -> forall a, In a ?u -> domain_stuck a, IHm : env_stuck ?ρ -> domain_stuck ?m,
             Hρ : env_stuck ?ρ |- domain_stuck ?r =>
               exact (IH Hρ (IHu Hρ) (IHm Hρ))
           end ].
    (* inductive types: the values are lists, of which evaluation takes
       segments *)
    all: try solve [ lazymatch goal with |- domain_stuck (d_ind _ _ _) => idtac | |- domain_stuck (d_con _ _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    (* the branch of a constructor, in the environment of its parameters,
       arguments and recursive results *)
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> ups_stuck ?o -> (forall x1, In x1 ?vs -> domain_stuck x1) -> forall x2, In x2 ?ihs -> domain_stuck x2,
        Hρ : env_stuck ?ρ, Ho : ups_stuck ?o, IHB : env_stuck (env_args ?ρ _) -> domain_stuck ?r |- domain_stuck ?r =>
          pose proof (IH Hρ Ho ltac:(all_in_with assumption));
          apply IHB, env_stuck_args; [ exact Hρ | all_in_with assumption ]
      end ].
    (* the eliminator on a neutral *)
    all: try solve [ match goal with
      | IH : env_stuck (env_args ?ρ _) -> domain_stuck ?t, Hρ : env_stuck ?ρ |- domain_stuck (⇑ ?t (d_elim _ _ _ _ _ _ _)) =>
          constructor;
            [ apply IH, env_stuck_args;
                [ exact Hρ | all_in_with ltac:(constructor; [ constructor; assumption | assumption ]) ]
            | constructor; assumption ]
      end ].
    (* the recursive results *)
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> ups_stuck ?o -> (forall x1, In x1 ?vs -> domain_stuck x1) -> forall x2, In x2 ?ihs -> domain_stuck x2,
        Hρ : env_stuck ?ρ, Ho : ups_stuck ?o, Hv : forall x3, In x3 (_ :: ?vs) -> domain_stuck x3, Ha : In ?d ?ihs |- domain_stuck ?d =>
          exact (IH Hρ Ho (all_in_tail _ _ _ Hv) _ Ha)
      | IH : env_stuck ?ρ -> ups_stuck ?o -> (forall x1, In x1 ?vs -> domain_stuck x1) -> forall x2, In x2 ?ihs -> domain_stuck x2,
        IHv : env_stuck ?ρ -> ups_stuck ?o -> domain_stuck ?v -> domain_stuck ?ih,
        Hρ : env_stuck ?ρ, Ho : ups_stuck ?o, Hv : forall x3, In x3 (?v :: ?vs) -> domain_stuck x3, Ha : In ?d (?ih :: ?ihs) |- domain_stuck ?d =>
          destruct Ha as [<- | Ha];
            [ exact (IHv Hρ Ho (all_in_head _ _ _ Hv)) | exact (IH Hρ Ho (all_in_tail _ _ _ Hv) _ Ha) ]
      end ].
    (* the lists of recursive results along leaf paths, and of their
       types: each member of a list built of stuck values *)
    all: try solve [ stuck_in ].
    (* a record view's value and type: a tuple of stuck fields, the
       record at stuck arguments *)
    all: try solve [ apply domain_stuck_tuple; intros ? ? Hin;
                     first [ destruct Hin
                           | apply List.in_combine_r, in_skipn_in in Hin; eapply stuck_app_snoc; [ eassumption | eassumption | exact Hin ] ] ].
    all: try solve [ apply domain_stuck_record; stuck_prem ].
    all: try solve [ eauto 4 with mctt ].
    (* the [⊥]-eliminator, whose scrutinee is stuck *)
    all: try solve [ match goal with H : env_stuck ?ρ -> domain_stuck (⇑ _ _), Hρ : env_stuck ?ρ |- _ =>
        specialize (H Hρ); inversion_clear H end; eauto 7 with mctt ].
    (* the [ℕ]-eliminator on a neutral *)
    all: try solve [ match goal with IHA : env_stuck (?ρ ↦ ⇑ ?b ?m) -> domain_stuck ?a, IHZ : env_stuck ?ρ -> domain_stuck ?mz,
                      Hρ : env_stuck ?ρ |- _ =>
        apply domain_stuck_neut; [ apply IHA; apply env_stuck_extend; auto with mctt | constructor; auto with mctt ] end ].
    (* arguments, one at a time *)
    all: try solve [ match goal with IH : domain_stuck ?m1 -> _ -> domain_stuck ?r, IH1 : domain_stuck ?m -> domain_stuck ?n -> domain_stuck ?m1,
                      Ha : forall a, In a (cons ?n _) -> domain_stuck a |- domain_stuck ?r =>
        apply IH; [ apply IH1; [ assumption | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ] end ].
    (* a member: the root is stuck, and so are the arguments *)
    all: try solve [ match goal with
      | IHa : domain_stuck ?f -> (forall a, In a ?ns -> domain_stuck a) -> domain_stuck ?r,
        IHs : dmstuck ?h -> domain_stuck ?f, IHh : env_stuck ?ρ -> dmstuck ?h,
        IHe : env_stuck ?ρ -> forall a, In a ?ns -> domain_stuck a, Hρ : env_stuck ?ρ |- domain_stuck ?r =>
          apply IHa; [ apply IHs, IHh, Hρ | apply IHe, Hρ ] end ].
    (* a list of terms *)
    all: try solve [ match goal with
      | Hin : In ?a (cons _ _) |- _ => destruct Hin as [<- | Hin]; eauto with mctt end ].
    (* the module of an inductive type, a record type: the type former, applied *)
    all: try solve [ match goal with
                     | IH : domain_stuck (d_ind _ _ nil) -> _ -> domain_stuck ?r |- domain_stuck ?r =>
                         apply IH; [ first [ constructor; intros ? [] | repeat constructor ] | assumption ]
                     | IH : domain_stuck (d_record _ nil) -> _ -> domain_stuck ?r |- domain_stuck ?r =>
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
    all: try solve [ apply domain_stuck_con;
      match goal with H : env_stuck (env_args nil _) -> forall a, In a _ -> domain_stuck a |- _ =>
        apply H; apply env_stuck_args;
          [ exact env_stuck_nil
          | first [ intros ? [] | intros a Ha; apply List.in_app_or in Ha as [Ha | [<- | []]]; auto ] ] end ].
    (* the type of a recursive argument: the member at the shape's
       parameters after the uniform ones *)
    all: try solve [ apply domain_stuck_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha]; auto ].
    (* a definition with a module part in a body: its term and its unit *)
    all: try solve [ apply env_stuck_extend_dm; eauto 6 with mctt ].
    (* module arguments, one at a time *)
    all: try solve [ match goal with IH : dmstuck ?h1 -> _ -> dmstuck ?r, IH1 : dmstuck ?h -> domain_stuck ?n -> dmstuck ?h1,
                      Ha : forall a, In a (cons ?n _) -> domain_stuck a |- dmstuck ?r =>
        apply IH; [ apply IH1; [ assumption | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ] end ].
    (* the rest: by the rules and the hypotheses *)
    all: eauto 6 with mctt.
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
      Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_stuck ρ -> forall a, In a vs -> domain_stuck a.
  Proof.
    destruct eval_stuck as (He & _).
    induction 1; intros Hρ; [ apply all_in_nil |].
    assert (domain_stuck a) by (eapply He; eassumption).
    apply all_in_cons; [ stuck_val | apply IHfresh_tele; stuck_env ].
  Qed.

  Lemma fresh_cargs_stuck : forall p ups ρ gs s vs,
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_stuck ρ -> (forall a, In a ups -> domain_stuck a) ->
      forall a, In a vs -> domain_stuck a.
  Proof.
    destruct eval_stuck as (He & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
    induction 1; intros Hρ Hu; [ apply all_in_nil | |].
    - assert (domain_stuck a) by (eapply He; eassumption).
      apply all_in_cons; [ stuck_val | apply IHfresh_cargs; [ stuck_env | assumption ] ].
    - assert (domain_stuck a) by (eapply Hsh; eassumption).
      apply all_in_cons; [ stuck_val | apply IHfresh_cargs; assumption ].
  Qed.

  (** The fresh variables along leaf paths, at stuck types. *)
  Lemma fresh_leaf_vars_stuck : forall bs as' s vs, fresh_leaf_vars bs as' s vs ->
      (forall a, In a as' -> domain_stuck a) -> forall a, In a vs -> domain_stuck a.
  Proof.
    induction 1; intros Ha; [ apply all_in_nil | | apply IHfresh_leaf_vars; all_in_with assumption ].
    apply all_in_cons; [ constructor; [ apply Ha; left; reflexivity | constructor ] | apply IHfresh_leaf_vars; all_in_with assumption ].
  Qed.

  Lemma fresh_ihs_stuck : forall ρ A p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ A at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> env_stuck ρ -> ups_stuck ups -> env_stuck ρa ->
      (forall a, In a vs -> domain_stuck a) -> forall a, In a ihs -> domain_stuck a.
  Proof.
    destruct eval_stuck as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hit & _).
    induction 1; intros Hρ Hu Hρa Hv; [ apply all_in_nil | apply IHfresh_ihs; [ assumption | assumption | stuck_env | all_in_with assumption ] | |].
    - apply all_in_app.
      + eapply fresh_leaf_vars_stuck; [ eassumption |].
        eapply Hit; [ eassumption | assumption | assumption | assumption | apply Hv; left; reflexivity ].
      + apply IHfresh_ihs; [ assumption | assumption | assumption | all_in_with assumption ].
    - apply IHfresh_ihs; [ assumption | assumption | assumption | all_in_with assumption ].
  Qed.

  (** The recursive results along leaf paths: each the group's or the
      container's variable, stuck; the variables left too. *)
  Lemma wrap_leaf_vals_stuck : forall bs rs ihs ihs' out, wrap_leaf_vals bs rs ihs ihs' out ->
      (forall a, In a rs -> domain_stuck a) -> (forall a, In a ihs -> domain_stuck a) ->
      (forall a, In a out -> domain_stuck a) /\ (forall a, In a ihs' -> domain_stuck a).
  Proof.
    induction 1; intros Hr Hi; [ split; [ apply all_in_nil | assumption ] | |].
    - destruct IHwrap_leaf_vals as [H1 H2]; [ all_in_with assumption | all_in_with assumption |].
      split; [ apply all_in_cons; [ apply Hi; left; reflexivity | exact H1 ] | exact H2 ].
    - destruct IHwrap_leaf_vals as [H1 H2]; [ all_in_with assumption | assumption |].
      split; [ apply all_in_cons; [ apply Hr; left; reflexivity | exact H1 ] | exact H2 ].
  Qed.

  Lemma wrap_ihs_eval_stuck : forall ρ p ups Bks Dc gs' gs vs ihs r,
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_stuck ρ -> ups_stuck ups ->
      (forall a, In a vs -> domain_stuck a) -> (forall a, In a ihs -> domain_stuck a) -> forall a, In a r -> domain_stuck a.
  Proof.
    destruct eval_stuck as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hih & _).
    induction 1; intros Hρ Ho Hv Hi; [ apply all_in_nil | | |].
    - match goal with Hw : wrap_leaf_vals _ _ _ _ _ |- _ => pose proof (wrap_leaf_vals_stuck _ _ _ _ _ Hw) as Hwl end.
      destruct Hwl as [Hw1 Hw2]; [ eapply Hih; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ] | exact Hi |].
      apply all_in_app; [ exact Hw1 | apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | exact Hw2 ] ].
    - apply all_in_app; [ eapply Hih; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ] |].
      apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | assumption ].
    - apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | assumption ].
  Qed.

  (** Forward reasoning on the premises of the readback of an inductive
      type: what each evaluation or telescope of fresh variables gives. *)
  Ltac stuck_fwd He Hes Hsh Hm :=
    repeat match goal with
      | H : eval_mref _ _ _ ?ups _ (_, _, ?pre) |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x pre -> domain_stuck x) by (exact (Hm _ _ _ _ H ltac:(solve [ all_in_with stuck_val ])));
          clear H
      | H : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ ?r |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x r -> domain_stuck x)
            by (eapply wrap_ihs_eval_stuck; [ exact H | stuck_env | assumption | solve [ all_in_with stuck_val ] | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : fresh_tele _ _ ?ρ _ _ ?ns |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ns -> domain_stuck x) by (eapply fresh_tele_stuck; [ exact H | stuck_env ]);
          clear H
      | H : fresh_cargs _ _ _ _ _ _ _ ?vs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x vs -> domain_stuck x)
            by (eapply fresh_cargs_stuck; [ exact H | stuck_env | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : fresh_ihs _ _ _ _ _ _ _ _ _ _ _ _ ?ihs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ihs -> domain_stuck x)
            by (eapply fresh_ihs_stuck; [ exact H | stuck_env | first [ assumption | solve [ all_in_with stuck_val ] ] | stuck_env
                                        | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : domain_stuck a) by (eapply He; [ exact H | stuck_env ]); clear H
      | H : eval_exps _ _ _ _ ?bs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x bs -> domain_stuck x) by (eapply Hes; [ exact H | stuck_env ]); clear H
      | H : eval_shty _ _ _ _ _ _ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : domain_stuck a) by (eapply Hsh; [ exact H | solve [ all_in_with stuck_val ] | stuck_env ]); clear H
      end.

  Lemma read_stuck :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> domain_nf_stuck m -> nf_stuck (gstuck Θ Ξ) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> domain_ne_stuck m -> ne_stuck (gstuck Θ Ξ) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> domain_stuck a -> nf_stuck (gstuck Θ Ξ) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       level_atoms_stuck xs -> all_list (fun a => ne_stuck (gstuck Θ Ξ) (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a vs -> domain_stuck a) -> all_list (nf_stuck (gstuck Θ Ξ)) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a ups -> domain_stuck a) -> (forall a, In a vs -> domain_stuck a) ->
       all_list (nf_stuck (gstuck Θ Ξ)) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       env_stuck ρ -> (forall a, In a ups -> domain_stuck a) -> domain_stuck x -> nf_stuck (gstuck Θ Ξ) X) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       env_stuck ρ -> ups_stuck ups ->
       all_list (fun b => nf_stuck (gstuck Θ Ξ) (block_motive b) /\
                          all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) (block_branches b)) NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       env_stuck ρ -> ups_stuck ups -> (forall a, In a (snd r) -> domain_stuck a) ->
       all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) Bs') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       env_stuck ρ -> domain_stuck v -> all_list (nf_stuck (gstuck Θ Ξ)) Fs).
  Proof.
    destruct eval_stuck as (He & Ha & Hes & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & Hsh & _ & Hpj & _ & Hpjs & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => domain_nf_stuck m -> nf_stuck (gstuck Θ Ξ) W)
             (fun s m M _ => domain_ne_stuck m -> ne_stuck (gstuck Θ Ξ) M)
             (fun s a A _ => domain_stuck a -> nf_stuck (gstuck Θ Ξ) A)
             (fun s xs ys _ => level_atoms_stuck xs -> all_list (fun a => ne_stuck (gstuck Θ Ξ) (atom_level a)) ys)
             (fun s ρ T vs Ms _ => env_stuck ρ -> (forall a, In a vs -> domain_stuck a) -> all_list (nf_stuck (gstuck Θ Ξ)) Ms)
             (fun s p ups ρ gs vs Ms _ => env_stuck ρ -> (forall a, In a ups -> domain_stuck a) ->
                                        (forall a, In a vs -> domain_stuck a) -> all_list (nf_stuck (gstuck Θ Ξ)) Ms)
             (fun s p ups ρ t x X _ => env_stuck ρ -> (forall a, In a ups -> domain_stuck a) -> domain_stuck x ->
                                     nf_stuck (gstuck Θ Ξ) X)
             (fun s ρ p ups Bks Dc sel i Ms NBks _ =>
                env_stuck ρ -> ups_stuck ups ->
                all_list (fun b => nf_stuck (gstuck Θ Ξ) (block_motive b) /\
                                   all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) (block_branches b)) NBks)
             (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ =>
                env_stuck ρ -> ups_stuck ups -> (forall a, In a (snd r) -> domain_stuck a) ->
                all_list (fun br => nf_stuck (gstuck Θ Ξ) (branch_body br)) Bs')
             (fun s ρ fl v Fs _ => env_stuck ρ -> domain_stuck v -> all_list (nf_stuck (gstuck Θ Ξ)) Fs));
      intros; cbn [snd] in *; cbn;
      (* a field of a value: stuck as the value is *)
      repeat match goal with
        | H : eval_proj _ _ _ ?v ?r, Hv : domain_stuck ?v |- _ =>
            let h := fresh "Hs" in assert (h : domain_stuck r) by exact (Hpj _ _ _ H Hv); clear H
        | H : eval_projs _ _ _ ?v ?ws, Hv : domain_stuck ?v |- _ =>
            let h := fresh "Hs" in assert (h : forall a, In a ws -> domain_stuck a) by exact (Hpjs _ _ _ H Hv); clear H
        end;
      repeat match goal with
        | H : domain_stuck (_ _) |- _ => inversion_clear H
        | H : domain_stuck (_ _ _) |- _ => inversion_clear H
        | H : domain_stuck (_ _ _ _) |- _ => inversion_clear H
        | H : domain_nf_stuck (_ _ _) |- _ => inversion_clear H
        | H : level_atoms_stuck (_ :: _) |- _ => inversion_clear H
        | H : domain_ne_stuck (_ _) |- _ => inversion_clear H
        | H : domain_ne_stuck (_ _ _) |- _ => inversion_clear H
        | H : domain_ne_stuck (_ _ _ _ _ _ _) |- _ => inversion_clear H
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
        [level_atoms_all_keep] and [level_atoms_all_sort] move the property of all the atoms
        across. *)
    all: try solve [ apply level_atoms_all_all_list, level_atoms_all_keep, level_atoms_all_sort, level_atoms_all_all_list; eauto 3 with mctt
                   | apply level_atoms_stuck_sort; eauto 3 with mctt ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try match goal with
         | IH : _ -> nf_stuck (gstuck Θ Ξ) (nf_lvl_of _) |- all_list _ _ =>
             apply IH; repeat constructor; assumption
         end.
    (* a recursive argument of a function shape, under a fresh variable *)
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b, e0 : $| ?x & ⇑! ?b ?s | _ ⍮ _ ↘ ?r, Hρ : env_stuck ?ρ, Hx : domain_stuck ?x,
        Hu : forall a, In a ?ups -> domain_stuck a,
        IH : env_stuck (?ρ ↦ _) -> (forall a, In a ?ups -> domain_stuck a) -> domain_stuck ?r -> nf_stuck (gstuck Θ Ξ) ?V
        |- nf_stuck (gstuck Θ Ξ) ?V =>
          let Hb := fresh "Hb" in
          assert (Hb : domain_stuck b) by (eapply He; eassumption);
          apply IH; [ apply env_stuck_extend; [ exact Hρ | repeat constructor; assumption ] | exact Hu
                    | eapply Ha; [ exact e0 | exact Hx | repeat constructor; assumption ] ]
      end ].
    (* each component is read back from a value built of stuck ones *)
    all: try apply all_list_app.
    all: match goal with
         | IH : context [ nf_stuck (gstuck Θ Ξ) ?W ] |- nf_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : context [ ne_stuck (gstuck Θ Ξ) ?W ] |- ne_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : context [ all_list _ ?W ] |- all_list _ ?W => apply IH
         end.
    all: repeat first [ eassumption | apply env_stuck_nil | constructor | apply env_stuck_extend | apply env_stuck_args
                      | eapply Hpjs; [ eassumption | ]
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
