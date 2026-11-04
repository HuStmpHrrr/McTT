(** * Stuck Globals in Normal Forms

    At any global context, a global reaches a normal form only as the head of
    a neutral, and only when it does not unfold: it resolves to an opaque
    definition or to an axiom ([global_stuck]).  At a transparent context there
    are none, which is [nbe_clean] ([Core.Semantic.Transparency]).

    Proofs are exempt, as in [nf_clean]: a proof reads back as its term
    under definitions of the variables it reads ([nf_proof]), which may
    name any global, and is compared erased.  So is the proof an ex falso
    carries ([ne_absurd]). *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Normal Forms Whose Global Heads Satisfy [G] *)

(** [nf_stuck G W]: every global heading a neutral in [W], outside its
    proofs, satisfies [G]; mutually, in the neutral [M]. *)
Fixpoint nf_stuck (G : qname -> Prop) (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_proof _ | nf_False
  | nf_proof_erased => True
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_stuck G (atom_level a)) xs
  | nf_pi _ A B | nf_fn A B | nf_and A B => nf_stuck G A /\ nf_stuck G B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list (nf_stuck G) Ms
  | nf_neut M => ne_stuck G M
  | nf_record _ Ms => all_list (nf_stuck G) Ms
  | nf_tuple _ Ms _ Ns => all_list (nf_stuck G) Ms /\ all_list (nf_stuck G) Ns
  end
with ne_stuck (G : qname -> Prop) (M : ne) : Prop :=
  match M with
  | ne_absurd A _ | ne_absurd_erased A => nf_stuck G A
  | ne_elim _ Us _ Bks M =>
      all_list (nf_stuck G) Us /\
      all_list (fun b => nf_stuck G (block_scrutinee_type b) /\ nf_stuck G (block_motive b) /\
                         all_list (fun br => nf_stuck G (branch_body br)) (block_branches b)) Bks /\
      ne_stuck G M
  | ne_app M N => ne_stuck G M /\ nf_stuck G N
  | ne_var _ => True
  | ne_glob p => G p
  | ne_proj _ M => ne_stuck G M
  end.

(** Erasure keeps the globals outside the proofs: it only replaces
    proofs. *)
Lemma nf_ne_stuck_erase : forall G, (forall W, nf_stuck G W -> nf_stuck G (nf_erase W)) /\
                                    (forall M, ne_stuck G M -> ne_stuck G (ne_erase M)).
Proof.
  intros G; apply nf_ne_ind; intros; cbn [nf_erase ne_erase nf_stuck ne_stuck] in *; intuition auto;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    rewrite ?all_list_map; try split; auto.
  all: eapply list_all_all_list_impl; [ eassumption | eassumption |]; cbn; intros x Hx Hy.
  all: try solve [ auto ].
  (** An atom of a level: its neutral *)
  all: try solve [ destruct Hx; cbn in *; auto ].
  (** A block: its scrutinee's type, its motive and its branches *)
  destruct Hx as [n' Z HZ A HA brs Hbrs]; cbn in *; destruct Hy as [HyZ [HyA Hybrs]]; split; [ auto | split; [ auto |] ];
    rewrite all_list_map; eapply list_all_all_list_impl; [ exact Hbrs | exact Hybrs |];
    intros br Hbr Hy'; destruct Hbr; cbn in *; auto.
Qed.

Lemma ne_stuck_erase : forall G M, ne_stuck G M -> ne_stuck G (ne_erase M).
Proof. intros G; apply nf_ne_stuck_erase. Qed.

(** Sorting erases the atoms ([level_atoms_sort]). *)
Lemma level_atoms_stuck_sort : forall G xs, all_list (fun a => ne_stuck G (atom_level a)) xs ->
    all_list (fun a => ne_stuck G (atom_level a)) (level_atoms_sort xs).
Proof.
  intros * H; apply level_atoms_all_all_list, level_atoms_all_sort, level_atoms_all_all_list;
    [ apply ne_stuck_erase | assumption ].
Qed.

(** The canonical form of a level keeps a subset of its atoms, erased. *)
Lemma level_atoms_stuck_canon : forall G c xs, all_list (fun a => ne_stuck G (atom_level a)) xs ->
    all_list (fun a => ne_stuck G (atom_level a)) (snd (lvl_canon (c, xs))).
Proof.
  intros * H; apply level_atoms_all_all_list, level_atoms_all_canon, level_atoms_all_all_list;
    [ apply ne_stuck_erase | assumption ].
Qed.

(** A global that does not unfold: an opaque definition or an axiom. *)
#[warnings="-cannot-define-projection"]
Record global_stuck (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop := mk_global_stuck
  { (** Whether the definition is transparent *)
    global_stuck_transparent : bool
    (** Whether it is private *)
  ; global_stuck_private : bool
    (** Its tag *)
  ; global_stuck_relevance : relevance
    (** Its type *)
  ; global_stuck_typ : typ
    (** Its body, if any *)
  ; global_stuck_body : option exp
    (** It is what the global resolves to *)
  ; global_stuck_resolve : gc_resolve Θ Ξ p = Some (ge_def global_stuck_transparent global_stuck_private global_stuck_relevance global_stuck_typ global_stuck_body)
    (** It does not unfold *)
  ; global_stuck_opaque : global_stuck_transparent = false \/ global_stuck_body = None }.

Section Stuck.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma global_stuck_intro : forall p b pv r A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv r A B) -> b = false \/ B = None -> global_stuck Θ Ξ p.
  Proof. intros * Hr Ho; exact (mk_global_stuck _ _ _ _ _ _ _ _ Hr Ho). Qed.
  #[local] Hint Resolve global_stuck_intro : mctt.

(** ** Values Whose Global Neutrals Are Stuck *)

(** [domain_stuck d]: every global neutral in the value [d], its closures'
    environments included, is stuck ([global_stuck]); mutually, for the other
    sorts of values. *)
Inductive domain_stuck : domain -> Prop :=
(** A [Π] of either tag: its domain and its closure's environment *)
| domain_stuck_pi : forall r a (ρ : env) B, domain_stuck a -> (forall x, dentry_stuck (env_entry ρ x)) -> domain_stuck (d_pi r a ρ B)
(** A large universe *)
| domain_stuck_univ : forall i, domain_stuck 𝕌ω@i
(** A small universe: its level *)
| domain_stuck_suniv : forall l, domain_stuck l -> domain_stuck 𝕌@l
(** A type of levels *)
| domain_stuck_level : forall n, domain_stuck (Levelᵈ@n)
(** The sort of the types of levels *)
| domain_stuck_level_sort : domain_stuck LevelSortᵈ
(** A level: its atoms *)
| domain_stuck_lvl : forall c xs, level_atoms_stuck xs -> domain_stuck (lvᵈ c xs)
(** [Prop] *)
| domain_stuck_prop : domain_stuck Propᵈ
(** The true proposition *)
| domain_stuck_True : domain_stuck ⊤ᵈ
(** A kept proof, whatever its term and environment: it reads back as a
    proof, which [nf_stuck] exempts *)
| domain_stuck_proof : forall M (ρ : env), domain_stuck ⋆ᵈ⟨M, ρ⟩
(** The false proposition *)
| domain_stuck_False : domain_stuck ⊥ᵈ
(** A [Σₚ]: its first component and its closure's environment *)
| domain_stuck_and : forall a (ρ : env) Q, domain_stuck a -> (forall x, dentry_stuck (env_entry ρ x)) -> domain_stuck (Σₚᵈ a ρ Q)
(** A λ: its domain and its closure's environment *)
| domain_stuck_fn : forall a (ρ : env) M, domain_stuck a -> (forall x, dentry_stuck (env_entry ρ x)) -> domain_stuck (λᵈ a ρ M)
(** A neutral: its type and itself *)
| domain_stuck_neut : forall a m, domain_stuck a -> domain_ne_stuck m -> domain_stuck (⇑ a m)
(** A member of a module value: the module value *)
| domain_stuck_member : forall h ch, dmod_stuck h -> domain_stuck (d_member h ch)
(** A type former: its arguments *)
| domain_stuck_indty : forall p k args, (forall a, In a args -> domain_stuck a) -> domain_stuck (d_ind p k args)
(** A constructor: its arguments *)
| domain_stuck_con : forall p k c args, (forall a, In a args -> domain_stuck a) -> domain_stuck (d_con p k c args)
(** A recursive result at a function shape: the eliminator's environment,
    its uniform parameters and the argument *)
| domain_stuck_ihfn : forall (ρ : env) Bks p ups t i f, (forall x, dentry_stuck (env_entry ρ x)) ->
    (forall a, In a ups -> domain_stuck a) -> domain_stuck f -> domain_stuck (d_ihfn ρ Bks p ups t i f)
(** A shape family: its uniform parameters and its environment *)
| domain_stuck_shfam : forall p ups (ρ : env) B t, (forall a, In a ups -> domain_stuck a) -> (forall x, dentry_stuck (env_entry ρ x)) ->
    domain_stuck (d_shfam p ups ρ B t)
(** A recursive result's family: the motive's and the shape's
    environments, the group's uniform parameters and the argument *)
| domain_stuck_ihfam : forall (ρm : env) As p ups (ρ : env) B t i f, (forall x, dentry_stuck (env_entry ρm x)) ->
    (forall a, In a ups -> domain_stuck a) -> (forall x, dentry_stuck (env_entry ρ x)) ->
    domain_stuck f -> domain_stuck (d_ihfam ρm As p ups ρ B t i f)
(** A record type former: its arguments *)
| domain_stuck_record : forall p args, (forall a, In a args -> domain_stuck a) -> domain_stuck (d_record p args)
(** A record value: its fields *)
| domain_stuck_tuple : forall vs, (forall f a, In (f, a) vs -> domain_stuck a) -> domain_stuck (d_tuple vs)
with domain_ne_stuck : domain_ne -> Prop :=
(** A variable *)
| domain_stuck_var : forall x, domain_ne_stuck (#ᵈ x)
(** A global, only if it is stuck *)
| domain_stuck_glob : forall p, global_stuck Θ Ξ p -> domain_ne_stuck (d_glob p)
(** An application: its head and its argument *)
| domain_stuck_app : forall m n, domain_ne_stuck m -> domain_nf_stuck n -> domain_ne_stuck (m $ᵈ n)
(** Ex falso: its type; the proof of [⊥] is a proof *)
| domain_stuck_absurd : forall c p, domain_stuck c -> domain_ne_stuck (d_absurd c p)
(** A stuck eliminator: its environment, its uniform parameters, its
    parameters and its scrutinee *)
| domain_stuck_elim : forall (ρ : env) Bks p ups j args m,
    (forall x, dentry_stuck (env_entry ρ x)) -> (forall a, In a ups -> domain_stuck a) ->
    (forall a, In a args -> domain_stuck a) -> domain_ne_stuck m ->
    domain_ne_stuck (d_elim ρ Bks p ups j args m)
(** The field of a neutral: the neutral *)
| domain_stuck_proj : forall f m, domain_ne_stuck m -> domain_ne_stuck (d_proj f m)
with domain_nf_stuck : domain_nf -> Prop :=
| domain_stuck_dom : forall a m, domain_stuck a -> domain_stuck m -> domain_nf_stuck (⇓ a m)
with dmod_stuck : dmod -> Prop :=
| dmod_stuck_global : forall p args, (forall a, In a args -> domain_stuck a) -> dmod_stuck (dm_global p args)
| dmod_stuck_local : forall Δ D (ρ : env),
    (forall x, dentry_stuck (env_entry ρ x)) -> dmod_stuck (dm_local Δ D ρ)
| dmod_stuck_member : forall h ch, dmod_stuck h -> dmod_stuck (dm_member h ch)
with level_atoms_stuck : list (nat * nat * domain_ne) -> Prop :=
| level_atoms_stuck_nil : level_atoms_stuck nil
| level_atoms_stuck_cons : forall k n m xs, domain_ne_stuck m -> level_atoms_stuck xs -> level_atoms_stuck ((k, n, m) :: xs)
(** The entries: their values.  The types and units they are stored at
    are read only in the readback of a kept proof, a proof. *)
with dentry_stuck : dentry -> Prop :=
(** A term: its value *)
| dentry_stuck_term : forall d t, domain_stuck d -> dentry_stuck (de_term d t)
(** A module slot: its module value *)
| dentry_stuck_mod : forall h U, dmod_stuck h -> dentry_stuck (de_mod h U)
(** A term with a module part: both values *)
| dentry_stuck_dm : forall d t h U, domain_stuck d -> dmod_stuck h -> dentry_stuck (de_dm d t h U).

Definition env_stuck (ρ : env) : Prop := forall x, dentry_stuck (env_entry ρ x).

(** The uniform parameters an eliminator carries, stuck.  A definition, so
    that the search does not use it as a lemma about every value. *)
Definition ups_stuck (ups : list domain) : Prop := forall a, In a ups -> domain_stuck a.

#[local] Hint Constructors domain_stuck domain_ne_stuck domain_nf_stuck level_atoms_stuck dmod_stuck dentry_stuck : mctt.

(** [domain_stuck_lvl] is not a hint: its premise is a quantified statement about the
    atoms, which the search would try to prove of an unknown level.  The
    level operations are reached through the three lemmas below instead. *)
#[local] Remove Hints domain_stuck_lvl : mctt.

(** Nor are the rules of inductive types, whose premises are about all the
    members of a list: [stuck_go] reaches them instead. *)
#[local] Remove Hints domain_stuck_indty domain_stuck_con domain_stuck_elim domain_stuck_shfam domain_stuck_ihfn domain_stuck_ihfam : mctt.
(** Nor are those of records, for the same reason. *)
#[local] Remove Hints domain_stuck_record domain_stuck_tuple : mctt.
#[local] Hint Unfold env_stuck : mctt.

(** The entry past the end of an environment: [Prop] at no type. *)
Lemma dentry_stuck_absent_entry : dentry_stuck absent_entry.
Proof. constructor; constructor. Qed.

Lemma env_stuck_nil : env_stuck nil.
Proof. intros x; induction x; cbn; [ exact dentry_stuck_absent_entry | assumption ]. Qed.

Lemma env_stuck_extend : forall ρ d t, env_stuck ρ -> domain_stuck d -> env_stuck (ρ ↦ d ⦂ t).
Proof. intros * Hρ Hd [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_extend_mod : forall ρ h U, env_stuck ρ -> dmod_stuck h -> env_stuck (ρ ↦ᵐ h ⦂ U).
Proof. intros * Hρ Hh [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_extend_dm : forall ρ d t h U, env_stuck ρ -> domain_stuck d -> dmod_stuck h -> env_stuck (ρ ↦ᵈ d ⦂ t ‖ h ⦂ U).
Proof. intros * Hρ Hd Hh [| x]; cbn; auto with mctt. Qed.

Lemma env_stuck_var : forall ρ x, env_stuck ρ -> domain_stuck (ρ x).
Proof. intros * H; unfold env_var; destruct (H x); auto with mctt. Qed.

Lemma env_stuck_mod : forall ρ x, env_stuck ρ -> dmod_stuck (env_mod ρ x).
Proof. intros * H; unfold env_mod; destruct (H x); auto with mctt; constructor; intros ? []. Qed.

(** An environment extended by stuck values, at any types. *)
Lemma env_stuck_extend_typed : forall vts ρ, env_stuck ρ -> (forall a, In a (List.map fst vts) -> domain_stuck a) ->
    env_stuck (env_extend_typed ρ vts).
Proof.
  induction vts as [| vt vts IH]; intros * Hρ Ha; cbn; [ assumption |].
  apply IH; [ apply env_stuck_extend; [ exact Hρ | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ].
Qed.

(** The values of the typed lists of entries evaluation extends
    environments by: the values given, whatever their types. *)
Lemma tele_entries_map_fst : forall vs ρ T, List.map fst (tele_entries ρ T vs) = vs.
Proof. induction vs as [| v vs IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma cargs_entries_map_fst : forall p ups vs ρ gs, List.map fst (cargs_entries p ups ρ gs vs) = vs.
Proof. intros p ups; induction vs as [| v vs IH]; intros ρ [| [] gs]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma pair_values_with_types_map_fst : forall vs ts, List.map fst (pair_values_with_types vs ts) = vs.
Proof. induction vs as [| v vs IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** Pads are [absent_entry]. *)
Lemma env_stuck_kinds_pads : forall n ρ, env_stuck ρ -> env_stuck (kinds_pads n ρ).
Proof.
  unfold kinds_pads; induction n as [| n IH]; intros ρ Hρ; cbn; [ exact Hρ |].
  intros [| x]; cbn; [ exact dentry_stuck_absent_entry | exact (IH ρ Hρ x) ].
Qed.

Lemma stuck_app_snoc : forall (args : list domain) n,
    (forall a, In a args -> domain_stuck a) -> domain_stuck n -> forall a, In a (args ++ n :: nil) -> domain_stuck a.
Proof. intros * H Hn a Ha; apply in_app_or in Ha as [Ha | [<- | []]]; auto. Qed.

Lemma env_stuck_entry : forall ρ x, env_stuck ρ -> dentry_stuck (env_entry ρ x).
Proof. intros * H; exact (H x). Qed.


Lemma dmod_stuck_global_nil : forall p, dmod_stuck (dm_global p nil).
Proof. intros; constructor; intros ? []. Qed.

(** The atoms a level value is built of.  The flat view of a neutral is the
    single atom [(0, m)], so the level operations preserve the property. *)
Lemma level_atoms_stuck_view : forall d, domain_stuck d -> level_atoms_stuck (domain_level_atoms d).
Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

Lemma level_atoms_stuck_suc : forall xs, level_atoms_stuck xs -> level_atoms_stuck (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
Proof. induction 1; cbn; repeat constructor; assumption. Qed.

Lemma level_atoms_stuck_app : forall xs ys, level_atoms_stuck xs -> level_atoms_stuck ys -> level_atoms_stuck (xs ++ ys).
Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

Lemma domain_stuck_lvl_lit : forall n, domain_stuck (domain_level_lit n).
Proof. intros; repeat constructor. Qed.

Lemma domain_stuck_lvl_suc : forall d, domain_stuck d -> domain_stuck (domain_level_suc d).
Proof. intros; unfold domain_level_suc; constructor; apply level_atoms_stuck_suc, level_atoms_stuck_view; assumption. Qed.

Lemma domain_stuck_lvl_max : forall d e, domain_stuck d -> domain_stuck e -> domain_stuck (domain_level_max d e).
Proof. intros; unfold domain_level_max; constructor; apply level_atoms_stuck_app; apply level_atoms_stuck_view; assumption. Qed.

#[local] Hint Resolve env_stuck_nil env_stuck_extend env_stuck_extend_mod env_stuck_extend_dm env_stuck_var env_stuck_mod
  env_stuck_extend_typed stuck_app_snoc dmod_stuck_global_nil env_stuck_entry : mctt.

(** The level lemmas are [Hint Extern], keyed on the operation in the goal: as
    [Hint Resolve] their conclusions would match a goal about an unknown
    value, since [domain_level_suc] and [domain_level_max] unfold to a flat level. *)
#[local] Hint Extern 1 (domain_stuck (domain_level_lit _)) => apply domain_stuck_lvl_lit : mctt.
#[local] Hint Extern 1 (domain_stuck (domain_level_suc _)) => apply domain_stuck_lvl_suc : mctt.
#[local] Hint Extern 1 (domain_stuck (domain_level_max _ _)) => apply domain_stuck_lvl_max : mctt.

(** A member of a suffix is a member of the list. *)
Lemma in_skipn_in : forall {A : Type} n (l : list A) x, In x (List.skipn n l) -> In x l.
Proof. intros A n; induction n as [| n IH]; intros [| y l] x H; cbn in H; auto; right; exact (IH _ _ H). Qed.

(** A member of a prefix is a member of the list. *)
Lemma in_firstn_in : forall {A : Type} n (l : list A) x, In x (List.firstn n l) -> In x l.
Proof.
  intros A n; induction n as [| n IH]; intros [| y l] x H; cbn in H; try contradiction.
  destruct H as [<- | H]; [ left; reflexivity | right; exact (IH _ _ H) ].
Qed.


(** The induction hypotheses at the premises the context proves: an
    environment, uniform parameters, a value or a list of values. *)
Ltac stuck_specialize :=
  repeat match goal with
    | H : env_stuck ?ρ -> _, Hρ : env_stuck ?ρ |- _ => specialize (H Hρ)
    | H : ups_stuck ?u -> _, Hu : ups_stuck ?u |- _ => specialize (H Hu)
    | H : domain_stuck ?a -> _, Ha : domain_stuck ?a |- _ => specialize (H Ha)
    | H : dmod_stuck ?a -> _, Ha : dmod_stuck ?a |- _ => specialize (H Ha)
    | H : domain_ne_stuck ?a -> _, Ha : domain_ne_stuck ?a |- _ => specialize (H Ha)
    | H : (forall u, In u ?l -> domain_stuck u) -> _, Hu : forall u, In u ?l -> domain_stuck u |- _ => specialize (H Hu)
    end.

(** The parts of the stuck values the context has, built by a rule. *)
Ltac stuck_invert :=
  repeat match goal with
    | H : domain_stuck ?d |- _ => tryif is_var d then fail else (inversion H; subst; clear H)
    | H : domain_ne_stuck ?d |- _ => tryif is_var d then fail else (inversion H; subst; clear H)
    | H : domain_nf_stuck ?d |- _ => tryif is_var d then fail else (inversion H; subst; clear H)
    | H : dmod_stuck ?d |- _ => tryif is_var d then fail else (inversion H; subst; clear H)
    | H : level_atoms_stuck (_ :: _) |- _ => inversion H; subst; clear H
    end.

(** A stuck value, environment or list of values, built of stuck parts,
    within [n] steps: an environment through the builders of its entries,
    whose types do not matter; a member of a list by its segments; a
    value by its rule; otherwise by a hypothesis, its premises in turn. *)
Ltac stuck_go n :=
  lazymatch n with
  | O => fail
  | S ?n' =>
      first
        [ assumption
        | exact env_stuck_nil
        | match goal with
          | |- env_stuck (env_tele _ _ _) => unfold env_tele; stuck_go n
          | |- env_stuck (decl_env _ _) => unfold decl_env; stuck_go n
          | |- env_stuck (global_proof_env _ _ _) => unfold global_proof_env; stuck_go n
          | |- env_stuck (kinds_pads _ _) => apply env_stuck_kinds_pads; stuck_go n'
          | |- env_stuck (env_extend_typed _ _) =>
              apply env_stuck_extend_typed;
                [ stuck_go n'
                | unfold branch_entries, motive_entries; cbv zeta; rewrite ?List.map_app, ?tele_entries_map_fst, ?cargs_entries_map_fst, ?pair_values_with_types_map_fst;
                  cbn [List.map fst]; stuck_go n' ]
          | |- env_stuck (_ ↦ _ ⦂ _) => apply env_stuck_extend; stuck_go n'
          | |- env_stuck (_ ↦ᵐ _ ⦂ _) => apply env_stuck_extend_mod; stuck_go n'
          | |- env_stuck (_ ↦ᵈ _ ⦂ _ ‖ _ ⦂ _) => apply env_stuck_extend_dm; stuck_go n'
          | |- ups_stuck _ => unfold ups_stuck; stuck_go n
          | |- forall x, dentry_stuck (env_entry ?ρ x) => change (env_stuck ρ); stuck_go n
          | |- forall _, _ => intro; stuck_go n
          | H : field_lookup ?vs _ = Some ?r, Hv : forall f a, In (f, a) ?vs -> domain_stuck a |- domain_stuck ?r =>
              exact (Hv _ _ (field_lookup_In _ _ _ H))
          | |- In _ _ => solve [ cbn; auto 6 using List.in_or_app, List.in_eq, List.in_cons ]
          | |- global_stuck _ _ _ => solve [ eapply global_stuck_intro; eassumption ]
          | H : List.nth_error ?l _ = Some ?a |- _ => apply List.nth_error_In in H; stuck_go n
          | H : In ?a (List.skipn _ _) |- _ => apply in_skipn_in in H; stuck_go n
          | H : In ?a (List.firstn _ _) |- _ => apply in_firstn_in in H; stuck_go n
          | H : In ?a (_ ++ _) |- _ => apply List.in_app_or in H as [H | H]; stuck_go n
          | H : In ?a (_ :: _) |- _ => destruct H as [<- | H]; stuck_go n
          | H : In _ nil |- _ => destruct H
          | H : In ?a (List.map _ _) |- _ => apply List.in_map_iff in H as (? & <- & ?); stuck_go n
          | H : forall x, In x ?l -> domain_stuck x, Ha : In ?a ?l |- domain_stuck ?a => exact (H _ Ha)
          | H : ups_stuck ?l, Ha : In ?a ?l |- domain_stuck ?a => exact (H _ Ha)
          | |- domain_stuck (env_var _ _) => apply env_stuck_var; stuck_go n'
          | |- dmod_stuck (env_mod _ _) => apply env_stuck_mod; stuck_go n'
          | |- domain_stuck (d_tuple (List.combine _ _)) =>
              apply domain_stuck_tuple; let f := fresh "f" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros f a Ha; apply List.in_combine_r in Ha; stuck_go n'
          | |- domain_stuck (domain_level_lit _) => apply domain_stuck_lvl_lit
          | |- domain_stuck (domain_level_suc _) => apply domain_stuck_lvl_suc; stuck_go n'
          | |- domain_stuck (domain_level_max _ _) => apply domain_stuck_lvl_max; stuck_go n'
          | |- domain_stuck _ => constructor; stuck_go n'
          | |- domain_ne_stuck _ => constructor; stuck_go n'
          | |- domain_nf_stuck _ => constructor; stuck_go n'
          | |- dmod_stuck (dm_global _ _) => constructor; stuck_go n'
          | |- dmod_stuck (dm_local _ _ _) => constructor; stuck_go n'
          | |- dmod_stuck (dm_member _ _) => constructor; stuck_go n'
          | |- dentry_stuck _ => constructor; stuck_go n'
          | |- level_atoms_stuck _ => constructor; stuck_go n'
          end
        | match goal with H : _ |- _ => solve [ eapply H; stuck_go n' ] end ]
  end.


  Lemma eval_stuck :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_stuck ρ -> domain_stuck m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> domain_stuck m -> domain_stuck n -> domain_stuck r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> env_stuck ρ -> forall a, In a ms -> domain_stuck a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> domain_stuck m -> (forall a, In a args -> domain_stuck a) -> domain_stuck r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmod_stuck h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmod_stuck h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmod_stuck h -> domain_stuck n -> dmod_stuck r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> dmod_stuck h -> (forall a, In a ns -> domain_stuck a) -> dmod_stuck r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmod_stuck h -> domain_stuck r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmod_stuck h -> dmod_stuck r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmod_stuck h -> domain_stuck r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmod_stuck h -> dmod_stuck r) /\
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
    (forall m ρ fl rs, eval_neutral_fields Θ Ξ m ρ fl rs -> domain_ne_stuck m -> env_stuck ρ ->
       forall a, In a rs -> domain_stuck a) /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> domain_stuck v -> forall a, In a ws -> domain_stuck a) /\
    (forall p ups ρm As ρ gs vs as', ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' -> ups_stuck ups ->
       env_stuck ρm -> env_stuck ρ -> (forall a, In a vs -> domain_stuck a) -> forall a, In a as' -> domain_stuck a) /\
    (forall rs Ms ρ vs, eval_field_vals Θ Ξ rs Ms ρ vs -> env_stuck ρ -> forall a, In a vs -> domain_stuck a) /\
    (forall f Ms ρ r, eval_app_args Θ Ξ f Ms ρ r -> domain_stuck f -> env_stuck ρ -> domain_stuck r).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_stuck ρ -> domain_stuck m)
             (fun m n r _ => domain_stuck m -> domain_stuck n -> domain_stuck r)
             (fun Ms ρ ms _ => env_stuck ρ -> forall a, In a ms -> domain_stuck a)
             (fun m args r _ => domain_stuck m -> (forall a, In a args -> domain_stuck a) -> domain_stuck r)
             (fun H ρ h _ => env_stuck ρ -> dmod_stuck h)
             (fun Δ D ρ h _ => env_stuck ρ -> dmod_stuck h)
             (fun h n r _ => dmod_stuck h -> domain_stuck n -> dmod_stuck r)
             (fun h ns r _ => dmod_stuck h -> (forall a, In a ns -> domain_stuck a) -> dmod_stuck r)
             (fun h x r _ => dmod_stuck h -> domain_stuck r)
             (fun h y r _ => dmod_stuck h -> dmod_stuck r)
             (fun h ch r _ => dmod_stuck h -> domain_stuck r)
             (fun h ch r _ => dmod_stuck h -> dmod_stuck r)
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
             (fun m ρ fl rs _ => domain_ne_stuck m -> env_stuck ρ -> forall a, In a rs -> domain_stuck a)
             (fun fl v ws _ => domain_stuck v -> forall a, In a ws -> domain_stuck a)
             (fun p ups ρm As ρ gs vs as' _ => ups_stuck ups -> env_stuck ρm -> env_stuck ρ ->
                (forall a, In a vs -> domain_stuck a) -> forall a, In a as' -> domain_stuck a)
             (fun rs Ms ρ vs _ => env_stuck ρ -> forall a, In a vs -> domain_stuck a)
             (fun f Ms ρ r _ => domain_stuck f -> env_stuck ρ -> domain_stuck r));
      intros; cbn [snd] in *.
    (* the induction hypotheses at the premises given, the parts of the
       stuck values given; then each value by its rule, shallowly first *)
    all: stuck_specialize; stuck_invert; stuck_specialize.
    all: try solve [ stuck_go 4 ].
    (* the deeper cases: the neutral eliminator at its motive, the
       projections of a neutral record, the shape families *)
    all: stuck_go 7.
  Qed.

  (** The fresh variables of the telescopes of a declaration are stuck. *)
  Lemma fresh_tele_stuck : forall ρ T s vs,
      Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_stuck ρ -> forall a, In a vs -> domain_stuck a.
  Proof.
    destruct eval_stuck as (He & _).
    induction 1; intros Hρ; [ intros ? [] |].
    assert (domain_stuck a) by (eapply He; eassumption).
    intros x [<- | Hx]; [ stuck_go 3 | apply IHfresh_tele; [ stuck_go 4 | exact Hx ] ].
  Qed.

  Lemma fresh_cargs_stuck : forall p ups ρ gs s vs,
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_stuck ρ -> (forall a, In a ups -> domain_stuck a) ->
      forall a, In a vs -> domain_stuck a.
  Proof.
    destruct eval_stuck as (He & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
    induction 1; intros Hρ Hu; [ intros ? [] | |].
    - assert (domain_stuck a) by (eapply He; eassumption).
      intros x [<- | Hx]; [ stuck_go 3 | apply IHfresh_cargs; [ stuck_go 4 | exact Hu | exact Hx ] ].
    - assert (domain_stuck a) by (eapply Hsh; eassumption).
      intros x [<- | Hx]; [ stuck_go 3 | apply IHfresh_cargs; [ exact Hρ | exact Hu | exact Hx ] ].
  Qed.

  (** The fresh variables along leaf paths, at stuck types. *)
  Lemma fresh_leaf_vars_stuck : forall bs as' s vs, fresh_leaf_vars bs as' s vs ->
      (forall a, In a as' -> domain_stuck a) -> forall a, In a vs -> domain_stuck a.
  Proof.
    induction 1; intros Ha; [ intros ? [] | | apply IHfresh_leaf_vars; intros; apply Ha; right; assumption ].
    intros x [<- | Hx]; [ constructor; [ apply Ha; left; reflexivity | constructor ] |].
    apply IHfresh_leaf_vars; [ intros; apply Ha; right; assumption | exact Hx ].
  Qed.

  Lemma fresh_ihs_stuck : forall ρ A p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ A at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> env_stuck ρ -> ups_stuck ups -> env_stuck ρa ->
      (forall a, In a vs -> domain_stuck a) -> forall a, In a ihs -> domain_stuck a.
  Proof.
    destruct eval_stuck as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hit & _).
    induction 1; intros Hρ Hu Hρa Hv;
      [ intros ? [] | apply IHfresh_ihs; [ assumption | assumption | stuck_go 4 | intros; apply Hv; right; assumption ] | |].
    - intros x Hx; apply List.in_app_or in Hx as [Hx | Hx].
      + eapply fresh_leaf_vars_stuck; [ eassumption | | exact Hx ].
        eapply Hit; [ eassumption | assumption | assumption | assumption | apply Hv; left; reflexivity ].
      + apply IHfresh_ihs; [ assumption | assumption | assumption | intros; apply Hv; right; assumption | exact Hx ].
    - apply IHfresh_ihs; [ assumption | assumption | assumption | intros; apply Hv; right; assumption ].
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
  Ltac stuck_fwd He Ha Hes Hsh Hm Hpj Hpjs :=
    repeat match goal with
      | H : eval_mref _ _ _ ?ups _ (_, _, ?pre) |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x pre -> domain_stuck x) by (refine (Hm _ _ _ _ H _); stuck_go 4);
          clear H
      | H : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ ?r |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x r -> domain_stuck x)
            by (eapply wrap_ihs_eval_stuck; [ exact H | stuck_go 4 | stuck_go 4 | stuck_go 4 | stuck_go 4 ]);
          clear H
      | H : fresh_tele _ _ ?ρ _ _ ?ns |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ns -> domain_stuck x) by (eapply fresh_tele_stuck; [ exact H | stuck_go 4 ]);
          clear H
      | H : fresh_cargs _ _ _ _ _ _ _ ?vs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x vs -> domain_stuck x)
            by (eapply fresh_cargs_stuck; [ exact H | stuck_go 4 | stuck_go 4 ]);
          clear H
      | H : fresh_ihs _ _ _ _ _ _ _ _ _ _ _ _ ?ihs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ihs -> domain_stuck x)
            by (eapply fresh_ihs_stuck; [ exact H | stuck_go 4 | stuck_go 4 | stuck_go 4 | stuck_go 4 ]);
          clear H
      | H : ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : domain_stuck a) by (eapply He; [ exact H | stuck_go 4 ]); clear H
      | H : eval_exps _ _ _ _ ?bs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x bs -> domain_stuck x) by (eapply Hes; [ exact H | stuck_go 4 ]); clear H
      | H : eval_shape_type _ _ _ _ _ _ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : domain_stuck a) by (eapply Hsh; [ exact H | stuck_go 4 | stuck_go 4 ]); clear H
      | H : eval_app _ _ ?m ?n ?r |- _ =>
          let h := fresh "Hs" in
          assert (h : domain_stuck r) by (eapply Ha; [ exact H | stuck_go 4 | stuck_go 4 ]); clear H
      | H : eval_proj _ _ _ ?v ?r |- _ =>
          let h := fresh "Hs" in
          assert (h : domain_stuck r) by (eapply Hpj; [ exact H | stuck_go 4 ]); clear H
      | H : eval_projs _ _ _ ?v ?ws |- _ =>
          let h := fresh "Hs" in
          assert (h : forall a, In a ws -> domain_stuck a) by (eapply Hpjs; [ exact H | stuck_go 4 ]); clear H
      end.

  (** A component read back: by an induction hypothesis, its premises
      stuck values ([stuck_go]). *)
  Ltac stuck_read n :=
    lazymatch n with
    | O => fail
    | S ?n' =>
        first [ assumption
              | exact I
              | match goal with |- _ /\ _ => split; stuck_read n' end
              | match goal with IH : _ |- _ => solve [ eapply IH; stuck_go 5 ] end ]
    end.

  Lemma read_stuck :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> domain_nf_stuck m -> nf_stuck (global_stuck Θ Ξ) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> domain_ne_stuck m -> ne_stuck (global_stuck Θ Ξ) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> domain_stuck a -> nf_stuck (global_stuck Θ Ξ) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       level_atoms_stuck xs -> all_list (fun a => ne_stuck (global_stuck Θ Ξ) (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a vs -> domain_stuck a) -> all_list (nf_stuck (global_stuck Θ Ξ)) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a ups -> domain_stuck a) -> (forall a, In a vs -> domain_stuck a) ->
       all_list (nf_stuck (global_stuck Θ Ξ)) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       env_stuck ρ -> (forall a, In a ups -> domain_stuck a) -> domain_stuck x -> nf_stuck (global_stuck Θ Ξ) X) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       env_stuck ρ -> ups_stuck ups ->
       all_list (fun b => nf_stuck (global_stuck Θ Ξ) (block_scrutinee_type b) /\ nf_stuck (global_stuck Θ Ξ) (block_motive b) /\
                          all_list (fun br => nf_stuck (global_stuck Θ Ξ) (branch_body br)) (block_branches b)) NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       env_stuck ρ -> ups_stuck ups -> (forall a, In a (snd r) -> domain_stuck a) ->
       all_list (fun br => nf_stuck (global_stuck Θ Ξ) (branch_body br)) Bs') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       env_stuck ρ -> domain_stuck v -> all_list (nf_stuck (global_stuck Θ Ξ)) Fs) /\
    (** The readbacks of a kept proof, which [nf_stuck] exempts, ask
        nothing *)
    (forall s v M, Rprf v in Θ ⍮ Ξ ⍮ s ↘ M -> True) /\
    (forall s ρ k bs, Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs -> True) /\
    (forall s e b, Rent e in Θ ⍮ Ξ ⍮ s ↘ b -> True).
  Proof.
    destruct eval_stuck as (He & Ha & Hes & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & Hsh & _ & Hpj & _ & Hpjs & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => domain_nf_stuck m -> nf_stuck (global_stuck Θ Ξ) W)
             (fun s m M _ => domain_ne_stuck m -> ne_stuck (global_stuck Θ Ξ) M)
             (fun s a A _ => domain_stuck a -> nf_stuck (global_stuck Θ Ξ) A)
             (fun s xs ys _ => level_atoms_stuck xs -> all_list (fun a => ne_stuck (global_stuck Θ Ξ) (atom_level a)) ys)
             (fun s ρ T vs Ms _ => env_stuck ρ -> (forall a, In a vs -> domain_stuck a) -> all_list (nf_stuck (global_stuck Θ Ξ)) Ms)
             (fun s p ups ρ gs vs Ms _ => env_stuck ρ -> (forall a, In a ups -> domain_stuck a) ->
                                        (forall a, In a vs -> domain_stuck a) -> all_list (nf_stuck (global_stuck Θ Ξ)) Ms)
             (fun s p ups ρ t x X _ => env_stuck ρ -> (forall a, In a ups -> domain_stuck a) -> domain_stuck x ->
                                     nf_stuck (global_stuck Θ Ξ) X)
             (fun s ρ p ups Bks Dc sel i Ms NBks _ =>
                env_stuck ρ -> ups_stuck ups ->
                all_list (fun b => nf_stuck (global_stuck Θ Ξ) (block_scrutinee_type b) /\ nf_stuck (global_stuck Θ Ξ) (block_motive b) /\
                                   all_list (fun br => nf_stuck (global_stuck Θ Ξ) (branch_body br)) (block_branches b)) NBks)
             (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ =>
                env_stuck ρ -> ups_stuck ups -> (forall a, In a (snd r) -> domain_stuck a) ->
                all_list (fun br => nf_stuck (global_stuck Θ Ξ) (branch_body br)) Bs')
             (fun s ρ fl v Fs _ => env_stuck ρ -> domain_stuck v -> all_list (nf_stuck (global_stuck Θ Ξ)) Fs)
             (fun s v M _ => True)
             (fun s ρ k bs _ => True)
             (fun s e b _ => True));
      intros; cbn [snd] in *; try exact I.
    (* what the evaluations of the premises give, and the parts of the
       stuck values given *)
    all: stuck_specialize; stuck_invert; stuck_specialize.
    all: stuck_fwd He Ha Hes Hsh Hm Hpj Hpjs.
    all: stuck_specialize; stuck_invert; stuck_specialize.
    (* each component read back of a stuck value, by its induction
       hypothesis; a level canonically, its atoms erased *)
    all: cbn [nf_stuck ne_stuck nf_lvl_of nf_univ_of fst snd all_list atom_level
              block_scrutinee_type block_motive block_branches branch_body] in *.
    all: repeat match goal with |- _ /\ _ => split end.
    all: try exact I.
    all: try apply all_list_app.
    all: try solve [ apply level_atoms_stuck_canon; stuck_read 3
                   | apply level_atoms_stuck_sort; stuck_read 3
                   | apply ne_stuck_erase; stuck_read 3
                   | stuck_read 4 ].
  Qed.

  Lemma initial_env_stuck : forall Γ ρ, initial_env Θ Ξ Γ ρ -> env_stuck ρ.
  Proof.
    destruct eval_stuck as (He & _ & _ & _ & Hm & _).
    induction 1;
      repeat first [ assumption | exact env_stuck_nil | apply env_stuck_extend | apply env_stuck_extend_mod
                   | apply env_stuck_extend_dm | constructor | eapply He; eassumption | eapply Hm; eassumption ].
  Qed.

  Theorem nbe_stuck : forall Γ M A W, nbe Θ Ξ Γ M A W -> nf_stuck (global_stuck Θ Ξ) W.
  Proof.
    destruct eval_stuck as (He & _); destruct read_stuck as (Hr & _).
    intros * Hn; inversion Hn; subst.
    match goal with Hρ : initial_env _ _ _ _ |- _ => pose proof (initial_env_stuck _ _ Hρ) end.
    (** The value read back, a proof kept as it is or the term's value, at
        the type's value *)
    match goal with Hw : nbe_term _ _ _ _ _ _ _ |- _ => destruct Hw end;
      (eapply Hr; [ eassumption | constructor; [ eapply He; eassumption | first [ constructor | eapply He; eassumption ] ] ]).
  Qed.
End Stuck.
