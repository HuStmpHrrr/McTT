(** * NbE at a Transparent Global Context

    At a transparent global context ([gc_transparent]) no global evaluates to
    a neutral, so no global reaches a normal form and the only neutrals are
    variables.  Module parameters are λ-variables, so they need no special
    treatment. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Values Without Global Neutrals *)

(** [dclean d]: the value [d], its closures' environments included, has no
    global neutral; mutually, for the other sorts of values. *)
Inductive dclean : domain -> Prop :=
(** A [Π]: its domain and its closure's environment *)
| dclean_pi : forall a (ρ : env) B, dclean a -> (forall x, declean (env_entry ρ x)) -> dclean (Πᵈ a ρ B)
(** A large universe *)
| dclean_univ : forall i, dclean 𝕌ω@i
(** A small universe: its level *)
| dclean_suniv : forall l, dclean l -> dclean 𝕌@l
(** A type of levels *)
| dclean_level : forall n, dclean (Levelᵈ@n)
(** A level: its atoms *)
| dclean_lvl : forall c xs, dclean_la xs -> dclean (lvᵈ c xs)
(** The unit type *)
| dclean_True : dclean ⊤ᵈ
(** The unit's element *)
| dclean_true : dclean ⋆ᵈ
(** The empty type *)
| dclean_False : dclean ⊥ᵈ
(** A λ: its closure's environment *)
| dclean_fn : forall (ρ : env) M, (forall x, declean (env_entry ρ x)) -> dclean (λᵈ ρ M)
(** A neutral: its type and itself *)
| dclean_neut : forall a m, dclean a -> dclean_ne m -> dclean (⇑ a m)
(** A member of a module value: the module value *)
| dclean_member : forall h ch, dmclean h -> dclean (d_member h ch)
(** A type former: its arguments *)
| dclean_indty : forall p k args, (forall a, In a args -> dclean a) -> dclean (d_ind p k args)
(** A constructor: its arguments *)
| dclean_con : forall p k c args, (forall a, In a args -> dclean a) -> dclean (d_con p k c args)
(** A recursive result at a function shape: the eliminator's environment,
    its uniform parameters and the argument *)
| dclean_ihfn : forall (ρ : env) Bks p ups t f, (forall x, declean (env_entry ρ x)) ->
    (forall a, In a ups -> dclean a) -> dclean f -> dclean (d_ihfn ρ Bks p ups t f)
(** A shape family: its uniform parameters and its environment *)
| dclean_shfam : forall p ups (ρ : env) t, (forall a, In a ups -> dclean a) -> (forall x, declean (env_entry ρ x)) ->
    dclean (d_shfam p ups ρ t)
(** A recursive result's family: the motive's and the shape's
    environments, and the argument *)
| dclean_ihfam : forall (ρm : env) As (ρ : env) t f, (forall x, declean (env_entry ρm x)) -> (forall x, declean (env_entry ρ x)) ->
    dclean f -> dclean (d_ihfam ρm As ρ t f)
(** A record type former: its arguments *)
| dclean_record : forall p args, (forall a, In a args -> dclean a) -> dclean (d_record p args)
(** A record value: its fields *)
| dclean_tuple : forall vs, (forall f a, In (f, a) vs -> dclean a) -> dclean (d_tuple vs)
with dclean_ne : domain_ne -> Prop :=
(** A variable; a global never is clean *)
| dclean_var : forall x, dclean_ne (#ᵈ x)
(** An application: its head and its argument *)
| dclean_app : forall m n, dclean_ne m -> dclean_nf n -> dclean_ne (m $ᵈ n)
(** A stuck [efq]: its environment and its scrutinee *)
| dclean_exfalso : forall (ρ : env) A m,
    (forall x, declean (env_entry ρ x)) -> dclean_ne m ->
    dclean_ne (efqᵈ m under ρ return A)
(** A stuck eliminator: its environment, its uniform parameters, its
    parameters and its scrutinee *)
| dclean_elim : forall (ρ : env) Bks p ups j args m,
    (forall x, declean (env_entry ρ x)) -> (forall a, In a ups -> dclean a) ->
    (forall a, In a args -> dclean a) -> dclean_ne m ->
    dclean_ne (d_elim ρ Bks p ups j args m)
(** The field of a neutral: the neutral *)
| dclean_proj : forall f m, dclean_ne m -> dclean_ne (d_proj f m)
with dclean_nf : domain_nf -> Prop :=
| dclean_dom : forall a m, dclean a -> dclean m -> dclean_nf (⇓ a m)
with dmclean : dmod -> Prop :=
| dmclean_global : forall p args, (forall a, In a args -> dclean a) -> dmclean (dm_global p args)
| dmclean_local : forall Δ D (ρ : env),
    (forall x, declean (env_entry ρ x)) -> dmclean (dm_local Δ D ρ)
| dmclean_member : forall h ch, dmclean h -> dmclean (dm_member h ch)
with dclean_la : list (nat * nat * domain_ne) -> Prop :=
| dclean_la_nil : dclean_la nil
| dclean_la_cons : forall k n m xs, dclean_ne m -> dclean_la xs -> dclean_la ((k, n, m) :: xs)
with declean : dentry -> Prop :=
| declean_term : forall d, dclean d -> declean (de_term d)
| declean_mod : forall h, dmclean h -> declean (de_mod h).

Definition env_clean (ρ : env) : Prop := forall x, declean (env_entry ρ x).

(** The uniform parameters an eliminator carries, clean.  A definition, so
    that the search does not use it as a lemma about every value. *)
Definition ups_clean (ups : list domain) : Prop := forall a, In a ups -> dclean a.

#[local] Hint Constructors dclean dclean_ne dclean_nf dclean_la dmclean declean : mctt.

(** [dclean_lvl] is not a hint: its premise is a quantified statement about the
    atoms, which the search would try to prove of an unknown level.  The
    level operations are reached through the three lemmas below instead. *)
#[local] Remove Hints dclean_lvl : mctt.

(** Nor are the rules of inductive types, whose premises are about all the
    members of a list: [all_in_with] reaches them instead. *)
#[local] Remove Hints dclean_indty dclean_con dclean_elim dclean_shfam dclean_ihfn dclean_ihfam : mctt.
(** Nor are those of records, for the same reason. *)
#[local] Remove Hints dclean_record dclean_tuple dclean_proj : mctt.
#[local] Hint Unfold env_clean : mctt.

Lemma env_clean_nil : env_clean nil.
Proof. intros x; induction x; cbn; auto with mctt. Qed.

Lemma env_clean_extend : forall ρ d, env_clean ρ -> dclean d -> env_clean (ρ ↦ d).
Proof. intros * Hρ Hd [| x]; cbn; auto with mctt. Qed.

Lemma env_clean_extend_mod : forall ρ h, env_clean ρ -> dmclean h -> env_clean (ρ ↦ᵐ h).
Proof. intros * Hρ Hh [| x]; cbn; auto with mctt. Qed.

Lemma env_clean_var : forall ρ x, env_clean ρ -> dclean (ρ x).
Proof. intros * H; unfold env_var; destruct (H x); auto with mctt. Qed.

Lemma env_clean_mod : forall ρ x, env_clean ρ -> dmclean (env_mod ρ x).
Proof. intros * H; unfold env_mod; destruct (H x); auto with mctt; constructor; intros ? []. Qed.

Lemma env_clean_args : forall args ρ, env_clean ρ -> (forall a, In a args -> dclean a) -> env_clean (env_args ρ args).
Proof.
  induction args; intros * Hρ Ha; cbn; [ assumption |].
  apply IHargs; [ apply env_clean_extend; auto with datatypes | intros; apply Ha; right; assumption ].
Qed.

Lemma clean_app_snoc : forall (args : list domain) n,
    (forall a, In a args -> dclean a) -> dclean n -> forall a, In a (args ++ n :: nil) -> dclean a.
Proof. intros * H Hn a Ha; apply in_app_or in Ha as [Ha | [<- | []]]; auto. Qed.

Lemma clean_app : forall (l1 l2 : list domain),
    (forall a, In a l1 -> dclean a) -> (forall a, In a l2 -> dclean a) -> forall a, In a (l1 ++ l2) -> dclean a.
Proof. intros * H1 H2 a Ha; apply in_app_or in Ha as [Ha | Ha]; auto. Qed.

(** The neutral projections of the fields of a neutral of a record type,
    one more: the next one at its type, then the rest after it. *)
Lemma nflds_cons_clean : forall t m g rs pre ns,
    dclean t -> (forall x, In x ns -> dclean x) -> dclean_ne m -> (forall x, In x pre -> dclean x) ->
    ((forall x, In x ns -> dclean x) -> dclean_ne m ->
       (forall y, In y (pre ++ ⇑ t (d_proj g m) :: nil) -> dclean y) -> forall z, In z rs -> dclean z) ->
    forall d, In d (⇑ t (d_proj g m) :: rs) -> dclean d.
Proof.
  intros * Ht Hns Hm Hpre IH d [<- | Hd]; [ constructor; [ exact Ht | constructor; exact Hm ] |].
  apply (IH Hns Hm); [| exact Hd ].
  apply clean_app_snoc; [ exact Hpre | constructor; [ exact Ht | constructor; exact Hm ] ].
Qed.

Lemma env_clean_entry : forall ρ x, env_clean ρ -> declean (env_entry ρ x).
Proof. intros * H; exact (H x). Qed.

Lemma dmclean_global_nil : forall p, dmclean (dm_global p nil).
Proof. intros; constructor; intros ? []. Qed.

(** The atoms a level value is built of.  The flat view of a neutral is the
    single atom [(0, m)], so the level operations preserve the property. *)
Lemma dclean_la_view : forall d, dclean d -> dclean_la (dlvl_atoms d).
Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

Lemma dclean_la_suc : forall xs, dclean_la xs -> dclean_la (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
Proof. induction 1; cbn; repeat constructor; assumption. Qed.

Lemma dclean_la_app : forall xs ys, dclean_la xs -> dclean_la ys -> dclean_la (xs ++ ys).
Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

Lemma dclean_lvl_lit : forall n, dclean (dlvl_lit n).
Proof. intros; repeat constructor. Qed.

Lemma dclean_lvl_suc : forall d, dclean d -> dclean (dlvl_suc d).
Proof. intros; unfold dlvl_suc; constructor; apply dclean_la_suc, dclean_la_view; assumption. Qed.

Lemma dclean_lvl_max : forall d e, dclean d -> dclean e -> dclean (dlvl_max d e).
Proof. intros; unfold dlvl_max; constructor; apply dclean_la_app; apply dclean_la_view; assumption. Qed.

#[local] Hint Resolve env_clean_nil env_clean_extend env_clean_extend_mod env_clean_var env_clean_mod
  env_clean_args clean_app_snoc dmclean_global_nil env_clean_entry : mctt.

(** The level lemmas are [Hint Extern], keyed on the operation in the goal: as
    [Hint Resolve] their conclusions would match a goal about an unknown
    value, since [dlvl_suc] and [dlvl_max] unfold to a flat level. *)
#[local] Hint Extern 1 (dclean (dlvl_lit _)) => apply dclean_lvl_lit : mctt.
#[local] Hint Extern 1 (dclean (dlvl_suc _)) => apply dclean_lvl_suc : mctt.
#[local] Hint Extern 1 (dclean (dlvl_max _ _)) => apply dclean_lvl_max : mctt.

Section Transparent.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Htr : gc_transparent Θ Ξ.

  Lemma eval_clean :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_clean ρ -> dclean m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dclean m -> dclean n -> dclean r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> env_clean ρ -> forall a, In a ms -> dclean a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> dclean m -> (forall a, In a args -> dclean a) -> dclean r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_clean ρ -> dmclean h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_clean ρ -> dmclean h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmclean h -> dclean n -> dmclean r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> dmclean h -> (forall a, In a ns -> dclean a) -> dmclean r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmclean h -> dclean r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmclean h -> dmclean r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmclean h -> dclean r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmclean h -> dmclean r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> env_clean ρ -> env_clean ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_clean ρ ->
       ups_clean ups -> dclean m -> dclean r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       env_clean ρ -> ups_clean ups -> (forall a, In a vs -> dclean a) -> forall a, In a ihs -> dclean a) /\
    (forall ρ p ups Bks t v r, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_clean ρ ->
       ups_clean ups -> dclean v -> dclean r) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> (forall u, In u ups -> dclean u) -> forall a, In a (snd r) -> dclean a) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> (forall u, In u ups -> dclean u) -> env_clean ρ -> dclean a) /\
    (forall ρm As ρ t v a, ⟦ihty v of t under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> env_clean ρm -> env_clean ρ -> dclean v -> dclean a) /\
    (forall f m r, eval_proj Θ Ξ f m r -> dclean m -> dclean r) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs -> (forall a, In a ns -> dclean a) -> dclean_ne m ->
       (forall a, In a pre -> dclean a) -> forall a, In a rs -> dclean a).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_clean ρ -> dclean m)
             (fun m n r _ => dclean m -> dclean n -> dclean r)
             (fun Ms ρ ms _ => env_clean ρ -> forall a, In a ms -> dclean a)
             (fun m args r _ => dclean m -> (forall a, In a args -> dclean a) -> dclean r)
             (fun H ρ h _ => env_clean ρ -> dmclean h)
             (fun Δ D ρ h _ => env_clean ρ -> dmclean h)
             (fun h n r _ => dmclean h -> dclean n -> dmclean r)
             (fun h ns r _ => dmclean h -> (forall a, In a ns -> dclean a) -> dmclean r)
             (fun h x r _ => dmclean h -> dclean r)
             (fun h y r _ => dmclean h -> dmclean r)
             (fun h ch r _ => dmclean h -> dclean r)
             (fun h ch r _ => dmclean h -> dmclean r)
             (fun ρ Φ ρ' _ => env_clean ρ -> env_clean ρ')
             (fun ρ p ups Bks j m r _ => env_clean ρ -> ups_clean ups -> dclean m -> dclean r)
             (fun ρ p ups Bks gs vs ihs _ => env_clean ρ -> ups_clean ups ->
                (forall a, In a vs -> dclean a) -> forall a, In a ihs -> dclean a)
             (fun ρ p ups Bks t v r _ => env_clean ρ -> ups_clean ups -> dclean v -> dclean r)
             (fun p ups j r _ => (forall u, In u ups -> dclean u) -> forall a, In a (snd r) -> dclean a)
             (fun p ups ρ t a _ => (forall u, In u ups -> dclean u) -> env_clean ρ -> dclean a)
             (fun ρm As ρ t v a _ => env_clean ρm -> env_clean ρ -> dclean v -> dclean a)
             (fun f m r _ => dclean m -> dclean r)
             (fun ns m fl pre rs _ => (forall a, In a ns -> dclean a) -> dclean_ne m ->
                (forall a, In a pre -> dclean a) -> forall a, In a rs -> dclean a));
      intros; cbn [snd] in *.
    (* records: a type former's arguments, a tuple's fields, and the
       projections of a neutral at their types *)
    all: try solve [ apply dclean_record; intros ? [] ].
    all: try solve [ match goal with
      | IH : env_clean ?ρ -> forall x, In x ?vs -> dclean x, Hρ : env_clean ?ρ |- dclean (d_tuple (List.combine _ ?vs)) =>
          apply dclean_tuple; intros f a Hin; apply (IH Hρ), (List.in_combine_r _ _ _ _ Hin)
      end ].
    all: try solve [ match goal with
      | IHp : dclean ?m -> dclean ?r, IHM : env_clean ?ρ -> dclean ?m, Hρ : env_clean ?ρ |- dclean ?r =>
          exact (IHp (IHM Hρ))
      end ].
    all: try solve [ match goal with
      | H : dclean (d_record _ _) |- dclean (d_record _ (_ ++ _ :: nil)) =>
          inversion_clear H; apply dclean_record, clean_app_snoc; assumption
      end ].
    all: try solve [ match goal with
      | H : dclean (d_tuple ?vs), Hl : field_lookup ?vs _ = Some ?r |- dclean ?r =>
          inversion H; subst; eauto using field_lookup_In
      end ].
    all: try solve [ match goal with
      | H : dclean (⇑ (d_record _ ?ns) ?m), Hk : List.nth_error ?rs _ = Some ?r,
        IH : (forall x, In x ?ns -> dclean x) -> dclean_ne ?m -> (forall y, In y nil -> dclean y) -> forall z, In z ?rs -> dclean z
        |- dclean ?r =>
          inversion H; subst;
          match goal with Hrec : dclean (d_record _ _), Hm : dclean_ne _ |- _ =>
            inversion Hrec; subst;
            eapply IH; [ eassumption | exact Hm | intros ? [] | eapply List.nth_error_In; exact Hk ] end
      end ].
    all: try solve [ match goal with Hin : In _ nil |- _ => destruct Hin end ].
    all: try solve [ match goal with
      | IHT : env_clean (env_args nil (?ns ++ ?pre)) -> dclean ?t, Hin : In ?d (⇑ ?t (d_proj _ ?m) :: ?rs) |- dclean ?d =>
          eapply (nflds_cons_clean t m _ rs pre ns);
            [ apply IHT, env_clean_args; [ exact env_clean_nil | apply clean_app; eassumption ] | eassumption .. ]
      end ].
    all: repeat match goal with
           | H : dclean (d_ind _ _ _) |- _ => inversion_clear H
           | H : dclean (d_con _ _ _ _) |- _ => inversion_clear H
           | H : dclean (_ _) |- _ => inversion_clear H
           | H : dmclean (_ _ _) |- _ => inversion_clear H
           | H : dmclean (_ _ _ _) |- _ => inversion_clear H
           end.
    (* a member's head and uniform parameters: the group's own, or a view's
       evaluated in them *)
    all: try solve [ match goal with
           | IH : env_clean (env_args nil ?ups) -> forall a, In a ?cups -> dclean a,
             Hu : forall u, In u ?ups -> dclean u |- forall a, In a ?cups -> dclean a =>
               apply IH, env_clean_args; [ apply env_clean_nil | exact Hu ]
           end ].
    (* the recursive results of function shapes and the families of their
       types: closures over clean environments *)
    all: try solve [ lazymatch goal with |- dclean (d_ihfn _ _ _ _ _ _) => constructor; assumption end ].
    all: try solve [ lazymatch goal with |- dclean (d_ind _ _ (?pre ++ ?bs)) =>
           match goal with IH : env_clean ?ρ -> forall a, In a bs -> dclean a, Hρ : env_clean ?ρ |- _ =>
             pose proof (IH Hρ) end;
           match goal with IHm : (forall u, In u ?ups -> dclean u) -> forall a, In a pre -> dclean a,
                           Hu : forall u, In u ?ups -> dclean u |- _ => pose proof (IHm Hu) end;
           constructor; all_in_with assumption end ].
    all: try solve [ lazymatch goal with |- dclean (Πᵈ _ (_ ↦ d_shfam _ _ _ _) _) =>
           match goal with IH : env_clean ?ρ -> dclean ?b, Hρ : env_clean ?ρ |- dclean (Πᵈ ?b _ _) =>
             constructor; [ exact (IH Hρ) | apply env_clean_extend; [ apply env_clean_nil | constructor; assumption ] ] end end ].
    all: try solve [ lazymatch goal with |- dclean (Πᵈ _ (_ ↦ d_ihfam _ _ _ _ _) _) =>
           match goal with IH : env_clean ?ρ -> dclean ?b, Hρ : env_clean ?ρ |- dclean (Πᵈ ?b _ _) =>
             constructor; [ exact (IH Hρ) | apply env_clean_extend; [ apply env_clean_nil | constructor; assumption ] ] end end ].
    all: try solve [ match goal with
           | IH : env_clean (env_args ?ρm (?bs ++ ?v :: nil)) -> dclean ?a,
             IHb : env_clean ?ρ -> forall x, In x ?bs -> dclean x, Hρ : env_clean ?ρ, Hρm : env_clean ?ρm,
             Hv : dclean ?v |- dclean ?a =>
               apply IH, env_clean_args; [ exact Hρm | apply clean_app_snoc; [ exact (IHb Hρ) | exact Hv ] ]
           end ].
    all: try solve [ match goal with
           | IH : (forall u, In u ?ups -> dclean u) -> env_clean (?ρ ↦ ?n) -> dclean ?a |- dclean ?a =>
               apply IH; [ assumption | apply env_clean_extend; assumption ]
           | IH2 : env_clean ?ρm -> env_clean (?ρ ↦ ?n) -> dclean ?fn -> dclean ?a,
             IH1 : dclean ?f -> dclean ?n -> dclean ?fn |- dclean ?a =>
               apply IH2; [ assumption | apply env_clean_extend; assumption | apply IH1; assumption ]
           | IH2 : env_clean ?ρ -> ups_clean ?o -> dclean ?fn -> dclean ?r,
             IH1 : dclean ?f -> dclean ?n -> dclean ?fn |- dclean ?r =>
               apply IH2; [ assumption | assumption | apply IH1; assumption ]
           end ].
    (* the eliminator: its uniform parameters, evaluated in a clean
       environment *)
    all: try solve [ match goal with
           | IH : env_clean ?ρ -> ups_clean ?u -> dclean ?m -> dclean ?r,
             IHu : env_clean ?ρ -> forall a, In a ?u -> dclean a, IHm : env_clean ?ρ -> dclean ?m,
             Hρ : env_clean ?ρ |- dclean ?r =>
               exact (IH Hρ (IHu Hρ) (IHm Hρ))
           end ].
    (* inductive types: the values are lists, of which evaluation takes
       segments *)
    all: try solve [ lazymatch goal with |- dclean (d_ind _ _ _) => idtac | |- dclean (d_con _ _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    (* the branch of a constructor, in the environment of its parameters,
       arguments and recursive results *)
    all: try solve [ match goal with
      | IH : env_clean ?ρ -> ups_clean ?o -> (forall x1, In x1 ?vs -> dclean x1) -> forall x2, In x2 ?ihs -> dclean x2,
        Hρ : env_clean ?ρ, Ho : ups_clean ?o, IHB : env_clean (env_args ?ρ _) -> dclean ?r |- dclean ?r =>
          pose proof (IH Hρ Ho ltac:(all_in_with assumption));
          apply IHB, env_clean_args; [ exact Hρ | all_in_with assumption ]
      end ].
    (* the eliminator on a neutral *)
    all: try solve [ match goal with
      | IH : env_clean (env_args ?ρ _) -> dclean ?t, Hρ : env_clean ?ρ |- dclean (⇑ ?t (d_elim _ _ _ _ _ _ _)) =>
          constructor;
            [ apply IH, env_clean_args;
                [ exact Hρ | all_in_with ltac:(constructor; [ constructor; assumption | assumption ]) ]
            | constructor; assumption ]
      end ].
    (* the recursive results *)
    all: try solve [ match goal with
      | IH : env_clean ?ρ -> ups_clean ?o -> (forall x1, In x1 ?vs -> dclean x1) -> forall x2, In x2 ?ihs -> dclean x2,
        Hρ : env_clean ?ρ, Ho : ups_clean ?o, Hv : forall x3, In x3 (_ :: ?vs) -> dclean x3, Ha : In ?d ?ihs |- dclean ?d =>
          exact (IH Hρ Ho (all_in_tail _ _ _ Hv) _ Ha)
      | IH : env_clean ?ρ -> ups_clean ?o -> (forall x1, In x1 ?vs -> dclean x1) -> forall x2, In x2 ?ihs -> dclean x2,
        IHv : env_clean ?ρ -> ups_clean ?o -> dclean ?v -> dclean ?ih,
        Hρ : env_clean ?ρ, Ho : ups_clean ?o, Hv : forall x3, In x3 (?v :: ?vs) -> dclean x3, Ha : In ?d (?ih :: ?ihs) |- dclean ?d =>
          destruct Ha as [<- | Ha];
            [ exact (IHv Hρ Ho (all_in_head _ _ _ Hv)) | exact (IH Hρ Ho (all_in_tail _ _ _ Hv) _ Ha) ]
      end ].
    all: try solve [ eauto 4 with mctt ].
    (* an opaque definition or an axiom *)
    all: try solve [ match goal with H : gc_resolve _ _ _ = Some (ge_def _ _ _ _), Ho : _ \/ _ |- _ =>
         destruct (gc_transparent_resolve _ _ _ _ _ _ _ Htr H) end; intuition congruence ].
    (* the [⊥]-eliminator, whose scrutinee is clean *)
    all: try solve [ match goal with H : env_clean ?ρ -> dclean (⇑ _ _), Hρ : env_clean ?ρ |- _ =>
        specialize (H Hρ); inversion_clear H end; eauto 7 with mctt ].
    (* the [ℕ]-eliminator on a neutral *)
    all: try solve [ match goal with IHA : env_clean (?ρ ↦ ⇑ ?b ?m) -> dclean ?a, IHZ : env_clean ?ρ -> dclean ?mz,
                      Hρ : env_clean ?ρ |- _ =>
        apply dclean_neut; [ apply IHA; apply env_clean_extend; auto with mctt | constructor; auto with mctt ] end ].
    (* arguments, one at a time *)
    all: try solve [ match goal with IH : dclean ?m1 -> _ -> dclean ?r, IH1 : dclean ?m -> dclean ?n -> dclean ?m1,
                      Ha : forall a, In a (cons ?n _) -> dclean a |- dclean ?r =>
        apply IH; [ apply IH1; [ assumption | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ] end ].
    (* a member: the root is clean, and so are the arguments *)
    all: try solve [ match goal with
      | IHa : dclean ?f -> (forall a, In a ?ns -> dclean a) -> dclean ?r,
        IHs : dmclean ?h -> dclean ?f, IHh : env_clean ?ρ -> dmclean ?h,
        IHe : env_clean ?ρ -> forall a, In a ?ns -> dclean a, Hρ : env_clean ?ρ |- dclean ?r =>
          apply IHa; [ apply IHs, IHh, Hρ | apply IHe, Hρ ] end ].
    (* a list of terms *)
    all: try solve [ match goal with
      | Hin : In ?a (cons _ _) |- _ => destruct Hin as [<- | Hin]; eauto with mctt end ].
    (* the module of an inductive type, a record type: the type former, applied *)
    all: try solve [ match goal with
                     | IH : dclean (d_ind _ _ nil) -> _ -> dclean ?r |- dclean ?r =>
                         apply IH; [ first [ constructor; intros ? [] | repeat constructor ] | assumption ]
                     | IH : dclean (d_record _ nil) -> _ -> dclean ?r |- dclean ?r =>
                         apply IH; [ constructor; intros ? [] | assumption ] end ].
    all: try solve [ eauto 6 with mctt ].
    (* a local open, and a name it declares: the entry its open makes *)
    all: try solve [ match goal with
      | IH2 : env_clean ?ρ1 -> env_clean ?ρ2, IH1 : env_clean ?ρ -> env_clean ?ρ1, Hρ : env_clean ?ρ |- env_clean ?ρ2 =>
          exact (IH2 (IH1 Hρ)) end ].
    all: try solve [ match goal with
      | IH : env_clean _ -> env_clean ?ρ', He : env_entry ?ρ' 0 = _ |- _ =>
          let Hs := fresh "Hs" in
          assert (Hs : env_clean ρ') by (apply IH; apply env_clean_args; assumption);
          specialize (Hs 0); rewrite He in Hs; inversion Hs; assumption end ].
    (* module arguments, one at a time *)
    all: try solve [ match goal with IH : dmclean ?h1 -> _ -> dmclean ?r, IH1 : dmclean ?h -> dclean ?n -> dmclean ?h1,
                      Ha : forall a, In a (cons ?n _) -> dclean a |- dmclean ?r =>
        apply IH; [ apply IH1; [ assumption | apply Ha; left; reflexivity ] | intros; apply Ha; right; assumption ] end ].
    (* a constructor of a view at the uniform parameters: the container's at
       the view's arguments, evaluated in an environment of clean values *)
    all: try solve [ apply dclean_con;
      match goal with H : env_clean (env_args nil _) -> forall a, In a _ -> dclean a |- _ =>
        apply H; apply env_clean_args;
          [ exact env_clean_nil
          | first [ intros ? [] | intros a Ha; apply List.in_app_or in Ha as [Ha | [<- | []]]; auto ] ] end ].
    (* the type of a recursive argument: the member at the shape's
       parameters after the uniform ones *)
    all: try solve [ apply dclean_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha]; auto ].
    all: match goal with Hin : In _ nil |- _ => destruct Hin end.
  Qed.

  (** A value built of clean ones, and an environment of clean values: by
      the hypotheses, the rules, and [all_in_with] for the lists. *)
  Ltac clean_val :=
    first [ assumption
          | solve [ eapply all_in_head; eassumption ]
          | solve [ constructor; [ clean_val | constructor ] ]
          | solve [ constructor; [ clean_val | assumption ] ]
          | solve [ constructor; all_in_with clean_val ] ].

  Ltac clean_env :=
    solve [ repeat first [ assumption
                         | apply env_clean_nil
                         | apply env_clean_extend; [| clean_val ]
                         | apply env_clean_args; [| solve [ all_in_with clean_val ] ] ] ].

  (** The fresh variables of the telescopes of a declaration are clean. *)
  Lemma fresh_tele_clean : forall ρ T s vs,
      Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_clean ρ -> forall a, In a vs -> dclean a.
  Proof.
    destruct eval_clean as (He & _).
    induction 1; intros Hρ; [ apply all_in_nil |].
    assert (dclean a) by (eapply He; eassumption).
    apply all_in_cons; [ clean_val | apply IHfresh_tele; clean_env ].
  Qed.

  Lemma fresh_cargs_clean : forall p ups ρ gs s vs,
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> env_clean ρ -> (forall a, In a ups -> dclean a) ->
      forall a, In a vs -> dclean a.
  Proof.
    destruct eval_clean as (He & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
    induction 1; intros Hρ Hu; [ apply all_in_nil | |].
    - assert (dclean a) by (eapply He; eassumption).
      apply all_in_cons; [ clean_val | apply IHfresh_cargs; [ clean_env | assumption ] ].
    - assert (dclean a) by (eapply Hsh; eassumption).
      apply all_in_cons; [ clean_val | apply IHfresh_cargs; assumption ].
  Qed.

  Lemma fresh_ihs_clean : forall ρ A ρa gs' gs vs s ihs,
      Fihs vs at gs' gs under ρ A in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> env_clean ρ -> env_clean ρa -> (forall a, In a vs -> dclean a) ->
      forall a, In a ihs -> dclean a.
  Proof.
    destruct eval_clean as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hit & _).
    induction 1; intros Hρ Hρa Hv; [ apply all_in_nil | apply IHfresh_ihs; [ assumption | clean_env | all_in_with assumption ] | |].
    - assert (dclean a) by (eapply Hit; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ]).
      apply all_in_cons; [ clean_val | apply IHfresh_ihs; [ assumption | assumption | all_in_with assumption ] ].
    - apply IHfresh_ihs; [ assumption | assumption | all_in_with assumption ].
  Qed.

  Lemma wrap_ihs_eval_clean : forall ρ p ups Bks gs' gs vs ihs r,
      ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_clean ρ -> ups_clean ups ->
      (forall a, In a vs -> dclean a) -> (forall a, In a ihs -> dclean a) -> forall a, In a r -> dclean a.
  Proof.
    destruct eval_clean as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hih & _).
    induction 1; intros Hρ Ho Hv Hi; [ apply all_in_nil | | |].
    - apply all_in_cons; [ apply Hi; left; reflexivity | apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | all_in_with assumption ] ].
    - apply all_in_cons; [ eapply Hih; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ] |].
      apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | assumption ].
    - apply IHwrap_ihs_eval; [ assumption | assumption | all_in_with assumption | assumption ].
  Qed.

  (** Forward reasoning on the premises of the readback of an inductive
      type: what each evaluation or telescope of fresh variables gives. *)
  Ltac clean_fwd He Hes Hsh Hm :=
    repeat match goal with
      | H : eval_mref _ _ _ ?ups _ (_, _, ?pre) |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x pre -> dclean x) by (exact (Hm _ _ _ _ H ltac:(solve [ all_in_with clean_val ])));
          clear H
      | H : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ ?r |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x r -> dclean x)
            by (eapply wrap_ihs_eval_clean; [ exact H | clean_env | assumption | solve [ all_in_with clean_val ] | solve [ all_in_with clean_val ] ]);
          clear H
      | H : fresh_tele _ _ ?ρ _ _ ?ns |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ns -> dclean x) by (eapply fresh_tele_clean; [ exact H | clean_env ]);
          clear H
      | H : fresh_cargs _ _ _ _ _ _ _ ?vs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x vs -> dclean x)
            by (eapply fresh_cargs_clean; [ exact H | clean_env | solve [ all_in_with clean_val ] ]);
          clear H
      | H : fresh_ihs _ _ _ _ _ _ _ _ _ ?ihs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ihs -> dclean x)
            by (eapply fresh_ihs_clean; [ exact H | clean_env | clean_env | solve [ all_in_with clean_val ] ]);
          clear H
      | H : ⟦ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : dclean a) by (eapply He; [ exact H | clean_env ]); clear H
      | H : eval_exps _ _ _ _ ?bs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x bs -> dclean x) by (eapply Hes; [ exact H | clean_env ]); clear H
      | H : eval_shty _ _ _ _ _ _ ?a |- _ =>
          let h := fresh "Hs" in
          assert (h : dclean a) by (eapply Hsh; [ exact H | solve [ all_in_with clean_val ] | clean_env ]); clear H
      end.

  Lemma read_clean :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> dclean_nf m -> nf_clean W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> dclean_ne m -> ne_clean M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> dclean a -> nf_clean A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       dclean_la xs -> all_list (fun a => ne_clean (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_clean ρ -> (forall a, In a vs -> dclean a) -> all_list nf_clean Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_clean ρ -> (forall a, In a ups -> dclean a) -> (forall a, In a vs -> dclean a) ->
       all_list nf_clean Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       env_clean ρ -> (forall a, In a ups -> dclean a) -> dclean x -> nf_clean X) /\
    (forall s ρ p ups Bks sel i Ms NBks, Rblks i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       env_clean ρ -> ups_clean ups ->
       all_list (fun b => nf_clean (block_motive b) /\ all_list (fun br => nf_clean (branch_body br)) (block_branches b)) NBks) /\
    (forall s ρ p ups Bks Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       env_clean ρ -> ups_clean ups -> (forall a, In a (snd r) -> dclean a) ->
       all_list (fun br => nf_clean (branch_body br)) Bs') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       env_clean ρ -> dclean v -> all_list nf_clean Fs).
  Proof.
    destruct eval_clean as (He & Ha & Hes & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & Hsh & _ & Hpj & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dclean_nf m -> nf_clean W)
             (fun s m M _ => dclean_ne m -> ne_clean M)
             (fun s a A _ => dclean a -> nf_clean A)
             (fun s xs ys _ => dclean_la xs -> all_list (fun a => ne_clean (atom_level a)) ys)
             (fun s ρ T vs Ms _ => env_clean ρ -> (forall a, In a vs -> dclean a) -> all_list nf_clean Ms)
             (fun s p ups ρ gs vs Ms _ => env_clean ρ -> (forall a, In a ups -> dclean a) ->
                                        (forall a, In a vs -> dclean a) -> all_list nf_clean Ms)
             (fun s p ups ρ t x X _ => env_clean ρ -> (forall a, In a ups -> dclean a) -> dclean x -> nf_clean X)
             (fun s ρ p ups Bks sel i Ms NBks _ =>
                env_clean ρ -> ups_clean ups ->
                all_list (fun b => nf_clean (block_motive b) /\
                                   all_list (fun br => nf_clean (branch_body br)) (block_branches b)) NBks)
             (fun s ρ p ups Bks Mv A Mi r cs Bs Bs' _ =>
                env_clean ρ -> ups_clean ups -> (forall a, In a (snd r) -> dclean a) ->
                all_list (fun br => nf_clean (branch_body br)) Bs')
             (fun s ρ fl v Fs _ => env_clean ρ -> dclean v -> all_list nf_clean Fs));
      intros; cbn [snd] in *; cbn;
      (* a field of a value: clean as the value is *)
      repeat match goal with
        | H : eval_proj _ _ _ ?v ?r, Hv : dclean ?v |- _ =>
            let h := fresh "Hs" in assert (h : dclean r) by exact (Hpj _ _ _ H Hv); clear H
        end;
      repeat match goal with
        | H : dclean (_ _) |- _ => inversion_clear H
        | H : dclean (_ _ _) |- _ => inversion_clear H
        | H : dclean (_ _ _ _) |- _ => inversion_clear H
        | H : dclean_nf (_ _ _) |- _ => inversion_clear H
        | H : dclean_la (_ :: _) |- _ => inversion_clear H
        | H : dclean_ne (_ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    (** Inductive types: each component is read back at a type, in an
        environment, of clean values. *)
    all: try solve [
      clean_fwd He Hes Hsh Hm;
      try apply all_list_app;
      match goal with
      | IH : context [ nf_clean ?W ] |- nf_clean ?W => apply IH
      | IH : context [ ne_clean ?W ] |- ne_clean ?W => apply IH
      | IH : context [ all_list _ ?W ] |- all_list _ ?W => apply IH
      end;
      first [ clean_env | solve [ all_in_with clean_val ] | clean_val | solve [ constructor; clean_val ] ] ].
    (** A level reads back canonically, so its atoms are sorted and merged;
        [la_all_keep] and [la_all_sort] move the property of all the atoms
        across. *)
    all: try solve [ apply la_clean_all, la_all_keep, la_all_sort, la_clean_all; eauto 3 with mctt
                   | apply la_clean_sort; eauto 3 with mctt ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try match goal with
         | IH : _ -> nf_clean (nf_lvl_of _) |- all_list _ _ =>
             apply IH; repeat constructor; assumption
         end.
    (* a recursive argument of a function shape, under a fresh variable *)
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b, e0 : $| ?x & ⇑! ?b ?s | _ ⍮ _ ↘ ?r, Hρ : env_clean ?ρ, Hx : dclean ?x,
        Hu : forall a, In a ?ups -> dclean a,
        IH : env_clean (?ρ ↦ _) -> (forall a, In a ?ups -> dclean a) -> dclean ?r -> nf_clean ?V
        |- nf_clean ?V =>
          let Hb := fresh "Hb" in
          assert (Hb : dclean b) by (eapply He; eassumption);
          apply IH; [ apply env_clean_extend; [ exact Hρ | repeat constructor; assumption ] | exact Hu
                    | eapply Ha; [ exact e0 | exact Hx | repeat constructor; assumption ] ]
      end ].
    (* each component is read back from a value built of clean ones *)
    all: match goal with
         | IH : _ -> nf_clean ?W |- nf_clean ?W => apply IH
         | IH : _ -> ne_clean ?W |- ne_clean ?W => apply IH
         | IH : _ -> all_list _ ?W |- all_list _ ?W => apply IH
         end.
    all: repeat first [ eassumption | constructor | apply env_clean_extend
                      | eapply He; [ eassumption |] | eapply Ha; [ eassumption | |] | eapply Hsh; [ eassumption | |] ].
  Qed.

  Lemma initial_env_clean : forall Γ ρ, initial_env Θ Ξ Γ ρ -> env_clean ρ.
  Proof.
    destruct eval_clean as (He & _ & _ & _ & Hm & _).
    induction 1; eauto with mctt.
  Qed.

  Theorem nbe_clean : forall Γ M A W, nbe Θ Ξ Γ M A W -> nf_clean W.
  Proof.
    destruct eval_clean as (He & _); destruct read_clean as (Hr & _).
    intros * Hn; inversion Hn; subst.
    match goal with Hρ : initial_env _ _ _ _ |- _ => pose proof (initial_env_clean _ _ Hρ) end.
    eapply Hr; eauto with mctt.
  Qed.
End Transparent.
