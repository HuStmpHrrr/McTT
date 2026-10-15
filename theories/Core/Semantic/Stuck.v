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
From Mctt.Core.Syntactic Require Import Inductives.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Normal Forms Whose Global Heads Satisfy [G] *)

Fixpoint nf_stuck (G : qname -> Prop) (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_True | nf_true | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => la_stuck G xs
  | nf_pi A B | nf_fn A B => nf_stuck G A /\ nf_stuck G B
  | nf_indty _ Ms | nf_con _ _ Ms => nfs_stuck G Ms
  | nf_neut M => ne_stuck G M
  end
with ne_stuck (G : qname -> Prop) (M : ne) : Prop :=
  match M with
  | ne_exfalso A M => nf_stuck G A /\ ne_stuck G M
  | ne_elim _ A Bs M => nf_stuck G A /\ nbrs_stuck G Bs /\ ne_stuck G M
  | ne_app M N => ne_stuck G M /\ nf_stuck G N
  | ne_var _ => True
  | ne_glob p => G p
  end
with la_stuck (G : qname -> Prop) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ _ M r => ne_stuck G M /\ la_stuck G r
  end
with nfs_stuck (G : qname -> Prop) (Ms : nfs) : Prop :=
  match Ms with
  | nfs_nil => True
  | nfs_cons M Ms => nf_stuck G M /\ nfs_stuck G Ms
  end
with nbrs_stuck (G : qname -> Prop) (Bs : nbrs) : Prop :=
  match Bs with
  | nbrs_nil => True
  | nbrs_cons _ _ B Bs => nf_stuck G B /\ nbrs_stuck G Bs
  end.

Lemma la_stuck_all : forall G xs, la_stuck G xs <-> la_all (ne_stuck G) xs.
Proof. intros G; induction xs as [| k s a r IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma la_stuck_canon : forall G c xs, la_stuck G xs -> la_stuck G (snd (lvl_canon (c, xs))).
Proof. intros * H; apply la_stuck_all, la_all_canon, la_stuck_all; assumption. Qed.

Lemma la_stuck_sort : forall G xs, la_stuck G xs -> la_stuck G (la_sort xs).
Proof. intros * H; apply la_stuck_all, la_all_sort, la_stuck_all; assumption. Qed.

Lemma nfs_stuck_app : forall G Ms Ns, nfs_stuck G Ms -> nfs_stuck G Ns -> nfs_stuck G (nfs_app Ms Ns).
Proof. induction Ms; cbn; intuition. Qed.

(** A global that does not unfold: an opaque definition or an axiom. *)
Definition gstuck (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop :=
  exists b pv A B, gc_resolve Θ Ξ p = Some (ge_def b pv A B) /\ (b = false \/ B = None).

Section Stuck.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma gstuck_intro : forall p b pv A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv A B) -> b = false \/ B = None -> gstuck Θ Ξ p.
  Proof. unfold gstuck; eauto 7. Qed.
  #[local] Hint Resolve gstuck_intro : mctt.

(** ** Values Whose Global Neutrals Are Stuck *)

Inductive dstuck : domain -> Prop :=
| dstuck_pi : forall a (ρ : env) B, dstuck a -> (forall x, destuck (env_entry ρ x)) -> dstuck (Πᵈ a ρ B)
| dstuck_univ : forall i, dstuck 𝕌ω@i
| dstuck_suniv : forall l, dstuck l -> dstuck 𝕌@l
| dstuck_level : forall n, dstuck (Levelᵈ@n)
| dstuck_lvl : forall c xs, dstuck_la xs -> dstuck (lvᵈ c xs)
| dstuck_True : dstuck ⊤ᵈ
| dstuck_true : dstuck ⋆ᵈ
| dstuck_False : dstuck ⊥ᵈ
| dstuck_fn : forall (ρ : env) M, (forall x, destuck (env_entry ρ x)) -> dstuck (λᵈ ρ M)
| dstuck_neut : forall a m, dstuck a -> dstuck_ne m -> dstuck (⇑ a m)
| dstuck_member : forall h ch, dmstuck h -> dstuck (d_member h ch)
| dstuck_indty : forall p args, (forall a, In a args -> dstuck a) -> dstuck (d_ind p args)
| dstuck_con : forall p c args, (forall a, In a args -> dstuck a) -> dstuck (d_con p c args)
| dstuck_ihfn : forall (ρ : env) nm A Bs t f, (forall x, destuck (env_entry ρ x)) -> dstuck f -> dstuck (d_ihfn ρ nm A Bs t f)
| dstuck_shfam : forall p ups (ρ : env) t, (forall a, In a ups -> dstuck a) -> (forall x, destuck (env_entry ρ x)) ->
    dstuck (d_shfam p ups ρ t)
| dstuck_ihfam : forall (ρm : env) A (ρ : env) t f, (forall x, destuck (env_entry ρm x)) -> (forall x, destuck (env_entry ρ x)) ->
    dstuck f -> dstuck (d_ihfam ρm A ρ t f)
with dstuck_ne : domain_ne -> Prop :=
| dstuck_var : forall x, dstuck_ne (#ᵈ x)
| dstuck_glob : forall p, gstuck Θ Ξ p -> dstuck_ne (d_glob p)
| dstuck_app : forall m n, dstuck_ne m -> dstuck_nf n -> dstuck_ne (m $ᵈ n)
| dstuck_exfalso : forall (ρ : env) A m,
    (forall x, destuck (env_entry ρ x)) -> dstuck_ne m ->
    dstuck_ne (efqᵈ m under ρ return A)
| dstuck_elim : forall (ρ : env) nm A Bs p args m,
    (forall x, destuck (env_entry ρ x)) -> (forall a, In a args -> dstuck a) -> dstuck_ne m ->
    dstuck_ne (d_elim ρ nm A Bs p args m)
with dstuck_nf : domain_nf -> Prop :=
| dstuck_dom : forall a m, dstuck a -> dstuck m -> dstuck_nf (⇓ a m)
with dmstuck : dmod -> Prop :=
| dmstuck_global : forall p args, (forall a, In a args -> dstuck a) -> dmstuck (dm_global p args)
| dmstuck_local : forall (ρ : env) U args,
    (forall x, destuck (env_entry ρ x)) -> (forall a, In a args -> dstuck a) -> dmstuck (dm_local ρ U args)
| dmstuck_member : forall h ch, dmstuck h -> dmstuck (dm_member h ch)
with dstuck_la : list (nat * nat * domain_ne) -> Prop :=
| dstuck_la_nil : dstuck_la nil
| dstuck_la_cons : forall k n m xs, dstuck_ne m -> dstuck_la xs -> dstuck_la ((k, n, m) :: xs)
with destuck : dentry -> Prop :=
| destuck_term : forall d, dstuck d -> destuck (de_term d)
| destuck_mod : forall h, dmstuck h -> destuck (de_mod h).

Definition env_stuck (ρ : env) : Prop := forall x, destuck (env_entry ρ x).

#[local] Hint Constructors dstuck dstuck_ne dstuck_nf dstuck_la dmstuck destuck : mctt.

(** [dstuck_lvl] is not a hint: its premise is a quantified statement about the
    atoms, which the search would try to prove of an unknown level.  The
    level operations are reached through the three lemmas below instead. *)
#[local] Remove Hints dstuck_lvl : mctt.

(** Nor are the rules of inductive types, whose premises are about all the
    members of a list: [all_in_with] reaches them instead. *)
#[local] Remove Hints dstuck_indty dstuck_con dstuck_elim dstuck_shfam dstuck_ihfn dstuck_ihfam : mctt.
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

Lemma env_stuck_entry : forall ρ x, env_stuck ρ -> destuck (env_entry ρ x).
Proof. intros * H; exact (H x). Qed.

Lemma dmstuck_local_nil : forall ρ U, env_stuck ρ -> dmstuck (dm_local ρ U nil).
Proof. intros; constructor; [ assumption | intros ? [] ]. Qed.

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
  env_stuck_args stuck_app_snoc dmstuck_local_nil dmstuck_global_nil env_stuck_entry : mctt.

(** The level lemmas are [Hint Extern], keyed on the operation in the goal: as
    [Hint Resolve] their conclusions would match a goal about an unknown
    value, since [dlvl_suc] and [dlvl_max] unfold to a flat level. *)
#[local] Hint Extern 1 (dstuck (dlvl_lit _)) => apply dstuck_lvl_lit : mctt.
#[local] Hint Extern 1 (dstuck (dlvl_suc _)) => apply dstuck_lvl_suc : mctt.
#[local] Hint Extern 1 (dstuck (dlvl_max _ _)) => apply dstuck_lvl_max : mctt.


  Lemma eval_stuck :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_stuck ρ -> dstuck m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dstuck m -> dstuck n -> dstuck r) /\
    (forall Ms ρ ms, eval_exps Θ Ξ Ms ρ ms -> env_stuck ρ -> forall a, In a ms -> dstuck a) /\
    (forall m args r, eval_apps Θ Ξ m args r -> dstuck m -> (forall a, In a args -> dstuck a) -> dstuck r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmstuck h) /\
    (forall h n r, eval_appm Θ Ξ h n r -> dmstuck h -> dstuck n -> dmstuck r) /\
    (forall h x r, eval_sel Θ Ξ h x r -> dmstuck h -> dstuck r) /\
    (forall h y r, eval_selm Θ Ξ h y r -> dmstuck h -> dmstuck r) /\
    (forall h ch r, eval_selc Θ Ξ h ch r -> dmstuck h -> dstuck r) /\
    (forall h ch r, eval_selmc Θ Ξ h ch r -> dmstuck h -> dmstuck r) /\
    (forall ρ Φ ρ', eval_benv Θ Ξ ρ Φ ρ' -> env_stuck ρ -> env_stuck ρ') /\
    (forall ρ nm A Bs m r, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> env_stuck ρ -> dstuck m -> dstuck r) /\
    (forall ρ nm A Bs gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       env_stuck ρ -> (forall a, In a vs -> dstuck a) -> forall a, In a ihs -> dstuck a) /\
    (forall ρ nm A Bs t v r, eval_ih Θ Ξ ρ nm A Bs t v r -> env_stuck ρ -> dstuck v -> dstuck r) /\
    (forall p ups ρ t a, eval_shty Θ Ξ p ups ρ t a -> (forall u, In u ups -> dstuck u) -> env_stuck ρ -> dstuck a) /\
    (forall ρm A ρ t v a, eval_ihty Θ Ξ ρm A ρ t v a -> env_stuck ρm -> env_stuck ρ -> dstuck v -> dstuck a).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_stuck ρ -> dstuck m)
             (fun m n r _ => dstuck m -> dstuck n -> dstuck r)
             (fun Ms ρ ms _ => env_stuck ρ -> forall a, In a ms -> dstuck a)
             (fun m args r _ => dstuck m -> (forall a, In a args -> dstuck a) -> dstuck r)
             (fun H ρ h _ => env_stuck ρ -> dmstuck h)
             (fun h n r _ => dmstuck h -> dstuck n -> dmstuck r)
             (fun h x r _ => dmstuck h -> dstuck r)
             (fun h y r _ => dmstuck h -> dmstuck r)
             (fun h ch r _ => dmstuck h -> dstuck r)
             (fun h ch r _ => dmstuck h -> dmstuck r)
             (fun ρ Φ ρ' _ => env_stuck ρ -> env_stuck ρ')
             (fun ρ nm A Bs m r _ => env_stuck ρ -> dstuck m -> dstuck r)
             (fun ρ nm A Bs gs vs ihs _ => env_stuck ρ -> (forall a, In a vs -> dstuck a) -> forall a, In a ihs -> dstuck a)
             (fun ρ nm A Bs t v r _ => env_stuck ρ -> dstuck v -> dstuck r)
             (fun p ups ρ t a _ => (forall u, In u ups -> dstuck u) -> env_stuck ρ -> dstuck a)
             (fun ρm A ρ t v a _ => env_stuck ρm -> env_stuck ρ -> dstuck v -> dstuck a));
      intros.
    all: repeat match goal with
           | H : dstuck (d_ind _ _) |- _ => inversion_clear H
           | H : dstuck (d_con _ _ _) |- _ => inversion_clear H
           | H : dstuck (_ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _ _) |- _ => inversion_clear H
           end.
    (* the recursive results of function shapes and the families of their
       types: closures over stuck environments *)
    all: try solve [ lazymatch goal with |- dstuck (d_ihfn _ _ _ _ _ _) => constructor; assumption end ].
    all: try solve [ lazymatch goal with |- dstuck (d_ind _ (_ ++ ?bs)) =>
           match goal with IH : env_stuck ?ρ -> forall a, In a bs -> dstuck a, Hρ : env_stuck ?ρ |- _ =>
             pose proof (IH Hρ); constructor; all_in_with assumption end end ].
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
           | IH2 : env_stuck ?ρ -> dstuck ?fn -> dstuck ?r,
             IH1 : dstuck ?f -> dstuck ?n -> dstuck ?fn |- dstuck ?r =>
               apply IH2; [ assumption | apply IH1; assumption ]
           end ].
    (* inductive types: the values are lists, of which evaluation takes
       segments *)
    all: try solve [ lazymatch goal with |- dstuck (d_ind _ _) => idtac | |- dstuck (d_con _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    (* the branch of a constructor, in the environment of its parameters,
       arguments and recursive results *)
    all: try solve [ match goal with
      | IH : env_stuck ?ρ -> (forall x1, In x1 ?vs -> dstuck x1) -> forall x2, In x2 ?ihs -> dstuck x2,
        Hρ : env_stuck ?ρ, IHB : env_stuck (env_args ?ρ _) -> dstuck ?r |- dstuck ?r =>
          pose proof (IH Hρ ltac:(all_in_with assumption));
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
      | IH : env_stuck ?ρ -> (forall x1, In x1 ?vs -> dstuck x1) -> forall x2, In x2 ?ihs -> dstuck x2,
        Hρ : env_stuck ?ρ, Hv : forall x3, In x3 (_ :: ?vs) -> dstuck x3, Ha : In ?d ?ihs |- dstuck ?d =>
          exact (IH Hρ (all_in_tail _ _ _ Hv) _ Ha)
      | IH : env_stuck ?ρ -> (forall x1, In x1 ?vs -> dstuck x1) -> forall x2, In x2 ?ihs -> dstuck x2,
        IHv : env_stuck ?ρ -> dstuck ?v -> dstuck ?ih,
        Hρ : env_stuck ?ρ, Hv : forall x3, In x3 (?v :: ?vs) -> dstuck x3, Ha : In ?d (?ih :: ?ihs) |- dstuck ?d =>
          destruct Ha as [<- | Ha];
            [ exact (IHv Hρ (all_in_head _ _ _ Hv)) | exact (IH Hρ (all_in_tail _ _ _ Hv) _ Ha) ]
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
    (* the module of an inductive type: the type former, applied *)
    all: try solve [ match goal with IH : dstuck (d_ind _ nil) -> _ -> dstuck ?r |- dstuck ?r =>
                       apply IH; [ first [ constructor; intros ? [] | repeat constructor ] | assumption ] end ].
    (* a local open, and a name it declares: the entry its open makes *)
    all: try solve [ match goal with
      | IH2 : env_stuck ?ρ1 -> env_stuck ?ρ2, IH1 : env_stuck ?ρ -> env_stuck ?ρ1, Hρ : env_stuck ?ρ |- env_stuck ?ρ2 =>
          exact (IH2 (IH1 Hρ)) end ].
    all: try solve [ match goal with
      | IH : env_stuck _ -> env_stuck ?ρ', He : env_entry ?ρ' 0 = _ |- _ =>
          let Hs := fresh "Hs" in
          assert (Hs : env_stuck ρ') by (apply IH; apply env_stuck_args; assumption);
          specialize (Hs 0); rewrite He in Hs; inversion Hs; assumption end ].
    all: match goal with Hin : In _ nil |- _ => destruct Hin end.
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
      fresh_tele Θ Ξ ρ T s vs -> env_stuck ρ -> forall a, In a vs -> dstuck a.
  Proof.
    destruct eval_stuck as (He & _).
    induction 1; intros Hρ; [ apply all_in_nil |].
    assert (dstuck a) by (eapply He; eassumption).
    apply all_in_cons; [ stuck_val | apply IHfresh_tele; stuck_env ].
  Qed.

  Lemma fresh_cargs_stuck : forall p ups ρ gs s vs,
      fresh_cargs Θ Ξ p ups ρ gs s vs -> env_stuck ρ -> (forall a, In a ups -> dstuck a) ->
      forall a, In a vs -> dstuck a.
  Proof.
    destruct eval_stuck as (He & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
    induction 1; intros Hρ Hu; [ apply all_in_nil | |].
    - assert (dstuck a) by (eapply He; eassumption).
      apply all_in_cons; [ stuck_val | apply IHfresh_cargs; [ stuck_env | assumption ] ].
    - assert (dstuck a) by (eapply Hsh; eassumption).
      apply all_in_cons; [ stuck_val | apply IHfresh_cargs; assumption ].
  Qed.

  Lemma fresh_ihs_stuck : forall ρ A ρa gs vs s ihs,
      fresh_ihs Θ Ξ ρ A ρa gs vs s ihs -> env_stuck ρ -> env_stuck ρa -> (forall a, In a vs -> dstuck a) ->
      forall a, In a ihs -> dstuck a.
  Proof.
    destruct eval_stuck as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hit).
    induction 1; intros Hρ Hρa Hv; [ apply all_in_nil | apply IHfresh_ihs; [ assumption | stuck_env | all_in_with assumption ] |].
    assert (dstuck a) by (eapply Hit; [ eassumption | assumption | assumption | apply Hv; left; reflexivity ]).
    apply all_in_cons; [ stuck_val | apply IHfresh_ihs; [ assumption | assumption | all_in_with assumption ] ].
  Qed.

  (** Forward reasoning on the premises of the readback of an inductive
      type: what each evaluation or telescope of fresh variables gives. *)
  Ltac stuck_fwd He Hes Hsh :=
    repeat match goal with
      | H : fresh_tele _ _ ?ρ _ _ ?ns |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x ns -> dstuck x) by (eapply fresh_tele_stuck; [ exact H | stuck_env ]);
          clear H
      | H : fresh_cargs _ _ _ _ _ _ _ ?vs |- _ =>
          let h := fresh "Hs" in
          assert (h : forall x, In x vs -> dstuck x)
            by (eapply fresh_cargs_stuck; [ exact H | stuck_env | solve [ all_in_with stuck_val ] ]);
          clear H
      | H : fresh_ihs _ _ _ _ _ _ _ _ ?ihs |- _ =>
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
       dstuck_la xs -> la_stuck (gstuck Θ Ξ) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       env_stuck ρ -> (forall a, In a vs -> dstuck a) -> nfs_stuck (gstuck Θ Ξ) Ms) /\
    (forall s p ups ρ gs vs Ms, read_cargs Θ Ξ s p ups ρ gs vs Ms ->
       env_stuck ρ -> (forall a, In a ups -> dstuck a) -> (forall a, In a vs -> dstuck a) ->
       nfs_stuck (gstuck Θ Ξ) Ms) /\
    (forall s ρ A p D ups cs Bs Bs', read_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
       env_stuck ρ -> (forall a, In a ups -> dstuck a) -> nbrs_stuck (gstuck Θ Ξ) Bs').
  Proof.
    destruct eval_stuck as (He & Ha & Hes & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dstuck_nf m -> nf_stuck (gstuck Θ Ξ) W)
             (fun s m M _ => dstuck_ne m -> ne_stuck (gstuck Θ Ξ) M)
             (fun s a A _ => dstuck a -> nf_stuck (gstuck Θ Ξ) A)
             (fun s xs ys _ => dstuck_la xs -> la_stuck (gstuck Θ Ξ) ys)
             (fun s ρ T vs Ms _ => env_stuck ρ -> (forall a, In a vs -> dstuck a) -> nfs_stuck (gstuck Θ Ξ) Ms)
             (fun s p ups ρ gs vs Ms _ => env_stuck ρ -> (forall a, In a ups -> dstuck a) ->
                                        (forall a, In a vs -> dstuck a) -> nfs_stuck (gstuck Θ Ξ) Ms)
             (fun s ρ A p D ups cs Bs Bs' _ => env_stuck ρ -> (forall a, In a ups -> dstuck a) ->
                                             nbrs_stuck (gstuck Θ Ξ) Bs'));
      intros; cbn;
      repeat match goal with
        | H : dstuck (_ _) |- _ => inversion_clear H
        | H : dstuck (_ _ _) |- _ => inversion_clear H
        | H : dstuck (_ _ _ _) |- _ => inversion_clear H
        | H : dstuck_nf (_ _ _) |- _ => inversion_clear H
        | H : dstuck_la (_ :: _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    (** Inductive types: each component is read back at a type, in an
        environment, of stuck values. *)
    all: try solve [
      stuck_fwd He Hes Hsh;
      try apply nfs_stuck_app;
      match goal with
      | IH : context [ nf_stuck _ ?W ] |- nf_stuck _ ?W => apply IH
      | IH : context [ ne_stuck _ ?W ] |- ne_stuck _ ?W => apply IH
      | IH : context [ nfs_stuck _ ?W ] |- nfs_stuck _ ?W => apply IH
      | IH : context [ nbrs_stuck _ ?W ] |- nbrs_stuck _ ?W => apply IH
      end;
      first [ stuck_env | solve [ all_in_with stuck_val ] | stuck_val | solve [ constructor; stuck_val ] ] ].
    (** A level reads back canonically, so its atoms are sorted and merged;
        [la_all_keep] and [la_all_sort] move the property of all the atoms
        across. *)
    all: try solve [ apply la_stuck_all, la_all_keep, la_all_sort, la_stuck_all; eauto 3 with mctt
                   | apply la_stuck_sort; eauto 3 with mctt ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try match goal with
         | IH : _ -> nf_stuck (gstuck Θ Ξ) (nf_lvl_of _) |- la_stuck (gstuck Θ Ξ) _ =>
             apply IH; repeat constructor; assumption
         end.
    (* each component is read back from a value built of stuck ones *)
    all: match goal with
         | IH : _ -> nf_stuck (gstuck Θ Ξ) ?W |- nf_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : _ -> ne_stuck (gstuck Θ Ξ) ?W |- ne_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : _ -> la_stuck (gstuck Θ Ξ) ?W |- la_stuck (gstuck Θ Ξ) ?W => apply IH
         end.
    all: repeat first [ eassumption | constructor | apply env_stuck_extend
                      | eapply He; [ eassumption |] | eapply Ha; [ eassumption | |] | eapply Hsh; [ eassumption | |] ].
  Qed.

  Lemma initial_env_stuck : forall Γ ρ, initial_env Θ Ξ Γ ρ -> env_stuck ρ.
  Proof.
    destruct eval_stuck as (He & _).
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
