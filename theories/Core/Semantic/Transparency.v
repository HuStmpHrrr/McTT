(** * NbE at a Transparent Global Context

    At a transparent global context ([gc_transparent]) no global evaluates to
    a neutral, so no global reaches a normal form and the only neutrals are
    variables.  Module parameters are λ-variables, so they need no special
    treatment. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Values Without Global Neutrals *)

Inductive dclean : domain -> Prop :=
| dclean_nat : dclean ℕᵈ
| dclean_pi : forall a (ρ : env) B, dclean a -> (forall x, declean (env_entry ρ x)) -> dclean (Πᵈ a ρ B)
| dclean_univ : forall i, dclean 𝕌@i
| dclean_suniv : forall l, dclean l -> dclean 𝕌ˢ@l
| dclean_level : dclean Levelᵈ
| dclean_lvl : forall c xs, dclean_la xs -> dclean (lvᵈ c xs)
| dclean_zero : dclean zeroᵈ
| dclean_succ : forall m, dclean m -> dclean (succᵈ m)
| dclean_True : dclean ⊤ᵈ
| dclean_true : dclean ⋆ᵈ
| dclean_False : dclean ⊥ᵈ
| dclean_fn : forall (ρ : env) M, (forall x, declean (env_entry ρ x)) -> dclean (λᵈ ρ M)
| dclean_neut : forall a m, dclean a -> dclean_ne m -> dclean (⇑ a m)
| dclean_member : forall h ch, dmclean h -> dclean (d_member h ch)
with dclean_ne : domain_ne -> Prop :=
| dclean_var : forall x, dclean_ne (#ᵈ x)
| dclean_app : forall m n, dclean_ne m -> dclean_nf n -> dclean_ne (m $ᵈ n)
| dclean_natrec : forall (ρ : env) A mz MS m,
    (forall x, declean (env_entry ρ x)) -> dclean mz -> dclean_ne m ->
    dclean_ne (recᵈ m under ρ return A | zero -> mz | succ -> MS end)
| dclean_exfalso : forall (ρ : env) A m,
    (forall x, declean (env_entry ρ x)) -> dclean_ne m ->
    dclean_ne (efqᵈ m under ρ return A)
with dclean_nf : domain_nf -> Prop :=
| dclean_dom : forall a m, dclean a -> dclean m -> dclean_nf (⇓ a m)
with dmclean : dmod -> Prop :=
| dmclean_global : forall p args, (forall a, In a args -> dclean a) -> dmclean (dm_global p args)
| dmclean_local : forall (ρ : env) U args,
    (forall x, declean (env_entry ρ x)) -> (forall a, In a args -> dclean a) -> dmclean (dm_local ρ U args)
| dmclean_member : forall h ch, dmclean h -> dmclean (dm_member h ch)
with dclean_la : list (nat * domain_ne) -> Prop :=
| dclean_la_nil : dclean_la nil
| dclean_la_cons : forall k m xs, dclean_ne m -> dclean_la xs -> dclean_la ((k, m) :: xs)
with declean : dentry -> Prop :=
| declean_term : forall d, dclean d -> declean (de_term d)
| declean_mod : forall h, dmclean h -> declean (de_mod h).

Definition env_clean (ρ : env) : Prop := forall x, declean (env_entry ρ x).

#[local] Hint Constructors dclean dclean_ne dclean_nf dclean_la dmclean declean : mctt.

(** [dclean_lvl] is not a hint: its premise is a quantified statement about the
    atoms, which the search would try to prove of an unknown level.  The
    level operations are reached through the three lemmas below instead. *)
#[local] Remove Hints dclean_lvl : mctt.
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

Lemma env_clean_entry : forall ρ x, env_clean ρ -> declean (env_entry ρ x).
Proof. intros * H; exact (H x). Qed.

Lemma dmclean_local_nil : forall ρ U, env_clean ρ -> dmclean (dm_local ρ U nil).
Proof. intros; constructor; [ assumption | intros ? [] ]. Qed.

Lemma dmclean_global_nil : forall p, dmclean (dm_global p nil).
Proof. intros; constructor; intros ? []. Qed.

(** The atoms a level value is built of.  The flat view of a neutral is the
    single atom [(0, m)], so the level operations preserve the property. *)
Lemma dclean_la_view : forall d, dclean d -> dclean_la (dlvl_atoms d).
Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

Lemma dclean_la_suc : forall xs, dclean_la xs -> dclean_la (List.map (fun ka => (S (fst ka), snd ka)) xs).
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
  env_clean_args clean_app_snoc dmclean_local_nil dmclean_global_nil env_clean_entry : mctt.

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
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       dclean m -> env_clean ρ -> dclean r) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dclean m -> dclean n -> dclean r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> env_clean ρ -> forall a, In a ms -> dclean a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> dclean m -> (forall a, In a args -> dclean a) -> dclean r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_clean ρ -> dmclean h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmclean h -> dclean n -> dmclean r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmclean h -> dclean r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmclean h -> dmclean r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmclean h -> dclean r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmclean h -> dmclean r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' -> env_clean ρ -> env_clean ρ').
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_clean ρ -> dclean m)
             (fun A MZ MS m ρ r _ => dclean m -> env_clean ρ -> dclean r)
             (fun m n r _ => dclean m -> dclean n -> dclean r)
             (fun Ms ρ ms _ => env_clean ρ -> forall a, In a ms -> dclean a)
             (fun m args r _ => dclean m -> (forall a, In a args -> dclean a) -> dclean r)
             (fun H ρ h _ => env_clean ρ -> dmclean h)
             (fun h n r _ => dmclean h -> dclean n -> dmclean r)
             (fun h x r _ => dmclean h -> dclean r)
             (fun h y r _ => dmclean h -> dmclean r)
             (fun h ch r _ => dmclean h -> dclean r)
             (fun h ch r _ => dmclean h -> dmclean r)
             (fun ρ Φ ρ' _ => env_clean ρ -> env_clean ρ'));
      intros.
    all: repeat match goal with
           | H : dclean (_ _) |- _ => inversion_clear H
           | H : dmclean (_ _ _) |- _ => inversion_clear H
           | H : dmclean (_ _ _ _) |- _ => inversion_clear H
           end.
    all: try solve [ eauto 4 with mctt ].
    (* an opaque definition or an axiom *)
    all: try solve [ match goal with H : gc_resolve _ _ _ = Some (ge_def _ _ _ _), Ho : _ \/ _ |- _ =>
         destruct (gc_transparent_resolve _ _ _ _ _ _ _ Htr H) end; intuition congruence ].
    all: try solve [ eauto 6 with mctt ].
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
    all: match goal with Hin : In _ nil |- _ => destruct Hin end.
  Qed.

  Lemma read_clean :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> dclean_nf m -> nf_clean W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> dclean_ne m -> ne_clean M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> dclean a -> nf_clean A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       dclean_la xs -> la_clean ys).
  Proof.
    destruct eval_clean as (He & _ & Ha & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dclean_nf m -> nf_clean W)
             (fun s m M _ => dclean_ne m -> ne_clean M)
             (fun s a A _ => dclean a -> nf_clean A)
             (fun s xs ys _ => dclean_la xs -> la_clean ys));
      intros; cbn;
      repeat match goal with
        | H : dclean (_ _) |- _ => inversion_clear H
        | H : dclean (_ _ _) |- _ => inversion_clear H
        | H : dclean (_ _ _ _) |- _ => inversion_clear H
        | H : dclean_nf (_ _ _) |- _ => inversion_clear H
        | H : dclean_la (_ :: _) |- _ => inversion_clear H
        | H : dclean_ne (_ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    (** A level reads back canonically, so its atoms are sorted and merged;
        [la_clean_sort] moves the property of all the atoms across. *)
    all: try solve [ apply la_clean_sort; eauto 3 with mctt ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try match goal with
         | IH : _ -> nf_clean (nf_lvl_of _) |- la_clean _ =>
             apply IH; repeat constructor; assumption
         end.
    (* each component is read back from a value built of clean ones *)
    all: match goal with
         | IH : _ -> nf_clean ?W |- nf_clean ?W => apply IH
         | IH : _ -> ne_clean ?W |- ne_clean ?W => apply IH
         | IH : _ -> la_clean ?W |- la_clean ?W => apply IH
         end.
    all: repeat first [ eassumption | constructor | apply env_clean_extend
                      | eapply He; [ eassumption |] | eapply Ha; [ eassumption | |] ].
  Qed.

  Lemma initial_env_clean : forall Γ ρ, initial_env Θ Ξ Γ ρ -> env_clean ρ.
  Proof.
    destruct eval_clean as (He & _).
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
