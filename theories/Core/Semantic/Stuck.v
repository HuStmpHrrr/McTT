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
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Normal Forms Whose Global Heads Satisfy [G] *)

Fixpoint nf_stuck (G : path -> Prop) (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_nat | nf_zero | nf_True | nf_true | nf_False => True
  | nf_succ W => nf_stuck G W
  | nf_pi A B | nf_fn A B => nf_stuck G A /\ nf_stuck G B
  | nf_neut M => ne_stuck G M
  end
with ne_stuck (G : path -> Prop) (M : ne) : Prop :=
  match M with
  | ne_natrec A MZ MS M => nf_stuck G A /\ nf_stuck G MZ /\ nf_stuck G MS /\ ne_stuck G M
  | ne_exfalso A M => nf_stuck G A /\ ne_stuck G M
  | ne_app M N => ne_stuck G M /\ nf_stuck G N
  | ne_var _ => True
  | ne_glob p => G p
  end.

(** A global that does not unfold: an opaque definition or an axiom. *)
Definition gstuck (Θ : gdeps) (Ξ : gstack) (p : path) : Prop :=
  exists b pv A B, gc_resolve Θ Ξ p = Some (ge_def b pv A B) /\ (b = false \/ B = None).

Section Stuck.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma gstuck_intro : forall p b pv A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv A B) -> b = false \/ B = None -> gstuck Θ Ξ p.
  Proof. unfold gstuck; eauto 7. Qed.
  #[local] Hint Resolve gstuck_intro : mctt.

(** ** Values Whose Global Neutrals Are Stuck *)

Inductive dstuck : domain -> Prop :=
| dstuck_nat : dstuck ℕᵈ
| dstuck_pi : forall a (ρ : env) B, dstuck a -> (forall x, destuck (env_entry ρ x)) -> dstuck (Πᵈ a ρ B)
| dstuck_univ : forall i, dstuck 𝕌@i
| dstuck_zero : dstuck zeroᵈ
| dstuck_succ : forall m, dstuck m -> dstuck (succᵈ m)
| dstuck_True : dstuck ⊤ᵈ
| dstuck_true : dstuck ⋆ᵈ
| dstuck_False : dstuck ⊥ᵈ
| dstuck_fn : forall (ρ : env) M, (forall x, destuck (env_entry ρ x)) -> dstuck (λᵈ ρ M)
| dstuck_neut : forall a m, dstuck a -> dstuck_ne m -> dstuck (⇑ a m)
| dstuck_member : forall h ch, dmstuck h -> dstuck (d_member h ch)
with dstuck_ne : domain_ne -> Prop :=
| dstuck_var : forall x, dstuck_ne (#ᵈ x)
| dstuck_glob : forall p, gstuck Θ Ξ p -> dstuck_ne (d_glob p)
| dstuck_app : forall m n, dstuck_ne m -> dstuck_nf n -> dstuck_ne (m $ᵈ n)
| dstuck_natrec : forall (ρ : env) A mz MS m,
    (forall x, destuck (env_entry ρ x)) -> dstuck mz -> dstuck_ne m ->
    dstuck_ne (recᵈ m under ρ return A | zero -> mz | succ -> MS end)
| dstuck_exfalso : forall (ρ : env) A m,
    (forall x, destuck (env_entry ρ x)) -> dstuck_ne m ->
    dstuck_ne (efqᵈ m under ρ return A)
with dstuck_nf : domain_nf -> Prop :=
| dstuck_dom : forall a m, dstuck a -> dstuck m -> dstuck_nf (⇓ a m)
with dmstuck : dmod -> Prop :=
| dmstuck_global : forall p args, (forall a, In a args -> dstuck a) -> dmstuck (dm_global p args)
| dmstuck_local : forall (ρ : env) U args,
    (forall x, destuck (env_entry ρ x)) -> (forall a, In a args -> dstuck a) -> dmstuck (dm_local ρ U args)
| dmstuck_member : forall h ch, dmstuck h -> dmstuck (dm_member h ch)
with destuck : dentry -> Prop :=
| destuck_term : forall d, dstuck d -> destuck (de_term d)
| destuck_mod : forall h, dmstuck h -> destuck (de_mod h).

Definition env_stuck (ρ : env) : Prop := forall x, destuck (env_entry ρ x).

#[local] Hint Constructors dstuck dstuck_ne dstuck_nf dmstuck destuck : mctt.
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

#[local] Hint Resolve env_stuck_nil env_stuck_extend env_stuck_extend_mod env_stuck_var env_stuck_mod
  env_stuck_args stuck_app_snoc dmstuck_local_nil dmstuck_global_nil env_stuck_entry : mctt.


  Lemma eval_stuck :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_stuck ρ -> dstuck m) /\
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       dstuck m -> env_stuck ρ -> dstuck r) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dstuck m -> dstuck n -> dstuck r) /\
    (forall Ms ρ ms, eval_exps Θ Ξ Ms ρ ms -> env_stuck ρ -> forall a, In a ms -> dstuck a) /\
    (forall m args r, eval_apps Θ Ξ m args r -> dstuck m -> (forall a, In a args -> dstuck a) -> dstuck r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> env_stuck ρ -> dmstuck h) /\
    (forall h n r, eval_appm Θ Ξ h n r -> dmstuck h -> dstuck n -> dmstuck r) /\
    (forall h x r, eval_sel Θ Ξ h x r -> dmstuck h -> dstuck r) /\
    (forall h y r, eval_selm Θ Ξ h y r -> dmstuck h -> dmstuck r) /\
    (forall h ch r, eval_selc Θ Ξ h ch r -> dmstuck h -> dstuck r) /\
    (forall h ch r, eval_selmc Θ Ξ h ch r -> dmstuck h -> dmstuck r) /\
    (forall ρ Φ ρ', eval_benv Θ Ξ ρ Φ ρ' -> env_stuck ρ -> env_stuck ρ').
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_stuck ρ -> dstuck m)
             (fun A MZ MS m ρ r _ => dstuck m -> env_stuck ρ -> dstuck r)
             (fun m n r _ => dstuck m -> dstuck n -> dstuck r)
             (fun Ms ρ ms _ => env_stuck ρ -> forall a, In a ms -> dstuck a)
             (fun m args r _ => dstuck m -> (forall a, In a args -> dstuck a) -> dstuck r)
             (fun H ρ h _ => env_stuck ρ -> dmstuck h)
             (fun h n r _ => dmstuck h -> dstuck n -> dmstuck r)
             (fun h x r _ => dmstuck h -> dstuck r)
             (fun h y r _ => dmstuck h -> dmstuck r)
             (fun h ch r _ => dmstuck h -> dstuck r)
             (fun h ch r _ => dmstuck h -> dmstuck r)
             (fun ρ Φ ρ' _ => env_stuck ρ -> env_stuck ρ'));
      intros.
    all: repeat match goal with
           | H : dstuck (_ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _) |- _ => inversion_clear H
           | H : dmstuck (_ _ _ _) |- _ => inversion_clear H
           end.
    all: try solve [ eauto 4 with mctt ].
    all: try solve [ eauto 6 with mctt ].
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
    all: match goal with Hin : In _ nil |- _ => destruct Hin end.
  Qed.

  Lemma read_stuck :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> dstuck_nf m -> nf_stuck (gstuck Θ Ξ) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> dstuck_ne m -> ne_stuck (gstuck Θ Ξ) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> dstuck a -> nf_stuck (gstuck Θ Ξ) A).
  Proof.
    destruct eval_stuck as (He & _ & Ha & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dstuck_nf m -> nf_stuck (gstuck Θ Ξ) W)
             (fun s m M _ => dstuck_ne m -> ne_stuck (gstuck Θ Ξ) M)
             (fun s a A _ => dstuck a -> nf_stuck (gstuck Θ Ξ) A));
      intros; cbn;
      repeat match goal with
        | H : dstuck (_ _) |- _ => inversion_clear H
        | H : dstuck (_ _ _) |- _ => inversion_clear H
        | H : dstuck (_ _ _ _) |- _ => inversion_clear H
        | H : dstuck_nf (_ _ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _ _) |- _ => inversion_clear H
        | H : dstuck_ne (_ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    (* each component is read back from a value built of stuck ones *)
    all: match goal with
         | IH : _ -> nf_stuck (gstuck Θ Ξ) ?W |- nf_stuck (gstuck Θ Ξ) ?W => apply IH
         | IH : _ -> ne_stuck (gstuck Θ Ξ) ?W |- ne_stuck (gstuck Θ Ξ) ?W => apply IH
         end.
    all: repeat first [ eassumption | constructor | apply env_stuck_extend
                      | eapply He; [ eassumption |] | eapply Ha; [ eassumption | |] ].
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
