(** * NbE at a Transparent Global Context

    At a transparent global context ([gc_transparent]) no global evaluates to
    a neutral, so none ever reaches a normal form: the only neutrals are
    variables.  Module parameters are λ-variables and impose nothing. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Values Without Global Neutrals *)

Inductive dclean : domain -> Prop :=
| dclean_nat : dclean ℕᵈ
| dclean_pi : forall a (ρ : env) B, dclean a -> (forall x, dclean (env_var ρ x)) -> dclean (Πᵈ a ρ B)
| dclean_univ : forall i, dclean 𝕌@i
| dclean_zero : dclean zeroᵈ
| dclean_succ : forall m, dclean m -> dclean (succᵈ m)
| dclean_fn : forall (ρ : env) M, (forall x, dclean (env_var ρ x)) -> dclean (λᵈ ρ M)
| dclean_neut : forall a m, dclean a -> dclean_ne m -> dclean (⇑ a m)
with dclean_ne : domain_ne -> Prop :=
| dclean_var : forall x, dclean_ne (#ᵈ x)
| dclean_app : forall m n, dclean_ne m -> dclean_nf n -> dclean_ne (m $ᵈ n)
| dclean_natrec : forall (ρ : env) A mz MS m,
    (forall x, dclean (env_var ρ x)) -> dclean mz -> dclean_ne m ->
    dclean_ne (recᵈ m under ρ return A | zero -> mz | succ -> MS end)
with dclean_nf : domain_nf -> Prop :=
| dclean_dom : forall a m, dclean a -> dclean m -> dclean_nf (⇓ a m).

Definition env_clean (ρ : env) : Prop := forall x, dclean (ρ x).

#[local] Hint Constructors dclean dclean_ne dclean_nf : mctt.
#[local] Hint Unfold env_clean : mctt.

Lemma env_clean_nil : env_clean nil.
Proof. intros x; induction x; cbn; auto with mctt. Qed.

Lemma env_clean_extend : forall ρ d, env_clean ρ -> dclean d -> env_clean (ρ ↦ d).
Proof. intros * Hρ Hd [| x]; cbn; auto. Qed.

#[local] Hint Resolve env_clean_nil env_clean_extend : mctt.

Section Transparent.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Htr : gc_transparent Θ Ξ.

  Lemma eval_clean :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> env_clean ρ -> dclean m) /\
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       dclean m -> env_clean ρ -> dclean r) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dclean m -> dclean n -> dclean r).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => env_clean ρ -> dclean m)
             (fun A MZ MS m ρ r _ => dclean m -> env_clean ρ -> dclean r)
             (fun m n r _ => dclean m -> dclean n -> dclean r));
      intros; auto with mctt.
    all: repeat match goal with H : dclean (_ _) |- _ => inversion_clear H end.
    all: try solve [ eauto 7 with mctt ].
    - (* an opaque definition or an axiom *)
      match goal with H : gc_resolve _ _ _ = Some _ |- _ =>
        destruct (gc_transparent_resolve _ _ _ _ _ _ _ Htr H) end.
      intuition congruence.
  Qed.

  Lemma read_clean :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> dclean_nf m -> nf_clean W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> dclean_ne m -> ne_clean M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> dclean a -> nf_clean A).
  Proof.
    destruct eval_clean as (He & _ & Ha).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dclean_nf m -> nf_clean W)
             (fun s m M _ => dclean_ne m -> ne_clean M)
             (fun s a A _ => dclean a -> nf_clean A));
      intros; cbn;
      repeat match goal with
        | H : dclean (_ _) |- _ => inversion_clear H
        | H : dclean (_ _ _) |- _ => inversion_clear H
        | H : dclean (_ _ _ _) |- _ => inversion_clear H
        | H : dclean_nf (_ _ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    (* each component is read back from a value built of clean ones *)
    all: match goal with
         | IH : _ -> nf_clean ?W |- nf_clean ?W => apply IH
         | IH : _ -> ne_clean ?W |- ne_clean ?W => apply IH
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
