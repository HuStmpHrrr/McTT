(** * NbE at a Transparent Global Context

    At a transparent global context ([gc_transparent]) no global and no
    parameter evaluates to a neutral, so neither ever reaches a normal form:
    the only neutrals are variables. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

(** ** Values Without Global or Parameter Neutrals *)

Inductive dclean : domain -> Prop :=
| dclean_nat : dclean ℕᵈ
| dclean_pi : forall a κ (ρ : env) B, dclean a -> mclean κ -> (forall x, dclean (env_var ρ x)) -> dclean (Πᵈ a κ ρ B)
| dclean_univ : forall i, dclean 𝕌@i
| dclean_zero : dclean zeroᵈ
| dclean_succ : forall m, dclean m -> dclean (succᵈ m)
| dclean_fn : forall κ (ρ : env) M, mclean κ -> (forall x, dclean (env_var ρ x)) -> dclean (λᵈ κ ρ M)
| dclean_neut : forall a m, dclean a -> dclean_ne m -> dclean (⇑ a m)
| dclean_gfn : forall κ a c (args : env) ip, mclean κ -> (forall x, dclean (env_var args x)) ->
    dclean (d_gfn κ a c args ip)
with dclean_ne : domain_ne -> Prop :=
| dclean_var : forall x, dclean_ne (#ᵈ x)
| dclean_app : forall m n, dclean_ne m -> dclean_nf n -> dclean_ne (m $ᵈ n)
| dclean_natrec : forall κ (ρ : env) A mz MS m,
    mclean κ -> (forall x, dclean (env_var ρ x)) -> dclean mz -> dclean_ne m ->
    dclean_ne (recᵈ m under κ ρ return A | zero -> mz | succ -> MS end)
with dclean_nf : domain_nf -> Prop :=
| dclean_dom : forall a m, dclean a -> dclean m -> dclean_nf (⇓ a m)
with mclean : menv -> Prop :=
| mclean_base : forall j, mclean (me_base j)
| mclean_frame : forall a (args : env) κ, (forall x, dclean (env_var args x)) -> mclean κ -> mclean (me_frame a args κ).

Definition env_clean (ρ : env) : Prop := forall x, dclean (ρ x).

#[local] Hint Constructors dclean dclean_ne dclean_nf mclean : mctt.
#[local] Hint Unfold env_clean : mctt.

Lemma env_clean_nil : env_clean nil.
Proof. intros x; induction x; cbn; auto with mctt. Qed.

Lemma env_clean_extend : forall ρ d, env_clean ρ -> dclean d -> env_clean (ρ ↦ d).
Proof. intros * Hρ Hd [| x]; cbn; auto. Qed.

Lemma mclean_drop : forall κ, mclean κ -> forall m, mclean (me_drop m κ).
Proof. induction 1; intros [| m]; cbn; auto with mctt. Qed.

#[local] Hint Resolve env_clean_nil env_clean_extend mclean_drop : mctt.

(** A transparent module has no opaque entry, at any depth. *)
Lemma gm_transparent_find : forall Φ x E, gm_transparent Φ -> gm_find Φ x = Some E -> ge_transparent E.
Proof.
  induction Φ as [| Φ IH y E']; intros * HΦ Hf; cbn in *; [ discriminate |].
  destruct HΦ as [HΦ HE]; destruct (String.eqb x y); [ injection Hf as <-; exact HE | eauto ].
Qed.

Lemma gm_walk_transparent : forall cs Δ Φ Δ' Φ', gm_transparent Φ -> gm_walk Δ Φ cs = Some (Δ', Φ') -> gm_transparent Φ'.
Proof.
  induction cs as [| x cs IH]; intros * HΦ Hw; cbn in Hw; [ injection Hw as <- <-; exact HΦ |].
  destruct (gm_find Φ x) as [[? ? ? ? | Δ0 Φ0] |] eqn:Hf; try discriminate.
  eapply IH; [| exact Hw ]; exact (gm_transparent_find _ _ _ HΦ Hf).
Qed.

Section Transparent.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Htr : gc_transparent Θ Ξ.

  Lemma frame_at_transparent : forall a Δ Φ, frame_at Θ Ξ a = Some (Δ, Φ) -> gm_transparent Φ.
  Proof.
    destruct Htr as [HΘ HΞ].
    intros [[fp | j] cs] * Hf; unfold frame_at in Hf; cbn in Hf.
    - destruct (gds_lookup Θ fp) as [U |] eqn:HU; [| discriminate ].
      eapply gm_walk_transparent; [| exact Hf ]; eapply HΘ, gd_lookup_in; exact HU.
    - destruct (List.nth_error Ξ j) as [U |] eqn:HU; [| discriminate ].
      eapply gm_walk_transparent; [| exact Hf ]; apply (HΞ U (List.nth_error_In _ _ HU)).
  Qed.

  Lemma eval_clean :
    (forall κ M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m -> env_clean ρ -> mclean κ -> dclean m) /\
    (forall κ A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r ->
       dclean m -> env_clean ρ -> mclean κ -> dclean r) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dclean m -> dclean n -> dclean r) /\
    (forall κ a c args ip r, eval_pend Θ Ξ κ a c args ip r -> mclean κ -> env_clean args -> dclean r) /\
    (forall κ ip r, eval_ent Θ Ξ κ ip r -> mclean κ -> dclean r) /\
    (forall κ j c Γ ρ, eval_ptele Θ Ξ κ j c Γ ρ -> True) /\
    (forall κ n h h1, eval_gne Θ Ξ κ n h h1 -> True) /\
    (forall κ Δ args h h1, eval_fargs Θ Ξ κ Δ args h h1 -> True).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun κ M ρ m _ => env_clean ρ -> mclean κ -> dclean m)
             (fun κ A MZ MS m ρ r _ => dclean m -> env_clean ρ -> mclean κ -> dclean r)
             (fun m n r _ => dclean m -> dclean n -> dclean r)
             (fun κ a c args ip r _ => mclean κ -> env_clean args -> dclean r)
             (fun κ ip r _ => mclean κ -> dclean r)
             (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True));
      intros; auto with mctt.
    all: repeat match goal with
      | H : dclean (_ _) |- _ => inversion_clear H
      | H : dclean (_ _ _) |- _ => inversion_clear H
      | H : dclean (_ _ _ _) |- _ => inversion_clear H
      | H : dclean (_ _ _ _ _) |- _ => inversion_clear H
      end.
    all: try solve [ eauto 7 with mctt ].
    - (* a parameter of a closed frame *)
      match goal with H : me_drop _ _ = me_frame _ _ _ |- _ =>
        pose proof (mclean_drop _ ltac:(eassumption) (lp_mod lp)) as Hc; rewrite H in Hc; inversion Hc; subst end.
      auto.
    - (* a parameter of an open frame: there is none *)
      exfalso.
      destruct Htr as [_ HΞ].
      match goal with H : List.nth_error Ξ _ = Some ?U |- _ =>
        destruct (HΞ _ (List.nth_error_In _ _ H)) as [HP _] end.
      match goal with H : eval_ptele _ _ _ _ _ _ _ |- _ => rewrite HP in H; destruct (lp_param lp); inversion H end.
    - (* an opaque definition: there is none *)
      exfalso.
      match goal with Hf : frame_at _ _ _ = Some _, Hy : gm_find _ _ = Some _ |- _ =>
        pose proof (gm_transparent_find _ _ _ (frame_at_transparent _ _ _ Hf) Hy) as [Hb HB] end.
      destruct o as [-> | ->]; [ discriminate | contradiction ].
  Qed.

  Lemma read_clean :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W -> dclean_nf m -> nf_clean W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M -> dclean_ne m -> ne_clean M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> dclean a -> nf_clean A).
  Proof.
    destruct eval_clean as (He & _ & Ha & _).
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => dclean_nf m -> nf_clean W)
             (fun s m M _ => dclean_ne m -> ne_clean M)
             (fun s a A _ => dclean a -> nf_clean A));
      intros; cbn;
      repeat match goal with
        | H : dclean (_ _) |- _ => inversion_clear H
        | H : dclean (_ _ _) |- _ => inversion_clear H
        | H : dclean (_ _ _ _) |- _ => inversion_clear H
        | H : dclean (_ _ _ _ _) |- _ => inversion_clear H
        | H : dclean_nf (_ _ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _) |- _ => inversion_clear H
        | H : dclean_ne (_ _ _ _ _ _ _) |- _ => inversion_clear H
        end;
      repeat split; auto.
    all: match goal with
         | IH : _ -> nf_clean ?W |- nf_clean ?W => apply IH
         | IH : _ -> ne_clean ?W |- ne_clean ?W => apply IH
         end.
    all: repeat first [ eassumption | constructor | apply env_clean_extend
                      | eapply He; [ eassumption | | ] | eapply Ha; [ eassumption | |] ].
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
