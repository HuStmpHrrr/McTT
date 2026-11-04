(** * NbE at a Transparent Global Context

    At a transparent global context ([gc_transparent]) no global reaches a
    normal form outside its proofs, and the only neutrals are variables.
    This is the stuck case ([Core.Semantic.Stuck]) with no stuck global:
    a stuck global resolves to an opaque definition or an axiom, and a
    transparent context has neither ([global_stuck_not_transparent]).
    Module parameters are λ-variables, so they need no special
    treatment. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Core.Semantic Require Export Stuck.
Import Domain_Notations.

(** A normal form whose global heads satisfy a predicate that holds of no
    global has none outside its proofs: [nf_stuck] at it is [nf_clean]. *)
Lemma nf_ne_stuck_clean : forall (G : qname -> Prop), (forall p, ~ G p) ->
    (forall W, nf_stuck G W -> nf_clean W) /\ (forall M, ne_stuck G M -> ne_clean M).
Proof.
  intros G HG; apply nf_ne_ind; intros; cbn [nf_stuck ne_stuck nf_clean ne_clean] in *; intuition auto;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try split; auto.
  all: try solve [ exact (HG _ H) ].
  all: eapply list_all_all_list_impl; [ eassumption | eassumption |]; cbn; intros x Hx Hy.
  all: try solve [ auto ].
  (** An atom of a level: its neutral *)
  all: try solve [ destruct Hx; cbn in *; auto ].
  (** A block: its scrutinee's type, its motive and its branches *)
  destruct Hx as [n' Z HZ A HA brs Hbrs]; cbn in *; destruct Hy as [HyZ [HyA Hybrs]]; split; [ auto | split; [ auto |] ];
    eapply list_all_all_list_impl; [ exact Hbrs | exact Hybrs |];
    intros br Hbr Hy'; destruct Hbr; cbn in *; auto.
Qed.

Lemma nf_stuck_clean : forall (G : qname -> Prop), (forall p, ~ G p) -> forall W, nf_stuck G W -> nf_clean W.
Proof. intros G HG; apply (nf_ne_stuck_clean G HG). Qed.

Lemma ne_stuck_clean : forall (G : qname -> Prop), (forall p, ~ G p) -> forall M, ne_stuck G M -> ne_clean M.
Proof. intros G HG; apply (nf_ne_stuck_clean G HG). Qed.

(** A transparent context has no stuck global: every definition it
    resolves to is transparent with a body ([gc_transparent_resolve]). *)
Lemma global_stuck_not_transparent : forall Θ Ξ, gc_transparent Θ Ξ -> forall p, ~ global_stuck Θ Ξ p.
Proof.
  intros * Htr p [b pv r A B Hres Ho].
  destruct (gc_transparent_resolve _ _ _ _ _ _ _ _ Htr Hres) as [Hb HB].
  destruct Ho as [Ho | Ho]; congruence.
Qed.

(** At a transparent context a normal form has no global head outside its
    proofs. *)
Theorem nbe_clean : forall Θ Ξ, gc_transparent Θ Ξ -> forall Γ M A W, nbe Θ Ξ Γ M A W -> nf_clean W.
Proof.
  intros * Htr * Hn.
  exact (nf_stuck_clean _ (global_stuck_not_transparent _ _ Htr) _ (nbe_stuck _ _ _ _ _ _ Hn)).
Qed.
