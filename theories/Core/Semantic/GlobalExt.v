(** * NbE Reads the Global Context Only Through Its Lookups

    Evaluation and readback read the global context through [gc_resolve],
    [gc_module], [ind_lookup] and [ind_alias_lookup] alone, so two global contexts with the same
    lookups normalize alike. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Inductives.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

Section GlobalExt.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hres : forall p, gc_resolve Θ1 Ξ1 p = gc_resolve Θ2 Ξ2 p.
  Hypothesis Hmod : forall p, gc_module Θ1 Ξ1 p = gc_module Θ2 Ξ2 p.
  Hypothesis Hind : forall p, ind_lookup Θ1 Ξ1 p = ind_lookup Θ2 Ξ2 p.
  Hypothesis Hia : forall p, ind_alias_lookup Θ1 Ξ1 p = ind_alias_lookup Θ2 Ξ2 p.

  Lemma ind_lookup_ext : forall p, ind_lookup Θ1 Ξ1 p = ind_lookup Θ2 Ξ2 p.
  Proof. exact Hind. Qed.

  #[local] Ltac ext_case :=
    intros; econstructor;
    try match goal with
        | H : ind_lookup Θ1 Ξ1 _ = _ |- _ => rewrite ind_lookup_ext in H
        end;
    try match goal with
        | H : gc_resolve Θ1 Ξ1 _ = _ |- _ => rewrite Hres in H
        end;
    try match goal with
        | H : gc_module Θ1 Ξ1 _ = _ |- _ => rewrite Hmod in H
        end;
    try match goal with
        | H : ind_alias_lookup Θ1 Ξ1 _ = _ |- _ => rewrite Hia in H
        end;
    eassumption.

  Lemma eval_ext :
    (forall M ρ m, ⟦ M ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ m -> ⟦ M ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ m) /\
    (forall A MZ MS m ρ r, eval_natrec Θ1 Ξ1 A MZ MS m ρ r -> eval_natrec Θ2 Ξ2 A MZ MS m ρ r) /\
    (forall m n r, eval_app Θ1 Ξ1 m n r -> eval_app Θ2 Ξ2 m n r) /\
    (forall Ms ρ ms, eval_exps Θ1 Ξ1 Ms ρ ms -> eval_exps Θ2 Ξ2 Ms ρ ms) /\
    (forall m ns r, eval_apps Θ1 Ξ1 m ns r -> eval_apps Θ2 Ξ2 m ns r) /\
    (forall H ρ h, eval_modexp Θ1 Ξ1 H ρ h -> eval_modexp Θ2 Ξ2 H ρ h) /\
    (forall h n r, eval_appm Θ1 Ξ1 h n r -> eval_appm Θ2 Ξ2 h n r) /\
    (forall h x r, eval_sel Θ1 Ξ1 h x r -> eval_sel Θ2 Ξ2 h x r) /\
    (forall h y r, eval_selm Θ1 Ξ1 h y r -> eval_selm Θ2 Ξ2 h y r) /\
    (forall h ch r, eval_selc Θ1 Ξ1 h ch r -> eval_selc Θ2 Ξ2 h ch r) /\
    (forall h ch r, eval_selmc Θ1 Ξ1 h ch r -> eval_selmc Θ2 Ξ2 h ch r) /\
    (forall ρ Φ ρ', eval_benv Θ1 Ξ1 ρ Φ ρ' -> eval_benv Θ2 Ξ2 ρ Φ ρ') /\
    (forall ρ nm A Bs m r, eval_elim Θ1 Ξ1 ρ nm A Bs m r -> eval_elim Θ2 Ξ2 ρ nm A Bs m r) /\
    (forall ρ nm A Bs gs vs ihs, eval_ihs Θ1 Ξ1 ρ nm A Bs gs vs ihs -> eval_ihs Θ2 Ξ2 ρ nm A Bs gs vs ihs) /\
    (forall ρ nm A Bs t v r, eval_ih Θ1 Ξ1 ρ nm A Bs t v r -> eval_ih Θ2 Ξ2 ρ nm A Bs t v r) /\
    (forall p ups ρ t a, eval_shty Θ1 Ξ1 p ups ρ t a -> eval_shty Θ2 Ξ2 p ups ρ t a) /\
    (forall ρm A ρ t v a, eval_ihty Θ1 Ξ1 ρm A ρ t v a -> eval_ihty Θ2 Ξ2 ρm A ρ t v a).
  Proof.
    apply (eval_mut_ind Θ1 Ξ1
             (fun M ρ m _ => ⟦ M ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ m)
             (fun A MZ MS m ρ r _ => eval_natrec Θ2 Ξ2 A MZ MS m ρ r)
             (fun m n r _ => eval_app Θ2 Ξ2 m n r)
             (fun Ms ρ ms _ => eval_exps Θ2 Ξ2 Ms ρ ms)
             (fun m ns r _ => eval_apps Θ2 Ξ2 m ns r)
             (fun H ρ h _ => eval_modexp Θ2 Ξ2 H ρ h)
             (fun h n r _ => eval_appm Θ2 Ξ2 h n r)
             (fun h x r _ => eval_sel Θ2 Ξ2 h x r)
             (fun h y r _ => eval_selm Θ2 Ξ2 h y r)
             (fun h ch r _ => eval_selc Θ2 Ξ2 h ch r)
             (fun h ch r _ => eval_selmc Θ2 Ξ2 h ch r)
             (fun ρ Φ ρ' _ => eval_benv Θ2 Ξ2 ρ Φ ρ')
             (fun ρ nm A Bs m r _ => eval_elim Θ2 Ξ2 ρ nm A Bs m r)
             (fun ρ nm A Bs gs vs ihs _ => eval_ihs Θ2 Ξ2 ρ nm A Bs gs vs ihs)
             (fun ρ nm A Bs t v r _ => eval_ih Θ2 Ξ2 ρ nm A Bs t v r)
             (fun p ups ρ t a _ => eval_shty Θ2 Ξ2 p ups ρ t a)
             (fun ρm A ρ t v a _ => eval_ihty Θ2 Ξ2 ρm A ρ t v a)).
    all: try solve [ ext_case | intros; econstructor; eauto
                   | intros * H; econstructor; intros ? ?; rewrite <- Hmod; apply H ].
  Qed.

  Lemma fresh_tele_ext : forall ρ T s vs, fresh_tele Θ1 Ξ1 ρ T s vs -> fresh_tele Θ2 Ξ2 ρ T s vs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma fresh_cargs_ext : forall p ups ρ gs s vs,
      fresh_cargs Θ1 Ξ1 p ups ρ gs s vs -> fresh_cargs Θ2 Ξ2 p ups ρ gs s vs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma fresh_ihs_ext : forall ρ A ρa gs vs s ihs,
      fresh_ihs Θ1 Ξ1 ρ A ρa gs vs s ihs -> fresh_ihs Θ2 Ξ2 ρ A ρa gs vs s ihs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma read_ext :
    (forall s m M, read_nf Θ1 Ξ1 s m M -> read_nf Θ2 Ξ2 s m M) /\
    (forall s m M, read_ne Θ1 Ξ1 s m M -> read_ne Θ2 Ξ2 s m M) /\
    (forall s m M, read_typ Θ1 Ξ1 s m M -> read_typ Θ2 Ξ2 s m M) /\
    (forall s xs ys, read_la Θ1 Ξ1 s xs ys -> read_la Θ2 Ξ2 s xs ys) /\
    (forall s ρ T vs Ms, read_ps Θ1 Ξ1 s ρ T vs Ms -> read_ps Θ2 Ξ2 s ρ T vs Ms) /\
    (forall s p ups ρ gs vs Ms, read_cargs Θ1 Ξ1 s p ups ρ gs vs Ms -> read_cargs Θ2 Ξ2 s p ups ρ gs vs Ms) /\
    (forall s ρ A p D ups cs Bs Bs', read_brs Θ1 Ξ1 s ρ A p D ups cs Bs Bs' -> read_brs Θ2 Ξ2 s ρ A p D ups cs Bs Bs').
  Proof.
    pose proof eval_ext as He; destruct_all.
    apply (read_mut_ind Θ1 Ξ1
             (fun s m M _ => read_nf Θ2 Ξ2 s m M)
             (fun s m M _ => read_ne Θ2 Ξ2 s m M)
             (fun s m M _ => read_typ Θ2 Ξ2 s m M)
             (fun s xs ys _ => read_la Θ2 Ξ2 s xs ys)
             (fun s ρ T vs Ms _ => read_ps Θ2 Ξ2 s ρ T vs Ms)
             (fun s p ups ρ gs vs Ms _ => read_cargs Θ2 Ξ2 s p ups ρ gs vs Ms)
             (fun s ρ A p D ups cs Bs Bs' _ => read_brs Θ2 Ξ2 s ρ A p D ups cs Bs Bs')).
    all: intros; econstructor;
      try match goal with
          | H : ind_lookup Θ1 Ξ1 _ = _ |- _ => rewrite ind_lookup_ext in H
          end; eauto using fresh_tele_ext, fresh_cargs_ext, fresh_ihs_ext.
  Qed.

  Lemma initial_env_ext : forall Γ ρ, initial_env Θ1 Ξ1 Γ ρ -> initial_env Θ2 Ξ2 Γ ρ.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma nbe_ty_ext : forall Γ A W, nbe_ty Θ1 Ξ1 Γ A W -> nbe_ty Θ2 Ξ2 Γ A W.
  Proof.
    pose proof eval_ext; pose proof read_ext; destruct_all.
    intros * []; econstructor; eauto using initial_env_ext.
  Qed.
End GlobalExt.
