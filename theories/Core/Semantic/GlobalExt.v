(** * NbE Reads the Global Context Only Through Its Lookups

    Evaluation and readback read the global context through [gc_resolve],
    [gc_module], [ind_lookup], [ind_alias_lookup], [gc_frame] and [gs_find_ind] alone, so two global contexts with the same
    lookups normalize alike. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import NbE.
Import Domain_Notations.

Section GlobalExt.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hres : forall p, gc_resolve Θ1 Ξ1 p = gc_resolve Θ2 Ξ2 p.
  Hypothesis Hmod : forall p, gc_module Θ1 Ξ1 p = gc_module Θ2 Ξ2 p.
  Hypothesis Hind : forall p, ind_lookup Θ1 Ξ1 p = ind_lookup Θ2 Ξ2 p.
  Hypothesis Hia : forall p, ind_alias_lookup Θ1 Ξ1 p = ind_alias_lookup Θ2 Ξ2 p.
  Hypothesis Hfr : forall p, gc_frame Ξ1 p = gc_frame Ξ2 p.
  Hypothesis Hfi : forall p, gs_find_ind Ξ1 p = gs_find_ind Ξ2 p.
  Hypothesis Hbody : forall p, gc_body Θ1 Ξ1 p = gc_body Θ2 Ξ2 p.

  Lemma ind_lookup_ext : forall p, ind_lookup Θ1 Ξ1 p = ind_lookup Θ2 Ξ2 p.
  Proof. exact Hind. Qed.

  Lemma ind_mlookup_ext : forall p, ind_mlookup Θ1 Ξ1 p = ind_mlookup Θ2 Ξ2 p.
  Proof. intros; rewrite !ind_mlookup_unfold, Hfi, Hmod; reflexivity. Qed.

  Lemma gc_loc_ext : forall p, gc_loc Θ1 Ξ1 p = gc_loc Θ2 Ξ2 p.
  Proof. intros; unfold gc_loc; rewrite Hfr, Hbody; reflexivity. Qed.

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

  Lemma kind_ext :
    (forall h ch k, dkind Θ1 Ξ1 h ch k -> dkind Θ2 Ξ2 h ch k) /\
    (forall ρ U ch k, ukind Θ1 Ξ1 ρ U ch k -> ukind Θ2 Ξ2 ρ U ch k) /\
    (forall ρ H ch k, skind Θ1 Ξ1 ρ H ch k -> skind Θ2 Ξ2 ρ H ch k) /\
    (forall ρ Φ ρ', kenv Θ1 Ξ1 ρ Φ ρ' -> kenv Θ2 Ξ2 ρ Φ ρ') /\
    (forall ρ Φ Φx, kbody Θ1 Ξ1 ρ Φ Φx -> kbody Θ2 Ξ2 ρ Φ Φx) /\
    (forall ρ H its gs, kgens Θ1 Ξ1 ρ H its gs -> kgens Θ2 Ξ2 ρ H its gs).
  Proof.
    apply kind_mut_ind; intros;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             end;
      rewrite ?Hres, ?Hmod, ?Hfr, ?gc_loc_ext in *;
      solve [ econstructor; eauto 6 ].
  Qed.

  Lemma eval_ext :
    (forall M ρ m, ⟦ M ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ m -> ⟦ M ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ m) /\
    (forall m n r, $| m & n | Θ1 ⍮ Ξ1 ↘ r -> $| m & n | Θ2 ⍮ Ξ2 ↘ r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ1 ⍮ Ξ1 ⍮ ρ ↘ ms -> ⟦ Ms ⟧* Θ2 ⍮ Ξ2 ⍮ ρ ↘ ms) /\
    (forall m ns r, $*| m & ns | Θ1 ⍮ Ξ1 ↘ r -> $*| m & ns | Θ2 ⍮ Ξ2 ↘ r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ1 ⍮ Ξ1 ⍮ ρ ↘ h -> ⟦ H ⟧ᵐ Θ2 ⍮ Ξ2 ⍮ ρ ↘ h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ1 ⍮ Ξ1 ⍮ ρ ↘ h -> ⟦ Δ ⊢ D ⟧ᶜ Θ2 ⍮ Ξ2 ⍮ ρ ↘ h) /\
    (forall h n r, $ᵐ| h & n | Θ1 ⍮ Ξ1 ↘ r -> $ᵐ| h & n | Θ2 ⍮ Ξ2 ↘ r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ1 ⍮ Ξ1 ↘ r -> $ᵐ*| h & ns | Θ2 ⍮ Ξ2 ↘ r) /\
    (forall h x r, h ·ₜ x Θ1 ⍮ Ξ1 ↘ r -> h ·ₜ x Θ2 ⍮ Ξ2 ↘ r) /\
    (forall h y r, h ·ₘ y Θ1 ⍮ Ξ1 ↘ r -> h ·ₘ y Θ2 ⍮ Ξ2 ↘ r) /\
    (forall h ch r, h ·ₜ* ch Θ1 ⍮ Ξ1 ↘ r -> h ·ₜ* ch Θ2 ⍮ Ξ2 ↘ r) /\
    (forall h ch r, h ·ₘ* ch Θ1 ⍮ Ξ1 ↘ r -> h ·ₘ* ch Θ2 ⍮ Ξ2 ↘ r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ1 ⍮ Ξ1 ⍮ ρ ↘ ρ' -> ⟦ Φ ⟧ᵇ Θ2 ⍮ Ξ2 ⍮ ρ ↘ ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ r -> ⟦elim m at j of p ups Bks ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ ihs ->
       ⟦ihs vs of gs under p ups Bks ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ ihs) /\
    (forall ρ p ups Bks t v r, ⟦ih v of t under p ups Bks ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ r -> ⟦ih v of t under p ups Bks ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ r) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ1 ⍮ Ξ1 ↘ r -> ⟦mref j of p ups ⟧ Θ2 ⍮ Ξ2 ↘ r) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ a -> ⟦shty t of p ups ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ a) /\
    (forall ρm As ρ t v a, ⟦ihty v of t under ρm As ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ a -> ⟦ihty v of t under ρm As ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ a).
  Proof.
    apply (eval_mut_ind Θ1 Ξ1
             (fun M ρ m _ => ⟦ M ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ m)
             (fun m n r _ => eval_app Θ2 Ξ2 m n r)
             (fun Ms ρ ms _ => eval_exps Θ2 Ξ2 Ms ρ ms)
             (fun m ns r _ => eval_apps Θ2 Ξ2 m ns r)
             (fun H ρ h _ => eval_modexp Θ2 Ξ2 H ρ h)
             (fun Δ D ρ h _ => eval_close Θ2 Ξ2 Δ D ρ h)
             (fun h n r _ => eval_appm Θ2 Ξ2 h n r)
             (fun h ns r _ => eval_appms Θ2 Ξ2 h ns r)
             (fun h x r _ => eval_sel Θ2 Ξ2 h x r)
             (fun h y r _ => eval_selm Θ2 Ξ2 h y r)
             (fun h ch r _ => eval_selc Θ2 Ξ2 h ch r)
             (fun h ch r _ => eval_selmc Θ2 Ξ2 h ch r)
             (fun ρ Φ ρ' _ => eval_benv Θ2 Ξ2 ρ Φ ρ')
             (fun ρ p ups Bks j m r _ => eval_elim Θ2 Ξ2 ρ p ups Bks j m r)
             (fun ρ p ups Bks gs vs ihs _ => eval_ihs Θ2 Ξ2 ρ p ups Bks gs vs ihs)
             (fun ρ p ups Bks t v r _ => eval_ih Θ2 Ξ2 ρ p ups Bks t v r)
             (fun p ups j r _ => eval_mref Θ2 Ξ2 p ups j r)
             (fun p ups ρ t a _ => eval_shty Θ2 Ξ2 p ups ρ t a)
             (fun ρm As ρ t v a _ => eval_ihty Θ2 Ξ2 ρm As ρ t v a)).
    all: intros;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             end;
      rewrite ?Hres, ?Hmod, ?Hfr, ?gc_loc_ext, ?ind_lookup_ext, ?ind_mlookup_ext, ?Hia in *.
    all: try solve [ econstructor; eauto; apply kind_ext; assumption ].
  Qed.

  Lemma fresh_tele_ext : forall ρ T s vs, Ftele T in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ vs -> Ftele T in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ vs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma fresh_cargs_ext : forall p ups ρ gs s vs,
      Fcargs gs of p ups in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ vs -> Fcargs gs of p ups in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ vs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma fresh_ihs_ext : forall ρ As ρa gs' gs vs s ihs,
      Fihs vs at gs' gs under ρ As in Θ1 ⍮ Ξ1 ⍮ ρa ⍮ s ↘ ihs -> Fihs vs at gs' gs under ρ As in Θ2 ⍮ Ξ2 ⍮ ρa ⍮ s ↘ ihs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma wrap_ihs_eval_ext : forall ρ p ups Bks gs' gs vs ihs r,
      ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ r ->
      ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ r.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma read_ext :
    (forall s m M, Rnf m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rnf m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s m M, Rne m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rne m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s m M, Rtyp m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rtyp m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s xs ys, Rla xs in Θ1 ⍮ Ξ1 ⍮ s ↘ ys -> Rla xs in Θ2 ⍮ Ξ2 ⍮ s ↘ ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Ms -> Rps vs at T in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Ms -> Rcargs vs at gs of p ups in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Ms) /\
    (forall s p ups ρ t v V, Rsh v at t of p ups in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ V -> Rsh v at t of p ups in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ V) /\
    (forall s ρ p ups Bks sel i Ms NBks, Rblks i Ms from p ups Bks sel in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ NBks ->
       Rblks i Ms from p ups Bks sel in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ NBks) /\
    (forall s ρ p ups Bks Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Bs' ->
       Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Bs').
  Proof.
    pose proof eval_ext as He; destruct_all.
    apply (read_mut_ind Θ1 Ξ1
             (fun s m M _ => read_nf Θ2 Ξ2 s m M)
             (fun s m M _ => read_ne Θ2 Ξ2 s m M)
             (fun s m M _ => read_typ Θ2 Ξ2 s m M)
             (fun s xs ys _ => read_la Θ2 Ξ2 s xs ys)
             (fun s ρ T vs Ms _ => read_ps Θ2 Ξ2 s ρ T vs Ms)
             (fun s p ups ρ gs vs Ms _ => read_cargs Θ2 Ξ2 s p ups ρ gs vs Ms)
             (fun s p ups ρ t v V _ => read_shape Θ2 Ξ2 s p ups ρ t v V)
             (fun s ρ p ups Bks sel i Ms NBks _ => read_blocks Θ2 Ξ2 s ρ p ups Bks sel i Ms NBks)
             (fun s ρ p ups Bks Mv A Mi r cs Bs Bs' _ => read_brs Θ2 Ξ2 s ρ p ups Bks Mv A Mi r cs Bs Bs')).
    all: intros; econstructor;
      repeat match goal with
          | H : ind_lookup Θ1 Ξ1 _ = _ |- _ => rewrite ind_lookup_ext in H
          end; eauto using fresh_tele_ext, fresh_cargs_ext, fresh_ihs_ext, wrap_ihs_eval_ext.
  Qed.

  Lemma initial_env_ext : forall Γ ρ, initial_env Θ1 Ξ1 Γ ρ -> initial_env Θ2 Ξ2 Γ ρ.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma nbe_ty_ext : forall Γ A W, nbe_ty Θ1 Ξ1 Γ A W -> nbe_ty Θ2 Ξ2 Γ A W.
  Proof.
    pose proof eval_ext; pose proof read_ext; destruct_all.
    intros * []; econstructor; eauto using initial_env_ext.
  Qed.
End GlobalExt.
