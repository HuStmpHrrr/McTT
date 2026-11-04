(** * NbE Reads the Global Context Only Through Its Lookups

    Evaluation and readback read the global context through [gc_resolve],
    [gc_module], [ind_lookup], [gc_entry], [record_lookup], [gc_frame] and [gs_find_ind] alone, so two global contexts with the same
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
  (** A definition with a module part is read off its entry. *)
  Hypothesis Hent : forall p, gc_entry Θ1 Ξ1 p = gc_entry Θ2 Ξ2 p.
  Hypothesis Hfr : forall p, gc_frame Ξ1 p = gc_frame Ξ2 p.
  Hypothesis Hfi : forall p, gs_find_ind Ξ1 p = gs_find_ind Ξ2 p.
  Hypothesis Hbody : forall p, gc_body Θ1 Ξ1 p = gc_body Θ2 Ξ2 p.
  (** The neutral projection reads the record's fields. *)
  Hypothesis Hrec : forall p, record_lookup Θ1 Ξ1 p = record_lookup Θ2 Ξ2 p.

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
        | H : gc_entry Θ1 Ξ1 _ = _ |- _ => rewrite Hent in H
        end;
    eassumption.

  (** The term part a path names is read off its lookups. *)
  Lemma gc_term_ext : forall p, gc_term Θ1 Ξ1 p = gc_term Θ2 Ξ2 p.
  Proof. intros; unfold gc_term; rewrite Hres, Hent; reflexivity. Qed.

  (** The kind of a function's next argument is read off the groups'
      declarations. *)
  Lemma arg_kind_ext : forall f, arg_kind Θ1 Ξ1 f = arg_kind Θ2 Ξ2 f.
  Proof. intros []; cbn; rewrite ?Hind; reflexivity. Qed.

  (** A member with a term part and a module part is one by its lookups. *)
  Lemma dm_path_ext : forall p, dm_path Θ1 Ξ1 p <-> dm_path Θ2 Ξ2 p.
  Proof. intros; unfold dm_path; rewrite ind_mlookup_ext, Hrec, Hent; reflexivity. Qed.

  Lemma kind_ext :
    (forall h ch k, dmod_member_kind Θ1 Ξ1 h ch k -> dmod_member_kind Θ2 Ξ2 h ch k) /\
    (forall ρ U ch k, gunit_member_kind Θ1 Ξ1 ρ U ch k -> gunit_member_kind Θ2 Ξ2 ρ U ch k) /\
    (forall ρ H ch k, modexp_member_kind Θ1 Ξ1 ρ H ch k -> modexp_member_kind Θ2 Ξ2 ρ H ch k) /\
    (forall ρ Φ ρ', kinds_env Θ1 Ξ1 ρ Φ ρ' -> kinds_env Θ2 Ξ2 ρ Φ ρ').
  Proof.
    apply kind_mut_ind; intros;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             end;
      unfold module_saturated in *;
      rewrite ?Hres, ?Hmod, ?Hfr, ?gc_loc_ext, ?dm_path_ext in *.
    (** A step through a definition: its five components, past [eauto]'s
        depth. *)
    all: try solve [ match goal with Hd : gc_resolve _ _ _ = Some (ge_def _ _ _ _ _) |- _ =>
           eapply dmod_member_kind_global_step; [ right; do 5 eexists; exact Hd | eauto | eauto ] end ].
    all: solve [ econstructor; eauto 6 ].
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
    (forall p ups ρm As ρ t v a, ⟦ihty v of t at p ups under ρm As ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ a ->
       ⟦ihty v of t at p ups under ρm As ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ a) /\
    (forall f m r, eval_proj Θ1 Ξ1 f m r -> eval_proj Θ2 Ξ2 f m r) /\
    (forall m ρ fl rs, eval_neutral_fields Θ1 Ξ1 m ρ fl rs -> eval_neutral_fields Θ2 Ξ2 m ρ fl rs) /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ1 ⍮ Ξ1 ↘ ws -> ⟦projs fl of v ⟧ Θ2 ⍮ Ξ2 ↘ ws) /\
    (forall p ups ρm As ρ gs vs a, ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ a ->
       ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ a) /\
    (forall rs Ms ρ vs, eval_field_vals Θ1 Ξ1 rs Ms ρ vs -> eval_field_vals Θ2 Ξ2 rs Ms ρ vs) /\
    (forall f Ms ρ r, eval_app_args Θ1 Ξ1 f Ms ρ r -> eval_app_args Θ2 Ξ2 f Ms ρ r).
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
             (fun ρ Φ ρ' _ => eval_body_env Θ2 Ξ2 ρ Φ ρ')
             (fun ρ p ups Bks j m r _ => eval_elim Θ2 Ξ2 ρ p ups Bks j m r)
             (fun ρ p ups Bks gs vs ihs _ => eval_ihs Θ2 Ξ2 ρ p ups Bks gs vs ihs)
             (fun ρ p ups Bks t v r _ => eval_ih Θ2 Ξ2 ρ p ups Bks t v r)
             (fun p ups j r _ => eval_mref Θ2 Ξ2 p ups j r)
             (fun p ups ρ t a _ => eval_shape_type Θ2 Ξ2 p ups ρ t a)
             (fun p ups ρm As ρ t v a _ => eval_ihty Θ2 Ξ2 p ups ρm As ρ t v a)
             (fun f m r _ => eval_proj Θ2 Ξ2 f m r)
             (fun m ρ fl rs _ => eval_neutral_fields Θ2 Ξ2 m ρ fl rs)
             (fun fl v ws _ => eval_projs Θ2 Ξ2 fl v ws)
             (fun p ups ρm As ρ gs vs a _ => eval_ihtys Θ2 Ξ2 p ups ρm As ρ gs vs a)
             (fun rs Ms ρ vs _ => eval_field_vals Θ2 Ξ2 rs Ms ρ vs)
             (fun f Ms ρ r _ => eval_app_args Θ2 Ξ2 f Ms ρ r)).
    all: intros;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             end;
      unfold module_saturated in *;
      rewrite ?Hres, ?Hmod, ?Hfr, ?gc_loc_ext, ?ind_lookup_ext, ?ind_mlookup_ext, ?Hent, ?Hrec, ?gc_term_ext,
        ?arg_kind_ext in *.
    all: try solve [ econstructor; eauto; apply kind_ext; assumption ].
  Qed.

  Lemma fresh_tele_ext : forall ρ T s vs, Ftele T in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ vs -> Ftele T in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ vs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma fresh_cargs_ext : forall p ups ρ gs s vs,
      Fcargs gs of p ups in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ vs -> Fcargs gs of p ups in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ vs.
  Proof. pose proof eval_ext; destruct_all; induction 1; econstructor; eauto. Qed.

  Lemma fresh_ihs_ext : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ1 ⍮ Ξ1 ⍮ ρa ⍮ s ↘ ihs ->
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ2 ⍮ Ξ2 ⍮ ρa ⍮ s ↘ ihs.
  Proof.
    pose proof eval_ext; destruct_all; induction 1; econstructor; eauto.
    rewrite <- ind_lookup_ext; eassumption.
  Qed.

  Lemma wrap_ihs_eval_ext : forall ρ p ups Bks Dc gs' gs vs ihs r,
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ1 ⍮ Ξ1 ⍮ ρ ↘ r ->
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ2 ⍮ Ξ2 ⍮ ρ ↘ r.
  Proof.
    pose proof eval_ext; destruct_all; induction 1; econstructor; eauto.
    rewrite <- ind_lookup_ext; eassumption.
  Qed.

  (** The type an entry is stored at is evaluated alike. *)
  Lemma eval_entry_type_ext : forall t a, eval_entry_type Θ1 Ξ1 t a -> eval_entry_type Θ2 Ξ2 t a.
  Proof. pose proof eval_ext as He; destruct_all; intros * []; econstructor; eauto. Qed.

  Lemma read_ext :
    (forall s m M, Rnf m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rnf m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s m M, Rne m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rne m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s m M, Rtyp m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rtyp m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s xs ys, Rla xs in Θ1 ⍮ Ξ1 ⍮ s ↘ ys -> Rla xs in Θ2 ⍮ Ξ2 ⍮ s ↘ ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Ms -> Rps vs at T in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Ms -> Rcargs vs at gs of p ups in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Ms) /\
    (forall s p ups ρ t v V, Rsh v at t of p ups in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ V -> Rsh v at t of p ups in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ V) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ NBks ->
       Rblks i Ms of Dc from p ups Bks sel in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Bs' ->
       Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Bs') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ1 ⍮ Ξ1 ⍮ ρ ⍮ s ↘ Fs -> Rflds v at fl in Θ2 ⍮ Ξ2 ⍮ ρ ⍮ s ↘ Fs) /\
    (forall s m M, Rprf m in Θ1 ⍮ Ξ1 ⍮ s ↘ M -> Rprf m in Θ2 ⍮ Ξ2 ⍮ s ↘ M) /\
    (forall s ρ k bs, Rlets ρ at k in Θ1 ⍮ Ξ1 ⍮ s ↘ bs -> Rlets ρ at k in Θ2 ⍮ Ξ2 ⍮ s ↘ bs) /\
    (forall s e b, Rent e in Θ1 ⍮ Ξ1 ⍮ s ↘ b -> Rent e in Θ2 ⍮ Ξ2 ⍮ s ↘ b).
  Proof.
    pose proof eval_ext as He; destruct_all.
    apply (read_mut_ind Θ1 Ξ1
             (fun s m M _ => read_nf Θ2 Ξ2 s m M)
             (fun s m M _ => read_ne Θ2 Ξ2 s m M)
             (fun s m M _ => read_typ Θ2 Ξ2 s m M)
             (fun s xs ys _ => read_level_atoms Θ2 Ξ2 s xs ys)
             (fun s ρ T vs Ms _ => read_ps Θ2 Ξ2 s ρ T vs Ms)
             (fun s p ups ρ gs vs Ms _ => read_cargs Θ2 Ξ2 s p ups ρ gs vs Ms)
             (fun s p ups ρ t v V _ => read_shape Θ2 Ξ2 s p ups ρ t v V)
             (fun s ρ p ups Bks Dc sel i Ms NBks _ => read_blocks Θ2 Ξ2 s ρ p ups Bks Dc sel i Ms NBks)
             (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ => read_brs Θ2 Ξ2 s ρ p ups Bks Dc Mv A Mi r cs Bs Bs')
             (fun s ρ fl v Fs _ => read_fields Θ2 Ξ2 s ρ fl v Fs)
             (fun s m M _ => read_proof Θ2 Ξ2 s m M)
             (fun s ρ k bs _ => read_lets Θ2 Ξ2 s ρ k bs)
             (fun s e b _ => read_entry Θ2 Ξ2 s e b)).
    all: intros; econstructor;
      repeat match goal with
          | H : ind_lookup Θ1 Ξ1 _ = _ |- _ => rewrite ind_lookup_ext in H
          | H : record_lookup Θ1 Ξ1 _ = _ |- _ => rewrite Hrec in H
          end; eauto using fresh_tele_ext, fresh_cargs_ext, fresh_ihs_ext, wrap_ihs_eval_ext, eval_entry_type_ext.
  Qed.

  Lemma initial_env_ext : forall Γ ρ, initial_env Θ1 Ξ1 Γ ρ -> initial_env Θ2 Ξ2 Γ ρ.
  Proof.
    pose proof eval_ext; destruct_all; induction 1;
      first [ solve [ eapply initial_env_cons_def; eauto ] | solve [ eapply initial_env_cons_def_proof; eauto ]
            | econstructor; eauto ].
  Qed.

  Lemma nbe_ty_ext : forall Γ A W, nbe_ty Θ1 Ξ1 Γ A W -> nbe_ty Θ2 Ξ2 Γ A W.
  Proof.
    pose proof eval_ext; pose proof read_ext; destruct_all.
    intros * []; econstructor; eauto using initial_env_ext.
  Qed.
End GlobalExt.
