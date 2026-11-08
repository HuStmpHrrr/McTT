(** * With the Skip Off, the Fast Relations Are Core's

    At [skip_off_mode] every recursive result is computed
    ([fast_eval_ihs_skip] needs the skip on), a kept proof reads back under
    its definitions ([fast_read_proof_kept]) and a type former at no
    argument is looked up ([fast_read_typ_indty_nil] needs the skip on):
    the rules left are those of [Core.Semantic.Evaluation] and
    [Core.Semantic.Readback], one for one.  So the extracted normalizer,
    run with the skip off, computes the Core normal form exactly; it does
    so where a normal form computed with the skip on has a proof in it
    ([Extraction.NbE]). *)
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback.
From Mctt.Extraction Require Import FastEval FastRead.
Import Domain_Notations.

Section Off.
  #[local] Existing Instance skip_off_mode.

  (** Core evaluation is fast evaluation with the skip off. *)
  Theorem core_to_fast_eval : forall Θ Ξ,
    (forall M ρ a, eval_exp Θ Ξ M ρ a -> fast_eval_exp Θ Ξ M ρ a) /\
    (forall m n r, eval_app Θ Ξ m n r -> fast_eval_app Θ Ξ m n r) /\
    (forall Ms ρ ms, eval_exps Θ Ξ Ms ρ ms -> fast_eval_exps Θ Ξ Ms ρ ms) /\
    (forall m ns r, eval_apps Θ Ξ m ns r -> fast_eval_apps Θ Ξ m ns r) /\
    (forall H ρ h, eval_modexp Θ Ξ H ρ h -> fast_eval_modexp Θ Ξ H ρ h) /\
    (forall Δ D ρ h, eval_close Θ Ξ Δ D ρ h -> fast_eval_close Θ Ξ Δ D ρ h) /\
    (forall h n r, eval_appm Θ Ξ h n r -> fast_eval_appm Θ Ξ h n r) /\
    (forall h ns r, eval_appms Θ Ξ h ns r -> fast_eval_appms Θ Ξ h ns r) /\
    (forall h x r, eval_sel Θ Ξ h x r -> fast_eval_sel Θ Ξ h x r) /\
    (forall h x r, eval_selm Θ Ξ h x r -> fast_eval_selm Θ Ξ h x r) /\
    (forall h c r, eval_selc Θ Ξ h c r -> fast_eval_selc Θ Ξ h c r) /\
    (forall h c r, eval_selmc Θ Ξ h c r -> fast_eval_selmc Θ Ξ h c r) /\
    (forall ρ Φ ρ', eval_body_env Θ Ξ ρ Φ ρ' -> fast_eval_body_env Θ Ξ ρ Φ ρ') /\
    (forall ρ p ups Bks j m r, eval_elim Θ Ξ ρ p ups Bks j m r -> fast_eval_elim Θ Ξ ρ p ups Bks j m r) /\
    (forall ρ p ups Bks gs vs r, eval_ihs Θ Ξ ρ p ups Bks gs vs r -> forall oB, fast_eval_ihs Θ Ξ ρ p ups Bks oB gs vs r) /\
    (forall ρ p ups Bks t v r, eval_ih Θ Ξ ρ p ups Bks t v r -> fast_eval_ih Θ Ξ ρ p ups Bks t v r) /\
    (forall p ups j r, eval_mref Θ Ξ p ups j r -> fast_eval_mref Θ Ξ p ups j r) /\
    (forall p ups ρ t a, eval_shape_type Θ Ξ p ups ρ t a -> fast_eval_shape_type Θ Ξ p ups ρ t a) /\
    (forall p ups ρm As ρ t v r, eval_ihty Θ Ξ p ups ρm As ρ t v r -> fast_eval_ihty Θ Ξ p ups ρm As ρ t v r) /\
    (forall f m r, eval_proj Θ Ξ f m r -> fast_eval_proj Θ Ξ f m r) /\
    (forall m ρ fl r, eval_neutral_fields Θ Ξ m ρ fl r -> fast_eval_neutral_fields Θ Ξ m ρ fl r) /\
    (forall fl v r, eval_projs Θ Ξ fl v r -> fast_eval_projs Θ Ξ fl v r) /\
    (forall p ups ρm As ρ gs vs r, eval_ihtys Θ Ξ p ups ρm As ρ gs vs r -> fast_eval_ihtys Θ Ξ p ups ρm As ρ gs vs r) /\
    (forall rs Ms ρ ms, eval_field_vals Θ Ξ rs Ms ρ ms -> fast_eval_field_vals Θ Ξ rs Ms ρ ms) /\
    (forall f Ms ρ r, eval_app_args Θ Ξ f Ms ρ r -> fast_eval_app_args Θ Ξ f Ms ρ r).
  Proof.
    intros Θ Ξ; apply eval_mut_ind; intros.
    all: solve [ eauto 3 with mctt core ].
  Qed.

  (** Fast evaluation with the skip off is Core evaluation. *)
  Theorem fast_to_core_eval : forall Θ Ξ,
    (forall M ρ a, fast_eval_exp Θ Ξ M ρ a -> eval_exp Θ Ξ M ρ a) /\
    (forall m n r, fast_eval_app Θ Ξ m n r -> eval_app Θ Ξ m n r) /\
    (forall Ms ρ ms, fast_eval_exps Θ Ξ Ms ρ ms -> eval_exps Θ Ξ Ms ρ ms) /\
    (forall m ns r, fast_eval_apps Θ Ξ m ns r -> eval_apps Θ Ξ m ns r) /\
    (forall H ρ h, fast_eval_modexp Θ Ξ H ρ h -> eval_modexp Θ Ξ H ρ h) /\
    (forall Δ D ρ h, fast_eval_close Θ Ξ Δ D ρ h -> eval_close Θ Ξ Δ D ρ h) /\
    (forall h n r, fast_eval_appm Θ Ξ h n r -> eval_appm Θ Ξ h n r) /\
    (forall h ns r, fast_eval_appms Θ Ξ h ns r -> eval_appms Θ Ξ h ns r) /\
    (forall h x r, fast_eval_sel Θ Ξ h x r -> eval_sel Θ Ξ h x r) /\
    (forall h x r, fast_eval_selm Θ Ξ h x r -> eval_selm Θ Ξ h x r) /\
    (forall h c r, fast_eval_selc Θ Ξ h c r -> eval_selc Θ Ξ h c r) /\
    (forall h c r, fast_eval_selmc Θ Ξ h c r -> eval_selmc Θ Ξ h c r) /\
    (forall ρ Φ ρ', fast_eval_body_env Θ Ξ ρ Φ ρ' -> eval_body_env Θ Ξ ρ Φ ρ') /\
    (forall ρ p ups Bks j m r, fast_eval_elim Θ Ξ ρ p ups Bks j m r -> eval_elim Θ Ξ ρ p ups Bks j m r) /\
    (forall ρ p ups Bks oB gs vs r, fast_eval_ihs Θ Ξ ρ p ups Bks oB gs vs r -> eval_ihs Θ Ξ ρ p ups Bks gs vs r) /\
    (forall ρ p ups Bks t v r, fast_eval_ih Θ Ξ ρ p ups Bks t v r -> eval_ih Θ Ξ ρ p ups Bks t v r) /\
    (forall p ups j r, fast_eval_mref Θ Ξ p ups j r -> eval_mref Θ Ξ p ups j r) /\
    (forall p ups ρ t a, fast_eval_shape_type Θ Ξ p ups ρ t a -> eval_shape_type Θ Ξ p ups ρ t a) /\
    (forall p ups ρm As ρ t v r, fast_eval_ihty Θ Ξ p ups ρm As ρ t v r -> eval_ihty Θ Ξ p ups ρm As ρ t v r) /\
    (forall f m r, fast_eval_proj Θ Ξ f m r -> eval_proj Θ Ξ f m r) /\
    (forall m ρ fl r, fast_eval_neutral_fields Θ Ξ m ρ fl r -> eval_neutral_fields Θ Ξ m ρ fl r) /\
    (forall fl v r, fast_eval_projs Θ Ξ fl v r -> eval_projs Θ Ξ fl v r) /\
    (forall p ups ρm As ρ gs vs r, fast_eval_ihtys Θ Ξ p ups ρm As ρ gs vs r -> eval_ihtys Θ Ξ p ups ρm As ρ gs vs r) /\
    (forall rs Ms ρ ms, fast_eval_field_vals Θ Ξ rs Ms ρ ms -> eval_field_vals Θ Ξ rs Ms ρ ms) /\
    (forall f Ms ρ r, fast_eval_app_args Θ Ξ f Ms ρ r -> eval_app_args Θ Ξ f Ms ρ r).
  Proof.
    intros Θ Ξ; apply fast_eval_mut_ind; intros.
    all: try solve [ eauto 3 with mctt core ].
    (** A skipped result needs the skip on *)
    all: exfalso; match goal with H : ihs_skip_at _ _ _ _ = true |- _ => discriminate H end.
  Qed.

  (** The fresh variables of the telescopes, the recursive results a
      branch is read under and the values of entry types *)
  Lemma core_to_fast_fresh : forall Θ Ξ,
    (forall ρ T s vs, fresh_tele Θ Ξ ρ T s vs -> fast_fresh_tele Θ Ξ ρ T s vs) /\
    (forall p ups ρ gs s vs, fresh_cargs Θ Ξ p ups ρ gs s vs -> fast_fresh_cargs Θ Ξ p ups ρ gs s vs) /\
    (forall ρm As p ups Dc ρ gs' gs vs s ihs, fresh_ihs Θ Ξ ρm As p ups Dc ρ gs' gs vs s ihs ->
       forall B, fast_fresh_ihs Θ Ξ ρm As p ups Dc B ρ gs' gs vs s ihs) /\
    (forall ρ p ups Bks Dc gs' gs vs ihs r, wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r ->
       fast_wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r) /\
    (forall t a, eval_entry_type Θ Ξ t a -> fast_eval_entry_type Θ Ξ t a).
  Proof.
    intros Θ Ξ; pose proof (core_to_fast_eval Θ Ξ) as HE; destruct_conjs.
    repeat split; [ induction 1 | induction 1 | induction 1; intros | induction 1 | induction 1 ].
    all: solve [ econstructor; eauto ].
  Qed.

  Lemma fast_to_core_fresh : forall Θ Ξ,
    (forall ρ T s vs, fast_fresh_tele Θ Ξ ρ T s vs -> fresh_tele Θ Ξ ρ T s vs) /\
    (forall p ups ρ gs s vs, fast_fresh_cargs Θ Ξ p ups ρ gs s vs -> fresh_cargs Θ Ξ p ups ρ gs s vs) /\
    (forall ρm As p ups Dc B ρ gs' gs vs s ihs, fast_fresh_ihs Θ Ξ ρm As p ups Dc B ρ gs' gs vs s ihs ->
       fresh_ihs Θ Ξ ρm As p ups Dc ρ gs' gs vs s ihs) /\
    (forall ρ p ups Bks Dc gs' gs vs ihs r, fast_wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r ->
       wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r) /\
    (forall t a, fast_eval_entry_type Θ Ξ t a -> eval_entry_type Θ Ξ t a).
  Proof.
    intros Θ Ξ; pose proof (fast_to_core_eval Θ Ξ) as HE; destruct_conjs.
    repeat split; induction 1.
    all: try solve [ econstructor; eauto ].
    all: exfalso; match goal with H : ihs_skip_at _ _ _ _ = true |- _ => discriminate H end.
  Qed.

  (** Core readback is fast readback with the skip off. *)
  Theorem core_to_fast_read : forall Θ Ξ,
    (forall s m M, read_nf Θ Ξ s m M -> fast_read_nf Θ Ξ s m M) /\
    (forall s m M, read_ne Θ Ξ s m M -> fast_read_ne Θ Ξ s m M) /\
    (forall s a A, read_typ Θ Ξ s a A -> fast_read_typ Θ Ξ s a A) /\
    (forall s xs ys, read_level_atoms Θ Ξ s xs ys -> fast_read_level_atoms Θ Ξ s xs ys) /\
    (forall s ρ T vs Ms, read_ps Θ Ξ s ρ T vs Ms -> fast_read_ps Θ Ξ s ρ T vs Ms) /\
    (forall s p ups ρ gs vs Ms, read_cargs Θ Ξ s p ups ρ gs vs Ms -> fast_read_cargs Θ Ξ s p ups ρ gs vs Ms) /\
    (forall s p ups ρ t v V, read_shape Θ Ξ s p ups ρ t v V -> fast_read_shape Θ Ξ s p ups ρ t v V) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, read_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks ->
       fast_read_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', read_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' ->
       fast_read_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs') /\
    (forall s ρ fl v Fs, read_fields Θ Ξ s ρ fl v Fs -> fast_read_fields Θ Ξ s ρ fl v Fs) /\
    (forall s m M, read_proof Θ Ξ s m M -> fast_read_proof Θ Ξ s m M) /\
    (forall s ρ k bs, read_lets Θ Ξ s ρ k bs -> fast_read_lets Θ Ξ s ρ k bs) /\
    (forall s e b, read_entry Θ Ξ s e b -> fast_read_entry Θ Ξ s e b).
  Proof.
    intros Θ Ξ; pose proof (core_to_fast_eval Θ Ξ) as HE; pose proof (core_to_fast_fresh Θ Ξ) as HF; destruct_conjs.
    apply read_mut_ind; intros.
    all: try solve [ econstructor; eauto ].
    (** A type former: the rule that looks it up *)
    all: eapply fast_read_typ_indty; eauto.
  Qed.

  (** Fast readback with the skip off is Core readback. *)
  Theorem fast_to_core_read : forall Θ Ξ,
    (forall s m M, fast_read_nf Θ Ξ s m M -> read_nf Θ Ξ s m M) /\
    (forall s m M, fast_read_ne Θ Ξ s m M -> read_ne Θ Ξ s m M) /\
    (forall s a A, fast_read_typ Θ Ξ s a A -> read_typ Θ Ξ s a A) /\
    (forall s xs ys, fast_read_level_atoms Θ Ξ s xs ys -> read_level_atoms Θ Ξ s xs ys) /\
    (forall s ρ T vs Ms, fast_read_ps Θ Ξ s ρ T vs Ms -> read_ps Θ Ξ s ρ T vs Ms) /\
    (forall s p ups ρ gs vs Ms, fast_read_cargs Θ Ξ s p ups ρ gs vs Ms -> read_cargs Θ Ξ s p ups ρ gs vs Ms) /\
    (forall s p ups ρ t v V, fast_read_shape Θ Ξ s p ups ρ t v V -> read_shape Θ Ξ s p ups ρ t v V) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, fast_read_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks ->
       read_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', fast_read_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' ->
       read_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs') /\
    (forall s ρ fl v Fs, fast_read_fields Θ Ξ s ρ fl v Fs -> read_fields Θ Ξ s ρ fl v Fs) /\
    (forall s m M, fast_read_proof Θ Ξ s m M -> read_proof Θ Ξ s m M) /\
    (forall s ρ k bs, fast_read_lets Θ Ξ s ρ k bs -> read_lets Θ Ξ s ρ k bs) /\
    (forall s e b, fast_read_entry Θ Ξ s e b -> read_entry Θ Ξ s e b).
  Proof.
    intros Θ Ξ; pose proof (fast_to_core_eval Θ Ξ) as HE; pose proof (fast_to_core_fresh Θ Ξ) as HF; destruct_conjs.
    apply fast_read_mut_ind; intros.
    all: try solve [ econstructor; eauto ].
    (** The rules that need the skip on *)
    all: exfalso; match goal with H : skip_on = true |- _ => discriminate H end.
  Qed.
End Off.
