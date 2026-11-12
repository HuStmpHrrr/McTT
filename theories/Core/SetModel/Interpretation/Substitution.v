(** * The Set Interpretation under Substitution

    A term moved by a substitution [σ] of the context, under the extension
    [Ψ] it is read in, has the value the term has at the environment that
    reads each variable of the context below at the value of its image
    ([set_interp_sub]).  The images are read in [σ]'s own context and
    weakened past the moved extension ([set_interp_wk]); the extension is
    well formed because every context the interpretation reads is
    ([⊢] premises of the binders). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Weakening.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members CoreInversions.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Lemmas Scoping.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf MemberLemmas DescTyping.
Require Import Mctt.Core.Syntactic.System.Inductives.Syntax.
Import ListNotations.

Lemma centry_kind_sub : forall e σ, centry_kind (centry_sub e σ) = centry_kind e.
Proof. intros [] σ; reflexivity. Qed.

Lemma ctx_kinds_tele_sub : forall Δ σ, ctx_kinds (tele_sub Δ σ) = ctx_kinds Δ.
Proof.
  induction Δ as [| e Δ IH]; intros σ; [reflexivity |]. unfold ctx_kinds in *. cbn [tele_sub List.map List.rev].
  rewrite IH, centry_kind_sub. reflexivity.
Qed.

Section Substitution.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** An extension of a context moves along a substitution into another. *)
Lemma ctx_sub : forall Ψ Γ Γ' σ, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ -> gc_deps ⍮ gc_stack ⍮ Γ' ⊢ˢ σ : Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ tele_sub Ψ σ ++ Γ'.
Proof. intros * HΓ Hσ. eapply ext_eq_ctx_left. exact (sub_preserves_ext _ _ _ _ _ _ _ (ext_of_ctx _ _ _ _ HΓ) Hσ). Qed.

(** A typing under an extension moves along a substitution of the context
    under it. *)
Lemma typing_sub : forall Ψ Γ Γ' σ M A, gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ ⊢ M : A -> gc_deps ⍮ gc_stack ⍮ Γ' ⊢ˢ σ : Γ ->
    gc_deps ⍮ gc_stack ⍮ tele_sub Ψ σ ++ Γ' ⊢ exp_sub M (sb_qn (List.length Ψ) σ) : exp_sub A (sb_qn (List.length Ψ) σ).
Proof.
  intros * HM Hσ. destruct (presup_exp HM) as [HΓ _].
  eapply sub_preserves_exp; [exact HM |]. apply wf_sub_ext; [exact Hσ | exact (ctx_sub _ _ _ _ HΓ Hσ) | exact HΓ].
Qed.

(** What an entry of the substitution gives the entry of the variable:
    its term part the term's value, its module part the module. *)
Definition sub_entry_agrees (Γ' : ctx) (ρb : set_env) (s : sentry) (e : set_entry) : Prop :=
  set_interp T γ Γ' ρb (sentry_exp s) (set_entry_value e) /\ set_interp_modexp T γ Γ' ρb (sentry_modexp s) (set_entry_module_part e).

(** [sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ']: a term of [Ξ] read at [ρ] is moved
    by [σ] to [tele_sub Ψ σ ++ Γ'], read at [ρ'], whose part below the
    extension is [ρb]. *)
Record sub_setting (Ξ : ctx) (ρ : set_env) (Ψ Γ Γ' : ctx) (σ : sub) (ρb ρ' : set_env) : Prop :=
  { (** [Ξ] is [Γ] under the extension [Ψ] *)
    sub_setting_ctx : Ξ = Ψ ++ Γ
    (** [σ] substitutes [Γ] in [Γ'] *)
  ; sub_setting_typed : gc_deps ⍮ gc_stack ⍮ Γ' ⊢ˢ σ : Γ
    (** The extension reads alike *)
  ; sub_setting_bound : forall x, x < List.length Ψ -> ρ x = ρ' x
    (** Below the extension, [ρ'] is [ρb] *)
  ; sub_setting_below : forall y, ρ' (List.length Ψ + y) = ρb y
    (** Below the extension, [ρ] reads the values of [σ]'s entries at
        [ρb] *)
  ; sub_setting_free : forall x, sub_entry_agrees Γ' ρb (σ x) (ρ (List.length Ψ + x)) }.

Lemma sub_setting_extend : forall Ξ ρ Ψ Γ Γ' σ ρb ρ' e d, sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
    sub_setting (e :: Ξ) (set_env_extend ρ d) (e :: Ψ) Γ Γ' σ ρb (set_env_extend ρ' d).
Proof.
  intros * [HΞ Hσ Hb Hl Hf]. constructor; [subst; reflexivity | exact Hσ | | exact Hl | exact Hf].
  intros [| x] Hx; cbn; [reflexivity | apply Hb; cbn in Hx; lia].
Qed.

(** A variable is read at the value of its image. *)
Lemma sub_setting_var : forall Ξ ρ Ψ Γ Γ' σ ρb ρ' x, ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
    sub_entry_agrees (tele_sub Ψ σ ++ Γ') ρ' (sb_qn (List.length Ψ) σ x) (ρ x).
Proof.
  intros * HΞ [-> Hσ Hb Hl Hf]. unfold sub_entry_agrees. destruct (Nat.lt_ge_cases x (List.length Ψ)) as [Hx | Hx].
  - rewrite sb_qn_lt by exact Hx. rewrite (Hb x Hx). split; constructor.
  - rewrite sb_qn_ge by exact Hx. rewrite <- sentry_exp_wk, <- sentry_modexp_wk.
    destruct (Hf (x - List.length Ψ)) as [He Hm]. replace (List.length Ψ + (x - List.length Ψ)) with x in He, Hm by lia.
    pose proof (ctx_sub _ _ _ _ HΞ Hσ) as HΓ'.
    assert (Hw : gc_deps ⍮ gc_stack ⍮ tele_sub Ψ σ ++ Γ' ⊢ʷ wk_shiftn (List.length Ψ) : Γ').
    { rewrite <- (length_tele_sub Ψ σ). apply wf_wk_shiftn_app; [exact HΓ' | exact (wf_sub_dom _ _ _ _ _ Hσ)]. }
    assert (Hag : env_agrees ρb ρ' (wk_qn (List.length (@nil centry)) (wk_shiftn (List.length Ψ)))).
    { intros y. cbn [List.length wk_qn wk_shiftn]. rewrite Nat.add_comm, Hl. reflexivity. }
    split.
    + exact (proj1 (set_interp_wk_all T γ) _ _ _ _ He nil Γ' _ _ ρ' (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag)).
    + exact (proj1 (proj2 (proj2 (proj2 (set_interp_wk_all T γ)))) _ _ _ _ Hm nil Γ' _ _ ρ'
               (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag)).
Qed.

Lemma set_env_extend_kinded_ge : forall vs κs ρ x, set_env_extend_kinded ρ κs vs (List.length vs + x) = ρ x.
Proof.
  induction vs as [| v vs IH]; intros κs ρ x; cbn [set_env_extend_kinded List.length]; [reflexivity |].
  replace (S (List.length vs) + x) with (List.length vs + S x) by lia. rewrite IH. reflexivity.
Qed.

Lemma set_env_extend_kinded_lt : forall vs κs ρ ρ' x, x < List.length vs ->
    set_env_extend_kinded ρ κs vs x = set_env_extend_kinded ρ' κs vs x.
Proof.
  induction vs as [| v vs IH]; intros κs ρ ρ' x Hx; cbn [set_env_extend_kinded List.length] in *; [lia |].
  destruct (Nat.lt_ge_cases x (List.length vs)) as [Hlt | Hge]; [apply IH; exact Hlt |].
  replace x with (List.length vs + 0) by lia. rewrite !set_env_extend_kinded_ge. reflexivity.
Qed.

(** A body's environment extends the one it is read at. *)
Lemma set_interp_gmod_extends : forall Ξ ρ Φ ms ρo, set_interp_gmod T γ Ξ ρ Φ ms ρo ->
    forall y, ρo (gm_binders Φ + y) = ρ y.
Proof. intros * H. induction H as [| ? ? ? ? ? ? ? ? _ _ IH _]; intros y; cbn [gm_binders]; [reflexivity |]. apply IH. Qed.

Lemma nth_error_blocks_sub : forall Bks j b τ, List.nth_error Bks j = Some b -> List.nth_error (blocks_sub Bks τ) j = Some (eblock_sub b τ).
Proof. intros * H. unfold blocks_sub. rewrite List.nth_error_map, H. reflexivity. Qed.

Lemma set_interp_sub_all :
  (forall Ξ ρ M v, set_interp T γ Ξ ρ M v -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp T γ (tele_sub Ψ σ ++ Γ') ρ' (exp_sub M (sb_qn (List.length Ψ) σ)) v) /\
  (forall Ξ ρ Ms vs, set_interp_list T γ Ξ ρ Ms vs -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_list T γ (tele_sub Ψ σ ++ Γ') ρ' (List.map (fun M => exp_sub M (sb_qn (List.length Ψ) σ)) Ms) vs) /\
  (forall Ξ ρ fs vs, set_interp_fields T γ Ξ ρ fs vs -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_fields T γ (tele_sub Ψ σ ++ Γ') ρ' (List.map (fun f => (fst f, exp_sub (snd f) (sb_qn (List.length Ψ) σ))) fs) vs) /\
  (forall Ξ ρ H m, set_interp_modexp T γ Ξ ρ H m -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_modexp T γ (tele_sub Ψ σ ++ Γ') ρ' (modexp_sub H (sb_qn (List.length Ψ) σ)) m) /\
  (forall Ξ ρ U m, set_interp_gunit T γ Ξ ρ U m -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_gunit T γ (tele_sub Ψ σ ++ Γ') ρ' (gunit_sub U (sb_qn (List.length Ψ) σ)) m) /\
  (forall Ξ ρ L D m, set_interp_unit_params T γ Ξ ρ L D m -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ ->
     sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_unit_params T γ (tele_sub Ψ σ ++ Γ') ρ' (List.rev (tele_sub (List.rev L) (sb_qn (List.length Ψ) σ)))
       (moddef_sub D (sb_qn (List.length L) (sb_qn (List.length Ψ) σ))) m) /\
  (forall Ξ ρ D m, set_interp_moddef T γ Ξ ρ D m -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_moddef T γ (tele_sub Ψ σ ++ Γ') ρ' (moddef_sub D (sb_qn (List.length Ψ) σ)) m) /\
  (forall Ξ ρ Φ ms ρo, set_interp_gmod T γ Ξ ρ Φ ms ρo -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ ->
     sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     exists ρo', set_interp_gmod T γ (tele_sub Ψ σ ++ Γ') ρ' (gmod_sub Φ (sb_qn (List.length Ψ) σ)) ms ρo' /\
       forall x, x < gm_binders Φ -> ρo x = ρo' x) /\
  (forall Ξ ρ E e, set_interp_gentry T γ Ξ ρ E e -> forall Ψ Γ Γ' σ ρb ρ', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
     set_interp_gentry T γ (tele_sub Ψ σ ++ Γ') ρ' (gentry_sub E (sb_qn (List.length Ψ) σ)) e) /\
  (forall Ξ ρ r p Us Bks j v res, set_elim T γ Ξ ρ r p Us Bks j v res -> forall Ψ Γ Γ' σ ρb ρ' D,
     ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' -> elim_shape p Us Bks D ->
     set_elim T γ (tele_sub Ψ σ ++ Γ') ρ' r p (List.map (fun U => exp_sub U (sb_qn (List.length Ψ) σ)) Us)
       (blocks_sub Bks (sb_qn (List.length Ψ) σ)) j v res) /\
  (forall Ξ ρ r p Us Bks gs vs ihs, set_ihs T γ Ξ ρ r p Us Bks gs vs ihs -> forall Ψ Γ Γ' σ ρb ρ' D,
     ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' -> elim_shape p Us Bks D ->
     set_ihs T γ (tele_sub Ψ σ ++ Γ') ρ' r p (List.map (fun U => exp_sub U (sb_qn (List.length Ψ) σ)) Us)
       (blocks_sub Bks (sb_qn (List.length Ψ) σ)) gs vs ihs) /\
  (forall Ξ ρ r p Us Bks t v ihs, set_ih T γ Ξ ρ r p Us Bks t v ihs -> forall Ψ Γ Γ' σ ρb ρ' D,
     ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' -> elim_shape p Us Bks D ->
     set_ih T γ (tele_sub Ψ σ ++ Γ') ρ' r p (List.map (fun U => exp_sub U (sb_qn (List.length Ψ) σ)) Us)
       (blocks_sub Bks (sb_qn (List.length Ψ) σ)) t v ihs).
Proof.
  (* same context *)
  Local Ltac same IH := eapply IH; eassumption.
  (* one binder more *)
  Local Ltac under IH e Hc := eapply (IH (e :: _)); [exact Hc | apply sub_setting_extend; eassumption].
  (* the extended context is well formed *)
  Local Ltac subctx Hc e Hs := exact (ctx_sub (e :: _) _ _ _ Hc (sub_setting_typed _ _ _ _ _ _ _ _ Hs)).
  Local Ltac start := intros ?Ψ ?Γ0 ?Γ' ?σ ?ρb ?ρ' ?HΞ ?Hs; pose proof (sub_setting_ctx _ _ _ _ _ _ _ _ Hs) as ->.
  Local Ltac start_elim := intros ?Ψ ?Γ0 ?Γ' ?σ ?ρb ?ρ' ?D0 ?HΞ ?Hs ?Hsh; pose proof (sub_setting_ctx _ _ _ _ _ _ _ _ Hs) as ->.
  apply (set_interp_combined_ind GC T γ); cbn [exp_sub modexp_sub binding_sub gentry_sub moddef_sub List.map fst snd].
  (** terms *)
  - intros; constructor.
  - intros Ξ ρ t l _ IH; start; constructor; same IH.
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros Ξ ρ M l _ IH; start; constructor; same IH.
  - intros Ξ ρ M N l l' _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros Ξ ρ P Q p q Hc _ IHP _ IHQ; start;
      econstructor; [subctx Hc (ce_ass ak_propositional P) Hs | same IHP | under IHQ (ce_ass ak_propositional P) Hc].
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros Ξ ρ P M v _ IH; start; constructor; same IH.
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros Ξ ρ r p Us m Bks M C v r0 Hr HC _ IHM _ IHE; start.
    destruct (elim_shape_of_typing _ _ _ _ _ _ _ _ HC) as [D HD].
    eapply set_interp_elim; [exact Hr | exact (typing_sub _ _ _ _ _ _ HC (sub_setting_typed _ _ _ _ _ _ _ _ Hs)) | same IHM |].
    eapply IHE; [exact HΞ | exact Hs | exact HD].
  - intros Ξ ρ κd A B a F Hc _ IHA _ IHB; start; econstructor; [subctx Hc (ce_ass κd A) Hs | same IHA |].
    intros x Hx. under (IHB x Hx) (ce_ass κd A) Hc.
  - intros Ξ ρ κd κc A B a F Hκ Hc _ IHA _ IHB; start; constructor; [exact Hκ | subctx Hc (ce_ass κd A) Hs | same IHA |].
    intros x Hx. under (IHB x Hx) (ce_ass κd A) Hc.
  - intros Ξ ρ A M κd C B HT; start. eapply set_interp_fn_proof.
    exact (typing_sub _ _ _ _ _ _ HT (sub_setting_typed _ _ _ _ _ _ _ _ Hs)).
  - intros Ξ ρ A M κd κc C B a F HT Hκ Hc _ IHA _ IHM; start.
    eapply set_interp_fn; [exact (typing_sub _ _ _ _ _ _ HT (sub_setting_typed _ _ _ _ _ _ _ _ Hs)) | exact Hκ
                          | subctx Hc (ce_ass κd A) Hs | same IHA |].
    intros x Hx. under (IHM x Hx) (ce_ass κd A) Hc.
  - intros Ξ ρ M N f n _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  - intros Ξ ρ x; start. exact (proj1 (sub_setting_var _ _ _ _ _ _ _ _ x HΞ Hs)).
  - intros Ξ ρ A M B v w Hc _ IHM _ IHB; start;
      econstructor; [subctx Hc (ce_def A M) Hs | same IHM | under IHB (ce_def A M) Hc].
  - intros Ξ ρ U B m w Hc _ IHU _ IHB; start;
      econstructor; [subctx Hc (ce_mod U) Hs | same IHU | under IHB (ce_mod U) Hc].
  - intros Ξ ρ A M U B v m w Hc _ IHM _ IHU _ IHB; start;
      econstructor; [subctx Hc (ce_dm A M U) Hs | same IHM | same IHU | under IHB (ce_dm A M U) Hc].
  - intros Ξ ρ H x m _ IH; start; constructor; same IH.
  - intros; constructor.
  - intros Ξ ρ A fs vs _ IH; start; constructor; same IH.
  - intros Ξ ρ f M v _ IH; start; constructor; same IH.
  (** lists and fields *)
  - intros; constructor.
  - intros Ξ ρ M Ms v vs _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  - intros; constructor.
  - intros Ξ ρ f M fs v vs _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  (** module expressions *)
  - intros; constructor.
  - intros Ξ ρ k; start. exact (proj2 (sub_setting_var _ _ _ _ _ _ _ _ k HΞ Hs)).
  - intros Ξ ρ H y m _ IH; start; constructor; same IH.
  - intros Ξ ρ H N m n _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  - intros Ξ ρ U m _ IH; start; constructor; same IH.
  (** units *)
  - intros Ξ ρ Δu D m _ IH; start. rewrite gunit_sub_mk. constructor.
    pose proof (IH _ _ _ _ _ _ HΞ Hs) as H.
    rewrite List.rev_involutive, List.length_rev in H. exact H.
  - intros Ξ ρ D m _ IH; start; cbn [List.rev tele_sub List.length sb_qn]; constructor; same IH.
  - intros Ξ ρ κ A L D a f Hc _ IHA _ IHL; start.
    rewrite tele_sub_rev_cons, List.rev_involutive. cbn [List.length centry_sub]. rewrite <- Nat.add_1_r, sb_qn_plus.
    econstructor; [subctx Hc (ce_ass κ A) Hs | same IHA |]. intros x Hx. under (IHL x Hx) (ce_ass κ A) Hc.
  - intros Ξ ρ A M L D v m Hc _ IHM _ IHL; start.
    rewrite tele_sub_rev_cons, List.rev_involutive. cbn [List.length centry_sub]. rewrite <- Nat.add_1_r, sb_qn_plus.
    econstructor; [subctx Hc (ce_def A M) Hs | same IHM | under IHL (ce_def A M) Hc].
  - intros Ξ ρ U L D mu m Hc _ IHU _ IHL; start.
    rewrite tele_sub_rev_cons, List.rev_involutive. cbn [List.length centry_sub]. rewrite <- Nat.add_1_r, sb_qn_plus.
    econstructor; [subctx Hc (ce_mod U) Hs | same IHU | under IHL (ce_mod U) Hc].
  - intros Ξ ρ A M U L D v mu m Hc _ IHM _ IHU _ IHL; start.
    rewrite tele_sub_rev_cons, List.rev_involutive. cbn [List.length centry_sub]. rewrite <- Nat.add_1_r, sb_qn_plus.
    econstructor; [subctx Hc (ce_dm A M U) Hs | same IHM | same IHU | under IHL (ce_dm A M U) Hc].
  (** definitions *)
  - intros Ξ ρ sm Φ ms ρo _ IH; start.
    destruct (IH _ _ _ _ _ _ HΞ Hs) as [ρo' [H _]].
    eapply set_interp_md_body. rewrite gm_expand_sub. exact H.
  - intros Ξ ρ E m _ IH; start; constructor; same IH.
  (** bodies *)
  - intros Ξ ρ; start. exists ρ'. split; [constructor | intros x Hx; cbn in Hx; lia].
  - intros Ξ ρ Φ x E ms ρo e Hc HΦ IHΦ _ IHE; start.
    pose proof (set_interp_gmod_nopens _ _ _ _ _ _ _ HΦ) as Hn.
    destruct (IHΦ _ _ _ _ _ _ HΞ Hs) as [ρo' [HΦ' Hago]].
    exists (set_env_extend ρo' e). split.
    2:{ intros [| y] Hy; cbn; [reflexivity | apply Hago; cbn in Hy; lia]. }
    cbn [gmod_sub]. destruct Hs as [_ Hσ Hb Hl Hf].
    pose proof (set_interp_gmod_extends _ _ _ _ _ HΦ) as E1.
    pose proof (set_interp_gmod_extends _ _ _ _ _ HΦ') as E2. rewrite gm_binders_sub in E2.
    assert (Hs' : sub_setting (body_ctx Φ ++ Ψ ++ Γ0) ρo (body_ctx Φ ++ Ψ) Γ0 Γ' σ ρb ρo').
    { constructor; [apply List.app_assoc | exact Hσ | | |].
      - intros z Hz. rewrite List.length_app, (length_body_ctx _ Hn) in Hz.
        destruct (Nat.lt_ge_cases z (gm_binders Φ)) as [Hlt | Hge]; [apply Hago; exact Hlt |].
        replace z with (gm_binders Φ + (z - gm_binders Φ)) by lia.
        rewrite E1, E2. apply Hb. lia.
      - intros y. rewrite List.length_app, (length_body_ctx _ Hn), <- Nat.add_assoc, E2. apply Hl.
      - intros y. rewrite List.length_app, (length_body_ctx _ Hn), <- Nat.add_assoc, E1. apply Hf. }
    constructor; [| exact HΦ' |].
    { rewrite (body_ctx_sub _ _ Hn), List.app_assoc, <- tele_sub_app.
      apply (ctx_sub _ Γ0); [rewrite <- List.app_assoc; exact Hc | exact Hσ]. }
    rewrite (body_ctx_sub _ _ Hn), List.app_assoc, <- tele_sub_app, <- (length_body_ctx _ Hn), <- sb_qn_plus, <- List.length_app.
    eapply IHE; [exact Hc | exact Hs'].
  (** entries *)
  - intros Ξ ρ b pv r A M v _ IH; start; constructor; same IH.
  - intros; constructor.
  - intros Ξ ρ pv U m _ IH; start; constructor; same IH.
  - intros Ξ ρ pv A M U v m _ IHM _ IHU; start; econstructor; [same IHM | same IHU].
  - intros; constructor.
  - intros; constructor.
  (** the eliminator *)
  - intros Ξ ρ r p Us Bks j v res D Mj pc k Dq Mk c gs ns vs nm Z A Bs n B ihs
      HD HMj Href HDq HMk Hgs Hv Hns Hvs Hb HB _ IHihs Hlen Hc _ IHB; start_elim.
    pose proof (elim_shape_lookup _ _ _ _ Hsh) as HD0. rewrite HD in HD0. injection HD0 as <-.
    set (τ := sb_qn (List.length Ψ) σ).
    set (bctx := elim_bctx r p D Mj gs (blocks_motives Bks) Us) in *.
    assert (Hw : tele_sub bctx τ =
                 elim_bctx r p D Mj gs (blocks_motives (blocks_sub Bks τ)) (List.map (fun U => exp_sub U τ) Us)).
    { apply elim_bctx_sub with (k := j) (c := c); [exact (elim_shape_closed _ _ _ _ Hsh) | exact HMj | exact (cons_lookup_in _ _ _ Hgs)
                          | exact (elim_shape_uniform _ _ _ _ Hsh) |].
      intros j' Mj' HMj'. apply (blocks_motives_sub D); [exact (elim_shape_binders _ _ _ _ Hsh) | exact HMj']. }
    assert (Hn : n = List.length bctx).
    { pose proof (elim_shape_counts _ _ _ _ Hsh _ _ _ _ _ _ _ HMj Hb Hgs (brs_lookup_in _ _ _ _ HB)) as E.
      subst bctx. rewrite length_elim_bctx. lia. }
    destruct Hs as [_ Hσ Hbd Hl Hf].
    eapply set_elim_con; [exact HD | exact HMj | exact Href | exact HDq | exact HMk | exact Hgs | exact Hv | exact Hns | exact Hvs
                         | exact (nth_error_blocks_sub _ _ _ τ Hb)
                         | rewrite brs_lookup_sub, HB; reflexivity
                         | eapply IHihs; [exact HΞ | econstructor; [reflexivity | eassumption ..] | exact Hsh]
                         | rewrite length_elim_bctx; subst bctx; rewrite length_elim_bctx in Hlen; exact Hlen | |].
    { fold τ bctx. rewrite <- Hw.
      pose proof (ctx_sub (bctx ++ Ψ) Γ0 Γ' σ ltac:(rewrite <- List.app_assoc; exact Hc) Hσ) as H.
      rewrite tele_sub_app, <- List.app_assoc in H. exact H. }
    cbn beta. fold τ bctx. rewrite <- Hw, ctx_kinds_tele_sub, Hn.
    pose proof (IHB (bctx ++ Ψ) Γ0 Γ' σ ρb (set_env_extend_kinded ρ' (ctx_kinds bctx) (ns ++ vs ++ ihs))) as H.
    rewrite tele_sub_app, <- List.app_assoc, List.length_app, sb_qn_plus in H. apply H; [exact Hc |].
    constructor; [apply List.app_assoc | exact Hσ | | |].
    + intros z Hz. rewrite List.length_app in Hz.
      destruct (Nat.lt_ge_cases z (List.length (ns ++ vs ++ ihs))) as [Hlt | Hge]; [apply set_env_extend_kinded_lt; exact Hlt |].
      replace z with (List.length (ns ++ vs ++ ihs) + (z - List.length (ns ++ vs ++ ihs))) by lia.
      rewrite !set_env_extend_kinded_ge. apply Hbd. lia.
    + intros y. rewrite List.length_app, <- Nat.add_assoc, <- Hlen, set_env_extend_kinded_ge. apply Hl.
    + intros y. rewrite List.length_app, <- Nat.add_assoc, <- Hlen, set_env_extend_kinded_ge. apply Hf.
  - intros; constructor.
  - intros Ξ ρ r p Us Bks κ T0 gs v vs ihs _ IH; start_elim; constructor. eapply IH; eassumption.
  - intros Ξ ρ r p Us Bks t gs v vs ihs1 ihs2 _ IH1 _ IH2; start_elim; constructor; [eapply IH1 | eapply IH2]; eassumption.
  - intros Ξ ρ r p Us Bks D j Mj Ps v r0 HD HMj Hrv _ IH; start_elim. eapply set_ih_self; [exact HD | exact HMj | exact Hrv |].
    eapply IH; eassumption.
  - intros Ξ ρ r p Us Bks D j Mj qr Is fl c gs Ps v rs HD HMj Hh Hc _ IH; start_elim.
    eapply set_ih_rview; [exact HD | exact HMj | exact Hh | exact Hc |]. eapply IH; eassumption.
  - intros Ξ ρ r p Us Bks D B t v Rs HD _ IH; start_elim. eapply set_ih_pi; [exact HD |].
    intros b Hb. eapply IH; eassumption.
Qed.

(** A term of a well-formed context, moved under the extension [Ψ] by a
    substitution [σ] of the context below, keeps its value. *)
Lemma set_interp_sub : forall Ξ ρ M v, set_interp T γ Ξ ρ M v -> ⊢ gc_deps ⍮ gc_stack ⍮ Ξ ->
    forall Ψ Γ Γ' σ ρb ρ', sub_setting Ξ ρ Ψ Γ Γ' σ ρb ρ' ->
    set_interp T γ (tele_sub Ψ σ ++ Γ') ρ' (exp_sub M (sb_qn (List.length Ψ) σ)) v.
Proof. intros * H HΞ * Hs. exact (proj1 set_interp_sub_all _ _ _ _ H _ _ _ _ _ _ HΞ Hs). Qed.

(** A term of [Γ ▹{κ} A] at the value [n] of a term [N] keeps its value
    with [N] substituted. *)
Lemma set_interp_single_sub : forall Γ ρ κ A N n X v, ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A :: Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κ A :: Γ ->
    set_interp T γ Γ ρ N n -> set_interp T γ (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ n)) X v ->
    set_interp T γ Γ ρ (exp_sub X (sb_extend sb_id (se_exp N))) v.
Proof.
  intros * Hc Hσ HN HX.
  apply (set_interp_sub _ _ _ _ HX Hc nil (ce_ass κ A :: Γ) Γ _ ρ ρ). constructor; [reflexivity | exact Hσ | | |].
  - intros x Hx. cbn in Hx. lia.
  - intros y. reflexivity.
  - intros [| y]; split; cbn; first [exact HN | constructor].
Qed.

End Substitution.
