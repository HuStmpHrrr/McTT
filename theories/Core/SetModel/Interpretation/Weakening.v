(** * The Set Interpretation under Weakening

    A term weakened by a renaming [φ] of the context, under the
    extension [Ψ] it is read in, has the value the term has, in an
    environment that reads each variable where the renaming sends it
    ([set_interp_wk]).  The typing premises of a λ and of an elimination
    move by the syntactic weakening lemma; an elimination's branches move
    under the binders their context adds, which the typing fixes
    ([elim_shape]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Interp.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members CoreInversions.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Lemmas Scoping.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf MemberLemmas.
From Mctt.Core.Syntactic.System.Inductives Require Typing.
Require Import Mctt.Core.Syntactic.System.Inductives.Syntax.
Import ListNotations.

(** ** Environments Along a Renaming *)

(** [ρ] reads each variable where [ρ'] reads its image by [φ]. *)
Definition env_agrees (ρ ρ' : set_env) (φ : wk) : Prop := forall x, ρ x = ρ' (φ x).

Lemma env_agrees_extend : forall ρ ρ' φ e, env_agrees ρ ρ' φ -> env_agrees (set_env_extend ρ e) (set_env_extend ρ' e) (wk_q φ).
Proof. intros * H [| x]; cbn; [reflexivity | apply H]. Qed.

Lemma wk_qn_q : forall n φ, wk_qn n (wk_q φ) = wk_qn (S n) φ.
Proof. intros. rewrite <- Nat.add_1_r, wk_qn_plus. reflexivity. Qed.

Lemma env_agrees_extend_kinded : forall vs κs ρ ρ' φ, env_agrees ρ ρ' φ ->
    env_agrees (set_env_extend_kinded ρ κs vs) (set_env_extend_kinded ρ' κs vs) (wk_qn (List.length vs) φ).
Proof.
  induction vs as [| v vs IH]; intros κs ρ ρ' φ H; cbn [set_env_extend_kinded List.length]; [exact H |].
  rewrite <- wk_qn_q. apply IH. apply env_agrees_extend. exact H.
Qed.

Lemma centry_kind_wk : forall e φ, centry_kind (centry_wk e φ) = centry_kind e.
Proof. intros [] φ; reflexivity. Qed.

Lemma ctx_kinds_tele_wk : forall Δ φ, ctx_kinds (tele_wk Δ φ) = ctx_kinds Δ.
Proof.
  induction Δ as [| e Δ IH]; intros φ; [reflexivity |]. unfold ctx_kinds in *. cbn [tele_wk List.map List.rev].
  rewrite IH, centry_kind_wk. reflexivity.
Qed.

Section Weakening.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** An extension of a context moves along a renaming of the context. *)
Lemma ctx_wk : forall Ψ Γ Δ φ, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ -> gc_deps ⍮ gc_stack ⍮ Δ ⊢ʷ φ : Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ tele_wk Ψ φ ++ Δ.
Proof. intros * HΓ Hφ. eapply ext_eq_ctx_left. exact (wk_preserves_ext _ _ _ _ _ _ _ (ext_of_ctx _ _ _ _ HΓ) Hφ). Qed.

(** A typing under an extension moves along a renaming of the context
    under it. *)
Lemma typing_wk : forall Ψ Γ Δ φ M A, gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ ⊢ M : A -> gc_deps ⍮ gc_stack ⍮ Δ ⊢ʷ φ : Γ ->
    gc_deps ⍮ gc_stack ⍮ tele_wk Ψ φ ++ Δ ⊢ exp_wk M (wk_qn (List.length Ψ) φ) : exp_wk A (wk_qn (List.length Ψ) φ).
Proof.
  intros * HM Hφ. destruct (presup_exp HM) as [HΓ _].
  pose proof (wk_preserves_ext _ _ _ _ _ _ _ (ext_of_ctx _ _ _ _ HΓ) Hφ) as Hx.
  eapply wk_preserves_exp; [exact HM |]. apply wf_wk_ext; [exact Hφ | eapply ext_eq_ctx_left; exact Hx | exact HΓ].
Qed.

(** [elim_shape p Us Bks D]: what the typing of an elimination of the
    group [D] at [p], at the uniform parameters [Us] and the blocks [Bks],
    fixes of their shapes, whatever the context. *)
Record elim_shape (p : qname) (Us : list exp) (Bks : list eblock) (D : ind_decl) : Prop :=
  { (** The group *)
    elim_shape_lookup : ind_lookup gc_deps gc_stack p = Some D
    (** It is closed *)
  ; elim_shape_closed : decl_closed D
    (** One uniform parameter each *)
  ; elim_shape_uniform : List.length Us = ind_nu D
    (** Each motive binds its member's parameters and the scrutinee *)
  ; elim_shape_binders : blocks_binder_count_ok D Bks
    (** Each branch binds its constructor's parameters, arguments and
        recursive results *)
  ; elim_shape_counts : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat }.

Lemma elim_shape_of_typing : forall Γ r p Us m Bks M C, gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_elim r p Us m Bks M : C ->
    exists D, elim_shape p Us Bks D.
Proof.
  intros * H. pose proof H as H'. apply wf_elim_inversion in H as [D Mm bm Ps i Hl Hm Hb HPl _ _ HUs HBt _].
  exists D. destruct (presup_exp H') as [HΓ _]. constructor.
  - exact Hl.
  - eapply gctx_closed_ind; [eapply wf_gctx_closed; exact HΓ | exact Hl].
  - subst Us. rewrite List.firstn_length_le; [reflexivity |]. rewrite HPl. unfold im_np. lia.
  - exact (Typing.blocks_typed_binder_count _ _ _ _ _ _ _ _ _ HBt).
  - exact (Typing.blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt).
Qed.

(** [wk_setting Ξ ρ Ψ Γ Δ φ ρ']: a term of [Ξ] read at [ρ] is moved to
    [tele_wk Ψ φ ++ Δ], read at [ρ']. *)
Record wk_setting (Ξ : ctx) (ρ : set_env) (Ψ Γ Δ : ctx) (φ : wk) (ρ' : set_env) : Prop :=
  { (** [Ξ] is [Γ] under the extension [Ψ] *)
    wk_setting_ctx : Ξ = Ψ ++ Γ
    (** [φ] renames [Γ] into [Δ] *)
  ; wk_setting_renaming : gc_deps ⍮ gc_stack ⍮ Δ ⊢ʷ φ : Γ
    (** [ρ] reads each variable where [ρ'] reads its image *)
  ; wk_setting_env : env_agrees ρ ρ' (wk_qn (List.length Ψ) φ) }.

(** A body read by the interpretation has no open. *)
Lemma set_interp_gmod_nopens : forall Ξ ρ Φ ms ρo, set_interp_gmod T γ Ξ ρ Φ ms ρo -> gm_nopens Φ = 0.
Proof. intros * H. induction H; cbn [gm_nopens]; auto. Qed.

(** The weakened blocks. *)
Lemma nth_error_blocks_wk : forall Bks j nm Z A Bs φ, List.nth_error Bks j = Some (eb_mk nm Z A Bs) ->
    List.nth_error (blocks_wk Bks φ) j =
      Some (eb_mk nm (exp_wk Z (wk_qn (nm - 1) φ)) (exp_wk A (wk_qn nm φ))
              (List.map (fun br => (fst br, exp_wk (snd br) (wk_qn (snd (fst br)) φ))) Bs)).
Proof. intros * H. unfold blocks_wk. rewrite List.nth_error_map, H. reflexivity. Qed.

Lemma set_interp_wk_all :
  (forall Ξ ρ M v, set_interp T γ Ξ ρ M v -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp T γ (tele_wk Ψ φ ++ Δ) ρ' (exp_wk M (wk_qn (List.length Ψ) φ)) v) /\
  (forall Ξ ρ Ms vs, set_interp_list T γ Ξ ρ Ms vs -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_list T γ (tele_wk Ψ φ ++ Δ) ρ' (List.map (fun M => exp_wk M (wk_qn (List.length Ψ) φ)) Ms) vs) /\
  (forall Ξ ρ fs vs, set_interp_fields T γ Ξ ρ fs vs -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_fields T γ (tele_wk Ψ φ ++ Δ) ρ' (List.map (fun f => (fst f, exp_wk (snd f) (wk_qn (List.length Ψ) φ))) fs) vs) /\
  (forall Ξ ρ H m, set_interp_modexp T γ Ξ ρ H m -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_modexp T γ (tele_wk Ψ φ ++ Δ) ρ' (modexp_wk H (wk_qn (List.length Ψ) φ)) m) /\
  (forall Ξ ρ U m, set_interp_gunit T γ Ξ ρ U m -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_gunit T γ (tele_wk Ψ φ ++ Δ) ρ' (gunit_wk U (wk_qn (List.length Ψ) φ)) m) /\
  (forall Ξ ρ L D m, set_interp_unit_params T γ Ξ ρ L D m -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_unit_params T γ (tele_wk Ψ φ ++ Δ) ρ' (List.rev (tele_wk (List.rev L) (wk_qn (List.length Ψ) φ)))
       (moddef_wk D (wk_qn (List.length L) (wk_qn (List.length Ψ) φ))) m) /\
  (forall Ξ ρ D m, set_interp_moddef T γ Ξ ρ D m -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_moddef T γ (tele_wk Ψ φ ++ Δ) ρ' (moddef_wk D (wk_qn (List.length Ψ) φ)) m) /\
  (forall Ξ ρ Φ ms ρo, set_interp_gmod T γ Ξ ρ Φ ms ρo -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     exists ρo', set_interp_gmod T γ (tele_wk Ψ φ ++ Δ) ρ' (gmod_wk Φ (wk_qn (List.length Ψ) φ)) ms ρo' /\
       env_agrees ρo ρo' (wk_qn (gm_binders Φ) (wk_qn (List.length Ψ) φ))) /\
  (forall Ξ ρ E e, set_interp_gentry T γ Ξ ρ E e -> forall Ψ Γ Δ φ ρ', wk_setting Ξ ρ Ψ Γ Δ φ ρ' ->
     set_interp_gentry T γ (tele_wk Ψ φ ++ Δ) ρ' (gentry_wk E (wk_qn (List.length Ψ) φ)) e) /\
  (forall Ξ ρ r p Us Bks j v res, set_elim T γ Ξ ρ r p Us Bks j v res -> forall Ψ Γ Δ φ ρ' D,
     wk_setting Ξ ρ Ψ Γ Δ φ ρ' -> elim_shape p Us Bks D ->
     set_elim T γ (tele_wk Ψ φ ++ Δ) ρ' r p (List.map (fun U => exp_wk U (wk_qn (List.length Ψ) φ)) Us)
       (blocks_wk Bks (wk_qn (List.length Ψ) φ)) j v res) /\
  (forall Ξ ρ r p Us Bks gs vs ihs, set_ihs T γ Ξ ρ r p Us Bks gs vs ihs -> forall Ψ Γ Δ φ ρ' D,
     wk_setting Ξ ρ Ψ Γ Δ φ ρ' -> elim_shape p Us Bks D ->
     set_ihs T γ (tele_wk Ψ φ ++ Δ) ρ' r p (List.map (fun U => exp_wk U (wk_qn (List.length Ψ) φ)) Us)
       (blocks_wk Bks (wk_qn (List.length Ψ) φ)) gs vs ihs) /\
  (forall Ξ ρ r p Us Bks t v ihs, set_ih T γ Ξ ρ r p Us Bks t v ihs -> forall Ψ Γ Δ φ ρ' D,
     wk_setting Ξ ρ Ψ Γ Δ φ ρ' -> elim_shape p Us Bks D ->
     set_ih T γ (tele_wk Ψ φ ++ Δ) ρ' r p (List.map (fun U => exp_wk U (wk_qn (List.length Ψ) φ)) Us)
       (blocks_wk Bks (wk_qn (List.length Ψ) φ)) t v ihs).
Proof.
  (* same context *)
  Local Ltac same IH := eapply IH; constructor; [reflexivity | assumption | assumption].
  (* one binder more *)
  Local Ltac under IH e := eapply (IH (e :: _)); constructor; [reflexivity | assumption | apply env_agrees_extend; assumption].
  (* the extended context is well formed *)
  Local Ltac wkctx Hc e := exact (ctx_wk (e :: _) _ _ _ Hc ltac:(eassumption)).
  Local Ltac start := intros ?Ψ ?Γ0 ?Δ ?φ ?ρ' [?HΞ ?Hφ ?Hag]; subst.
  Local Ltac start_elim := intros ?Ψ ?Γ0 ?Δ ?φ ?ρ' ?D0 [?HΞ ?Hφ ?Hag] ?Hsh; subst.
  apply (set_interp_combined_ind GC T γ); cbn [exp_wk modexp_wk binding_wk gentry_wk moddef_wk List.map fst snd].
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
  - intros Ξ ρ P Q p F Hc _ IHP _ IHQ; start; econstructor; [wkctx Hc (ce_ass ak_propositional P) | same IHP |].
    intros x Hx. under (IHQ x Hx) (ce_ass ak_propositional P).
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros Ξ ρ P M v _ IH; start; constructor; same IH.
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros Ξ ρ r p Us m Bks M C v r0 Hr HC _ IHM _ IHE; start.
    destruct (elim_shape_of_typing _ _ _ _ _ _ _ _ HC) as [D HD].
    eapply set_interp_elim; [exact Hr | exact (typing_wk _ _ _ _ _ _ HC Hφ) | same IHM |].
    eapply IHE; [constructor; [reflexivity | assumption | assumption] | exact HD].
  - intros Ξ ρ κd A B a F Hc _ IHA _ IHB; start; econstructor; [wkctx Hc (ce_ass κd A) | same IHA |].
    intros x Hx. under (IHB x Hx) (ce_ass κd A).
  - intros Ξ ρ κd κc A B a F Hκ Hc _ IHA _ IHB; start; constructor; [exact Hκ | wkctx Hc (ce_ass κd A) | same IHA |].
    intros x Hx. under (IHB x Hx) (ce_ass κd A).
  - intros Ξ ρ A M κd C B HT; start. eapply set_interp_fn_proof. exact (typing_wk _ _ _ _ _ _ HT Hφ).
  - intros Ξ ρ A M κd κc C B a F HT Hκ Hc _ IHA _ IHM; start.
    eapply set_interp_fn; [exact (typing_wk _ _ _ _ _ _ HT Hφ) | exact Hκ | wkctx Hc (ce_ass κd A) | same IHA |].
    intros x Hx. under (IHM x Hx) (ce_ass κd A).
  - intros Ξ ρ M N f n _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  - intros Ξ ρ x; start. rewrite (Hag x). constructor.
  - intros Ξ ρ A M B v w Hc _ IHM _ IHB; start; econstructor; [wkctx Hc (ce_def A M) | same IHM | under IHB (ce_def A M)].
  - intros Ξ ρ U B m w Hc _ IHU _ IHB; start; econstructor; [wkctx Hc (ce_mod U) | same IHU | under IHB (ce_mod U)].
  - intros Ξ ρ A M U B v m w Hc _ IHM _ IHU _ IHB; start;
      econstructor; [wkctx Hc (ce_dm A M U) | same IHM | same IHU | under IHB (ce_dm A M U)].
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
  - intros Ξ ρ k; start. rewrite (Hag k). constructor.
  - intros Ξ ρ H y m _ IH; start; constructor; same IH.
  - intros Ξ ρ H N m n _ IH1 _ IH2; start; econstructor; [same IH1 | same IH2].
  - intros Ξ ρ U m _ IH; start; constructor; same IH.
  (** units *)
  - intros Ξ ρ Δu D m _ IH; start. rewrite gunit_wk_mk. constructor.
    pose proof (IH Ψ Γ0 Δ φ ρ' (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hφ Hag)) as H.
    rewrite List.rev_involutive, List.length_rev in H. exact H.
  - intros Ξ ρ D m _ IH; start; cbn [List.rev tele_wk List.length wk_qn]; constructor; same IH.
  - intros Ξ ρ κ A L D a f Hc _ IHA _ IHL; start.
    rewrite tele_wk_rev_cons, List.rev_involutive. cbn [List.length centry_wk]. rewrite <- wk_qn_q.
    econstructor; [wkctx Hc (ce_ass κ A) | same IHA |]. intros x Hx. under (IHL x Hx) (ce_ass κ A).
  - intros Ξ ρ A M L D v m Hc _ IHM _ IHL; start.
    rewrite tele_wk_rev_cons, List.rev_involutive. cbn [List.length centry_wk]. rewrite <- wk_qn_q.
    econstructor; [wkctx Hc (ce_def A M) | same IHM | under IHL (ce_def A M)].
  - intros Ξ ρ U L D mu m Hc _ IHU _ IHL; start.
    rewrite tele_wk_rev_cons, List.rev_involutive. cbn [List.length centry_wk]. rewrite <- wk_qn_q.
    econstructor; [wkctx Hc (ce_mod U) | same IHU | under IHL (ce_mod U)].
  - intros Ξ ρ A M U L D v mu m Hc _ IHM _ IHU _ IHL; start.
    rewrite tele_wk_rev_cons, List.rev_involutive. cbn [List.length centry_wk]. rewrite <- wk_qn_q.
    econstructor; [wkctx Hc (ce_dm A M U) | same IHM | same IHU | under IHL (ce_dm A M U)].
  (** definitions *)
  - intros Ξ ρ sm Φ ms ρo _ IH; start.
    destruct (IH Ψ Γ0 Δ φ ρ' (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hφ Hag)) as [ρo' [H _]].
    eapply set_interp_md_body. rewrite gm_expand_wk. exact H.
  - intros Ξ ρ E m _ IH; start; constructor; same IH.
  (** bodies *)
  - intros Ξ ρ; start. exists ρ'. split; [constructor | exact Hag].
  - intros Ξ ρ Φ x E ms ρo e Hc HΦ IHΦ _ IHE; start.
    pose proof (set_interp_gmod_nopens _ _ _ _ _ HΦ) as Hn.
    destruct (IHΦ Ψ Γ0 Δ φ ρ' (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hφ Hag)) as [ρo' [HΦ' Hago]].
    exists (set_env_extend ρo' e). split; [| apply env_agrees_extend; exact Hago].
    cbn [gmod_wk]. constructor; [| exact HΦ' |].
    { rewrite (body_ctx_wk _ _ Hn), List.app_assoc, <- tele_wk_app.
      apply (ctx_wk _ Γ0); [rewrite <- List.app_assoc; exact Hc | exact Hφ]. }
    rewrite (body_ctx_wk _ _ Hn), List.app_assoc, <- tele_wk_app, <- (length_body_ctx _ Hn), <- wk_qn_plus, <- List.length_app.
    eapply IHE. constructor; [apply List.app_assoc | exact Hφ |].
    rewrite List.length_app, wk_qn_plus, (length_body_ctx _ Hn). exact Hago.
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
    set (bctx := elim_bctx r p D Mj gs (blocks_motives Bks) Us) in *.
    assert (Hw : tele_wk bctx (wk_qn (List.length Ψ) φ) =
                 elim_bctx r p D Mj gs (blocks_motives (blocks_wk Bks (wk_qn (List.length Ψ) φ)))
                   (List.map (fun U => exp_wk U (wk_qn (List.length Ψ) φ)) Us)).
    { apply elim_bctx_wk with (k := j) (c := c); [exact (elim_shape_closed _ _ _ _ Hsh) | exact HMj | exact (cons_lookup_in _ _ _ Hgs)
                          | exact (elim_shape_uniform _ _ _ _ Hsh) |].
      intros j' Mj' HMj'. apply (blocks_motives_wk D); [exact (elim_shape_binders _ _ _ _ Hsh) | exact HMj']. }
    assert (Hn : n = List.length bctx).
    { pose proof (elim_shape_counts _ _ _ _ Hsh _ _ _ _ _ _ _ HMj Hb Hgs (brs_lookup_in _ _ _ _ HB)) as E.
      subst bctx. rewrite length_elim_bctx. lia. }
    eapply set_elim_con; [exact HD | exact HMj | exact Href | exact HDq | exact HMk | exact Hgs | exact Hv | exact Hns | exact Hvs
                         | apply nth_error_blocks_wk; exact Hb
                         | exact (brs_lookup_map (fun br => exp_wk (snd br) (wk_qn (snd (fst br)) (wk_qn (List.length Ψ) φ))) Bs c n B HB)
                         | eapply IHihs; [constructor; [reflexivity | assumption | assumption] | exact Hsh]
                         | rewrite length_elim_bctx; subst bctx; rewrite length_elim_bctx in Hlen; exact Hlen | |].
    { fold bctx. rewrite <- Hw.
      pose proof (ctx_wk (bctx ++ Ψ) Γ0 Δ φ ltac:(rewrite <- List.app_assoc; exact Hc) Hφ) as H.
      rewrite tele_wk_app, <- List.app_assoc in H. exact H. }
    cbn beta. fold bctx. rewrite <- Hw, ctx_kinds_tele_wk, Hn.
    pose proof (IHB (bctx ++ Ψ) Γ0 Δ φ (set_env_extend_kinded ρ' (ctx_kinds bctx) (ns ++ vs ++ ihs))) as H.
    rewrite tele_wk_app, <- List.app_assoc, List.length_app, wk_qn_plus in H. apply H.
    constructor; [apply List.app_assoc | exact Hφ |]. rewrite List.length_app, wk_qn_plus, <- Hlen.
    apply env_agrees_extend_kinded. exact Hag.
  - intros; constructor.
  - intros Ξ ρ r p Us Bks κ T0 gs v vs ihs _ IH; start_elim; constructor.
    eapply IH; [constructor; [reflexivity | assumption | assumption] | exact Hsh].
  - intros Ξ ρ r p Us Bks t gs v vs ihs1 ihs2 _ IH1 _ IH2; start_elim; constructor;
      [eapply IH1 | eapply IH2]; (split; [reflexivity | assumption | assumption]) || exact Hsh.
  - intros Ξ ρ r p Us Bks D j Mj Ps v r0 HD HMj Hrv _ IH; start_elim. eapply set_ih_self; [exact HD | exact HMj | exact Hrv |].
    eapply IH; [constructor; [reflexivity | assumption | assumption] | exact Hsh].
  - intros Ξ ρ r p Us Bks D j Mj qr Is fl c gs Ps v rs HD HMj Hh Hc _ IH; start_elim.
    eapply set_ih_rview; [exact HD | exact HMj | exact Hh | exact Hc |].
    eapply IH; [constructor; [reflexivity | assumption | assumption] | exact Hsh].
  - intros Ξ ρ r p Us Bks D B t v Rs HD _ IH; start_elim. eapply set_ih_pi; [exact HD |].
    intros b Hb. eapply IH; [exact Hb | constructor; [reflexivity | assumption | assumption] | exact Hsh].
Qed.

(** A term, weakened under the extension [Ψ] by a renaming [φ] of the
    context below, keeps its value. *)
Lemma set_interp_wk : forall Ξ ρ M v, set_interp T γ Ξ ρ M v ->
    forall Ψ Γ Δ φ ρ', Ξ = Ψ ++ Γ -> gc_deps ⍮ gc_stack ⍮ Δ ⊢ʷ φ : Γ ->
    (forall x, ρ x = ρ' (wk_qn (List.length Ψ) φ x)) ->
    set_interp T γ (tele_wk Ψ φ ++ Δ) ρ' (exp_wk M (wk_qn (List.length Ψ) φ)) v.
Proof. intros * H * HΞ Hφ Hag. exact (proj1 set_interp_wk_all _ _ _ _ H _ _ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ HΞ Hφ Hag)). Qed.

End Weakening.
