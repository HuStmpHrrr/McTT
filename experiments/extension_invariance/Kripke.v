(** * (d) Kripke Closure of the Completeness Judgments over Extensions

    The judgments of [Core/Completeness/LogicalRelation/Definitions.v] are not
    monotone along [gc_ext] by any argument that treats the term as a black box
    ([env_not_antimono]: the judgment at the bigger context quantifies over
    environments the smaller one knows nothing about).  The minimal change is to
    close each judgment under extensions — a box modality on [GCtx]:

      [□ J G := forall G', gc_ext G G' -> J G']

    This file shows that (i) boxed judgments are monotone by construction,
    (ii) every existing case lemma — all of which are proved for an arbitrary
    instance [GC] — lifts to the boxed judgments with a one-line, generic
    proof, so the existing fundamental theorem survives unchanged, and
    (iii) the recorded semantic validity of globals then transports along the
    grow step (1), the new member's validity being exactly what the
    fundamental theorem gives at the context the member was checked at. *)

From Stdlib Require Import List String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import ModSubst.
From Mctt.Core.Completeness Require Import LogicalRelation NatCases FunctionCases.
From ExtInv Require Import Ext.
Import Domain_Notations GlobalCtx_Notations.

(** ** The modality *)

Definition box (J : GCtx -> Prop) (G : GCtx) : Prop :=
  forall G', gc_ext G G' -> J G'.

Lemma box_elim : forall J G, box J G -> J G.
Proof. intros * H; apply H, gc_ext_refl. Qed.

(** Monotone by construction: this is all "used later up to weakening" asks. *)
Lemma box_mono : forall J G G', gc_ext G G' -> box J G -> box J G'.
Proof. intros J G G1 H12 H G2 H2; apply H; exact (gc_ext_trans _ _ _ H12 H2). Qed.

Lemma box_dup : forall J G, box J G -> box (box J) G.
Proof. intros J G H G1 H1 G2 H2; apply H; exact (gc_ext_trans _ _ _ H1 H2). Qed.

(** How a case lemma of the fundamental theorem lifts: the lemma is proved at
    every instance, so it holds at every extension. *)
Lemma box_intro : forall (J : GCtx -> Prop) G, (forall G', J G') -> box J G.
Proof. intros * H G' _; apply H. Qed.

Lemma box_lift1 : forall (J1 J2 : GCtx -> Prop) G,
    (forall G', J1 G' -> J2 G') -> box J1 G -> box J2 G.
Proof. intros * H H1 G' Hx; apply H, H1, Hx. Qed.

Lemma box_lift2 : forall (J1 J2 J3 : GCtx -> Prop) G,
    (forall G', J1 G' -> J2 G' -> J3 G') -> box J1 G -> box J2 G -> box J3 G.
Proof. intros * H H1 H2 G' Hx; apply H; [ apply H1 | apply H2 ]; exact Hx. Qed.

Lemma box_lift3 : forall (J1 J2 J3 J4 : GCtx -> Prop) G,
    (forall G', J1 G' -> J2 G' -> J3 G' -> J4 G') -> box J1 G -> box J2 G -> box J3 G -> box J4 G.
Proof. intros * H H1 H2 H3 G' Hx; apply H; [ apply H1 | apply H2 | apply H3 ]; exact Hx. Qed.

(** ** The boxed judgments *)

Definition bsem_ctx Γ : GCtx -> Prop := box (fun G => @sem_ctx G Γ).
Definition brel_exp Γ A M M' : GCtx -> Prop := box (fun G => @rel_exp_under_ctx G Γ A M M').
Definition bvalid_exp Γ A M : GCtx -> Prop := brel_exp Γ A M M.
Definition bsubtyp Γ A A' : GCtx -> Prop := box (fun G => @subtyp_under_ctx G Γ A A').

(** A few real case lemmas, lifted.  The proofs are all the same line; a
    tactic ([box_lift_tac] below) does the whole fundamental theorem's worth. *)

Ltac box_lift_tac lem :=
  intros; unfold bsem_ctx, bvalid_exp, brel_exp, bsubtyp, box in *;
  let G' := fresh "G'" in
  let Hx := fresh "Hx" in
  intros G' Hx; eapply lem; eauto.

Lemma brel_exp_sym : forall G Γ A M M', brel_exp Γ A M M' G -> brel_exp Γ A M' M G.
Proof. box_lift_tac @rel_exp_under_ctx_sym. Qed.

Lemma brel_exp_trans : forall G Γ A M1 M2 M3,
    brel_exp Γ A M1 M2 G -> brel_exp Γ A M2 M3 G -> brel_exp Γ A M1 M3 G.
Proof. box_lift_tac @rel_exp_under_ctx_trans. Qed.

Lemma brel_exp_succ_cong : forall G Γ M M',
    brel_exp Γ ℕ M M' G -> brel_exp Γ ℕ (succ M) (succ M') G.
Proof. box_lift_tac @rel_exp_succ_cong. Qed.

Lemma bvalid_exp_zero : forall G Γ, bsem_ctx Γ G -> bvalid_exp Γ ℕ zero G.
Proof. box_lift_tac @valid_exp_zero. Qed.

Lemma brel_exp_app_cong : forall G Γ A i B M M' N N',
    brel_exp Γ (Type@i) A A G ->
    brel_exp (Γ ▹ A) (Type@i) B B G ->
    brel_exp Γ (Π A B) M M' G ->
    brel_exp Γ A N N' G ->
    brel_exp Γ B[Id ,, N] (M $ N) (M' $ N') G.
Proof. box_lift_tac @rel_exp_app_cong. Qed.

Lemma brel_exp_pi_beta : forall G Γ A i B M N,
    brel_exp Γ (Type@i) A A G ->
    brel_exp (Γ ▹ A) (Type@i) B B G ->
    brel_exp (Γ ▹ A) B M M G ->
    brel_exp Γ A N N G ->
    brel_exp Γ B[Id ,, N] ((λ A M) $ N) M[Id,,N] G.
Proof. box_lift_tac @rel_exp_pi_beta. Qed.

(** Nothing is lost at the context itself: the boxed judgment implies the old
    one, so the consequences of completeness ([nbe] agreement) are extracted
    unchanged. *)
Lemma brel_exp_unbox : forall G Γ A M M', brel_exp Γ A M M' G -> @rel_exp_under_ctx G Γ A M M'.
Proof. intros *; apply box_elim. Qed.

(** ** Recorded validity of globals *)

(** What is recorded when an entry is inserted: its type, and (if it has one)
    its body, both valid in [⋅] *at every extension*. *)
Definition valid_entry (Δ : ctx) (E : gentry) : GCtx -> Prop :=
  match E with
  | ge_def b pv A B =>
      fun G =>
        box (fun G' => exists i, @valid_exp_under_ctx G' nil (Type@i) (ctx_pi Δ A)) G /\
        (forall M, B = Some M -> box (fun G' => @valid_exp_under_ctx G' nil (ctx_pi Δ A) (ctx_fn Δ M)) G)
  | ge_mod _ _ => fun _ => True
  end.

(** What [⊢g] means semantically: every resolvable global is valid. *)
Definition sem_globals (G : GCtx) : Prop :=
  forall p Δ E, gc_resolve (@gc_deps G) (@gc_stack G) p = Some (Δ, E) -> valid_entry Δ E G.

Lemma valid_entry_mono : forall Δ E G G', gc_ext G G' -> valid_entry Δ E G -> valid_entry Δ E G'.
Proof.
  intros Δ [b pv A B | ? ?] * Hext; cbn; [| auto ].
  intros [HA HB]; split; [ exact (box_mono _ _ _ Hext HA) |].
  intros M HM; exact (box_mono _ _ _ Hext (HB M HM)).
Qed.

(** Along any extension, validity of the old globals is transported for free;
    only the *new* ones need an argument. *)
Theorem sem_globals_ext : forall G1 G2,
    gc_ext G1 G2 ->
    sem_globals G1 ->
    (forall p Δ E,
        gc_resolve (@gc_deps G2) (@gc_stack G2) p = Some (Δ, E) ->
        gc_resolve (@gc_deps G1) (@gc_stack G1) p = None ->
        valid_entry Δ E G2) ->
    sem_globals G2.
Proof.
  intros * Hext H1 Hnew p Δ E Hr.
  destruct (gc_resolve (@gc_deps G1) (@gc_stack G1) p) as [[Δ1 E1] |] eqn:Hr1.
  - pose proof (proj1 Hext _ _ Hr1) as Hr1'; rewrite Hr in Hr1'; injection Hr1' as <- <-.
    apply (valid_entry_mono _ _ G1 G2); [ eassumption | eapply H1; eassumption ].
  - eapply Hnew; eassumption.
Qed.

(** *** The grow step (1): a member [x := E] added to the current frame *)

Lemma msub_option_shift_zero : forall (B : option exp), B[↑ₘ 0]ᵐ = B.
Proof. intros [M |]; cbn; [ f_equal; apply exp_msub_shift_zero | reflexivity ]. Qed.

Lemma gc_resolve_grow_cases : forall Θ Ξ Δ0 Φ x b pv A B p r,
    gc_resolve Θ (gu_mk Δ0 (Φ ⊳ x ↦ ge_def b pv A B) :: Ξ) p = Some r ->
    (p = p_rel 0 (x :: nil) /\ r = (nil, ge_def b pv A B)) \/
    gc_resolve Θ (gu_mk Δ0 Φ :: Ξ) p = Some r.
Proof.
  intros * H; destruct p as [[fp | [| n]] ip]; unfold gc_resolve in *; cbn in *; auto.
  destruct ip as [| y ip]; [ discriminate |].
  destruct (String.eqb_spec y x) as [-> |]; [| auto ].
  destruct ip as [| z ip]; [| auto ].
  left; split; [ reflexivity |].
  cbn in H; injection H as <-.
  change (ctx_msub (↑ₘ 0) nil) with (@nil exp).
  change (msubst (↑ₘ 0) A) with A[↑ₘ 0]ᵐ.
  rewrite exp_msub_shift_zero, msub_option_shift_zero; reflexivity.
Qed.

(** The new member was checked (by [wf_gmod_ext] under [wf_gstack_cons]) at
    exactly the frame before the growth, [G1]; the fundamental theorem there,
    in its boxed form, is the hypothesis [Hx].  Then all of [G2] is valid. *)
Theorem sem_globals_grow : forall Θ Ξ Δ0 Φ x b pv A B,
    gm_canon (Φ ⊳ x ↦ ge_def b pv A B) ->
    let G1 := gc_mk Θ (gu_mk Δ0 Φ :: Ξ) in
    let G2 := gc_mk Θ (gu_mk Δ0 (Φ ⊳ x ↦ ge_def b pv A B) :: Ξ) in
    sem_globals G1 ->
    valid_entry nil (ge_def b pv A B) G1 ->
    sem_globals G2.
Proof.
  intros * Hc G1 G2 H1 Hx.
  assert (Hext : gc_ext G1 G2) by (apply gc_ext_grow_member; assumption).
  intros p Δ E Hr.
  destruct (gc_resolve_grow_cases _ _ _ _ _ _ _ _ _ _ _ Hr) as [[-> [= -> ->]] | Hr1].
  - apply (valid_entry_mono _ _ G1 G2); eassumption.
  - apply (valid_entry_mono _ _ G1 G2); [ exact Hext | exact (H1 _ _ _ Hr1) ].
Qed.

(** *** Level filing (4): the old globals transport by [sem_globals_ext] and
    [gc_ext_file_level]; the new ones are the paths [p_abs fp ip] of the
    filed units, whose validity comes from checking the unit at [Θ ⍮ nil] and
    then *closing* it — a renaming, step (3), outside this experiment. *)
Corollary sem_globals_file_level : forall Θ Ξ d,
    (forall fp, List.In fp (List.map fst d) -> gds_fresh fp Θ) ->
    sem_globals (gc_mk Θ Ξ) ->
    (forall p Δ E,
        gc_resolve (d :: Θ) Ξ p = Some (Δ, E) ->
        gc_resolve Θ Ξ p = None ->
        valid_entry Δ E (gc_mk (d :: Θ) Ξ)) ->
    sem_globals (gc_mk (d :: Θ) Ξ).
Proof.
  intros * Hfr H1 Hnew; eapply sem_globals_ext; [| eassumption | exact Hnew ].
  apply gc_ext_file_level; assumption.
Qed.

(** *** The glob case of the boxed fundamental theorem

    Suppose the unboxed δ-case is available at every fixed instance (this is a
    lemma about one global context, to be proved in [Completeness]; it is the
    hypothesis [delta_case] here).  Then the boxed δ-case follows from
    [sem_globals] alone: resolution is kept by [gc_ext], and the recorded body
    validity is boxed. *)
Theorem bglob_delta_case :
  (forall (GC : GCtx) Γ p Δ pv A M,
      @sem_ctx GC Γ ->
      gc_resolve gc_deps gc_stack p = Some (Δ, ge_def true pv A (Some M)) ->
      @valid_exp_under_ctx GC nil (ctx_pi Δ A) (ctx_fn Δ M) ->
      @rel_exp_under_ctx GC Γ (ctx_pi Δ A) (a_glob p) (ctx_fn Δ M)) ->
  forall G Γ p Δ pv A M,
    sem_globals G ->
    bsem_ctx Γ G ->
    gc_resolve (@gc_deps G) (@gc_stack G) p = Some (Δ, ge_def true pv A (Some M)) ->
    brel_exp Γ (ctx_pi Δ A) (a_glob p) (ctx_fn Δ M) G.
Proof.
  intros delta_case * HG HΓ Hr G' Hext.
  apply (delta_case G' Γ p Δ pv A M); [ apply HΓ, Hext | apply (proj1 Hext _ _ Hr) |].
  destruct (HG _ _ _ Hr) as [_ HB].
  apply (HB M eq_refl), Hext.
Qed.
