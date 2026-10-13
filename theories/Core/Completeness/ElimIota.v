(** * The [ι] Rule of an Inductive Type

    The eliminator at a constructor is its branch at the arguments and the
    recursive results ([elim_ihs]): at a recursive argument [f] of a
    function shape, the recursive result is [λx. elim (f x)], under the
    shape's domains.  Its evaluation is not the eliminator's own value at
    [f] ([d_ihfn]), so the rule relates the two at the type of the
    recursive result: the eliminator at weakened data, in an environment
    extended by the domains' values, against the eliminator at its own
    ([elim_shift]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping IndSyntax GlobalPresup IndTyping MemberLemmas.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases GlobalSem MemberReps
  VariableCases FunctionCases LevelCases IndSem TeleSem IndCases NatCases SubtypingCases ElimCases.
From Mctt.Core.Semantic Require Import Realizability IndPER IndElim Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma gsub_args : forall Γ p D Us Ns c gs As, decl_closed D -> ⊨ Γ -> ind_con D c = Some gs ->
    List.length Ns = ind_nn D ->
    ⊨ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ -> ⊨ cinst Γ p D Us gs ->
    (forall k N T, List.nth_error Ns k = Some N ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Γ ⊨ N : T) ->
    gsub Γ (sb_of_list Id (Ns ++ As)) (cinst Γ p D Us gs).
Proof.
  intros * Hc HΓ Hcon HNl HNt HC HNs HAl HAs.
  assert (HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ)).
  { apply gsub_of_list; [ constructor; exact HΓ | apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact HNt
                        | rewrite length_ind_nparams_sub; exact HNl |].
    intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by (intros x; cbn; apply sentry_sub_id).
    exact (HNs _ _ _ HN HT). }
  rewrite sb_of_list_app; unfold cinst in HC |- *.
  apply gsub_of_list; [ exact HgN | apply tele_ass_sub, cargs_ctx_aux_ass | exact HC
                      | rewrite length_tele_sub, length_cargs_ctx; exact HAl |].
  intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
  rewrite (tele_insts_sb_eq _ _ (sb_of_list Id (Us ++ Ns))) in HT; [ exact (HAs _ _ _ HN HT) |].
  rewrite <- HNl; etransitivity; [ apply sb_qn_of_list |].
  etransitivity; [ apply sb_of_list_cong; intros x; cbn; apply sentry_sub_id |].
  rewrite <- sb_of_list_app; reflexivity.
Qed.

Lemma params_valid_join : forall D Γ Us Ns, decl_closed D -> List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T) ->
    (forall k N T, List.nth_error Ns k = Some N ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T) ->
    forall k P T, List.nth_error (Us ++ Ns) k = Some P -> List.nth_error (tele_insts (ind_params D) Id (Us ++ Ns)) k = Some T -> Γ ⊨ P : T.
Proof.
  intros * Hc HUl HUs HNs k P T HP HT.
  pose proof (decl_closed_nu D Hc) as Hle.
  rewrite params_split, tele_insts_app in HT by (try apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; reflexivity).
  assert (Hl2 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; lia).
  destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HP by lia; rewrite List.nth_error_app1 in HT by lia; exact (HUs _ _ _ HP HT).
  - rewrite List.nth_error_app2 in HP, HT by lia; rewrite HUl in HP; rewrite Hl2 in HT; exact (HNs _ _ _ HP HT).
Qed.

Lemma eval_elim_inv : forall p nm A Bs M ρ r, ⟦ a_elim p nm A Bs M ⟧ ρ ↘ r ->
    exists m, ⟦ M ⟧ ρ ↘ m /\ ⟦elim m under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma eval_elim_con_inv : forall ρ nm A Bs p c vs r, ⟦elim d_con p c vs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
    exists D gs n B ihs, ind_lookup gc_deps gc_stack p = Some D /\ ind_con D c = Some gs /\ brs_lookup Bs c = Some (n, B) /\
      ⟦ihs List.skipn (ind_np D) vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
      ⟦ B ⟧ env_args ρ (List.skipn (ind_nu D) (List.firstn (ind_np D) vs) ++ List.skipn (ind_np D) vs ++ ihs) ↘ r.
Proof. intros * H; inversion H; subst; do 5 eexists; repeat split; eassumption. Qed.

Lemma eval_apps_con' : forall D p, ind_lookup gc_deps gc_stack p = Some D ->
    forall c gs ys xs, ind_con D c = Some gs -> List.length xs + List.length ys <= ind_np D + List.length gs ->
    $*| d_con p c xs & ys | gc_deps ⍮ gc_stack ↘ d_con p c (xs ++ ys).
Proof.
  intros D p Hl c gs; induction ys as [| y ys IH]; intros xs Hcon Hlen; [ rewrite List.app_nil_r; constructor |].
  econstructor; [ eapply eval_app_con; [ exact Hl | exact Hcon | cbn in *; lia ] |].
  replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
  apply IH; [ exact Hcon | rewrite List.length_app; cbn in *; lia ].
Qed.

(** ** Weakening Under a Telescope *)
Lemma tele_wk_sem : forall Δ Γ0 Γ' φ, tele_ass Δ -> ⊨ Δ ++ Γ0 -> ⊨ Γ' -> Γ' ⊨w φ : Γ0 ->
    ⊨ tele_wk Δ φ ++ Γ' /\ tele_wk Δ φ ++ Γ' ⊨w (wk_qn (List.length Δ) φ) : Δ ++ Γ0.
Proof.
  induction Δ as [| e Δ IH]; intros * Ha HΔ HΓ' Hφ; cbn [tele_wk List.app List.length wk_qn]; [ split; assumption |].
  assert (He : exists A, e = ce_ass A) by (inversion Ha as [| ? ? He _]; exact He).
  destruct He as [A0 ->].
  assert (Ha' : tele_ass Δ) by (inversion Ha; assumption).
  destruct (sem_ctx_ass_inv HΔ) as [j HA0].
  destruct (IH _ _ _ Ha' (sem_ctx_tail HΔ) HΓ' Hφ) as [HC Hw].
  pose proof (rel_exp_under_ctx_wk Hw HA0) as HA1; cbn [exp_wk] in HA1.
  cbn [centry_wk].
  split; [ exact (sem_ctx_ext_typ _ _ _ HC HA1) | exact (rel_wk_under_ctx_q Hw HA0) ].
Qed.

(** The premises of an eliminator, weakened. *)
Lemma elim_premises_wk_sem : forall Γ0 Ψ φ p D Us A (i : nat) Bs, decl_closed D -> List.length Us = ind_nu D -> ⊨ Ψ ->
    Ψ ⊨w φ : Γ0 ->
    elim_mctx p D Us ++ Γ0 ⊨ A : Typeω@i -> ⊨ elim_mctx p D Us ++ Γ0 ->
    (forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A Us ++ Γ0) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> elim_bctx p D gs A Us ++ Γ0 ⊨ B : elim_bty p D c gs A Us) ->
    elim_mctx p D (List.map (fun U => U[φ]ʷ) Us) ++ Ψ ⊨ A[wk_qn (S (ind_nn D)) φ]ʷ : Typeω@i /\
    ⊨ elim_mctx p D (List.map (fun U => U[φ]ʷ) Us) ++ Ψ /\
    (forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us) ++ Ψ) /\
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_wk Bs φ) -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) /\
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_wk Bs φ) ->
       elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us) ++ Ψ
         ⊨ B : elim_bty p D c gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us)).
Proof.
  intros * Hc HUl HΨ Hφ HA HM HBc Hk HB.
  destruct (tele_wk_sem _ _ _ _ (elim_mctx_ass p D Us Hc) HM HΨ Hφ) as [HM' HwM].
  rewrite elim_mctx_wk, length_elim_mctx in * by assumption.
  split; [ pose proof (rel_exp_under_ctx_wk HwM HA) as H; cbn [exp_wk] in H; exact H | split; [ exact HM' |] ].
  assert (HBc' : forall c gs, ind_con D c = Some gs ->
                 ⊨ elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us) ++ Ψ /\
                 elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us) ++ Ψ
                   ⊨w (wk_qn (cargs_nrec gs + List.length gs + ind_nn D) φ) : elim_bctx p D gs A Us ++ Γ0).
  { intros c gs Hcon.
    destruct (tele_wk_sem _ _ _ _ (elim_bctx_ass p D gs A Us Hc) (HBc c gs Hcon) HΨ Hφ) as [H1 H2].
    rewrite (elim_bctx_wk p D c gs A Us φ Hc (cons_lookup_in _ _ _ Hcon) HUl) in H1, H2; rewrite length_elim_bctx in H2.
    split; assumption. }
  split; [ intros c gs Hcon; exact (proj1 (HBc' c gs Hcon)) | split ].
  - intros c gs n B' Hcon Hin; unfold brs_wk in Hin; apply brs_in_map in Hin as (B & Hin & ->); eapply Hk; eassumption.
  - intros c gs n B' Hcon Hin; unfold brs_wk in Hin; apply brs_in_map in Hin as (B & Hin & ->); cbn [fst snd].
    rewrite (Hk _ _ _ _ Hcon Hin), <- elim_bty_wk.
    replace (ind_nn D + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + ind_nn D) by lia.
    exact (rel_exp_under_ctx_wk (proj2 (HBc' c gs Hcon)) (HB _ _ _ _ Hcon Hin)).
Qed.

(** ** The Data of a Recursive Result under the Domains *)
Fixpoint ihA (nm k : nat) (A : exp) : exp :=
  match k with 0 => A | S k => (ihA nm k A)[wk_qn nm wk_shift]ʷ end.
Fixpoint ihBs (k : nat) (Bs : list (String.string * nat * exp)) : list (String.string * nat * exp) :=
  match k with 0 => Bs | S k => brs_wk (ihBs k Bs) wk_shift end.

Lemma ihA_eq : forall nm k A, ihA nm k A = A[wk_qn nm (wk_shiftn k)]ʷ.
Proof.
  intros nm; induction k as [| k IH]; intros A; cbn [ihA].
  - symmetry; apply exp_wk_id_ext, wk_qn_id_ext, wk_shiftn_zero.
  - rewrite IH, exp_wk_wk; apply exp_wk_wk_eq.
    etransitivity; [ apply wk_qn_compose |]; apply wk_qn_cong; intros z; cbn; lia.
Qed.

Lemma eval_exps_firstn' : forall Ms ρ ms k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ List.firstn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn k ms.
Proof.
  induction Ms as [| M Ms IH]; intros * H; inversion H; subst; destruct k; cbn; try constructor; [ assumption | apply IH; assumption ].
Qed.

Lemma brs_wk_eq : forall Bs φ ψ, wk_eq φ ψ -> brs_wk Bs φ = brs_wk Bs ψ.
Proof. intros * E; unfold brs_wk; apply List.map_ext; intros b; f_equal; apply exp_wk_wk_eq, wk_qn_cong, E. Qed.

Lemma ihBs_eq : forall k Bs, ihBs k Bs = brs_wk Bs (wk_shiftn k).
Proof.
  induction k as [| k IH]; intros Bs; cbn [ihBs].
  - unfold brs_wk; rewrite <- (List.map_id Bs) at 1; apply List.map_ext; intros [[c n] B]; cbn.
    rewrite exp_wk_id_ext; [ reflexivity | apply wk_qn_id_ext, wk_shiftn_zero ].
  - rewrite IH, brs_wk_wk; apply brs_wk_eq; intros z; cbn; lia.
Qed.

Lemma args_rel_at : forall p D ups nr ar dr pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists x x', List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
      ind_shape_rel p D ups nr ar dr (pre ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t x x'.
Proof.
  induction 1; intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst;
    try match goal with IH : forall _ _ _, _ = _ -> _ |- _ => destruct (IH _ _ _ eq_refl) as (x & x' & Hx & Hx' & Hr0) end.
  - exists x, x'; cbn; rewrite <- List.app_assoc in Hr0; repeat split; assumption.
  - do 2 eexists; cbn; rewrite List.app_nil_r; repeat split; eassumption.
  - exists x, x'; cbn; repeat split; assumption.
Qed.

Lemma brs_sub_of_wk : forall Bs φ, ElimCases.brs_sub Bs (sb_of_wk φ) = brs_wk Bs φ.
Proof. intros; unfold ElimCases.brs_sub, brs_wk; apply List.map_ext; intros b; f_equal; apply exp_sub_qn_of_wk. Qed.

Lemma fe_apps : forall m args r1 r2, $*| m & args | gc_deps ⍮ gc_stack ↘ r1 -> $*| m & args | gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros * H1 H2; exact (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_eval gc_deps gc_stack))))) _ _ _ H1 _ H2). Qed.

Section Iota.
  Variable (Γ : ctx) (p : qname) (D : ind_decl) (Us Ns As : list exp) (c : String.string) (gs : list carg)
    (nm : nat) (A : exp) (i : nat) (Bs : list (String.string * nat * exp)).
  Hypothesis (HD : sem_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)) (Hdt : decl_typed gc_deps gc_stack D)
    (Hl : ind_lookup gc_deps gc_stack p = Some D) (HΓ : ⊨ Γ) (Hcon : ind_con D c = Some gs)
    (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T)
    (HNl : List.length Ns = ind_nn D) (HAl : List.length As = List.length gs)
    (Hnm : nm = S (ind_nn D)) (HA : elim_mctx p D Us ++ Γ ⊨ A : Typeω@i) (HM : ⊨ elim_mctx p D Us ++ Γ)
    (HBn : brs_names (ind_cons D) Bs)
    (HBc : forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A Us ++ Γ)
    (Hnb : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat)
    (HBv : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
             elim_bctx p D gs A Us ++ Γ ⊨ B : elim_bty p D c gs A Us)
    (HNs : forall k N T, List.nth_error Ns k = Some N ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T)
    (HAs : forall k N T, List.nth_error As k = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Γ ⊨ N : T).
  Let HDc : sem_core D := HD.
  Let Hle : ind_nu D <= ind_np D := decl_closed_nu D Hc.
  Let σP := sb_of_list Id (Us ++ Ns).

  Lemma elim_valid_at : forall Q a, List.length Q = ind_nn D -> gsub Γ (sb_of_list Id (Q ++ a :: nil)) (elim_mctx p D Us ++ Γ) ->
      Γ ⊨ a : apps (a_ind p) (Us ++ Q) -> Γ ⊨ a_elim p nm A Bs a : A[sb_of_list Id (Q ++ a :: nil)].
  Proof.
    intros * HQl Hg Ha.
    eapply (rel_exp_elim_at Γ p D Us Q a a nm A A i Bs Bs); try eassumption; [ reflexivity |].
    intros * Hk Hk' Hcon'; rewrite Hk in Hk'; injection Hk' as <-.
    exact (HBv _ _ _ _ Hcon' (List.nth_error_In _ _ Hk)).
  Qed.

  (** *** The Parameters and the Arguments Before a Position *)
  Lemma gsub_P : gsub Γ σP (ind_params D ++ Γ).
  Proof.
    apply gsub_closed_inst; [ apply decl_closed_params, Hc | exact (sd_params _ HDc) | exact HΓ
                            | rewrite List.length_app, HUl, HNl; unfold ind_nn, ind_np in *; lia |].
    apply params_valid_join; assumption.
  Qed.

  Lemma gsub_args_pre : forall k, k <= List.length gs ->
      gsub Γ (sb_of_list σP (List.firstn k As)) (cargs_ctx p D (List.firstn k gs) ++ ind_params D ++ Γ).
  Proof.
    intros k Hk.
    pose proof (sd_cargs D HD p c gs Hl Hcon) as HΨ.
    assert (Heq : gs = List.firstn k gs ++ List.skipn k gs) by (symmetry; apply List.firstn_skipn).
    pose proof (cargs_prefix_sem D p gs HΨ _ _ Heq) as Hp.
    assert (Hpa : tele_ass (cargs_ctx p D (List.firstn k gs) ++ ind_params D))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
    destruct (closed_app_sem _ _ Hpa Hp HΓ) as [HpΓ _]; rewrite <- List.app_assoc in HpΓ.
    apply gsub_of_list; [ exact gsub_P | apply cargs_ctx_aux_ass | exact HpΓ
                        | rewrite List.length_firstn, length_cargs_ctx, List.length_firstn; lia |].
    intros j N T HN HT.
    assert (Hj : j < List.length (List.firstn k As)) by (apply List.nth_error_Some; congruence).
    rewrite List.length_firstn in Hj.
    apply (HAs j); [ rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec j k); [ exact HN | lia ] |].
    rewrite Heq at 1; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r.
    rewrite <- (List.firstn_skipn k As), tele_insts_app;
      [| apply cargs_ctx_aux_ass | rewrite List.length_firstn, length_cargs_ctx_aux, List.length_firstn; lia ].
    rewrite List.nth_error_app1; [ exact HT |].
    rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux, !List.length_firstn; lia.
  Qed.

  (** The substitution of a shape's components after [gs1]. *)
  Lemma gsub_sigt : forall gs1 gs2, gs = gs1 ++ gs2 ->
      gsub Γ (cargs_sub σP gs1 As) (cargs_strat gs1 ++ ind_params D ++ Γ).
  Proof.
    intros * Heq.
    assert (Lg1 : List.length gs1 <= List.length gs) by (rewrite Heq, List.length_app; lia).
    pose proof (gsub_args_pre _ Lg1) as Hg.
    assert (Hfg : List.firstn (List.length gs1) gs = gs1) by (rewrite Heq; apply firstn_app_exact; reflexivity).
    rewrite Hfg in Hg.
    destruct (gsub_props Hg) as [Hgv Hgl].
    pose proof (sd_cargs D HD p c gs Hl Hcon) as HΨ.
    pose proof (cargs_prefix_sem D p gs HΨ _ _ Heq) as Hp.
    assert (Hpa : tele_ass (cargs_ctx p D gs1 ++ ind_params D))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
    destruct (closed_app_sem _ _ Hpa Hp HΓ) as [HpΓ _]; rewrite <- List.app_assoc in HpΓ.
    assert (HSa : tele_ass (cargs_strat gs1 ++ ind_params D))
      by (apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass | apply decl_closed_params, Hc ]).
    assert (HSs : ⊨ cargs_strat gs1 ++ ind_params D)
      by (rewrite (astrat_prefix gs1 gs2), <- Heq; apply (sd_strat _ HDc _ _ _ Hcon); rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    destruct (closed_app_sem _ _ HSa HSs HΓ) as [HSΓ _]; rewrite <- List.app_assoc in HSΓ.
    pose proof (gsub_wk _ _ _ (cargs_wk_ext D HD Hc p Hl Γ HΓ Us HUl (List.repeat d_zero (ind_nu D)) (List.repeat_length _ _) c gs Hcon gs1 gs2 Heq) HpΓ HSΓ) as G0.
    eapply gsub_eq; [ exact (gsub_comp _ _ _ _ _ G0 HΓ Hgv Hgl) |].
    rewrite <- (cargs_sub_firstn gs1 σP As).
    apply cargs_sub_pat; rewrite List.length_firstn; lia.
  Qed.

  Lemma eval_sigt : forall gs1 gs2 ρ us ns avs, gs = gs1 ++ gs2 ->
      ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ us -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns -> ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ avs ->
      ⟦ cargs_sub σP gs1 As ⟧s ρ ↘ env_args ρ (us ++ ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) avs)).
  Proof.
    intros * Heq Hu Hn Ha.
    assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; lia).
    rewrite <- (cargs_sub_firstn gs1 σP As).
    eapply eval_sub_sb_eq; [ apply cargs_sub_pat; rewrite List.length_firstn; lia |].
    pose proof (eval_exps_firstn' As ρ avs (List.length gs1) Ha) as Ha1.
    assert (La1 : List.length (List.firstn (List.length gs1) avs) = List.length gs1)
      by (rewrite List.length_firstn, (eval_exps_length _ _ _ Ha); lia).
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) ltac:(apply eval_exps_app; [ exact Hu | exact Hn ])) Ha1) as Hτ.
    replace (env_args ρ (us ++ ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) avs)))
      with (⟪wk_pat (cargs_pat gs1)⟫ (env_args (env_args ρ (us ++ ns)) (List.firstn (List.length gs1) avs)))
      by (rewrite eval_wk_pat_args by exact La1; rewrite <- env_args_app, List.app_assoc; reflexivity).
    intros x; cbn [sb_compose sb_of_wk sentry_sub]; rewrite (eval_wk_entry _ _ (wk_mono_pat _)).
    exact (Hτ _).
  Qed.

  (** *** A Recursive Argument and Its Recursive Result *)
  Section RecArg.
    #[local] Set Default Proof Using "All".
    Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
    Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
    Let K := List.length (cargs_nonrec gs1).
    Let L := List.length (ptyp_doms t).
    Let σt := cargs_sub σP gs1 As.
    Let Mt := List.nth (List.length gs1) As (a_var 0).
    Let Ψ k := tele_sub (doms_ctx (List.firstn k (ptyp_doms t))) σt ++ Γ.
    Let Tg := cargs_strat gs1 ++ ind_params D ++ Γ.
    Let UsL := List.map (fun U => U[wk_shiftn L]ʷ) Us.
    Let Ps' := List.map (fun P => P[sb_qn L σt]) (ptyp_ps t).
    Let xL := ihx L Mt.

    Lemma r_simp : ptyp_simple t = true.
    Proof. exact (sd_simple _ HDc c gs gs1 t gs2 Hcon Heq). Qed.

    Lemma r_strat : cargs_strat gs1 = astrat gs (List.length (cargs_nonrec gs1)).
    Proof. rewrite Heq; apply astrat_prefix. Qed.

    Lemma r_dctx : forall k, k <= L -> ⊨ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
    Proof. intros k Hk; rewrite r_strat; exact (sd_dctx _ HDc _ _ _ _ _ k Hcon Heq Hk). Qed.

    Lemma r_dass : forall k, tele_ass (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D).
    Proof.
      intros; apply List.Forall_app; split; [ apply List.Forall_rev, tele_ass_map_ass |].
      apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass | apply decl_closed_params, Hc ].
    Qed.

    Lemma r_dlen : forall k, k <= L -> List.length (doms_ctx (List.firstn k (ptyp_doms t))) = k.
    Proof. intros; rewrite doms_ctx_length, List.length_firstn; unfold L in *; lia. Qed.

    Lemma r_dctxΓ : forall k, k <= L -> ⊨ doms_ctx (List.firstn k (ptyp_doms t)) ++ Tg.
    Proof.
      intros k Hk; destruct (closed_app_sem _ _ (r_dass k) (r_dctx k Hk) HΓ) as [H _].
      unfold Tg; rewrite <- !List.app_assoc in H; exact H.
    Qed.

    Lemma r_gsub : forall k, k <= L -> gsub (Ψ k) (sb_qn k σt) (doms_ctx (List.firstn k (ptyp_doms t)) ++ Tg).
    Proof.
      intros k Hk; unfold Ψ; rewrite <- (r_dlen k Hk) at 2.
      apply gsub_qn; [ exact (gsub_sigt gs1 _ Heq) | unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass | exact (r_dctxΓ k Hk) ].
    Qed.

    Lemma r_HΨ : forall k, k <= L -> ⊨ Ψ k.
    Proof. intros k Hk; exact (gsub_sem_ctx _ _ _ (r_gsub k Hk)). Qed.

    Lemma r_wk : forall k, k <= L -> Ψ k ⊨w (wk_shiftn k) : Γ.
    Proof.
      intros k Hk; pose proof (rel_wk_under_ctx_shiftn _ _ (r_HΨ k Hk)) as H.
      rewrite length_tele_sub, (r_dlen k Hk) in H; exact H.
    Qed.

    Lemma r_uc : shape_uc D Us (cargs_strat gs1 ++ ind_params D) σt Id.
    Proof.
      intros y Hy.
      assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      unfold σt; rewrite <- (cargs_sub_firstn gs1 σP As).
      rewrite <- (cargs_sub_pat gs1 σP (List.firstn (List.length gs1) As)) by (rewrite List.length_firstn; lia).
      cbn [sb_compose sb_of_wk sentry_sub].
      replace (y + (List.length (cargs_strat gs1 ++ ind_params D) - ind_nu D)) with (pat_nargs (cargs_pat gs1) + (ind_nn D + y))
        by (rewrite List.length_app, pat_nargs_cargs_pat; unfold ind_nn, ind_np in *; lia).
      rewrite wk_pat_ge, length_cargs_pat.
      replace (List.length gs1 + (ind_nn D + y)) with (List.length (List.firstn (List.length gs1) As) + (ind_nn D + y))
        by (rewrite List.length_firstn; lia).
      rewrite sb_of_list_ge; unfold σP; rewrite sb_of_list_app.
      replace (ind_nn D + y) with (List.length Ns + y) by lia.
      rewrite sb_of_list_ge; cbn [sb_compose]; rewrite sentry_sub_id; reflexivity.
    Qed.

    Lemma r_ucK : forall k, k <= L ->
        shape_uc D Us (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D) (sb_qn k σt) (ihb k Id).
    Proof.
      induction k as [| k IH]; intros Hk; [ exact r_uc |].
      destruct (nth_error_lt_some' (ptyp_doms t) k ltac:(unfold L in Hk; lia)) as [Bk HBk].
      rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc; cbn [sb_qn ihb List.app].
      apply shape_uc_pi; [| apply IH; lia ].
      rewrite !List.length_app, params_split, List.length_app, length_ind_uparams by exact Hle; lia.
    Qed.

    Lemma r_Mt : Γ ⊨ Mt : ptyp_ty_at p Us σt t.
    Proof.
      assert (Hk : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' As (List.length gs1) Hk) as [M HM0].
      unfold Mt; rewrite (List.nth_error_nth _ _ _ HM0).
      set (As1 := List.firstn (List.length gs1) As).
      assert (LAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (HAeq : As = As1 ++ M :: List.skipn (S (List.length gs1)) As)
        by (unfold As1; rewrite <- (skipn_nth_cons' _ _ _ HM0), List.firstn_skipn; reflexivity).
      apply (HAs (List.length gs1)); [ exact HM0 |].
      rewrite Heq at 1; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; cbn [cargs_ctx_aux].
      rewrite HAeq.
      rewrite (tele_insts_app (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2 ++ ce_ass (ptyp_ty p D (cargs_pat gs1) t) :: nil)
                 (cargs_ctx_aux p D nil gs1)); [| apply cargs_ctx_aux_ass | rewrite length_cargs_ctx_aux; exact LAs1 ].
      rewrite List.nth_error_app2 by (rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux; lia).
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux, LAs1.
      replace (List.length gs1 - Nat.min (List.length gs1) (List.length gs1)) with 0 by lia.
      change (M :: List.skipn (S (List.length gs1)) As) with ((M :: nil) ++ List.skipn (S (List.length gs1)) As).
      rewrite tele_insts_app; [| repeat constructor; eexists; reflexivity | reflexivity ].
      cbn; unfold tele_insts at 1; cbn [List.rev List.app tele_insts_aux]; f_equal.
      rewrite ptyp_ty_eq_at, ptyp_ty_at_sub.
      rewrite (ptyp_ty_at_sb_eq _ _ _ _ σt); [ f_equal |].
      - unfold ind_uvars; rewrite length_cargs_pat.
        unfold σP; rewrite <- sb_of_list_app, <- List.app_assoc.
        replace (List.length gs1 + ind_nn D) with (List.length (Ns ++ As1)) by (rewrite List.length_app; lia).
        rewrite <- HUl; apply vars_from_sb_of_list_app.
      - unfold σt; rewrite <- (cargs_sub_firstn gs1 σP As); fold As1.
        apply cargs_sub_pat; exact LAs1.
    Qed.

    Lemma r_Ps_valid : forall m P T0, List.nth_error (ptyp_ps t) m = Some P ->
        List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) m = Some T0 ->
        ptyp_tele t ++ Tg ⊨ P : T0.
    Proof.
      intros * HP HT; pose proof (sd_rec _ HDc _ _ _ _ _ _ _ _ Hcon Heq HP HT) as H; rewrite <- r_strat in H.
      assert (He : ptyp_tele t = doms_ctx (List.firstn L (ptyp_doms t))) by (unfold ptyp_tele, L; rewrite List.firstn_all; reflexivity).
      pose proof (r_dass L) as Ha; pose proof (r_dctx L (le_n _)) as Hs; rewrite <- He in Ha, Hs.
      pose proof (closed_app_valid _ _ _ _ _ Ha Hs HΓ H) as H'; unfold Tg; rewrite <- !List.app_assoc in H'; exact H'.
    Qed.

    Lemma r_tele : ptyp_tele t = doms_ctx (List.firstn L (ptyp_doms t)).
    Proof. unfold ptyp_tele, L; rewrite List.firstn_all; reflexivity. Qed.

    (** The leaf's parameters, at instances agreeing with the shape's
        substitution on the uniform parameters. *)
    Lemma r_Ps_gen : forall σ', (forall y, y < ind_nu D -> sentry_exp ((sb_of_list Id Us ⨟ ihb L Id) y) = sentry_exp (σ' y)) ->
        forall m N T0, List.nth_error Ps' m = Some N -> List.nth_error (tele_insts (ind_nparams D) σ' Ps') m = Some T0 -> Ψ L ⊨ N : T0.
    Proof.
      intros σ' Hσ' m N T0 HN HT.
      unfold Ps' in HN, HT; apply nth_error_map_inv in HN as (P & HPk & ->).
      set (σ0 := sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))).
      pose proof (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
      assert (HT1 : exists T1, List.nth_error (tele_insts (ind_nparams D) σ0 (ptyp_ps t)) m = Some T1).
      { assert (Hm : m < List.length (ptyp_ps t)) by (apply List.nth_error_Some; congruence).
        apply nth_error_lt_some'; rewrite length_tele_insts by (apply decl_closed_nparams_ass, Hc).
        rewrite length_nparams; lia. }
      destruct HT1 as [T1 HT1].
      pose proof (r_Ps_valid _ _ _ HPk HT1) as HP1.
      pose proof (r_gsub L (le_n _)) as Hg.
      replace (doms_ctx (List.firstn L (ptyp_doms t)) ++ Tg) with (ptyp_tele t ++ Tg) in Hg by (rewrite r_tele; reflexivity).
      pose proof (rel_exp_under_ctx_gsub Hg HP1) as HP2.
      replace T0 with T1[sb_qn L σt]; [ exact HP2 |].
      rewrite <- (tele_insts_sub_mvc (ind_nparams D) (ind_nu D) σ0 σ' (sb_qn L σt) (ptyp_ps t)) in HT.
      + apply nth_error_map_inv in HT as (T2 & HT2 & ->); rewrite HT1 in HT2; injection HT2 as ->; reflexivity.
      + apply decl_closed_nparams_ass, Hc.
      + apply (decl_nparams_mvc _ _ _ Hdt).
      + apply decl_closed_nparams_scoped, Hc.
      + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn].
        pose proof (r_ucK L (le_n _) y Hy) as H; rewrite <- Hσ' by exact Hy.
        etransitivity; [| exact H ]; f_equal; f_equal.
        rewrite !List.length_app, (r_dlen L (le_n _)), cargs_strat_nonrec, List.length_rev, List.length_map, params_split,
          List.length_app, length_nparams, length_ind_uparams by exact Hle; unfold ptyp_depth, K; fold L; lia.
    Qed.

    Lemma r_base : gsub (Ψ L) (ihb L Id) Γ.
    Proof.
      eapply gsub_eq; [ exact (gsub_wk _ _ _ (r_wk L (le_n _)) (r_HΨ L (le_n _)) HΓ) |].
      rewrite ihb_eq, sb_compose_id_left; reflexivity.
    Qed.

    Lemma r_nsub : gsub (Ψ L) (sb_of_list (ihb L Id) Ps') (tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ).
    Proof.
      pose proof (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
      assert (HNt : ⊨ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ)
        by (pose proof HM as H; unfold elim_mctx in H; cbn [List.app] in H; exact (sem_ctx_tail H)).
      apply gsub_of_list; [ exact r_base | apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact HNt
                          | unfold Ps'; rewrite List.length_map, length_tele_sub, length_nparams; exact HPl |].
      intros m N T0 HN HT; rewrite tele_insts_tele_sub in HT.
      exact (r_Ps_gen _ (fun y _ => eq_refl) m N T0 HN HT).
    Qed.

    Lemma r_UsL : List.map (fun U => U[ihb L Id]) Us = UsL.
    Proof.
      unfold UsL; apply List.map_ext; intros U; rewrite <- exp_sub_of_wk; apply exp_sub_sb_eq.
      rewrite ihb_eq, sb_compose_id_left; reflexivity.
    Qed.

    Lemma r_x_typed : Ψ L ⊨ xL : apps (a_ind p) (UsL ++ Ps').
    Proof.
      pose proof (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
      pose proof r_Mt as HMt.
      rewrite (ptyp_ty_at_ctx_pi p t Us σt r_simp) in HMt; unfold ptyp_depth in HMt; fold L in HMt.
      pose proof HM as HM'; unfold elim_mctx in HM'; cbn [List.app] in HM'.
      destruct (sem_ctx_ass_inv HM') as [jI HIT].
      pose proof (rel_exp_under_ctx_gsub r_nsub HIT) as HIT'.
      rewrite ind_head_inst in HIT' by (unfold Ps'; rewrite List.length_map; exact HPl).
      rewrite r_UsL in HIT'.
      unfold xL; rewrite ihx_eq.
      unfold Ψ in HIT' |- *; rewrite <- r_tele in HIT' |- *.
      apply (valid_apps_vars L (tele_sub (ptyp_tele t) σt) Γ _ jI Mt);
        [ rewrite length_tele_sub, r_tele; exact (r_dlen L (le_n _))
        | apply tele_ass_sub; unfold ptyp_tele, doms_ctx; apply List.Forall_rev, tele_ass_map_ass
        | pose proof (r_HΨ L (le_n _)) as H; unfold Ψ in H; rewrite <- r_tele in H; exact H
        | exact HIT' | exact HMt ].
    Qed.

    (** The end: the eliminator, moved past the domains, at the argument
        applied to them. *)
    Lemma r_leaf : Ψ L ⊨ a_elim p nm (ihA nm L A) (ihBs L Bs) xL : A[sb_of_list (ihb L Id) (Ps' ++ xL :: nil)].
    Proof.
      pose proof (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
      pose proof (r_HΨ L (le_n _)) as HΨL.
      pose proof (r_wk L (le_n _)) as HwL.
      destruct (elim_premises_wk_sem Γ (Ψ L) (wk_shiftn L) p D Us A i Bs Hc HUl HΨL HwL HA HM HBc Hnb HBv)
        as (HA' & HM' & HBc' & Hnb' & HBv').
      fold UsL in HA', HM', HBc', HBv'.
      assert (LUsL : List.length UsL = ind_nu D) by (unfold UsL; rewrite List.length_map; exact HUl).
      assert (LPs' : List.length Ps' = ind_nn D) by (unfold Ps'; rewrite List.length_map; exact HPl).
      assert (HUsL : forall k U T, List.nth_error UsL k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id UsL) k = Some T ->
                       Ψ L ⊨ U : T).
      { intros k U' T' HU HT; unfold UsL in *.
        rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
        apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T0 & HT & ->).
        exact (rel_exp_under_ctx_wk HwL (HUs _ _ _ HU HT)). }
      assert (HPsL : forall k N T0, List.nth_error Ps' k = Some N ->
                       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id UsL) Ps') k = Some T0 -> Ψ L ⊨ N : T0).
      { apply r_Ps_gen; intros y Hy; cbn [sb_compose].
        unfold UsL; rewrite sb_of_list_map by lia.
        rewrite <- !sentry_exp_sub, <- exp_sub_of_wk; apply exp_sub_sb_eq.
        rewrite ihb_eq, sb_compose_id_left; reflexivity. }
      pose proof (gsub_tau D Hc p (Ψ L) HΨL UsL LUsL HM' Ps' xL LPs' HPsL r_x_typed) as Hg.
      rewrite ihA_eq, ihBs_eq, Hnm.
      pose proof (rel_exp_elim_at (Ψ L) p D UsL Ps' xL xL (S (ind_nn D)) A[wk_qn (S (ind_nn D)) (wk_shiftn L)]ʷ
                    A[wk_qn (S (ind_nn D)) (wk_shiftn L)]ʷ i (brs_wk Bs (wk_shiftn L)) (brs_wk Bs (wk_shiftn L))
                    HD Hc Hsu Hdt Hl HΨL LUsL HUsL LPs' Hg r_x_typed eq_refl HA' HM'
                    ltac:(unfold brs_wk; apply brs_names_map; exact HBn) HBc' eq_refl Hnb') as H.
      replace (A[sb_of_list (ihb L Id) (Ps' ++ xL :: nil)])
        with (A[wk_qn (S (ind_nn D)) (wk_shiftn L)]ʷ[sb_of_list Id (Ps' ++ xL :: nil)]).
      - apply H; intros * Hk Hk' Hcon'; rewrite Hk in Hk'; injection Hk' as <-.
        exact (HBv' _ _ _ _ Hcon' (List.nth_error_In _ _ Hk)).
      - rewrite <- exp_sub_qn_of_wk.
        replace (S (ind_nn D)) with (List.length (Ps' ++ xL :: nil)) by (rewrite List.length_app; cbn; lia).
        rewrite exp_sub_qn_of_list; apply exp_sub_sb_eq, sb_of_list_cong.
        rewrite ihb_eq, sb_compose_id_left; reflexivity.
    Qed.

    (** The recursive result after [k] domains. *)
    Lemma r_tm : forall n k, k + n = L ->
        Ψ k ⊨ ptyp_ih p nm (ihA nm k A) (ihBs k Bs) (sb_qn k σt) (ihx k Mt) (ptyp_skip k t)
          : ptyp_ihty A (ihb k Id) (sb_qn k σt) (ihx k Mt) (ptyp_skip k t).
    Proof.
      induction n as [| n IH]; intros k Hkn.
      - assert (Hk : k = L) by lia; rewrite Hk.
        pose proof (ptyp_skip_end t r_simp) as HsL; change (List.length (ptyp_doms t)) with L in HsL; rewrite HsL.
        cbn [ptyp_ih ptyp_ihty ptyp_ps]; exact r_leaf.
      - assert (Hk : k < L) by lia.
        destruct (ptyp_skip_lt k t Hk) as (Bk & HBk & Hs); rewrite Hs.
        cbn [ptyp_ih ptyp_ihty].
        destruct (sd_dom _ HDc _ _ _ _ _ _ _ Hcon Heq HBk) as (_ & j & HBv0); rewrite <- r_strat in HBv0.
        pose proof (closed_app_valid _ _ _ _ _ (r_dass k) (r_dctx k ltac:(lia)) HΓ HBv0) as HBv1.
        rewrite <- !List.app_assoc in HBv1; fold Tg in HBv1.
        pose proof (rel_exp_under_ctx_gsub (r_gsub k ltac:(lia)) HBv1) as HBk'; cbn [exp_sub] in HBk'.
        pose proof (IH (S k) ltac:(lia)) as H.
        unfold Ψ in H; rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc in H; cbn [tele_sub List.app centry_sub] in H.
        rewrite (r_dlen k ltac:(lia)) in H.
        exact (rel_exp_fn_cong HBk' H).
    Qed.
  End RecArg.

  (** *** The Recursive Results Are of the Branch's Types *)
  Lemma ihs_pre : forall gs1 gs2, gs = gs1 ++ gs2 -> ⊨ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Us gs.
  Proof.
    intros * Heq; pose proof (HBc c gs Hcon) as H; unfold elim_bctx in H.
    replace (ihs_ctx_aux D A Us (List.length gs) nil 0 gs)
      with (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1 ++ nil) (0 + cargs_nrec gs1) gs2
              ++ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in H
      by (rewrite <- ihs_ctx_aux_app, <- Heq; reflexivity).
    unfold cinst; rewrite <- !List.app_assoc in H; exact (sem_ctx_app_r _ _ H).
  Qed.

  Lemma gsub_iota_ihs : forall rest gs1 L0, gs = gs1 ++ rest -> List.length L0 = cargs_nrec gs1 ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0)) (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Us gs) ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0 ++ elim_ihs p nm A Bs (cargs_sub σP gs1 As) rest (List.skipn (List.length gs1) As)))
        (ihs_ctx_aux D A Us (List.length gs) nil 0 (gs1 ++ rest) ++ cinst Γ p D Us gs).
  Proof.
    induction rest as [| [B0 | t] rest IH]; intros gs1 L0 Heq HL Hδ.
    - cbn [elim_ihs]; rewrite !List.app_nil_r; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      assert (Hcs : cargs_sub σP (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub σP gs1 As ,, a)).
      { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
        apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg B0 :: nil)) by (rewrite List.length_app; cbn; lia).
      rewrite <- Hcs.
      replace (gs1 ++ ca_arg B0 :: rest) with ((gs1 ++ ca_arg B0 :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_app; cbn; lia |].
      rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app]; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      set (σg := cargs_sub σP gs1 As).
      assert (Hcs : cargs_sub σP (gs1 ++ ca_rec t :: nil) As = σg).
      { unfold σg; rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
        apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
      set (E := ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in *.
      set (θ := ihs_sub D Us (List.length gs) (cargs_pat gs1) (cargs_nrec gs1)).
      set (b := cargs_nrec gs1 + List.length gs + ind_nn D).
      set (x := cargs_nrec gs1 + List.length gs - 1 - List.length (cargs_pat gs1)).
      assert (Hent : ihs_ctx_aux D A Us (List.length gs) nil 0 (gs1 ++ ca_rec t :: nil)
                     = ce_ass (ptyp_ihty A (sb_of_wk (wk_shiftn b)) θ (a_var x) t) :: E)
        by (unfold E, θ, b, x; rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add]; reflexivity).
      pose proof (ihs_pre (gs1 ++ ca_rec t :: nil) rest ltac:(rewrite <- List.app_assoc; exact Heq)) as HCT.
      rewrite Hent in HCT; cbn [List.app] in HCT.
      destruct (sem_ctx_ass_inv HCT) as [j HTj].
      set (δ := sb_of_list Id (Ns ++ As ++ L0)) in *.
      assert (Hθδ : sb_eq (θ ⨟ δ) σg).
      { pose proof (ihs_sub_iota D (Us ++ Ns) As L0 gs1 gs Hc ltac:(rewrite List.length_app, HUl, HNl; unfold ind_nn; lia) HAl
                      ltac:(rewrite Heq, List.length_app; lia)) as H.
        rewrite firstn_app_exact, skipn_app_exact, HL in H by exact HUl; exact H. }
      assert (Hbδ : sb_eq (sb_of_wk (wk_shiftn b) ⨟ δ) Id).
      { intros z; unfold b, δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        replace (z + (cargs_nrec gs1 + List.length gs + ind_nn D)) with (List.length (Ns ++ As ++ L0) + z)
          by (rewrite !List.length_app, HNl, HAl, HL; lia).
        rewrite sb_of_list_ge; reflexivity. }
      assert (Hidx : (a_var x)[δ] = a).
      { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ, x.
        rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, HNl, HAl, HL, Heq, List.length_app, length_cargs_pat; cbn; lia).
        rewrite !List.length_app, HNl, HAl, HL, length_cargs_pat.
        replace (ind_nn D + (List.length gs + cargs_nrec gs1) - 1 - (cargs_nrec gs1 + List.length gs - 1 - List.length gs1))
          with (ind_nn D + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
        cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) by lia.
        rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha. }
      pose proof (r_tm gs1 t rest Heq _ 0 eq_refl) as Hih.
      cbn [ihA ihBs ihb ihx sb_qn ptyp_skip List.firstn doms_ctx List.map List.rev tele_sub List.app] in Hih.
      rewrite (List.nth_error_nth _ _ _ Ha) in Hih; fold σg in Hih.
      replace (Ns ++ As ++ L0 ++ ptyp_ih p nm A Bs σg a t :: elim_ihs p nm A Bs σg rest (List.skipn (S (List.length gs1)) As))
        with (Ns ++ As ++ (L0 ++ ptyp_ih p nm A Bs σg a t :: nil) ++ elim_ihs p nm A Bs σg rest (List.skipn (S (List.length gs1)) As))
        by (rewrite <- !List.app_assoc; reflexivity).
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec t :: nil)) by (rewrite List.length_app; cbn; lia).
      rewrite <- Hcs.
      replace (gs1 ++ ca_rec t :: rest) with ((gs1 ++ ca_rec t :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite List.length_app, cargs_nrec_app, HL; cbn; lia |].
      rewrite Hent, Hcs.
      replace (Ns ++ As ++ L0 ++ ptyp_ih p nm A Bs σg a t :: nil) with ((Ns ++ As ++ L0) ++ ptyp_ih p nm A Bs σg a t :: nil)
        by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (sb_of_list_app (Ns ++ As ++ L0) (ptyp_ih p nm A Bs σg a t :: nil) Id).
      change (sb_of_list (sb_of_list Id (Ns ++ As ++ L0)) (ptyp_ih p nm A Bs σg a t :: nil))
        with (sb_of_list Id (Ns ++ As ++ L0) ,, ptyp_ih p nm A Bs σg a t).
      cbn [List.app]; eapply gsub_ass; [ exact Hδ | exact HTj |].
      fold δ; rewrite ptyp_ihty_sub, Hidx.
      rewrite (ptyp_ihty_sb_eq t A (sb_of_wk (wk_shiftn b) ⨟ δ) Id (θ ⨟ δ) σg a); [ exact Hih | exact Hbδ | exact Hθδ ].
  Qed.

  Lemma gsub_iota : gsub Γ (sb_of_list Id (Ns ++ As ++ elim_ihs p nm A Bs σP gs As)) (elim_bctx p D gs A Us ++ Γ).
  Proof.
    pose proof (ihs_pre nil gs eq_refl) as HC; cbn [ihs_ctx_aux List.app] in HC.
    pose proof (gsub_args Γ p D Us Ns c gs As Hc HΓ Hcon HNl (sem_ctx_tail HM) HC HNs HAl HAs) as Hδ.
    rewrite <- (List.app_nil_r As) in Hδ at 1.
    pose proof (gsub_iota_ihs gs nil nil eq_refl eq_refl Hδ) as H.
    cbn [List.app List.skipn List.length cargs_sub] in H.
    unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
  Qed.

  Lemma iota_Mc_valid : Γ ⊨ apps (a_con p c) (Us ++ Ns ++ As) : apps (a_ind p) (Us ++ Ns).
  Proof.
    rewrite List.app_assoc.
    apply (rel_exp_con_apps D HD Hc Hsu p Hl Γ c gs (Us ++ Ns) As HΓ Hcon);
      [ rewrite List.length_app; unfold ind_nn in *; lia | | exact HAl | exact HAs ].
    apply params_valid_join; assumption.
  Qed.

  (** *** The Values of the Recursive Results

      In an environment [C] of [Γ], the recursive results of the branch's
      environment (closures) are related, by [ihs_rel], to those of the
      eliminator's own evaluation. *)
  Section IotaSem.
    #[local] Set Default Proof Using "All".
    Variable (RΓ RU : relation env).
    Hypothesis (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
    Variable (C : env) (u0 ns avs : list domain) (a0 : domain).
    Hypothesis (HCC : RΓ C C) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u0)
      (HNC : ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ ns) (HAC : ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ avs)
      (Hu0g : per_gargs (List.rev (ind_uparams D)) nil nil u0 u0) (Hu0l : List.length u0 = ind_nu D)
      (Ha0 : ⟦ ind_sort D ⟧ env_args nil u0 ↘ a0).
    Let nr := ind_nr D u0.
    Let ar := ind_ar D u0.
    Let dr := ind_dr u0.
    Let T := List.rev (ind_nparams D).
    Let HNt : ⊨ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ := sem_ctx_tail HM.
    Let canon := u0_canon D HD Hc Hsu u0 a0 Hu0g Hu0l Ha0.
    Let HnP := proj1 canon.
    Let HnI := proj1 (proj2 canon).
    Let HaP := proj1 (proj2 (proj2 canon)).
    Let HaI := proj1 (proj2 (proj2 (proj2 canon))).
    Let HdP := proj1 (proj2 (proj2 (proj2 (proj2 canon)))).
    Let HdI := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 canon))))).
    Let Had := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 canon))))).
    Let Rel := fun ns m ns' m' => per_head A A (env_args C (ns ++ m :: nil)) (env_args C (ns' ++ m' :: nil)).
    Let isym := proj1 (ind_rel_sym_all p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had).
    Let itrans := proj1 (ind_rel_trans_all p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had).
    Let Ln : List.length ns = ind_nn D := eq_trans (eval_exps_length _ _ _ HNC) HNl.
    Let La : List.length avs = List.length gs := eq_trans (eval_exps_length _ _ _ HAC) HAl.

    Lemma s_IT : ⟦ apps (a_ind p) (Us ++ Ns) ⟧ C ↘ d_ind p (u0 ++ ns) /\ tele_full nr T ns ns /\
        (per_head (apps (a_ind p) (Us ++ Ns)) (apps (a_ind p) (Us ++ Ns)) C C <~> ind_rel p D u0 nr ar dr ns).
    Proof.
      assert (Eind : ⟦ apps (a_ind p) (Us ++ Ns) ⟧ C ↘ d_ind p (u0 ++ ns)).
      { apply eval_apps_exp; exists (d_ind p nil), (u0 ++ ns); split; [ constructor | split ].
        - apply eval_exps_app; assumption.
        - change (d_ind p (u0 ++ ns)) with (d_ind p (nil ++ (u0 ++ ns))); apply (IndCases.eval_apps_ind D p Hl).
          cbn; rewrite List.length_app, Hu0l, Ln; unfold ind_nn; lia. }
      destruct (presup_rel_exp_under_ctx iota_Mc_valid) as [iT HIT].
      destruct (rel_exp_of_typ_inversion_simple_at HRΓ HIT _ _ HCC) as (t1 & t2 & Et1 & Et2 & [R HR]).
      assert (t1 = d_ind p (u0 ++ ns)) as -> by (eapply functional_eval_exp; eassumption).
      assert (t2 = d_ind p (u0 ++ ns)) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (ind_univ_inv _ _ _ _ _ _ _ _ HR Hu0l Hu0l Hl) as Hnn.
      pose proof (ind_relate D HD Hc Hsu p Hl u0 u0 ns ns a0 Hu0g Hu0l Ha0 Hnn) as HIR.
      split; [ exact Eind | split; [ exact Hnn |] ].
      etransitivity; [ symmetry; exact (per_head_iff Et1 Et2 HR) | eapply per_univ_elem_right_irrel; [ exact HR | exact HIR ] ].
    Qed.

    Lemma s_Mc : ⟦ apps (a_con p c) (Us ++ Ns ++ As) ⟧ C ↘ d_con p c (u0 ++ ns ++ avs).
    Proof.
      apply eval_apps_exp; exists (d_con p c nil), (u0 ++ ns ++ avs); split; [ constructor | split ].
      - apply eval_exps_app; [ exact HUC | apply eval_exps_app; assumption ].
      - change (d_con p c (u0 ++ ns ++ avs)) with (d_con p c (nil ++ (u0 ++ ns ++ avs))).
        apply (eval_apps_con' D p Hl c gs); [ exact Hcon | cbn; rewrite !List.length_app, Hu0l, Ln, La; unfold ind_nn; lia ].
    Qed.

    Lemma s_con_inv : forall ns0 vs ws, List.length vs = List.length gs ->
        ind_rel p D u0 nr ar dr ns0 (d_con p c (u0 ++ ns ++ vs)) (d_con p c ws) ->
        tele_full nr T ns0 ns0 /\
        tele_full (ar ns0 c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs (List.skipn (ind_np D) ws)) /\
        ind_args_rel p D u0 nr ar dr ns0 gs vs (List.skipn (ind_np D) ws).
    Proof.
      intros * Lv H; inversion H; subst.
      match goal with H1 : ?bs ++ ?vs0 = u0 ++ ns ++ vs, H5 : List.length ?bs = ind_np D, H6 : List.length ?bs' = ind_np D,
                      Hcg : ind_con D c = Some ?g |- _ =>
        rewrite Hcon in Hcg; injection Hcg as <-;
        rewrite List.app_assoc in H1;
        destruct (app_split_eq _ _ _ _ H1 ltac:(rewrite H5, List.length_app, Hu0l, Ln; unfold ind_nn; lia)) as [_ <-];
        rewrite (skipn_app_exact bs' _ _ H6)
      end.
      split; [ assumption | split; assumption ].
    Qed.

    Lemma s_self : tele_full nr T ns ns /\ tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs avs) (nonrec_vals gs avs) /\
        ind_args_rel p D u0 nr ar dr ns gs avs avs.
    Proof.
      destruct s_IT as (_ & _ & ERM).
      destruct (rel_exp_under_ctx_simple_at HRΓ iota_Mc_valid _ _ HCC) as (m & m' & Em & Em' & Hmm).
      assert (m = d_con p c (u0 ++ ns ++ avs)) as -> by (eapply functional_eval_exp; [ exact Em | exact s_Mc ]).
      assert (m' = d_con p c (u0 ++ ns ++ avs)) as -> by (eapply functional_eval_exp; [ exact Em' | exact s_Mc ]).
      apply ERM in Hmm.
      destruct (s_con_inv ns avs (u0 ++ ns ++ avs) La Hmm) as (H1 & H2 & H3).
      assert (E : List.skipn (ind_np D) (u0 ++ ns ++ avs) = avs)
        by (rewrite List.app_assoc; apply skipn_app_exact; rewrite List.length_app, Hu0l, Ln; unfold ind_nn; lia).
      rewrite E in H2, H3; split; [| split ]; assumption.
    Qed.

    (** **** A Recursive Argument *)
    Section RecSem.
      Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
      Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
      Let K := List.length (cargs_nonrec gs1).
      Let L := List.length (ptyp_doms t).
      Let σt := cargs_sub σP gs1 As.
      Let Mt := List.nth (List.length gs1) As (a_var 0).
      Let Ψ k := tele_sub (doms_ctx (List.firstn k (ptyp_doms t))) σt ++ Γ.
      Let Tg := cargs_strat gs1 ++ ind_params D ++ Γ.
      Let nv := nonrec_vals gs1 (List.firstn (List.length gs1) avs).
      Let Hsimp := sd_simple D HDc.
      Let Hplen := sd_plen D HDc.

      Lemma s_a : exists a, List.nth_error avs (List.length gs1) = Some a /\
          ind_shape_rel p D u0 nr ar dr (ns ++ nv) t a a.
      Proof.
        destruct s_self as (_ & _ & Hia).
        destruct (args_rel_at _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & x' & Hx & Hx' & Hr).
        rewrite Hx in Hx'; injection Hx' as <-; exists x; split; assumption.
      Qed.

      Lemma s_nv : List.length nv = K /\ tele_pre (ar ns c) K nv nv.
      Proof.
        destruct s_self as (_ & Hnv & _).
        assert (Lf : List.length (List.firstn (List.length gs1) avs) = List.length gs1)
          by (rewrite List.length_firstn, La, Heq, List.length_app; lia).
        split; [ apply length_nonrec_vals; exact Lf |].
        rewrite <- (List.firstn_skipn (List.length gs1) avs) in Hnv.
        exact (nonrec_prefix_gen _ gs gs1 (ca_rec t :: gs2) _ _ _ _ Heq Lf Lf Hnv).
      Qed.

      (** The shape's relation, after related values of the domains. *)
      Lemma s_unfold : forall k, k <= L -> forall x x' ys ys',
          ind_shape_rel p D u0 nr ar dr (ns ++ nv) t x x' ->
          tele_pre (shape_tr dr ns nv (ptyp_doms t)) k ys ys' ->
          exists f f', $*| x & ys | gc_deps ⍮ gc_stack ↘ f /\ $*| x' & ys' | gc_deps ⍮ gc_stack ↘ f' /\
            ind_shape_rel p D u0 nr ar dr (ns ++ nv ++ ys) (ptyp_skip k t) f f'.
      Proof.
        induction k as [| k IH]; intros Hk * Hsh Hys.
        - pose proof Hys as Hys0; rewrite tele_pre_iff in Hys0; destruct Hys0 as (L1 & L2 & _).
          destruct ys; [| discriminate ]; destruct ys'; [| discriminate ].
          exists x, x'; split; [ constructor | split; [ constructor |] ].
          rewrite List.app_nil_r; exact Hsh.
        - pose proof Hys as Hys0; rewrite tele_pre_iff in Hys0; destruct Hys0 as (L1 & L2 & Hr).
          destruct (List.exists_last (l := ys) ltac:(intros ->; discriminate)) as (ys0 & y & ->).
          destruct (List.exists_last (l := ys') ltac:(intros ->; discriminate)) as (ys0' & y' & ->).
          rewrite List.length_app in L1, L2; cbn in L1, L2.
          pose proof (tele_pre_of_pre _ _ _ _ k Hys ltac:(lia)) as Hys1.
          rewrite !firstn_app_exact in Hys1 by lia.
          pose proof (Hr k y y' ltac:(rewrite List.nth_error_app2 by lia; replace (k - List.length ys0) with 0 by lia; reflexivity)
                        ltac:(rewrite List.nth_error_app2 by lia; replace (k - List.length ys0') with 0 by lia; reflexivity)) as Hyy.
          rewrite firstn_app_exact in Hyy by lia.
          destruct (IH ltac:(lia) _ _ _ _ Hsh Hys1) as (g & g' & Eg & Eg' & Hsh0).
          destruct (ptyp_skip_lt k t ltac:(unfold L in Hk; lia)) as (Bk & HBk & Hs).
          rewrite Hs in Hsh0.
          unfold shape_tr in Hyy; rewrite (List.nth_error_nth _ _ _ HBk) in Hyy.
          destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ Hsh0 y y' Hyy) as (r & r' & Er & Er' & Hsh1).
          exists r, r'; split; [| split ].
          + apply eval_apps_app; exists g; split; [ exact Eg | econstructor; [ exact Er | constructor ] ].
          + apply eval_apps_app; exists g'; split; [ exact Eg' | econstructor; [ exact Er' | constructor ] ].
          + rewrite <- !List.app_assoc in Hsh1; exact Hsh1.
      Qed.

      (** The closure of the recursive result after [k] domains, against
          the eliminator's own value. *)
      Lemma s_clo : forall a, List.nth_error avs (List.length gs1) = Some a ->
          forall n k, k + n = L -> forall ys ys' f f',
          tele_pre (shape_tr dr ns nv (ptyp_doms t)) k ys ys' ->
          $*| a & ys | gc_deps ⍮ gc_stack ↘ f -> $*| a & ys' | gc_deps ⍮ gc_stack ↘ f' ->
          ind_shape_rel p D u0 nr ar dr (ns ++ nv ++ ys) (ptyp_skip k t) f f' ->
          exists re rc, eval_ih gc_deps gc_stack C nm A Bs (ptyp_skip k t) f re /\
            ⟦ ptyp_ih p nm (ihA nm k A) (ihBs k Bs) (sb_qn k σt) (ihx k Mt) (ptyp_skip k t) ⟧ env_args C ys' ↘ rc /\
            ih_rel u0 dr Rel (ns ++ nv ++ ys) (ptyp_skip k t) f f' re rc.
      Proof.
        intros a Ha; induction n as [| n IH]; intros k Hkn * Hys Ef Ef' Hsh.
        - assert (k = L) as -> by lia.
          pose proof (ptyp_skip_end t (r_simp gs1 t gs2 Heq)) as HsL; change (List.length (ptyp_doms t)) with L in HsL.
          rewrite HsL in Hsh |- *; cbn [ptyp_ih ih_rel].
          destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & Ebs & Hff).
          pose proof Hys as Hys0; rewrite tele_pre_iff in Hys0; destruct Hys0 as (Lys & Lys' & _).
          destruct s_self as (Hnn & _ & _).
          destruct s_nv as (Lnv & Hnvp).
          (** The environment of the domains. *)
          set (EL := env_args C ys').
          pose proof (r_HΨ gs1 t gs2 Heq L (le_n _)) as HΨL.
          destruct (sem_ctx_per_ctx_env HΨL) as [RΨ HRΨ].
          assert (HU00 : RU (env_args nil u0) (env_args nil u0)).
          { destruct (us_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C C HCC) as (u1 & u2 & Hu1 & Hu2 & H12).
            pose proof (functional_eval_exps' _ _ _ _ Hu1 HUC) as ->; pose proof (functional_eval_exps' _ _ _ _ Hu2 HUC) as ->.
            exact H12. }
          assert (HEL : RΨ EL EL).
          { destruct (sem_ctx_per_ctx_env (ihs_pre gs1 _ Heq)) as [RS HRS].
            pose proof (tsh_refl_r p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs gs1 t gs2 nv
                          Hnn Hcon Heq Hnvp L ys ys' (le_n _) Hys) as Hys''.
            pose proof (side_dom_gargs D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs u0 a0 Hu0g Hu0l Ha0 HNt HM
                          A i HA C C HCC HUC c gs Hcon (HBc c gs Hcon) gs1 t gs2 Heq RS HRS L C u0 ns nv ys' (le_n _)
                          HU00 Hu0l Ln Lnv Hnn Hnvp Hys'') as Hg.
            apply (tele_stage_rel (doms_ctx (List.firstn L (ptyp_doms t))) Tg Γ σt RΓ C _ ltac:(unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass)
                     (r_dctxΓ gs1 t gs2 Heq L (le_n _)) HRΓ (proj1 (gsub_props (gsub_sigt gs1 _ Heq))) HCC
                     (eval_sigt gs1 _ C u0 ns avs Heq HUC HNC HAC) ys' Hg
                     ltac:(rewrite (r_dlen gs1 t gs2 Heq L (le_n _)); exact Lys') RΨ HRΨ). }
          assert (Hwk : Ψ L ⊨s sb_of_wk (wk_shiftn L) ≈ sb_of_wk (wk_shiftn L) : Γ)
            by exact (proj1 (gsub_props (gsub_wk _ _ _ (r_wk gs1 t gs2 Heq L (le_n _)) HΨL HΓ))).
          assert (Hev : ⟦ sb_of_wk (wk_shiftn L) ⟧s EL ↘ C).
          { pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn L) EL (wk_mono_shiftn _)) as H.
            unfold EL in H; rewrite <- Lys', eval_wk_shiftn_args in H; rewrite <- Lys'; intros x; exact (H x). }
          (** The scrutinee, weakened, against itself. *)
          destruct (exp_inst_link _ _ _ _ _ _ _ _ _ iota_Mc_valid HRΨ Hwk HEL Hev) as (mw & mC & Emw & EmC & Hm).
          assert (mC = d_con p c (u0 ++ ns ++ avs)) as -> by (eapply functional_eval_exp; [ exact EmC | exact s_Mc ]).
          destruct s_IT as (_ & _ & ERM).
          apply ERM, isym in Hm.
          rewrite apps_exp_sub in Emw; cbn [exp_sub] in Emw.
          apply eval_apps_exp in Emw as (f0 & ws & Ef0 & Ews & Eapp).
          assert (f0 = d_con p c nil) as -> by (inversion Ef0; reflexivity).
          assert (Lws : List.length ws = ind_np D + List.length gs)
            by (rewrite (eval_exps_length _ _ _ Ews), List.length_map, !List.length_app, HUl, HNl, HAl; unfold ind_nn; lia).
          assert (mw = d_con p c ws) as ->.
          { pose proof (eval_apps_con' D p Hl c gs ws nil Hcon ltac:(cbn; lia)) as H; cbn in H.
            exact (fe_apps _ _ _ _ Eapp H). }
          destruct (s_con_inv ns avs ws La Hm) as (_ & _ & Hia).
          destruct (args_rel_at _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & x' & Hx & Hx' & Hshw).
          rewrite Ha in Hx; injection Hx as <-.
          assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
          destruct (nth_error_lt_some As _ Hlt) as [M0 HM0].
          assert (EMt : Mt = M0) by (unfold Mt; apply List.nth_error_nth; exact HM0).
          assert (Ew : ⟦ Mt[sb_of_wk (wk_shiftn L)] ⟧ EL ↘ x').
          { rewrite List.nth_error_skipn in Hx'.
            destruct (eval_exps_nth _ _ _ (ind_np D + List.length gs1) (Mt[sb_of_wk (wk_shiftn L)]) Ews) as (v & Hv & Ev).
            - rewrite List.nth_error_map, List.app_assoc, List.nth_error_app2 by (rewrite List.length_app, HUl, HNl; unfold ind_nn; lia).
              rewrite List.length_app, HUl, HNl.
              replace (ind_np D + List.length gs1 - (ind_nu D + ind_nn D)) with (List.length gs1) by (unfold ind_nn; lia).
              rewrite HM0, EMt; reflexivity.
            - rewrite Hx' in Hv; injection Hv as <-; exact Ev. }
          (** Along the domains. *)
          destruct (s_unfold L (le_n _) a x' ys ys' Hshw Hys) as (f1 & mL & Ef1 & EmL & HshL).
          pose proof (fe_apps _ _ _ _ Ef1 Ef) as ->.
          rewrite HsL in HshL.
          destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ HshL) as (bs1 & Ebs1 & HfmL).
          pose proof (functional_eval_exps' _ _ _ _ Ebs1 Ebs) as ->.
          assert (ExL : ⟦ ihx L Mt ⟧ EL ↘ mL).
          { rewrite ihx_eq, <- exp_sub_of_wk.
            apply eval_apps_exp; exists x', ys'; split; [ exact Ew | split; [| exact EmL ] ].
            unfold EL; pose proof (eval_vars_from_args ys' C nil) as H; cbn [List.length] in H.
            rewrite List.app_nil_r, Lys' in H; exact H. }
          (** The two eliminations. *)
          assert (Hbb : tele_full nr T bs bs)
            by exact (ind_rel_ns_refl p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen _ _ _ Hff).
          destruct (elim_shift D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs u0 a0 Hu0g Hu0l Ha0 HNt HM A A i HA C C HCC HUC HBc
                      Bs nm Hnm HBn Hnb (fun c0 gs0 n0 B0 Hc0 Hlk => HBv c0 gs0 n0 B0 Hc0 (brs_lookup_in _ _ _ _ Hlk))
                      (Ψ L) RΨ (sb_of_wk (wk_shiftn L)) EL HRΨ Hwk HEL Hev bs bs mL f Hbb (isym _ _ _ HfmL))
            as (r1 & r2 & E1 & E2 & HR12).
          exists r2, r1; split; [ constructor; exact E2 | split ].
          + econstructor; [ exact ExL |].
            rewrite ihA_eq, ihBs_eq, <- exp_sub_qn_of_wk, <- brs_sub_of_wk; exact E1.
          + exists bs; split; [ exact Ebs |].
            assert (Hfff : ind_rel p D u0 nr ar dr bs f f) by exact (itrans _ _ _ Hff _ (isym _ _ _ Hff)).
            pose proof (proj1 (Rel_resp D HD Hc Hsu p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs u0 a0 Hu0g Hu0l Ha0 HNt HM A A i HA C C HCC HUC
                                 bs mL bs f bs f bs f' Hbb Hbb Hbb (isym _ _ _ HfmL) Hfff Hff r1 r2) HR12) as H.
            pose proof (Rel_PER D HD Hc Hsu p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs u0 a0 Hu0g Hu0l Ha0 HNt HM A A i HA C C HCC HUC
                          bs bs f f' Hbb Hff) as HP.
            symmetry; exact H.
        - assert (Hk : k < L) by lia.
          destruct (ptyp_skip_lt k t Hk) as (Bk & HBk & Hs).
          rewrite Hs in Hsh |- *.
          remember (ptyp_skip (S k) t) as t' eqn:Ht'.
          do 2 eexists; split; [ constructor | split; [ cbn [ptyp_ih]; constructor |] ].
          cbn [ih_rel]; intros c0 c0' Hcc.
          destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ Hsh c0 c0' Hcc) as (fc & fc' & Efc & Efc' & Hsh').
          destruct (IH (S k) ltac:(lia) (ys ++ c0 :: nil) (ys' ++ c0' :: nil) fc fc') as (re & rc & Ere & Erc & Hih).
          + apply tele_pre_snoc; [ exact Hys |]; unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HBk); exact Hcc.
          + apply eval_apps_app; exists f; split; [ exact Ef | econstructor; [ exact Efc | constructor ] ].
          + apply eval_apps_app; exists f'; split; [ exact Ef' | econstructor; [ exact Efc' | constructor ] ].
          + rewrite <- Ht'; rewrite <- !List.app_assoc in Hsh'; exact Hsh'.
          + rewrite <- Ht' in Ere, Erc, Hih.
            exists fc, fc', re, rc; split; [ exact Efc | split; [ exact Efc' | split; [| split ] ] ].
            * econstructor; [ exact Efc | exact Ere ].
            * constructor; rewrite env_args_snoc in Erc; exact Erc.
            * rewrite <- !List.app_assoc; exact Hih.
      Qed.
    End RecSem.

    Lemma s_ihs : forall rest gs1, gs = gs1 ++ rest ->
        exists ihe ihc, eval_ihs gc_deps gc_stack C nm A Bs rest (List.skipn (List.length gs1) avs) ihe /\
          ⟦ elim_ihs p nm A Bs (cargs_sub σP gs1 As) rest (List.skipn (List.length gs1) As) ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ ihc /\
          ihs_rel u0 dr Rel (ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) avs)) rest
            (List.skipn (List.length gs1) avs) (List.skipn (List.length gs1) avs) ihe ihc.
    Proof.
      induction rest as [| g rest IH]; intros gs1 Heq.
      - assert (E : List.skipn (List.length gs1) avs = nil)
          by (apply List.skipn_all2; rewrite La, Heq, List.app_nil_r; lia).
        rewrite E; exists nil, nil; split; [ constructor | split; [ cbn; constructor | constructor ] ].
      - assert (Hlt : List.length gs1 < List.length avs) by (rewrite La, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some avs _ Hlt) as [v Hv].
        assert (HltA : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some As _ HltA) as [M0 HM0].
        assert (Lf : List.length (List.firstn (List.length gs1) avs) = List.length gs1) by (rewrite List.length_firstn; lia).
        assert (Heq' : gs = (gs1 ++ g :: nil) ++ rest) by (rewrite <- List.app_assoc; exact Heq).
        destruct (IH _ Heq') as (ihe & ihc & Ee & Ec & Hr).
        rewrite List.length_app in Ee, Ec, Hr; cbn [List.length] in Ee, Ec, Hr; rewrite Nat.add_1_r in Ee, Ec, Hr.
        rewrite (firstn_S_nth _ _ _ Hv), nonrec_vals_app in Hr by exact Lf.
        rewrite (skipn_nth_cons _ _ _ Hv), (skipn_nth_cons _ _ _ HM0).
        destruct g as [B0 | t].
        + assert (Hcs : cargs_sub σP (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub σP gs1 As ,, M0)).
          { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ HM0).
            apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
          rewrite Hcs in Ec; cbn [nonrec_vals] in Hr; rewrite List.app_assoc in Hr.
          exists ihe, ihc; split; [ constructor; exact Ee | split; [ cbn [elim_ihs]; exact Ec | constructor; exact Hr ] ].
        + assert (Hcs : cargs_sub σP (gs1 ++ ca_rec t :: nil) As = cargs_sub σP gs1 As).
          { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ HM0).
            apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
          rewrite Hcs in Ec; cbn [nonrec_vals] in Hr; rewrite List.app_nil_r in Hr.
          destruct (s_a gs1 t rest Heq) as (a & Ha & Hsh).
          rewrite Hv in Ha; injection Ha as <-.
          destruct (s_clo gs1 t rest Heq v Hv _ 0 eq_refl nil nil v v (tele_pre_nil _) ltac:(constructor) ltac:(constructor)
                      ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact Hsh)) as (re & rc & Ere & Erc & Hih).
          cbn [ihA ihBs ihx sb_qn ptyp_skip env_args List.fold_left] in Ere, Erc, Hih.
          rewrite List.app_nil_r in Hih.
          rewrite (List.nth_error_nth _ _ _ HM0) in Erc.
          exists (re :: ihe), (rc :: ihc); split; [ constructor; [ exact Ere | exact Ee ] | split ].
          * cbn [elim_ihs]; constructor; [ exact Erc | exact Ec ].
          * constructor; [ exact Hih | exact Hr ].
    Qed.
  End IotaSem.

  (** *** The Rule *)
  Lemma rel_exp_elim_iota_at : forall n B, brs_lookup Bs c = Some (n, B) ->
      Γ ⊨ a_elim p nm A Bs (apps (a_con p c) (Us ++ Ns ++ As)) ≈ B[sb_of_list Id (Ns ++ As ++ elim_ihs p nm A Bs σP gs As)]
        : A[sb_of_list Id (Ns ++ apps (a_con p c) (Us ++ Ns ++ As) :: nil)].
  Proof.
    intros n B Hlk.
    set (Mc := apps (a_con p c) (Us ++ Ns ++ As)).
    pose proof iota_Mc_valid as HMc; fold Mc in HMc.
    pose proof (gsub_tau D Hc p Γ HΓ Us HUl HM Ns Mc HNl HNs HMc) as Hg.
    pose proof (elim_valid_at Ns Mc HNl Hg HMc) as HL.
    pose proof gsub_iota as Hgi.
    pose proof (HBv _ _ _ _ Hcon (brs_lookup_in _ _ _ _ Hlk)) as HBv'.
    assert (Lih : List.length (elim_ihs p nm A Bs σP gs As) = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
    pose proof (rel_exp_under_ctx_gsub Hgi HBv') as HR.
    rewrite elim_bty_iota in HR by assumption.
    destruct (sem_ctx_per_ctx_env HΓ) as [RΓ HRΓ].
    destruct (sem_ctx_per_ctx_env (uparams_sem D HD)) as [RU HRU].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    destruct (presup_rel_exp_under_ctx HL) as [iT HT].
    destruct (presup_rel_exp_under_ctx HBv') as [iB HTb].
    apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
    intros ρ ρ' Hρρ'.
    assert (Hρ'ρ' : RΓ ρ' ρ') by (etransitivity; [ symmetry; exact Hρρ' | exact Hρρ' ]).
    destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as (l & l' & El & El' & Hll').
    (** The values at [ρ']. *)
    destruct (us_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ρ' ρ' Hρ'ρ') as (u0 & u0' & Hu0 & Hu0' & HU00).
    pose proof (functional_eval_exps' _ _ _ _ Hu0' Hu0) as ->.
    assert (Hu0l : List.length u0 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hu0); exact HUl).
    pose proof (U_gargs D HD Hc RU HRU _ _ HU00 Hu0l Hu0l) as Hu0g.
    destruct (sd_sort D HD) as [j HS].
    destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HU00) as (a0 & _ & Ha0 & _ & _).
    apply eval_elim_inv in El' as (m & Em & Eel).
    pose proof Em as Em'; unfold Mc in Em'; apply eval_apps_exp in Em' as (f & vall & Ef & Evall & Eapp).
    apply eval_exps_app_inv in Evall as (us' & vrest & -> & Eus & Evrest).
    apply eval_exps_app_inv in Evrest as (ns' & as' & -> & Ens & Eas).
    pose proof (functional_eval_exps' _ _ _ _ Eus Hu0) as ->.
    set (Rel := fun ns m ns' m' => per_head A A (env_args ρ' (ns ++ m :: nil)) (env_args ρ' (ns' ++ m' :: nil))).
    assert (Ln : List.length ns' = ind_nn D) by (rewrite (eval_exps_length _ _ _ Ens); exact HNl).
    assert (La : List.length as' = List.length gs) by (rewrite (eval_exps_length _ _ _ Eas); exact HAl).
    assert (m = d_con p c (u0 ++ ns' ++ as')) as ->
      by (eapply functional_eval_exp; [ exact Em | exact (s_Mc RΓ RU HRΓ HRU ρ' u0 ns' as' a0 Hρ'ρ' Hu0 Ens Eas Hu0g Hu0l Ha0) ]).
    destruct (s_self RΓ RU HRΓ HRU ρ' u0 ns' as' a0 Hρ'ρ' Hu0 Ens Eas Hu0g Hu0l Ha0) as (Hnn & Hnv & Hia).
    destruct (s_ihs RΓ RU HRΓ HRU ρ' u0 ns' as' a0 Hρ'ρ' Hu0 Ens Eas Hu0g Hu0l Ha0 gs nil eq_refl) as (ihe & ihc & Ee & Ec & Hir).
    cbn [List.length List.skipn List.firstn nonrec_vals cargs_sub] in Ee, Ec, Hir; rewrite List.app_nil_r in Hir.
    (** The eliminator's own value. *)
    apply eval_elim_con_inv in Eel as (D' & gs' & n' & B' & ihs & Hl' & Hcon' & Hlk' & Eih & EB).
    rewrite Hl in Hl'; injection Hl' as <-; rewrite Hcon in Hcon'; injection Hcon' as <-.
    rewrite Hlk in Hlk'; injection Hlk' as <- <-.
    assert (Hnp : List.length (u0 ++ ns') = ind_np D) by (rewrite List.length_app, Hu0l, Ln; unfold ind_nn; lia).
    replace (u0 ++ ns' ++ as') with ((u0 ++ ns') ++ as') in EB, Eih by (rewrite <- List.app_assoc; reflexivity).
    rewrite (skipn_app_exact (u0 ++ ns') as' _ Hnp) in EB, Eih.
    rewrite (firstn_app_exact (u0 ++ ns') as' _ Hnp), (skipn_app_exact u0 ns' _ Hu0l) in EB.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
                  (@functional_eval gc_deps gc_stack)))))))))))))) _ _ _ _ _ _ _ Eih _ Ee) as ->.
    (** The branch's environments. *)
    destruct (sem_ctx_per_ctx_env (HBc c gs Hcon)) as [RB HRB].
    assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
    pose proof (cv_bctx D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs u0 a0 Hu0g Hu0l Ha0 (sem_ctx_tail HM) HM A i HA
                  ρ' ρ' Hρ'ρ' Hu0 c gs Hcon (HBc c gs Hcon) ρ' ρ' Hρ'ρ' Hρ'ρ' ns' ns' ns' as' as' ihe ihc Hnn Hnn Hnv Hia Hir RB HRB) as Hec.
    set (Eτ := env_args ρ' (ns' ++ as' ++ ihc)) in *.
    assert (Hτ : ⟦ sb_of_list Id (Ns ++ As ++ elim_ihs p nm A Bs σP gs As) ⟧s ρ' ↘ Eτ)
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact Ens | apply eval_exps_app; [ exact Eas | exact Ec ] ] ]).
    destruct (rel_exp_under_ctx_simple_at HRB HBv' _ _ Hec) as (r1 & r2 & Er1 & Er2 & Hr12).
    assert (r1 = l') as -> by (eapply functional_eval_exp; eassumption).
    destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HBv' HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ) as (r & n0 & Er & En0 & Hrn).
    assert (n0 = r2) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hcc : RB Eτ Eτ) by (etransitivity; [ symmetry; exact Hec | exact Hec ]).
    assert (EC1 : per_head (elim_bty p D c gs A Us) (elim_bty p D c gs A Us) (env_args ρ' (ns' ++ as' ++ ihe)) Eτ
                  <~> per_head (elim_bty p D c gs A Us) (elim_bty p D c gs A Us) Eτ Eτ).
    { apply (per_head_of_typ_resp HRB HTb).
      apply rel_chain_cons; [ exact Hec |]. apply rel_chain_cons; [ exact Hcc |]. apply rel_chain_of_pair; exact Hcc. }
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HTb HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ Hτ) as ER.
    rewrite elim_bty_iota in ER by assumption.
    exists l, r; split; [ exact El | split; [ exact Er |] ].
    assert (HT' : Γ ⊨ A[sb_of_list Id (Ns ++ Mc :: nil)] : Typeω@iT) by exact (rel_exp_under_ctx_refl_left HT).
    assert (Hl'r2 : per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ' ρ' l' r2)
      by (apply ER, EC1; exact Hr12).
    assert (Hrr2 : per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ' ρ' r r2)
      by (apply ER; exact Hrn).
    pose proof (per_head_sym _ _ _ _ _ _ HRΓ HT' Hρ'ρ' _ _ Hrr2) as Hr2r.
    pose proof (per_head_trans _ _ _ _ _ _ HRΓ HT' Hρ'ρ' _ _ _ Hl'r2 Hr2r) as Hlr.
    assert (EC : per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ' ρ'
                 <~> per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ ρ').
    { apply (per_head_of_typ_resp HRΓ HT).
      apply rel_chain_cons; [ exact Hρ'ρ' |]. apply rel_chain_cons; [ symmetry; exact Hρρ' |]. apply rel_chain_of_pair; exact Hρρ'. }
    exact (per_head_trans _ _ _ _ _ _ HRΓ HT' Hρρ' _ _ _ Hll' (proj1 (EC _ _) Hlr)).
  Qed.
End Iota.


End Fixed_GCtx.
