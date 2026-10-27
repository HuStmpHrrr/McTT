(** * The Elements of a Record View, as the Record's

    A record view [j] of a group [D] at [p] is the record [R] at [qr] at
    the instance [Is]: its type is the record's at [⟦Is⟧ups], so its
    elements are related by the record's relation there, field by field.
    The group relates them by its own relation at the record view
    ([ind_rel_record]): their projections, as the arguments of the record
    view's constructor.  The record view equation ([vg_rview_fields]) makes
    the two telescopes agree position by position ([rview_tele_link]), so
    the two relations are one ([rview_end_rel_of_ends]), given those of the
    types of the members the recursive fields' shapes end in.  These are
    of lower rank; the rank induction ([ViewArgs]) gives them. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations CargsRel.
From Mctt.Core.Completeness.Records Require Model.
From Mctt.Core.Semantic Require Import Realizability RecordPER.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The record's fields' context, cut at the field [k]. *)
Lemma record_fctx_split : forall R k f A, List.nth_error (record_fields R) k = Some (f, A) ->
    exists X, record_fctx R (List.length (record_fields R)) = X ++ ce_ass A :: record_fctx R k.
Proof.
  intros * Hk; unfold record_fctx.
  rewrite List.firstn_all.
  pose proof (List.firstn_skipn (S k) (record_fields R)) as E.
  rewrite (firstn_S_snoc _ _ _ Hk) in E.
  exists (List.rev (List.map (fun fT : (String.string * typ)%type => ce_ass (snd fT)) (List.skipn (S k) (record_fields R)))).
  transitivity (List.rev (List.map (fun fT : (String.string * typ)%type => ce_ass (snd fT))
                  ((List.firstn k (record_fields R) ++ (f, A) :: nil) ++ List.skipn (S k) (record_fields R))));
    [ rewrite E; reflexivity |].
  rewrite !List.map_app, !List.rev_app_distr; cbn [List.map List.rev List.app snd]; reflexivity.
Qed.

(** The entry of an argument. *)
Lemma cargs_ctx_single : forall pq D nn pat g, exists G, cargs_ctx_aux pq D nn pat (g :: nil) = ce_ass G :: nil.
Proof. intros * ; destruct g; cbn; eexists; reflexivity. Qed.

(** A record's projections, by its fields' names. *)
Lemma record_projs_iff : forall R fl v vs, fl = List.map fst (record_fields R) ->
    (record_projs R v vs <-> ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ vs).
Proof.
  intros R fl v vs ->; unfold record_projs; generalize (record_fields R) as fs; intros fs; revert vs.
  induction fs as [| [f T] fs IH]; intros vs; cbn; split; intro H.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; subst; constructor; [ assumption | apply IH; assumption ].
  - inversion H; subst; constructor; [ assumption | apply IH; assumption ].
Qed.

(** Arguments related at a telescope with one more type: related at the
    telescope, and the last at the type's relation there. *)
Lemma per_gargs_snoc_inv : forall ts A E E' zs zs' x x', List.length zs = List.length ts ->
    per_gargs (ts ++ ce_ass A :: nil) E E' (zs ++ x :: nil) (zs' ++ x' :: nil) ->
    per_gargs ts E E' zs zs' /\ exists (i : nat) R, rel_typ i A (env_args E zs) A (env_args E' zs') R /\ R x x'.
Proof.
  intros * Hl H.
  assert (Hl' : List.length zs' = List.length ts).
  { destruct (per_gargs_length _ _ _ _ _ H) as [L _]; rewrite !List.length_app in L; cbn in L; lia. }
  destruct (per_gargs_app _ _ _ _ _ _ _ _ Hl H Hl') as [H1 H2].
  split; [ exact H1 |].
  inversion H2 as [| i T ? ? ? ? ? ? ? R HT Hxx]; subst; eauto.
Qed.

(** Two telescopes, each with one more type, whose arguments so far are
    related alike, and whose last types have the same relation there:
    their arguments are related alike. *)
Lemma per_gargs_snoc_transfer : forall ts1 A1 E1 E1' ts2 A2 E2 E2' zs zs' x x',
    List.length zs = List.length ts1 -> List.length zs = List.length ts2 ->
    (per_gargs ts1 E1 E1' zs zs' <-> per_gargs ts2 E2 E2' zs zs') ->
    (per_gargs ts1 E1 E1' zs zs' -> exists (i : nat) R, rel_typ i A1 (env_args E1 zs) A1 (env_args E1' zs') R) ->
    (per_gargs ts2 E2 E2' zs zs' -> exists (i : nat) R, rel_typ i A2 (env_args E2 zs) A2 (env_args E2' zs') R) ->
    (per_gargs ts1 E1 E1' zs zs' -> forall (i1 : nat) R1 (i2 : nat) R2,
       rel_typ i1 A1 (env_args E1 zs) A1 (env_args E1' zs') R1 -> rel_typ i2 A2 (env_args E2 zs) A2 (env_args E2' zs') R2 ->
       (R1 <~> R2)) ->
    (per_gargs (ts1 ++ ce_ass A1 :: nil) E1 E1' (zs ++ x :: nil) (zs' ++ x' :: nil) <->
     per_gargs (ts2 ++ ce_ass A2 :: nil) E2 E2' (zs ++ x :: nil) (zs' ++ x' :: nil)).
Proof.
  intros * Hl1 Hl2 Hiff Hv1 Hv2 HE; split; intro H.
  - destruct (per_gargs_snoc_inv _ _ _ _ _ _ _ _ Hl1 H) as [Hp (i1 & R1 & HR1 & Hx)].
    pose proof (proj1 Hiff Hp) as Hp2.
    destruct (Hv2 Hp2) as (i2 & R2 & HR2).
    apply (per_gargs_snoc _ _ _ _ _ _ _ _ i2 R2); [ exact Hl2 | exact Hp2 | exact HR2 |].
    exact (proj1 (HE Hp _ _ _ _ HR1 HR2 _ _) Hx).
  - destruct (per_gargs_snoc_inv _ _ _ _ _ _ _ _ Hl2 H) as [Hp2 (i2 & R2 & HR2 & Hx)].
    pose proof (proj2 Hiff Hp2) as Hp.
    destruct (Hv1 Hp) as (i1 & R1 & HR1).
    apply (per_gargs_snoc _ _ _ _ _ _ _ _ i1 R1); [ exact Hl1 | exact Hp | exact HR1 |].
    exact (proj2 (HE Hp _ _ _ _ HR1 HR2 _ _) Hx).
Qed.

(** ** The Telescopes of a Record View *)
Section RviewArgs.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (j : nat) (Mj : imember) (qr : qname) (Is : list exp) (fl : list String.string) (R : record_decl)
    (c : String.string) (gs : list carg).
  Hypotheses (HMj : ind_member D j = Some Mj) (Hh : im_head Mj = mh_record qr Is fl) (HR : valid_rview_record qr R)
    (Hcs : im_cons Mj = (c, gs) :: nil).
  Variables (ups cups : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups).
  Let HlR := valid_rview_record_lookup _ _ HR.
  Let HaR := typed_params_ass _ _ _ (valid_rview_record_typed _ _ HR).
  Let HWR := params_valid _ (valid_rview_record_valid _ _ HR).

  Lemma rv_nparams : im_nparams Mj = nil.
  Proof. exact (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh). Qed.

  Lemma rv_params : im_params D Mj = ind_uparams D.
  Proof. unfold im_params; rewrite rv_nparams; reflexivity. Qed.

  Lemma rv_nn : im_nn Mj = 0.
  Proof. unfold im_nn; rewrite rv_nparams; reflexivity. Qed.

  Lemma rv_con : ind_con Mj c = Some gs.
  Proof. exact (ind_con_single _ _ _ Hcs). Qed.

  Lemma rv_names : fl = List.map fst (record_fields R).
  Proof.
    destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as [R' HR'].
    pose proof (rview_record_lookup _ _ _ _ _ _ HR') as HlR'; rewrite HlR in HlR'; injection HlR' as <-.
    exact (rview_record_names _ _ _ _ _ _ HR').
  Qed.

  Lemma rv_len : List.length gs = List.length (record_fields R).
  Proof.
    destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs0 & Hcs0 & Hl0).
    rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
    rewrite Hl0, rv_names, List.length_map; reflexivity.
  Qed.

  Lemma rv_cups_rel : per_gargs (List.rev (record_params R)) nil nil cups cups.
  Proof.
    destruct (vg_rview_args_values p D Hg _ _ _ _ _ _ HMj Hh HR _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hc0).
    pose proof (functional_eval_exps' _ _ _ _ E0 Ecups) as ->; pose proof (functional_eval_exps' _ _ _ _ E0' Ecups) as ->.
    exact Hc0.
  Qed.

  Lemma rv_cups_len : List.length cups = List.length (record_params R).
  Proof. rewrite (eval_exps_length _ _ _ Ecups); exact (rview_record_len p D Hg _ _ _ _ _ _ HMj Hh HR). Qed.

  (** ** The Types at a Position

      At arguments [zs] before a field related at both telescopes, the
      field's type at [cups] and the constructor's argument's at [ups]
      have the same head PER, and both are types. *)
  Record rview_type_link (A G : typ) (Er Eg : env) : Prop := mk_rview_type_link
    { (** The two head PERs agree *)
      rtl_heads : per_head A A Er Er <~> per_head G G Eg Eg
      (** The group's type evaluates to a type *)
    ; rtl_group : exists (i : nat) R0 b, ⟦ G ⟧ Eg ↘ b /\ DF b ≈ b ∈ per_univ_elem i ↘ R0
      (** The field's type evaluates to a type *)
    ; rtl_record : exists (i : nat) R0 a, ⟦ A ⟧ Er ↘ a /\ DF a ≈ a ∈ per_univ_elem i ↘ R0
      (** The two types' values are related types *)
    ; rtl_types : exists (i : nat) R0, rel_typ i A Er G Eg R0 }.

  Lemma rview_arg_link : forall k f A gsA g gsB G zs, List.nth_error (record_fields R) k = Some (f, A) ->
      gs = gsA ++ g :: gsB -> List.length gsA = k -> List.length zs = k ->
      cargs_ctx p D Mj (gsA ++ g :: nil) = ce_ass G :: cargs_ctx p D Mj gsA ->
      per_gargs (List.rev (cargs_ctx p D Mj gsA ++ ind_uparams D)) nil nil (ups ++ zs) (ups ++ zs) ->
      per_gargs (List.rev (record_fctx R k ++ record_params R)) nil nil (cups ++ zs) (cups ++ zs) ->
      rview_type_link A G (env_args nil (cups ++ zs)) (env_args nil (ups ++ zs)).
  Proof.
    intros * Hk Heq Hlk Hlz HG Hg1 Hg2.
    (** The record view equation, cut at the position. *)
    destruct (vg_rview_fields p D Hg _ _ _ _ _ _ _ _ HMj Hh HlR Hcs) as [_ _ [Rx HRx]].
    destruct (record_fctx_split _ _ _ _ Hk) as [X EF0].
    assert (Eg : cargs_ctx p D Mj gs = cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB
                                         ++ ce_ass G :: cargs_ctx p D Mj gsA).
    { rewrite Heq; replace (gsA ++ g :: gsB) with ((gsA ++ g :: nil) ++ gsB) by (rewrite <- List.app_assoc; reflexivity).
      unfold cargs_ctx at 1; rewrite cargs_ctx_aux_app.
      change (cargs_ctx_aux p D (im_nn Mj) nil (gsA ++ g :: nil)) with (cargs_ctx p D Mj (gsA ++ g :: nil)).
      rewrite HG; reflexivity. }
    rewrite EF0, Eg, tele_sub_app in HRx; cbn [tele_sub centry_sub List.length] in HRx.
    rewrite <- !List.app_assoc in HRx; cbn [List.app] in HRx.
    assert (HlX : List.length X = List.length (cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB)).
    { assert (Hk0 : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
      pose proof (f_equal (@List.length _) EF0) as L.
      rewrite length_record_fctx in L by lia.
      rewrite List.length_app in L; cbn [List.length] in L; rewrite length_record_fctx in L by lia.
      rewrite length_cargs_ctx_aux.
      pose proof rv_len as Lg; rewrite Heq, List.length_app in Lg; cbn in Lg.
      lia. }
    assert (Hlt : List.length (tele_sub X (sb_qn (S (List.length (record_fctx R k))) (sb_of_list Id Is)))
                  = List.length (cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB))
      by (rewrite length_tele_sub; exact HlX).
    destruct (per_ctx_env_app_tail _ _ _ _ _ Hlt HRx) as (RT & HRT).
    destruct (per_ctx_env_ass_inv _ _ _ _ _ HRT) as (RT0 & HRT0 & _ & Hty).
    (** The group's prefix, at the arguments. *)
    destruct (vg_cargs_sem_all p D Hg Hcv j Mj c gs HMj rv_con gsA (g :: gsB) Heq) as [HWg _].
    rewrite rv_params in HWg.
    destruct (rel_ctx_wf_per_ctx_env HWg) as [RG HRG].
    assert (HρG : RG (env_args nil (ups ++ zs)) (env_args nil (ups ++ zs))).
    { apply (gargs_env_rel _ _ _ _ _ _ HRG HWg); [| exact Hg1 ].
      rewrite !List.length_app, length_cargs_ctx; unfold ind_nu in *; lia. }
    assert (E0 : RG <~> RT0)
      by (destruct (per_ctx_env_sym _ _ _ HRT0) as [HRT0' _]; eapply per_ctx_env_right_irrel; [ exact HRG | exact HRT0' ]).
    destruct (Hty _ _ (proj1 (E0 _ _) HρG)) as (i0 & R0 & [a1 b Ea1 Eb HR0]).
    (** The field's type, over [cups]. *)
    pose proof (valid_rview_record_valid _ _ HR) as [_ [is HS] HF HT].
    pose proof (record_typed_sort_univ _ _ _ (valid_rview_record_typed _ _ HR)) as Hsu.
    assert (Hkl : k <= List.length (record_fields R)) by (apply nth_error_lt_length in Hk; lia).
    pose proof (Records.Model.record_fctx_sem R HF k Hkl) as HWc.
    destruct (Records.Model.field_typ_large R Hsu HT k f A Hk) as [ic HCv].
    set (Δc := record_fctx R k).
    assert (HaC : tele_ass (Δc ++ record_params R)) by (apply record_fctx_params_ass; exact HaR).
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (closed_app_sem _ (ind_uparams D) HaC HWc HUD) as [HWcU _].
    pose proof (closed_app_valid _ (ind_uparams D) _ _ _ HaC HWc HUD HCv) as HCvU.
    rewrite <- List.app_assoc in HWcU, HCvU.
    assert (HaΔc : tele_ass Δc) by apply record_fctx_ass.
    destruct (gsub_props (vg_rview_args_gsub p D Hg _ _ _ _ _ _ HMj Hh HR)) as [Hτ _].
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id (env_args nil ups)) Ecups) as Eτ.
    destruct (rel_ctx_wf_per_ctx_env HWR) as [RQ HRQ].
    pose proof rv_cups_len as Hlc.
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)) by exact (gargs_env_rel _ _ _ _ _ _ HRQ HWR Hlc rv_cups_rel).
    assert (HQ1 : RQ (env_args nil cups) (env_args (env_args nil ups) cups))
      by exact (closed_env_base _ _ _ _ _ _ _ _ HaR HWR HRQ Hlc Hlc HQ0).
    assert (Hgc0 : per_gargs (List.rev Δc) (env_args nil cups) (env_args nil cups) zs zs).
    { rewrite List.rev_app_distr in Hg2.
      assert (Hlr : List.length cups = List.length (List.rev (record_params R))) by (rewrite List.length_rev; exact Hlc).
      destruct (per_gargs_app (List.rev (record_params R)) (List.rev Δc) nil nil cups cups zs zs Hlr Hg2 Hlr) as [_ H]; exact H. }
    assert (HWΔ : ⊨ List.rev (List.rev Δc) ++ record_params R) by (rewrite List.rev_involutive; exact HWc).
    pose proof (per_gargs_base _ _ _ HRQ HWΔ (List.Forall_rev HaΔc) _ _ _ _ _ _ HQ0 HQ1 HQ1 Hgc0) as Hgc1.
    assert (Hlx : List.length zs = List.length Δc) by (unfold Δc; rewrite length_record_fctx by exact Hkl; exact Hlz).
    destruct (outer_typ_link Δc (record_params R ++ ind_uparams D) (ind_uparams D) RU (sb_of_list Id Is) (env_args nil ups)
                (env_args (env_args nil ups) cups) A A ic HaΔc HWcU HCvU HRU Hτ HρU Eτ zs Hgc1 Hlx)
      as (a2 & b2 & Ea2 & Eb2 & [R2 HR2]).
    rewrite <- env_args_app in Ea2.
    pose proof (functional_eval_exp _ _ _ _ Ea2 Ea1) as ->.
    (** From the instance's base to none: the record's telescope is
        closed. *)
    destruct (rel_ctx_wf_per_ctx_env HWc) as [RK HRK].
    assert (Hl3 : List.length (cups ++ zs) = List.length (Δc ++ record_params R))
      by (rewrite !List.length_app, Hlc, Hlx; lia).
    assert (HKF : RK (env_args nil (cups ++ zs)) (env_args nil (cups ++ zs)))
      by exact (gargs_env_rel _ _ _ _ _ _ HRK HWc Hl3 Hg2).
    assert (HKF' : RK (env_args (env_args nil ups) (cups ++ zs)) (env_args nil (cups ++ zs)))
      by exact (closed_env_base _ _ _ _ nil nil (env_args nil ups) nil HaC HWc HRK Hl3 Hl3 HKF).
    destruct (rel_exp_of_typ_inversion_simple_at HRK HCv _ _ HKF') as (c1 & c2 & Ec1 & Ec2 & [Rk HRk]).
    replace (env_args (env_args (env_args nil ups) cups) zs) with (env_args (env_args nil ups) (cups ++ zs))
      in Eb2 by (rewrite env_args_app; reflexivity).
    pose proof (functional_eval_exp _ _ _ _ Eb2 Ec1) as ->.
    constructor.
    - etransitivity; [ symmetry; exact (per_head_right Ec1 Ec2 HRk) |].
      etransitivity; [ symmetry; exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR2 HRk) |].
      etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR2 | exact HR0 ] |].
      exact (per_head_right Ea1 Eb HR0).
    - exists i0, R0, b; split; [ exact Eb |].
      exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR0) HR0).
    - exists ic, Rk, c2; split; [ exact Ec2 |].
      exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRk) HRk).
    - assert (Hcb : Dom c2 ≈ b ∈ per_univ ic).
      { eapply per_univ_trans'; [ exact (per_univ_sym' _ _ _ (ex_intro _ Rk HRk)) |].
        eapply per_univ_trans'; [ exact (per_univ_sym' _ _ _ (ex_intro _ R2 HR2)) | exact (ex_intro _ R0 HR0) ]. }
      destruct Hcb as [Rcb HRcb].
      exists ic, Rcb; exact (mk_rel_mod_eval c2 b Ec2 Eb HRcb).
  Qed.

  Lemma record_fctx_succ : forall n f A, List.nth_error (record_fields R) n = Some (f, A) ->
      record_fctx R (S n) = ce_ass A :: record_fctx R n.
  Proof. intros * Hf; unfold record_fctx; rewrite (firstn_S_snoc _ _ _ Hf), List.map_app, List.rev_app_distr; reflexivity. Qed.

  (** ** The Two Telescopes Relate the Same Arguments

      The record's fields at [cups] and the record view's constructor's
      arguments at [ups], position by position. *)
  Lemma rview_tele_link : forall n zs zs', n <= List.length gs -> List.length zs = n -> List.length zs' = n ->
      (per_gargs (List.firstn n (Records.Model.field_tele R)) (env_args nil cups) (env_args nil cups) zs zs' <->
       per_gargs (List.rev (cargs_ctx p D Mj (List.firstn n gs))) (env_args nil ups) (env_args nil ups) zs zs').
  Proof.
    pose proof rv_len as Hlg.
    pose proof (valid_rview_record_valid _ _ HR) as [_ [is HS] HF HT].
    pose proof (record_typed_sort_univ _ _ _ (valid_rview_record_typed _ _ HR)) as Hsu.
    pose proof rv_cups_len as Hlc.
    destruct (rel_ctx_wf_per_ctx_env HWR) as [RQ HRQ].
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)) by exact (gargs_env_rel _ _ _ _ _ _ HRQ HWR Hlc rv_cups_rel).
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    induction n as [| n IH]; intros zs zs' Hn Hlz Hlz'.
    - destruct zs, zs'; try discriminate; cbn; unfold cargs_ctx; cbn; split; intro; constructor.
    - destruct (nth_error_lt_some' gs n ltac:(lia)) as [g Hg0].
      destruct (nth_error_lt_some' (record_fields R) n ltac:(lia)) as [[f A] Hf].
      assert (HfT : List.nth_error (Records.Model.field_tele R) n = Some (ce_ass A))
        by (unfold Records.Model.field_tele; rewrite List.nth_error_map, Hf; reflexivity).
      destruct (List.exists_last (l := zs) ltac:(intros ->; discriminate)) as (zs0 & x & ->).
      destruct (List.exists_last (l := zs') ltac:(intros ->; discriminate)) as (zs0' & x' & ->).
      rewrite List.length_app in Hlz, Hlz'; cbn in Hlz, Hlz'.
      assert (Lz : List.length zs0 = n) by lia; assert (Lz' : List.length zs0' = n) by lia.
      assert (Heq : gs = List.firstn n gs ++ g :: List.skipn (S n) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn n gs) = n) by (rewrite List.length_firstn; lia).
      destruct (cargs_ctx_single p D (im_nn Mj) (cargs_pat (List.firstn n gs)) g) as [G HG1].
      assert (HG : cargs_ctx p D Mj (List.firstn n gs ++ g :: nil) = ce_ass G :: cargs_ctx p D Mj (List.firstn n gs))
        by (rewrite cargs_ctx_snoc, HG1; reflexivity).
      rewrite (firstn_S_snoc _ _ _ HfT), (firstn_S_snoc _ _ _ Hg0), HG; cbn [List.rev].
      assert (Lft : List.length (List.firstn n (Records.Model.field_tele R)) = n)
        by (rewrite List.length_firstn, Records.Model.length_field_tele; lia).
      assert (Lcg : List.length (List.rev (cargs_ctx p D Mj (List.firstn n gs))) = n)
        by (rewrite List.length_rev, length_cargs_ctx; exact Lk).
      assert (EF0 : List.rev (record_fctx R n ++ record_params R)
                    = List.rev (record_params R) ++ List.firstn n (Records.Model.field_tele R))
        by (rewrite List.rev_app_distr, Records.Model.rev_record_fctx; reflexivity).
      (** The prefixes' contexts. *)
      pose proof (Records.Model.record_fctx_sem R HF n ltac:(lia)) as HWc.
      pose proof (Records.Model.record_fctx_sem R HF (S n) ltac:(lia)) as HWc1.
      rewrite (record_fctx_succ _ _ _ Hf) in HWc1.
      destruct (rel_ctx_wf_ass_inv HWc1) as [iA HAv].
      destruct (rel_ctx_wf_per_ctx_env HWc) as [RK HRK].
      destruct (vg_cargs_sem_all p D Hg Hcv j Mj c gs HMj rv_con (List.firstn (S n) gs) (List.skipn (S n) gs)
                  ltac:(rewrite List.firstn_skipn; reflexivity)) as [HWg1 _].
      rewrite (firstn_S_snoc _ _ _ Hg0), HG, rv_params in HWg1; cbn [List.app] in HWg1.
      destruct (rel_ctx_wf_ass_inv HWg1) as [iG HGv].
      pose proof (rel_ctx_wf_tail HWg1) as HWg.
      destruct (rel_ctx_wf_per_ctx_env HWg) as [RG HRG].
      assert (HtaC : tele_ass (List.firstn n (Records.Model.field_tele R)))
        by (rewrite <- Records.Model.rev_record_fctx; apply List.Forall_rev, record_fctx_ass).
      assert (HtaG : tele_ass (List.rev (cargs_ctx p D Mj (List.firstn n gs))))
        by (apply List.Forall_rev, cargs_ctx_aux_ass).
      apply per_gargs_snoc_transfer; [ lia | lia | exact (IH zs0 zs0' ltac:(lia) Lz Lz') | | |].
      + (** The field's types are related. *)
        intros Hp.
        assert (HE : RK (env_args nil (cups ++ zs0)) (env_args nil (cups ++ zs0'))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRK HWc); [ rewrite !List.length_app, length_record_fctx by lia; lia |].
          rewrite EF0; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlc | exact rv_cups_rel | exact Hp ]. }
        destruct (rel_exp_of_typ_inversion_simple_at HRK HAv _ _ HE) as (a & a' & Ea & Ea' & [R0 HR0]).
        rewrite env_args_app in Ea, Ea'.
        exists iA, R0; exact (mk_rel_mod_eval _ _ Ea Ea' HR0).
      + (** The constructor's argument types are related. *)
        intros Hp.
        assert (HE : RG (env_args nil (ups ++ zs0)) (env_args nil (ups ++ zs0'))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRG HWg); [ rewrite !List.length_app, length_cargs_ctx; unfold ind_nu in *; lia |].
          rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; unfold ind_nu in *; lia | exact Hgu | exact Hp ]. }
        destruct (rel_exp_of_typ_inversion_simple_at HRG HGv _ _ HE) as (b & b' & Eb & Eb' & [R0 HR0]).
        rewrite env_args_app in Eb, Eb'.
        exists iG, R0; exact (mk_rel_mod_eval _ _ Eb Eb' HR0).
      + (** Their relations agree: the heads at the left prefix. *)
        intros Hp i1 R1 i2 R2 [a a' Ea Ea' HR1] [b b' Eb Eb' HR2].
        assert (HpL : per_gargs (List.firstn n (Records.Model.field_tele R)) (env_args nil cups) (env_args nil cups) zs0 zs0).
        { assert (HWr : ⊨ List.rev (List.firstn n (Records.Model.field_tele R)) ++ record_params R)
            by (rewrite <- Records.Model.rev_record_fctx, List.rev_involutive; exact HWc).
          exact (per_gargs_refl_l _ _ _ HRQ HWr HtaC _ _ _ _ HQ0 Hp). }
        pose proof (proj1 (IH zs0 zs0 ltac:(lia) Lz Lz) HpL) as HqL.
        assert (Hg1 : per_gargs (List.rev (cargs_ctx p D Mj (List.firstn n gs) ++ ind_uparams D)) nil nil (ups ++ zs0) (ups ++ zs0)).
        { rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; unfold ind_nu in *; lia | exact Hgu | exact HqL ]. }
        assert (Hg2 : per_gargs (List.rev (record_fctx R n ++ record_params R)) nil nil (cups ++ zs0) (cups ++ zs0)).
        { rewrite EF0; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlc | exact rv_cups_rel | exact HpL ]. }
        pose proof (rview_arg_link n f A (List.firstn n gs) g (List.skipn (S n) gs) G zs0 Hf Heq Lk Lz HG Hg1 Hg2) as Hlk.
        rewrite <- !env_args_app in Ea, Eb.
        etransitivity; [ exact (per_head_left Ea Ea' HR1) |].
        etransitivity; [ exact (rtl_heads _ _ _ _ Hlk) |].
        symmetry; exact (per_head_left Eb Eb' HR2).
  Qed.

  (** ** The Elements

      Given the relations of the types of the members the recursive
      fields' shapes end in, the record's elements at [cups] are the
      group's at the record view, at the bases [ups]. *)
  Lemma rview_elems : (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        view_end_rel p D ups ups (ptyp_mem t) /\ rview_end_rel p D ups ups (ptyp_mem t)) ->
      forall x y, record_rel R (canon_fields_rel R cups) x y <->
        grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) j ups ups nil nil x y.
  Proof.
    intros Hends x y.
    pose proof rv_len as Hlg.
    pose proof (valid_rview_record_valid _ _ HR) as [_ [is HS] HF HT].
    pose proof (record_typed_sort_univ _ _ _ (valid_rview_record_typed _ _ HR)) as Hsu.
    destruct (Records.Model.sort_tele_value (record_params R) (record_sort R) HWR (ex_intro _ is HS) cups rv_cups_rel rv_cups_len)
      as [a Ha].
    assert (Hf : List.firstn (ind_nu D) ups = ups) by (apply List.firstn_all2; lia).
    assert (Hs : List.skipn (ind_nu D) ups = nil) by (apply List.skipn_all2; lia).
    assert (Hgp : per_gargs (List.rev (im_params D Mj)) nil nil ups ups) by (rewrite rv_params; exact Hgu).
    assert (Hlp : List.length ups = im_np D Mj) by (unfold im_np; rewrite rv_nn; lia).
    assert (Hn0 : tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) nil nil)
      by (rewrite rv_nparams; split; reflexivity + exact I).
    assert (Hends' : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
              view_end_rel p D (List.firstn (ind_nu D) ups) (List.firstn (ind_nu D) ups) (ptyp_mem t) /\
              rview_end_rel p D (List.firstn (ind_nu D) ups) (List.firstn (ind_nu D) ups) (ptyp_mem t))
      by (rewrite Hf; exact Hends).
    assert (EN : List.firstn (List.length (record_fields R)) gs = gs) by (apply List.firstn_all2; lia).
    split.
    - intros [ws ws' Hp Hp' Hrel].
      pose proof (record_projs_length _ _ _ Hp) as Lw.
      pose proof (record_projs_length _ _ _ Hp') as Lw'.
      pose proof (Records.Model.canon_fields_gargs R Hsu HF (ex_intro _ is HS) HT cups cups a rv_cups_rel rv_cups_len Ha
                    (List.length (record_fields R)) ws ws' (le_n _) (tele_rel_pre _ _ _ _ Hrel)) as HgF.
      pose proof (proj1 (rview_tele_link (List.length (record_fields R)) ws ws' ltac:(lia) Lw Lw') HgF) as HgC.
      rewrite EN in HgC.
      destruct (con_args_canon p D Hg Hcv j Mj c gs HMj rv_con ups ups ws ws' Hgp Hlp HgC ltac:(lia) Hends') as [Hnr Hia].
      rewrite Hf, Hs in Hnr, Hia.
      eapply ind_rel_record; [ exact HMj | exact Hh | exact rv_nparams | exact Hcs
                             | apply (record_projs_iff R fl); [ exact rv_names | exact Hp ]
                             | apply (record_projs_iff R fl); [ exact rv_names | exact Hp' ]
                             | exact Hnr | exact Hia ].
    - intros Hxy; inversion Hxy; subst; try no_rview_rel.
      match goal with H0 : ind_member D j = Some ?M0, H0' : im_head ?M0 = _, H0'' : im_cons ?M0 = _ |- _ =>
        rewrite HMj in H0; injection H0 as <-; rewrite Hh in H0'; injection H0' as <- <- <-;
        rewrite Hcs in H0''; injection H0'' as <- <- end.
      match goal with Hq1 : ⟦projs fl of x ⟧ _ ⍮ _ ↘ ?ws, Hq2 : ⟦projs fl of y ⟧ _ ⍮ _ ↘ ?ws',
                      Ha1 : tele_rel _ _ _ _, Ha2 : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        rename Hq1 into Hp; rename Hq2 into Hp'; rename Ha1 into Hnr; rename Ha2 into Hia end.
      apply (record_projs_iff R fl _ _ rv_names) in Hp, Hp'.
      pose proof (record_projs_length _ _ _ Hp) as Lw.
      pose proof (record_projs_length _ _ _ Hp') as Lw'.
      pose proof (cargs_gargs p D Hg Hcv ups Hgu Hu j Mj c gs HMj rv_con Hends nil nil _ _ Hn0 Hnr Hia
                    (List.length (record_fields R)) ltac:(lia)) as HgC.
      rewrite EN, List.app_nil_r, !List.firstn_all2 in HgC by lia.
      pose proof (proj2 (rview_tele_link (List.length (record_fields R)) _ _ ltac:(lia) Lw Lw') ltac:(rewrite EN; exact HgC)) as HgF.
      assert (Htr : forall k0 A0 pre, List.nth_error (List.firstn (List.length (record_fields R)) (Records.Model.field_tele R)) k0 = Some (ce_ass A0) ->
                (canon_fields_rel R cups k0 pre <~> per_head A0 A0 (env_args (env_args nil cups) pre) (env_args (env_args nil cups) pre))).
      { intros k0 A0 pre Hk0.
        rewrite List.firstn_all2 in Hk0 by (rewrite Records.Model.length_field_tele; lia).
        destruct (Records.Model.field_tele_nth _ _ _ Hk0) as [f0 Hf0].
        unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hf0), <- !env_args_app; reflexivity. }
      pose proof (gargs_tele_canon _ _ _ Htr _ _ _ HgF ltac:(rewrite List.length_firstn, Records.Model.length_field_tele; lia)) as Htl.
      econstructor; [ exact Hp | exact Hp' |].
      destruct Htl as [_ Htl]; split; [ exact Lw | exact Htl ].
  Qed.
End RviewArgs.

(** ** The Pseudo-Constructor of a Record View

    At parameters and arguments related at their telescopes, the tuple of
    the arguments, by the fields' names, is an element of the record view
    at the canonical relations. *)
Lemma con_rel_rview : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk qr Is fl c gs, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl -> im_cons Mk = (c, gs) :: nil ->
    forall ps ps' as1 as1', per_gargs (List.rev (im_params D Mk)) nil nil ps ps' -> List.length ps = im_np D Mk ->
      per_gargs (List.rev (cargs_ctx p D Mk gs)) (env_args nil ps) (env_args nil ps') as1 as1' -> List.length as1 = List.length gs ->
      (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
         view_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t) /\
         rview_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t)) ->
      ind_rel p D (okr_at D (List.firstn (ind_nu D) ps) (canon_nparams_rel D (List.firstn (ind_nu D) ps)))
        (canon_nparams_rel D (List.firstn (ind_nu D) ps)) (canon_args_rel D (List.firstn (ind_nu D) ps))
        (canon_doms_rel (List.firstn (ind_nu D) ps)) k (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps') nil nil
        (d_tuple (List.combine fl as1)) (d_tuple (List.combine fl as1')).
Proof.
  intros p D Hg Hcv k Mk qr Is fl c gs HM Hh Hcs ps ps' as1 as1' Hgp Hlp Hga Hla Hends.
  pose proof (valid_group_typed _ _ Hg) as Hdt.
  pose proof (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HM Hh) as Hnp.
  pose proof (ind_con_single _ _ _ Hcs) as Hcon.
  destruct (con_args_canon p D Hg Hcv k Mk c gs HM Hcon ps ps' as1 as1' Hgp Hlp Hga Hla Hends) as [Hnr Hia].
  assert (Hlp' : List.length ps' = im_np D Mk) by (destruct (per_gargs_length _ _ _ _ _ Hgp) as [L _]; lia).
  assert (Hnn : im_nn Mk = 0) by (unfold im_nn; rewrite Hnp; reflexivity).
  assert (Hs : List.skipn (ind_nu D) ps = nil) by (apply List.skipn_all2; unfold im_np in Hlp; lia).
  assert (Hs' : List.skipn (ind_nu D) ps' = nil) by (apply List.skipn_all2; unfold im_np in Hlp'; lia).
  rewrite Hs in Hnr, Hia; rewrite Hs' in Hia.
  pose proof (per_gargs_length _ _ _ _ _ Hga) as [Hla' _].
  destruct (valid_group_records _ _ Hg _ _ _ _ _ HM Hh) as [R HR].
  pose proof (rv_names p D Hg k Mk qr Is fl R HM Hh HR) as Hfl.
  pose proof (rv_len p D Hg k Mk qr Is fl R c gs HM Hh HR Hcs) as Hlg.
  pose proof (typed_nodup _ _ _ (valid_rview_record_typed _ _ HR)) as Hnd.
  assert (Hpj : forall vs, List.length vs = List.length gs -> ⟦projs fl of d_tuple (List.combine fl vs) ⟧ gc_deps ⍮ gc_stack ↘ vs).
  { intros vs Lv; apply (record_projs_iff R fl _ _ Hfl).
    pose proof (Records.Model.tuple_projs R Hnd (record_fields R) vs eq_refl ltac:(lia)) as H.
    rewrite <- Hfl in H; exact H. }
  eapply ind_rel_record; [ exact HM | exact Hh | exact Hnp | exact Hcs | exact (Hpj as1 Hla) | exact (Hpj as1' ltac:(lia)) | exact Hnr | exact Hia ].
Qed.

(** ** The Coherence of a Record View

    Given the relations of the types of the members its recursive fields'
    shapes end in, the record view's type relates the group's elements
    there. *)
Lemma rview_end_rel_of_ends : forall p D, valid_group p D -> containers_valid D ->
    forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall j, (forall Mj qr Is fl c gs gs1 t gs2, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
                 im_cons Mj = (c, gs) :: nil -> gs = gs1 ++ ca_rec t :: gs2 ->
                 view_end_rel p D ups ups (ptyp_mem t) /\ rview_end_rel p D ups ups (ptyp_mem t)) ->
      rview_end_rel p D ups ups' j.
Proof.
  intros p D Hg Hcv ups ups' Hgu Hu j Hends Mj qr Is fl R cups cups' HMj Hh HlR Ecups Ecups' cs cs' i Rel Hcs Hcs' HRel.
  pose proof (uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu) as Hgd.
  destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R0 HR0].
  rewrite (valid_rview_record_lookup _ _ HR0) in HlR; injection HlR as ->.
  destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HMj Hh) as (gs & Hcs0 & _).
  (** The record's relation at the instance's value. *)
  pose proof (rv_cups_len p D Hg j Mj qr Is fl R HMj Hh HR0 ups cups Ecups) as Hlc.
  destruct (vrr_type_rel qr R cups cs HR0 Hcs Hlc) as [i1 HR1].
  assert (E1 : record_rel R (canon_fields_rel R cups) <~> Rel) by exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR1 HRel).
  (** The group's, at the bases [ups]. *)
  pose proof (rview_elems p D Hg Hcv j Mj qr Is fl R rview_con gs HMj Hh HR0 Hcs0 ups cups Hgd Hu Ecups
                (fun gs1 t gs2 Heq => Hends _ _ _ _ _ _ gs1 t gs2 HMj Hh Hcs0 Heq)) as E2.
  (** And at the bases [ups] and [ups']. *)
  destruct (vg_canon p D Hg ups Hgd Hu) as [CnP CnI CaP CaI CdP CdI].
  pose proof (vg_adm p D Hg ups ups Hgd Hu Hgd) as Add.
  pose proof (vg_adm p D Hg ups ups' Hgd Hu Hgu) as Ad'.
  intros x y; split; intro Hxy.
  - apply E1, E2 in Hxy.
    exact (proj1 (ind_rel_base_r p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI ups' Ad' ups Add) _ _ _ _ _ _ _ Hxy eq_refl).
  - pose proof (proj1 (ind_rel_base_r p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI ups Add ups' Ad')
                  _ _ _ _ _ _ _ Hxy eq_refl) as H.
    apply E1, E2, H.
Qed.

End Fixed_GCtx.
