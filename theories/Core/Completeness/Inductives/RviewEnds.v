(** * The Elements of a Record View, as the Record's

    A record view [j] of a group [D] at [p] is the record [R] at [qr] at
    the instance [Is]: its type is the record's at [⟦Is⟧ups], so its
    elements are related by the record's relation there, field by field.
    The group relates them by its own relation at the record view
    ([ind_rel_record]): their projections, as the arguments of the record
    view's constructor.  The record view equation ([valid_group_views_rview_fields]) makes
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
    exists X, record_fctx R (List.length (record_fields R)) = X ++ ce_ass (record_field_kind R k) A :: record_fctx R k.
Proof.
  intros * Hk.
  assert (Hkl : S k <= List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
  assert (HS : record_fctx R (S k) = ce_ass (record_field_kind R k) A :: record_fctx R k).
  { unfold record_fctx; rewrite (firstn_S_snoc _ _ _ Hk), fields_tele_snoc.
    rewrite List.length_firstn, Nat.min_l by lia; reflexivity. }
  unfold record_fctx in HS |- *; rewrite List.firstn_all.
  exists (fields_tele (List.skipn (S k) (record_fields R)) (List.skipn (List.length (List.firstn (S k) (record_fields R))) (record_field_kinds R))).
  rewrite <- HS, <- fields_tele_app, List.firstn_skipn; reflexivity.
Qed.

(** A closed telescope's arguments, related to themselves, over no base
    and over any other: related environments of the telescope's context,
    and arguments over the other base. *)
Lemma closed_tele_base_rel : forall C RC ρ ρ' xs, all_assumptions C -> ⊨ C -> EF C ≈ C ∈ per_ctx_env ↘ RC ->
    per_tele_args (List.rev C) nil nil xs xs -> List.length xs = List.length C ->
    RC (env_tele nil (List.rev C) xs) (env_tele ρ (List.rev C) xs) /\ per_tele_args (List.rev C) ρ ρ' xs xs.
Proof.
  intros * Ha HC HRC Hg Hl.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (Ha' : all_assumptions (List.rev C)) by (apply List.Forall_rev; exact Ha).
  pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HC' Ha' nil nil nil ρ xs xs I I I Hg) as Hg1.
  pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HC' Ha' nil nil ρ ρ' xs xs I I I Hg) as Hg2.
  split; [| exact Hg2 ].
  assert (HRC' : EF C ++ ⋅ ≈ C ++ ⋅ ∈ per_ctx_env ↘ RC) by (rewrite List.app_nil_r; exact HRC).
  assert (HC0 : ⊨ C ++ ⋅) by (rewrite List.app_nil_r; exact HC).
  exact (tele_args_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HRC' HC0 I Hl Hg1).
Qed.

Lemma cargs_ctx_single : forall pq D nn pat g, exists κ G, cargs_ctx_aux pq D nn pat (g :: nil) = ce_ass κ G :: nil.
Proof. intros * ; destruct g; cbn; do 2 eexists; reflexivity. Qed.

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
Lemma per_tele_args_snoc_inv : forall ts κ A E E' zs zs' x x', List.length zs = List.length ts ->
    per_tele_args (ts ++ ce_ass κ A :: nil) E E' (zs ++ x :: nil) (zs' ++ x' :: nil) ->
    per_tele_args ts E E' zs zs' /\ exists (i : nat) R, rel_typ i A (env_tele E ts zs) A (env_tele E' ts zs') R /\ R x x'.
Proof.
  intros * Hl H.
  assert (Hl' : List.length zs' = List.length ts).
  { destruct (per_tele_args_length _ _ _ _ _ H) as [L _]; rewrite !List.length_app in L; cbn in L; lia. }
  destruct (per_tele_args_app _ _ _ _ _ _ _ _ Hl H Hl') as [H1 H2].
  split; [ exact H1 |].
  inversion H2 as [| i T ? ? ? ? ? ? ? ? R HT Hxx]; subst; eauto.
Qed.

(** Two telescopes, each with one more type, whose arguments so far are
    related alike, and whose last types have the same relation there:
    their arguments are related alike. *)
Lemma per_tele_args_snoc_transfer : forall ts1 κ1 A1 E1 E1' ts2 κ2 A2 E2 E2' zs zs' x x',
    List.length zs = List.length ts1 -> List.length zs = List.length ts2 ->
    (per_tele_args ts1 E1 E1' zs zs' <-> per_tele_args ts2 E2 E2' zs zs') ->
    (per_tele_args ts1 E1 E1' zs zs' -> exists (i : nat) R, rel_typ i A1 (env_tele E1 ts1 zs) A1 (env_tele E1' ts1 zs') R) ->
    (per_tele_args ts2 E2 E2' zs zs' -> exists (i : nat) R, rel_typ i A2 (env_tele E2 ts2 zs) A2 (env_tele E2' ts2 zs') R) ->
    (per_tele_args ts1 E1 E1' zs zs' -> forall (i1 : nat) R1 (i2 : nat) R2,
       rel_typ i1 A1 (env_tele E1 ts1 zs) A1 (env_tele E1' ts1 zs') R1 -> rel_typ i2 A2 (env_tele E2 ts2 zs) A2 (env_tele E2' ts2 zs') R2 ->
       (R1 <~> R2)) ->
    (per_tele_args (ts1 ++ ce_ass κ1 A1 :: nil) E1 E1' (zs ++ x :: nil) (zs' ++ x' :: nil) <->
     per_tele_args (ts2 ++ ce_ass κ2 A2 :: nil) E2 E2' (zs ++ x :: nil) (zs' ++ x' :: nil)).
Proof.
  intros * Hl1 Hl2 Hiff Hv1 Hv2 HE; split; intro H.
  - destruct (per_tele_args_snoc_inv _ _ _ _ _ _ _ _ _ Hl1 H) as [Hp (i1 & R1 & HR1 & Hx)].
    pose proof (proj1 Hiff Hp) as Hp2.
    destruct (Hv2 Hp2) as (i2 & R2 & HR2).
    apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ i2 R2); [ exact Hl2 | exact Hp2 | exact HR2 |].
    exact (proj1 (HE Hp _ _ _ _ HR1 HR2 _ _) Hx).
  - destruct (per_tele_args_snoc_inv _ _ _ _ _ _ _ _ _ Hl2 H) as [Hp2 (i2 & R2 & HR2 & Hx)].
    pose proof (proj2 Hiff Hp2) as Hp.
    destruct (Hv1 Hp) as (i1 & R1 & HR1).
    apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ i1 R1); [ exact Hl1 | exact Hp | exact HR1 |].
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
  Hypotheses (Hgu : per_tele_args (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups).
  Let HlR := valid_rview_record_lookup _ _ HR.
  Let HaR := typed_params_ass _ _ _ (valid_rview_record_typed _ _ HR).
  Let HWR := params_valid _ (valid_rview_record_valid _ _ HR).

  Lemma rview_args_nparams : im_nparams Mj = nil.
  Proof. exact (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh). Qed.

  Lemma rview_args_params : im_params D Mj = ind_uparams D.
  Proof. unfold im_params; rewrite rview_args_nparams; reflexivity. Qed.

  Lemma rview_args_nn : im_nn Mj = 0.
  Proof. unfold im_nn; rewrite rview_args_nparams; reflexivity. Qed.

  Lemma rview_args_con : ind_con Mj c = Some gs.
  Proof. exact (ind_con_single _ _ _ Hcs). Qed.

  Lemma rview_args_names : fl = List.map fst (record_fields R).
  Proof.
    destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as [R' HR'].
    pose proof (rview_record_lookup _ _ _ _ _ _ HR') as HlR'; rewrite HlR in HlR'; injection HlR' as <-.
    exact (rview_record_names _ _ _ _ _ _ HR').
  Qed.

  Lemma rview_args_len : List.length gs = List.length (record_fields R).
  Proof.
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs0 & Hcs0 & Hl0).
    rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
    rewrite Hl0, rview_args_names, List.length_map; reflexivity.
  Qed.

  Lemma rview_args_container_uparams_rel : per_tele_args (List.rev (record_params R)) nil nil cups cups.
  Proof.
    destruct (valid_group_views_rview_args_values p D Hg _ _ _ _ _ _ HMj Hh HR _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hc0).
    pose proof (functional_eval_exps' _ _ _ _ E0 Ecups) as ->; pose proof (functional_eval_exps' _ _ _ _ E0' Ecups) as ->.
    exact Hc0.
  Qed.

  Lemma rview_args_container_uparams_len : List.length cups = List.length (record_params R).
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

  Lemma rview_arg_link : forall k f A gsA g gsB κG G zs, List.nth_error (record_fields R) k = Some (f, A) ->
      gs = gsA ++ g :: gsB -> List.length gsA = k -> List.length zs = k ->
      cargs_ctx p D Mj (gsA ++ g :: nil) = ce_ass κG G :: cargs_ctx p D Mj gsA ->
      per_tele_args (List.rev (cargs_ctx p D Mj gsA ++ ind_uparams D)) nil nil (ups ++ zs) (ups ++ zs) ->
      per_tele_args (List.rev (record_fctx R k ++ record_params R)) nil nil (cups ++ zs) (cups ++ zs) ->
      rview_type_link A G (env_tele (env_tele nil (List.rev (record_params R)) cups) (List.firstn k (Records.Model.field_tele R)) zs)
        (env_tele (decl_env D ups) (List.rev (cargs_ctx p D Mj gsA)) zs).
  Proof.
    intros * Hk Heq Hlk Hlz HG Hg1 Hg2.
    set (EU := decl_env D ups).
    set (Pc := env_tele nil (List.rev (record_params R)) cups).
    pose proof rview_args_container_uparams_len as Hlc.
    (** The record view equation, cut at the position. *)
    destruct (valid_group_views_rview_fields p D Hg _ _ _ _ _ _ _ _ HMj Hh HlR Hcs) as [_ _ [Rx HRx]].
    destruct (record_fctx_split _ _ _ _ Hk) as [X EF0].
    assert (Eg : cargs_ctx p D Mj gs = cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB
                                         ++ ce_ass κG G :: cargs_ctx p D Mj gsA).
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
      pose proof rview_args_len as Lg; rewrite Heq, List.length_app in Lg; cbn in Lg.
      lia. }
    assert (Hlt : List.length (tele_sub X (sb_qn (S (List.length (record_fctx R k))) (sb_of_list Id Is)))
                  = List.length (cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB))
      by (rewrite length_tele_sub; exact HlX).
    destruct (per_ctx_env_app_tail _ _ _ _ _ Hlt HRx) as (RT & HRT).
    destruct (per_ctx_env_ass_inv _ _ _ _ _ _ _ HRT) as (RT0 & HRT0 & _ & Hty).
    (** The group's prefix, at the arguments. *)
    destruct (valid_group_cargs_sem_all p D Hg Hcv j Mj c gs HMj rview_args_con gsA (g :: gsB) Heq) as [HWg _].
    rewrite rview_args_params in HWg.
    destruct (rel_ctx_wf_per_ctx_env HWg) as [RG HRG].
    assert (HlU : List.length ups = List.length (ind_uparams D)) by (unfold ind_nu in Hu; exact Hu).
    set (EG := env_tele EU (List.rev (cargs_ctx p D Mj gsA)) zs).
    assert (HEgc : env_tele nil (List.rev (cargs_ctx p D Mj gsA ++ ind_uparams D)) (ups ++ zs) = EG)
      by (unfold EG, EU, decl_env; apply env_tele_closed_app; exact HlU).
    assert (HρG : RG EG EG).
    { rewrite <- HEgc; apply (tele_args_env_rel _ _ _ _ _ _ HRG HWg); [| exact Hg1 ].
      rewrite !List.length_app, length_cargs_ctx; unfold ind_nu in *; lia. }
    assert (E0 : RG <~> RT0)
      by (destruct (per_ctx_env_sym _ _ _ HRT0) as [HRT0' _]; eapply per_ctx_env_right_irrel; [ exact HRG | exact HRT0' ]).
    destruct (Hty _ _ (proj1 (E0 _ _) HρG)) as (i0 & R0 & [a1 b Ea1 Eb HR0]).
    (** The group's arguments, with their types. *)
    rewrite List.rev_app_distr in Hg1.
    destruct (per_tele_args_app (List.rev (ind_uparams D)) (List.rev (cargs_ctx p D Mj gsA)) nil nil ups ups zs zs
                ltac:(rewrite List.length_rev; exact HlU) Hg1 ltac:(rewrite List.length_rev; exact HlU)) as [_ Hgz].
    fold (decl_env D ups) EU in Hgz.
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hgz) as [Rvg _].
    set (vtsg := tele_entries EU (List.rev (cargs_ctx p D Mj gsA)) zs) in *.
    assert (Hvg : List.map fst vtsg = zs) by apply tele_entries_values.
    (** The field's type, over [cups]. *)
    pose proof (valid_rview_record_valid _ _ HR) as [_ HPr [is HS] HF HT HFk].
    pose proof (record_typed_sort_univ _ _ _ (valid_rview_record_typed _ _ HR)) as Hsu.
    assert (Hkl : k <= List.length (record_fields R)) by (apply nth_error_lt_length in Hk; lia).
    pose proof (Records.Model.record_fctx_sem R HF k Hkl) as HWc.
    (** The field's type is of a sort, a type of one universe there. *)
    destruct (Records.Model.field_typ_sort R Hsu HT HFk k f A Hk) as (Sc & HSc & HCv).
    destruct (rel_type_of_sort_at (sort_kind_type_sort _ _ HSc)) as [ic Hic].
    set (Δc := record_fctx R k).
    assert (HaC : all_assumptions (Δc ++ record_params R)) by (apply record_fctx_params_ass; exact HaR).
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (closed_app_sem _ (ind_uparams D) HaC HWc HUD) as [HWcU _].
    pose proof (closed_app_valid _ (ind_uparams D) _ _ _ HaC HWc HUD HCv) as HCvU.
    rewrite <- List.app_assoc in HWcU, HCvU.
    assert (HaΔc : all_assumptions Δc) by apply record_fctx_ass.
    destruct (gsub_props (valid_group_views_rview_args_gsub p D Hg _ _ _ _ _ _ HMj Hh HR)) as [Hτ _].
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU; fold EU in HρU.
    (** The instance's value: the record's parameters at [cups], over the
        uniform parameters. *)
    destruct (valid_group_views_rview_args_sub_eval p D Hg _ _ _ _ _ _ HMj Hh HR _ _ Hgu Hu) as (cups0 & Ecups0 & Eτ).
    pose proof (functional_eval_exps' _ _ _ _ Ecups0 Ecups) as ->; fold EU in Eτ.
    set (Ec := components_env D ups (List.rev (record_params R)) cups) in *.
    destruct (rel_ctx_wf_per_ctx_env HWR) as [RQ HRQ].
    destruct (closed_tele_base_rel (record_params R) RQ EU EU cups HaR HWR HRQ rview_args_container_uparams_rel Hlc) as [HQ1 HgcU].
    fold Pc in HQ1; change (env_tele EU (List.rev (record_params R)) cups) with Ec in HQ1.
    assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
    assert (HQ0 : RQ Pc Pc) by (etransitivity; [ exact HQ1 | symmetry; exact HQ1 ]).
    assert (HQ2 : RQ Ec Ec) by (etransitivity; [ symmetry; exact HQ1 | exact HQ1 ]).
    assert (Hgc0 : per_tele_args (List.rev Δc) Pc Pc zs zs).
    { rewrite List.rev_app_distr in Hg2.
      assert (Hlr : List.length cups = List.length (List.rev (record_params R))) by (rewrite List.length_rev; exact Hlc).
      destruct (per_tele_args_app (List.rev (record_params R)) (List.rev Δc) nil nil cups cups zs zs Hlr Hg2 Hlr) as [_ H]; exact H. }
    assert (HWΔ : ⊨ List.rev (List.rev Δc) ++ record_params R) by (rewrite List.rev_involutive; exact HWc).
    pose proof (per_tele_args_base _ _ _ HRQ HWΔ (List.Forall_rev HaΔc) _ _ _ _ _ _ HQ0 HQ1 HQ1 Hgc0) as Hgc1.
    assert (Hlx : List.length zs = List.length Δc) by (unfold Δc; rewrite length_record_fctx by exact Hkl; exact Hlz).
    (** The field's type under the instance, at the group's arguments, is
        the field's type at the instance's value extended by them. *)
    rewrite <- Hvg in Hgc1.
    destruct (outer_type_link Δc (record_params R ++ ind_uparams D) (ind_uparams D) RU (sb_of_list Id Is) EU Ec A ic
                HaΔc HWcU (Hic _ _ _ HCvU) HRU Hτ HρU Eτ vtsg Hgc1
                ltac:(unfold vtsg; rewrite tele_entries_length; exact Hlx) Rvg)
      as (a2 & b2 & Ea2 & Eb2 & [R2 HR2]).
    change (env_extend_typed EU vtsg) with EG in Ea2.
    pose proof (functional_eval_exp _ _ _ _ Ea2 Ea1) as ->.
    (** From the instance's base to none: the record's telescope is
        closed. *)
    destruct (rel_ctx_wf_per_ctx_env HWc) as [RK HRK].
    assert (Hl3 : List.length (cups ++ zs) = List.length (Δc ++ record_params R))
      by (rewrite !List.length_app, Hlc, Hlx; lia).
    set (Kc := env_tele nil (List.rev (Δc ++ record_params R)) (cups ++ zs)).
    assert (HKF : RK Kc Kc) by exact (tele_args_env_rel _ _ _ _ _ _ HRK HWc Hl3 Hg2).
    pose proof (per_tele_args_entries_readable _ _ _ _ _ HgcU) as [Rvc _].
    assert (HKF' : RK (env_extend_typed EU (tele_entries EU (List.rev (record_params R)) cups ++ vtsg)) Kc).
    { set (vtsK := tele_entries nil (List.rev (Δc ++ record_params R)) (cups ++ zs)).
      assert (HKl : List.length vtsK = List.length (Δc ++ record_params R)) by (unfold vtsK; rewrite tele_entries_length; exact Hl3).
      pose proof (per_tele_args_entries_readable _ _ _ _ _ Hg2) as [Rvk _]; fold vtsK in Rvk.
      apply (closed_env_base (Δc ++ record_params R) RK vtsK vtsK (tele_entries EU (List.rev (record_params R)) cups ++ vtsg) vtsK
               nil nil EU nil HaC HWc HRK HKl HKl); [ | reflexivity | | exact Rvk | exact HKF ].
      - unfold vtsK; rewrite List.map_app, !tele_entries_values, Hvg; reflexivity.
      - apply List.Forall_app; split; assumption. }
    destruct (rel_type_inversion_simple_at HRK (Hic _ _ _ HCv) _ _ HKF') as (c1 & c2 & Ec1 & Ec2 & [Rk HRk]).
    rewrite env_extend_typed_app in Ec1; change (env_extend_typed EU (tele_entries EU (List.rev (record_params R)) cups)) with Ec in Ec1.
    pose proof (functional_eval_exp _ _ _ _ Eb2 Ec1) as ->.
    assert (HKc : Kc = env_tele Pc (List.firstn k (Records.Model.field_tele R)) zs).
    { unfold Kc, Pc; rewrite (env_tele_closed_app (record_params R) Δc cups zs Hlc).
      unfold Δc; rewrite Records.Model.rev_record_fctx; reflexivity. }
    rewrite HKc in Ec2.
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
      record_fctx R (S n) = ce_ass (record_field_kind R n) A :: record_fctx R n.
  Proof. exact (Records.Model.record_fctx_S R). Qed.

  (** ** The Two Telescopes Relate the Same Arguments

      The record's fields at [cups] and the record view's constructor's
      arguments at [ups], position by position. *)
  Lemma rview_tele_link : forall n zs zs', n <= List.length gs -> List.length zs = n -> List.length zs' = n ->
      (per_tele_args (List.firstn n (Records.Model.field_tele R)) (env_tele nil (List.rev (record_params R)) cups)
         (env_tele nil (List.rev (record_params R)) cups) zs zs' <->
       per_tele_args (List.rev (cargs_ctx p D Mj (List.firstn n gs))) (decl_env D ups) (decl_env D ups) zs zs').
  Proof.
    pose proof rview_args_len as Hlg.
    pose proof (valid_rview_record_valid _ _ HR) as [_ HPr [is HS] HF HT HFk].
    pose proof (record_typed_sort_univ _ _ _ (valid_rview_record_typed _ _ HR)) as Hsu.
    pose proof rview_args_container_uparams_len as Hlc.
    destruct (rel_ctx_wf_per_ctx_env HWR) as [RQ HRQ].
    assert (HQ0 : RQ (env_tele nil (List.rev (record_params R)) cups) (env_tele nil (List.rev (record_params R)) cups))
      by exact (tele_args_env_rel _ _ _ _ _ _ HRQ HWR Hlc rview_args_container_uparams_rel).
    assert (HlU : List.length ups = List.length (ind_uparams D)) by (unfold ind_nu in Hu; exact Hu).
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    induction n as [| n IH]; intros zs zs' Hn Hlz Hlz'.
    - destruct zs, zs'; try discriminate; cbn; unfold cargs_ctx; cbn; split; intro; constructor.
    - destruct (nth_error_lt_some' gs n ltac:(lia)) as [g Hg0].
      destruct (nth_error_lt_some' (record_fields R) n ltac:(lia)) as [[f A] Hf].
      pose proof (Records.Model.field_tele_nth_of _ _ _ _ Hf) as HfT.
      destruct (List.exists_last (l := zs) ltac:(intros ->; discriminate)) as (zs0 & x & ->).
      destruct (List.exists_last (l := zs') ltac:(intros ->; discriminate)) as (zs0' & x' & ->).
      rewrite List.length_app in Hlz, Hlz'; cbn in Hlz, Hlz'.
      assert (Lz : List.length zs0 = n) by lia; assert (Lz' : List.length zs0' = n) by lia.
      assert (Heq : gs = List.firstn n gs ++ g :: List.skipn (S n) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn n gs) = n) by (rewrite List.length_firstn; lia).
      destruct (cargs_ctx_single p D (im_nn Mj) (cargs_pat (List.firstn n gs)) g) as (κG & G & HG1).
      assert (HG : cargs_ctx p D Mj (List.firstn n gs ++ g :: nil) = ce_ass κG G :: cargs_ctx p D Mj (List.firstn n gs))
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
      destruct (rel_ctx_wf_ass_inv HWc1) as (SA & HSA & HAv0).
      destruct (rel_type_of_sort (sort_kind_type_sort _ _ HSA) HAv0) as [iA HAv].
      destruct (rel_ctx_wf_per_ctx_env HWc) as [RK HRK].
      destruct (valid_group_cargs_sem_all p D Hg Hcv j Mj c gs HMj rview_args_con (List.firstn (S n) gs) (List.skipn (S n) gs)
                  ltac:(rewrite List.firstn_skipn; reflexivity)) as [HWg1 _].
      rewrite (firstn_S_snoc _ _ _ Hg0), HG, rview_args_params in HWg1; cbn [List.app] in HWg1.
      destruct (rel_ctx_wf_ass_inv HWg1) as (SG & HSG & HGv0).
      destruct (rel_type_of_sort (sort_kind_type_sort _ _ HSG) HGv0) as [iG HGv].
      pose proof (rel_ctx_wf_tail HWg1) as HWg.
      destruct (rel_ctx_wf_per_ctx_env HWg) as [RG HRG].
      assert (HtaC : all_assumptions (List.firstn n (Records.Model.field_tele R)))
        by (rewrite <- Records.Model.rev_record_fctx; apply List.Forall_rev, record_fctx_ass).
      assert (HtaG : all_assumptions (List.rev (cargs_ctx p D Mj (List.firstn n gs))))
        by (apply List.Forall_rev, cargs_ctx_aux_ass).
      apply per_tele_args_snoc_transfer; [ lia | lia | exact (IH zs0 zs0' ltac:(lia) Lz Lz') | | |].
      + (** The field's types are related. *)
        intros Hp.
        assert (HE : RK (env_tele nil (List.rev (record_fctx R n ++ record_params R)) (cups ++ zs0))
                        (env_tele nil (List.rev (record_fctx R n ++ record_params R)) (cups ++ zs0'))).
        { apply (tele_args_env_rel _ _ _ _ _ _ HRK HWc); [ rewrite !List.length_app, length_record_fctx by lia; lia |].
          rewrite EF0; apply per_tele_args_app_intro; [ rewrite List.length_rev; exact Hlc | exact rview_args_container_uparams_rel | exact Hp ]. }
        destruct (rel_type_inversion_simple_at HRK HAv _ _ HE) as (a & a' & Ea & Ea' & [R0 HR0]).
        rewrite !env_tele_closed_app, Records.Model.rev_record_fctx in Ea, Ea' by exact Hlc.
        exists iA, R0; exact (mk_rel_mod_eval _ _ Ea Ea' HR0).
      + (** The constructor's argument types are related. *)
        intros Hp.
        assert (HE : RG (env_tele nil (List.rev (cargs_ctx p D Mj (List.firstn n gs) ++ ind_uparams D)) (ups ++ zs0))
                        (env_tele nil (List.rev (cargs_ctx p D Mj (List.firstn n gs) ++ ind_uparams D)) (ups ++ zs0'))).
        { apply (tele_args_env_rel _ _ _ _ _ _ HRG HWg); [ rewrite !List.length_app, length_cargs_ctx; unfold ind_nu in *; lia |].
          rewrite List.rev_app_distr; apply per_tele_args_app_intro; [ rewrite List.length_rev; unfold ind_nu in *; lia | exact Hgu | exact Hp ]. }
        destruct (rel_type_inversion_simple_at HRG HGv _ _ HE) as (b & b' & Eb & Eb' & [R0 HR0]).
        rewrite !env_tele_closed_app in Eb, Eb' by exact HlU.
        exists iG, R0; exact (mk_rel_mod_eval _ _ Eb Eb' HR0).
      + (** Their relations agree: the heads at the left prefix. *)
        intros Hp i1 R1 i2 R2 [a a' Ea Ea' HR1] [b b' Eb Eb' HR2].
        assert (HpL : per_tele_args (List.firstn n (Records.Model.field_tele R)) (env_tele nil (List.rev (record_params R)) cups)
                        (env_tele nil (List.rev (record_params R)) cups) zs0 zs0).
        { assert (HWr : ⊨ List.rev (List.firstn n (Records.Model.field_tele R)) ++ record_params R)
            by (rewrite <- Records.Model.rev_record_fctx, List.rev_involutive; exact HWc).
          exact (per_tele_args_refl_l _ _ _ HRQ HWr HtaC _ _ _ _ HQ0 Hp). }
        pose proof (proj1 (IH zs0 zs0 ltac:(lia) Lz Lz) HpL) as HqL.
        assert (Hg1 : per_tele_args (List.rev (cargs_ctx p D Mj (List.firstn n gs) ++ ind_uparams D)) nil nil (ups ++ zs0) (ups ++ zs0)).
        { rewrite List.rev_app_distr; apply per_tele_args_app_intro; [ rewrite List.length_rev; unfold ind_nu in *; lia | exact Hgu | exact HqL ]. }
        assert (Hg2 : per_tele_args (List.rev (record_fctx R n ++ record_params R)) nil nil (cups ++ zs0) (cups ++ zs0)).
        { rewrite EF0; apply per_tele_args_app_intro; [ rewrite List.length_rev; exact Hlc | exact rview_args_container_uparams_rel | exact HpL ]. }
        pose proof (rview_arg_link n f A (List.firstn n gs) g (List.skipn (S n) gs) κG G zs0 Hf Heq Lk Lz HG Hg1 Hg2) as Hlk.
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
        grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) j ups ups nil nil x y.
  Proof.
    intros Hends x y.
    pose proof rview_args_len as Hlg.
    pose proof (valid_rview_record_valid _ _ HR) as [_ HPr [is HS] HF HT HFk].
    pose proof (record_typed_sort_univ _ _ _ (valid_rview_record_typed _ _ HR)) as Hsu.
    destruct (Records.Model.sort_tele_value (record_params R) (record_sort R) HWR (ex_intro _ is HS) cups rview_args_container_uparams_rel rview_args_container_uparams_len)
      as [a Ha].
    assert (Hf : List.firstn (ind_nu D) ups = ups) by (apply List.firstn_all2; lia).
    assert (Hs : List.skipn (ind_nu D) ups = nil) by (apply List.skipn_all2; lia).
    assert (Hgp : per_tele_args (List.rev (im_params D Mj)) nil nil ups ups) by (rewrite rview_args_params; exact Hgu).
    assert (Hlp : List.length ups = im_np D Mj) by (unfold im_np; rewrite rview_args_nn; lia).
    assert (Hn0 : tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) nil nil)
      by (rewrite rview_args_nparams; split; reflexivity + exact I).
    assert (Hends' : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
              view_end_rel p D (List.firstn (ind_nu D) ups) (List.firstn (ind_nu D) ups) (ptyp_mem t) /\
              rview_end_rel p D (List.firstn (ind_nu D) ups) (List.firstn (ind_nu D) ups) (ptyp_mem t))
      by (rewrite Hf; exact Hends).
    assert (EN : List.firstn (List.length (record_fields R)) gs = gs) by (apply List.firstn_all2; lia).
    split.
    - intros [ws ws' Hp Hp' Hrel].
      pose proof (record_projs_length _ _ _ Hp) as Lw.
      pose proof (record_projs_length _ _ _ Hp') as Lw'.
      pose proof (Records.Model.canon_fields_tele_args R Hsu HF (ex_intro _ is HS) HT HFk cups cups a rview_args_container_uparams_rel rview_args_container_uparams_len Ha
                    (List.length (record_fields R)) ws ws' (le_n _) (tele_rel_pre _ _ _ _ Hrel)) as HgF.
      pose proof (proj1 (rview_tele_link (List.length (record_fields R)) ws ws' ltac:(lia) Lw Lw') HgF) as HgC.
      rewrite EN in HgC.
      destruct (con_args_canon p D Hg Hcv j Mj c gs HMj rview_args_con ups ups ws ws' Hgp Hlp
                  ltac:(rewrite rview_args_params; exact HgC) ltac:(lia) Hends') as [Hnr Hia].
      rewrite Hf, Hs in Hnr, Hia; rewrite rview_args_nparams in Hia.
      eapply ind_rel_record; [ exact HMj | exact Hh | exact rview_args_nparams | exact Hcs
                             | apply (record_projs_iff R fl); [ exact rview_args_names | exact Hp ]
                             | apply (record_projs_iff R fl); [ exact rview_args_names | exact Hp' ]
                             | exact Hnr | exact Hia ].
    - intros Hxy; inversion Hxy; subst; try no_rview_rel.
      match goal with H0 : ind_member D j = Some ?M0, H0' : im_head ?M0 = _, H0'' : im_cons ?M0 = _ |- _ =>
        rewrite HMj in H0; injection H0 as <-; rewrite Hh in H0'; injection H0' as <- <- <-;
        rewrite Hcs in H0''; injection H0'' as <- <- end.
      match goal with Hq1 : ⟦projs fl of x ⟧ _ ⍮ _ ↘ ?ws, Hq2 : ⟦projs fl of y ⟧ _ ⍮ _ ↘ ?ws',
                      Ha1 : tele_rel _ _ _ _, Ha2 : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        rename Hq1 into Hp; rename Hq2 into Hp'; rename Ha1 into Hnr; rename Ha2 into Hia end.
      apply (record_projs_iff R fl _ _ rview_args_names) in Hp, Hp'.
      pose proof (record_projs_length _ _ _ Hp) as Lw.
      pose proof (record_projs_length _ _ _ Hp') as Lw'.
      pose proof (cargs_tele_args p D Hg Hcv ups Hgu Hu j Mj c gs HMj rview_args_con Hends nil nil _ _ Hn0 Hnr
                    ltac:(rewrite rview_args_nparams; exact Hia)
                    (List.length (record_fields R)) ltac:(lia)) as HgC.
      rewrite EN, List.app_nil_r, !List.firstn_all2, rview_args_params in HgC by lia.
      pose proof (proj2 (rview_tele_link (List.length (record_fields R)) _ _ ltac:(lia) Lw Lw') ltac:(rewrite EN; exact HgC)) as HgF.
      assert (Htr : forall k0 κ0 A0 pre, List.nth_error (List.firstn (List.length (record_fields R)) (Records.Model.field_tele R)) k0 = Some (ce_ass κ0 A0) ->
                (canon_fields_rel R cups k0 pre <~>
                 per_head A0 A0 (env_tele (env_tele nil (List.rev (record_params R)) cups) (List.firstn (List.length (record_fields R)) (Records.Model.field_tele R)) pre)
                   (env_tele (env_tele nil (List.rev (record_params R)) cups) (List.firstn (List.length (record_fields R)) (Records.Model.field_tele R)) pre))).
      { intros k0 κ0 A0 pre Hk0.
        rewrite List.firstn_all2 in Hk0 |- * by (rewrite Records.Model.length_field_tele; lia).
        destruct (Records.Model.field_tele_nth _ _ _ _ Hk0) as [f0 [Hf0 _]].
        unfold canon_fields_rel, record_fields_env; rewrite (nth_ftyp_eq _ _ _ _ Hf0), Records.Model.record_fields_tele_eq; reflexivity. }
      pose proof (tele_rel_of_per_tele_args _ _ _ Htr _ _ _ HgF ltac:(rewrite List.length_firstn, Records.Model.length_field_tele; lia)) as Htl.
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
    forall ps ps' as1 as1', per_tele_args (List.rev (im_params D Mk)) nil nil ps ps' -> List.length ps = im_np D Mk ->
      per_tele_args (List.rev (cargs_ctx p D Mk gs)) (env_tele nil (List.rev (im_params D Mk)) ps) (env_tele nil (List.rev (im_params D Mk)) ps') as1 as1' ->
      List.length as1 = List.length gs ->
      (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
         view_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t) /\
         rview_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t)) ->
      ind_rel p D (admissible_index_at D (List.firstn (ind_nu D) ps) (canon_nparams_rel D (List.firstn (ind_nu D) ps)))
        (canon_nparams_rel D (List.firstn (ind_nu D) ps)) (canon_args_rel D (List.firstn (ind_nu D) ps))
        (canon_doms_rel D (List.firstn (ind_nu D) ps)) k (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps') nil nil
        (d_tuple (List.combine fl as1)) (d_tuple (List.combine fl as1')).
Proof.
  intros p D Hg Hcv k Mk qr Is fl c gs HM Hh Hcs ps ps' as1 as1' Hgp Hlp Hga Hla Hends.
  pose proof (valid_group_typed _ _ Hg) as Hdt.
  pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) as Hnp.
  pose proof (ind_con_single _ _ _ Hcs) as Hcon.
  destruct (con_args_canon p D Hg Hcv k Mk c gs HM Hcon ps ps' as1 as1' Hgp Hlp Hga Hla Hends) as [Hnr Hia].
  assert (Hlp' : List.length ps' = im_np D Mk) by (destruct (per_tele_args_length _ _ _ _ _ Hgp) as [L _]; lia).
  assert (Hnn : im_nn Mk = 0) by (unfold im_nn; rewrite Hnp; reflexivity).
  assert (Hs : List.skipn (ind_nu D) ps = nil) by (apply List.skipn_all2; unfold im_np in Hlp; lia).
  assert (Hs' : List.skipn (ind_nu D) ps' = nil) by (apply List.skipn_all2; unfold im_np in Hlp'; lia).
  rewrite Hs in Hnr, Hia; rewrite Hs' in Hia.
  pose proof (per_tele_args_length _ _ _ _ _ Hga) as [Hla' _].
  destruct (valid_group_records _ _ Hg _ _ _ _ _ HM Hh) as [R HR].
  pose proof (rview_args_names p D Hg k Mk qr Is fl R HM Hh HR) as Hfl.
  pose proof (rview_args_len p D Hg k Mk qr Is fl R c gs HM Hh HR Hcs) as Hlg.
  pose proof (typed_nodup _ _ _ (valid_rview_record_typed _ _ HR)) as Hnd.
  assert (Hpj : forall vs, List.length vs = List.length gs -> ⟦projs fl of d_tuple (List.combine fl vs) ⟧ gc_deps ⍮ gc_stack ↘ vs).
  { intros vs Lv; apply (record_projs_iff R fl _ _ Hfl).
    pose proof (Records.Model.tuple_projs R Hnd (record_fields R) vs eq_refl ltac:(lia)) as H.
    rewrite <- Hfl in H; exact H. }
  rewrite Hnp in Hia.
  eapply ind_rel_record; [ exact HM | exact Hh | exact Hnp | exact Hcs | exact (Hpj as1 Hla) | exact (Hpj as1' ltac:(lia)) | exact Hnr | exact Hia ].
Qed.

(** ** The Coherence of a Record View

    Given the relations of the types of the members its recursive fields'
    shapes end in, the record view's type relates the group's elements
    there. *)
Lemma rview_end_rel_of_ends : forall p D, valid_group p D -> containers_valid D ->
    forall ups ups', per_tele_args (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall j, (forall Mj qr Is fl c gs gs1 t gs2, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
                 im_cons Mj = (c, gs) :: nil -> gs = gs1 ++ ca_rec t :: gs2 ->
                 view_end_rel p D ups ups (ptyp_mem t) /\ rview_end_rel p D ups ups (ptyp_mem t)) ->
      rview_end_rel p D ups ups' j.
Proof.
  intros p D Hg Hcv ups ups' Hgu Hu j Hends Mj qr Is fl R cups cups' HMj Hh HlR Ecups Ecups' cs cs' i Rel Hcs Hcs' HRel.
  pose proof (uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu) as Hgd.
  destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R0 HR0].
  rewrite (valid_rview_record_lookup _ _ HR0) in HlR; injection HlR as ->.
  destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HMj Hh) as (gs & Hcs0 & _).
  (** The record's relation at the instance's value. *)
  pose proof (rview_args_container_uparams_len p D Hg j Mj qr Is fl R HMj Hh HR0 ups cups Ecups) as Hlc.
  destruct (vrr_type_rel qr R cups cs HR0 Hcs Hlc) as [i1 HR1].
  assert (E1 : record_rel R (canon_fields_rel R cups) <~> Rel) by exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR1 HRel).
  (** The group's, at the bases [ups]. *)
  pose proof (rview_elems p D Hg Hcv j Mj qr Is fl R rview_con gs HMj Hh HR0 Hcs0 ups cups Hgd Hu Ecups
                (fun gs1 t gs2 Heq => Hends _ _ _ _ _ _ gs1 t gs2 HMj Hh Hcs0 Heq)) as E2.
  (** And at the bases [ups] and [ups']. *)
  destruct (valid_group_canon p D Hg ups Hgd Hu) as [CnP CnI CaP CaI CdP CdI].
  pose proof (valid_group_adm p D Hg ups ups Hgd Hu Hgd) as Add.
  pose proof (valid_group_adm p D Hg ups ups' Hgd Hu Hgu) as Ad'.
  intros x y; split; intro Hxy.
  - apply E1, E2 in Hxy.
    exact (proj1 (ind_rel_base_r p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI ups' Ad' ups Add) _ _ _ _ _ _ _ Hxy eq_refl).
  - pose proof (proj1 (ind_rel_base_r p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI ups Add ups' Ad')
                  _ _ _ _ _ _ _ Hxy eq_refl) as H.
    apply E1, E2, H.
Qed.

End Fixed_GCtx.
