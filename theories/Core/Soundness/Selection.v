(** * Selections of Glued Module Values

    A submodule selected from a glued module value is glued as the
    selection ([glu_dmod_sel]).  A value lacking a parameter recurses
    through its applications: the selection from the application is moved
    to the application of the selection, which has the same module part
    ([mdenote_mem_app_part]), by the transfer between module expressions
    with the same module part ([glu_dmod_same_part_typed]).  The transfer
    needs no equation between the module expressions: their members are
    equal through their δ-reducts or as the filed members they are
    ([wf_exp_eq_mem_same_part]). *)

From Stdlib Require Import Lia List PeanoNat RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Modules Require Import Values ModuleVal.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases ModuleValues.
From Mctt.Core.Soundness.Global Require Import GlobalValues.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Members of Module Expressions with the Same Module Part *)

Lemma mdesc_ats_term_none_eq : forall Ns κ A R, mdesc_ats (mdesc_term κ A None) Ns = Some R -> exists A', R = mdesc_term κ A' None.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [ exact (IH _ _ _ Ha) | discriminate ].
Qed.

(** A member looked up as a term of no δ-reduct is an axiom or an abstract
    definition of a stored body, read bare: the module expression's module
    part is the body's path at no argument and no outside parameter. *)
Lemma mem_no_red : forall Θ Ξ Γ H x R A,
    mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A -> mdesc_reduct R = None ->
    exists R0 p T Φ Φ0 b pv κ oM,
      mdenote Θ Ξ Γ H R0 /\ mdesc_mod R0 = Some (mdesc_closed nil p T Φ nil) /\
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv κ A oM)) /\ (if b then oM else None) = None.
Proof.
  intros * Hm Ht Hr.
  assert (HR : exists κ, R = mdesc_term κ A None)
    by (destruct R as [κ A' om | | | ]; cbn in Ht, Hr; try discriminate; subst; injection Ht as ->; eauto).
  destruct HR as [κ ->].
  inversion Hm as [| | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd |]; subst.
  destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in He; try discriminate.
  - (* an open body reads only transparent definitions and modules *)
    destruct (gm_prefix_upto Φx x) as [[| Φ' y E0 | ? ? ?] |]; try discriminate.
    destruct E0 as [[] pv κ' A' [M |] | pv U | | |]; try discriminate; injection He as <- <- <-.
    + inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
    + inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn in Hrd; destruct (gm_fill Φ'); cbn in Hrd; [| discriminate ].
      injection Hrd as Heq; destruct Re; cbn in Hmm, Heq; try contradiction; discriminate.
    + (* a definition with a module part reads as one, with both parts *)
      inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
  - destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as Heq.
    destruct E0 as [b pv κ' A' oM | pv [Δ [sm Φy | E'] ] | pv pq k' D ΦD | pv Ad Md Ud | pv Rr ΦR ].
    + (* a definition: one of no body, read bare *)
      cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
      destruct (if b then oM else None) as [M |] eqn:Ho.
      * exfalso; destruct (mdesc_ats_some_red _ _ _ _ _ Hats) as (A1 & M1 & ->).
        rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
      * destruct (mdesc_ats_term_none_eq _ _ _ _ Hats) as (A1 & ->).
        destruct (mdesc_named_term_none Θ' Ns (apps (a_mem (qname_mod p) x) Ns) κ' A1) as [(Hn & -> & ->) | Hn];
          rewrite Hn in Heq; cbn in Heq; [| discriminate ].
        cbn in Hats; injection Hats as ->; injection Heq as -> ->.
        exists R0, p, T, Φ, Φ0, b, pv, κ, oM; repeat split; assumption.
    + exfalso; assert (Hmm : mdesc_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (mdesc_ats_read_mod _ _ Hmm) in Hats.
      pose proof (mdesc_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; assert (Hmm : mdesc_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (mdesc_ats_read_mod _ _ Hmm) in Hats.
      pose proof (mdesc_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a member of a group: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read ind_former_desc] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a definition with a module part: read with its module part, no term *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a record type: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read record_former_desc] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
Qed.

(** ** Selection Commutes with Application, on Descriptions *)

(** Reading a term as a name leaves its module part. *)
Lemma mdesc_mod_named : forall Θ Ns M R, mdesc_mod (mdesc_named Θ Ns M R) = mdesc_mod R.
Proof.
  intros; apply (mdesc_named_cases (fun X => mdesc_mod X = mdesc_mod R)); [ reflexivity |].
  destruct R as [r A [] | | |]; reflexivity.
Qed.

(** The outermost parameter of a telescope ending in an assumption, the
    rest left as it is. *)
Lemma tele_split_last : forall Δ0 κ B, tele_split (rev (Δ0 ++ ce_ass κ B :: nil)) = inl (B, Δ0, Id).
Proof. intros; rewrite rev_app_distr; cbn; rewrite rev_involutive; reflexivity. Qed.

(** Applying to one more argument, last. *)
Lemma mdesc_ats_snoc : forall Ns R N,
    mdesc_ats R (Ns ++ N :: nil) = match mdesc_ats R Ns with Some R1 => mdesc_at R1 N | None => None end.
Proof.
  induction Ns as [| N0 Ns IH]; intros; cbn; [ destruct (mdesc_at R N); reflexivity |].
  destruct (mdesc_at R N0); [ apply IH | reflexivity ].
Qed.

Lemma mdesc_term_part_ats_snoc : forall Ns R N,
    mdesc_term_part_ats R (Ns ++ N :: nil) =
      match mdesc_term_part_ats R Ns with Some R1 => mdesc_term_part_at R1 N | None => None end.
Proof.
  induction Ns as [| N0 Ns IH]; intros; cbn; [ destruct (mdesc_term_part_at R N); reflexivity |].
  destruct (mdesc_term_part_at R N0); [ apply IH | reflexivity ].
Qed.

(** The term part of a definition with a module part, or of a type former,
    whose type is a [Π] over a telescope of assumptions and whose body is
    a [λ] over it or a type former, given fewer arguments than the
    telescope has, takes one more. *)
Lemma term_part_ats_more : forall Ns P X r M r' B M' N, all_assumptions P -> List.length Ns < List.length P ->
    (app_const M = true \/ exists M0, M = ctx_fn P M0) ->
    mdesc_term_part_ats (mdesc_term r (ctx_pi P X) (Some M)) Ns = Some (mdesc_term r' B (Some M')) ->
    exists R'', mdesc_term_part_at (mdesc_term r' B (Some M')) N = Some R''.
Proof.
  induction Ns as [| N0 Ns IH]; intros * HP Hl HM Ha.
  - cbn in Ha; injection Ha as <- <- <-.
    destruct (all_assumptions_last _ HP ltac:(intros ->; cbn in Hl; lia)) as (P0 & κ & A & ->).
    unfold ctx_pi; rewrite ctx_pi_app; cbn [ctx_pi_at mdesc_term_part_at pi_view].
    destruct HM as [Hc | (M0 & ->)]; [ destruct (fn_view M); [| rewrite Hc ]; eexists; reflexivity |].
    rewrite ctx_fn_app; cbn [ctx_fn fn_view]; eexists; reflexivity.
  - destruct (all_assumptions_last _ HP ltac:(intros ->; cbn in Hl; lia)) as (P0 & κ & A & ->).
    unfold all_assumptions in HP; apply Forall_app in HP as [HP0 _].
    cbn [mdesc_term_part_ats] in Ha.
    unfold ctx_pi in Ha; rewrite ctx_pi_app in Ha; cbn [ctx_pi_at mdesc_term_part_at pi_view] in Ha.
    rewrite length_app in Hl; cbn in Hl.
    destruct HM as [Hc | (M0 & ->)].
    + destruct (fn_view M) as [M1 |] eqn:Ef.
      * (** a type former applied is no [λ] *)
        exfalso; clear - Hc Ef; revert M1 Ef; induction M; intros; cbn in *; try discriminate.
      * rewrite Hc in Ha.
        rewrite ctx_pi_sub in Ha.
        refine (IH _ _ _ _ _ _ _ _ _ _ _ Ha); [ apply all_assumptions_sub; exact HP0 | rewrite length_tele_sub; lia | left; cbn; exact Hc ].
    + rewrite ctx_fn_app in Ha; cbn [ctx_fn fn_view] in Ha.
      rewrite ctx_pi_sub, ctx_fn_sub in Ha.
      refine (IH _ _ _ _ _ _ _ _ _ _ _ Ha); [ apply all_assumptions_sub; exact HP0 | rewrite length_tele_sub; lia | right; eexists; reflexivity ].
Qed.

(** A description under a substitution equal to the identity is itself. *)
Lemma mdesc_sub_id_ext : forall R σ, sb_eq σ Id -> mdesc_sub R σ = R.
Proof.
  induction R as [r A om | Δ Φ Φx | Θ p T Φ Ns | Θ A M Rm IH]; intros σ Hσ; cbn [mdesc_sub].
  - rewrite exp_sub_id_ext by exact Hσ; destruct om; cbn; [ rewrite exp_sub_id_ext by exact Hσ |]; reflexivity.
  - rewrite (tele_sub_sb_eq Δ σ Id Hσ), tele_sub_id, !gmod_sub_id_ext by (apply sb_qn_id_ext; exact Hσ); reflexivity.
  - rewrite (tele_sub_sb_eq Θ σ Id Hσ), tele_sub_id; f_equal.
    induction Ns as [| N Ns IHNs]; cbn; [ reflexivity |].
    rewrite exp_sub_id_ext by (apply sb_qn_id_ext; exact Hσ); f_equal; exact IHNs.
  - rewrite (tele_sub_sb_eq Θ σ Id Hσ), tele_sub_id, !exp_sub_id_ext by (apply sb_qn_id_ext; exact Hσ).
    rewrite (IH _ Hσ); reflexivity.
Qed.

(** A description abstracted over a telescope ending in assumptions [T2]
    given as many arguments: the arguments are substituted for the
    assumptions, in the rest of the telescope and in the description. *)
Lemma mdesc_ats_up_prefix : forall Ns P T2 R, all_assumptions T2 -> List.length T2 = List.length Ns ->
    mdesc_ats (mdesc_up (P ++ T2) R) Ns =
      Some (mdesc_up (tele_sub P (sb_of_list Id Ns)) (mdesc_sub R (sb_qn (List.length P) (sb_of_list Id Ns)))).
Proof.
  induction Ns as [| N Ns IH]; intros * HT Hl.
  - destruct T2; [| cbn in Hl; discriminate ]; cbn.
    rewrite app_nil_r, tele_sub_id, (mdesc_sub_id_ext R) by (apply sb_qn_id_ext; reflexivity); reflexivity.
  - destruct (List.exists_last (l := T2)) as (T2' & e & ->); [ intros ->; cbn in Hl; discriminate |].
    unfold all_assumptions in HT; apply List.Forall_app in HT as [HT' He]; apply List.Forall_cons_iff in He as [(κB & B & ->) _].
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [mdesc_ats]; rewrite app_assoc, mdesc_at_up, tele_sub_app.
    rewrite (IH _ _ _ (all_assumptions_sub _ _ HT') ltac:(rewrite length_tele_sub; lia)).
    rewrite tele_sub_sub, mdesc_sub_sub_ext with (δ := sb_qn (List.length P) (sb_of_list Id (N :: Ns))).
    + do 2 f_equal; apply tele_sub_sb_eq; cbn [sb_of_list].
      replace (length T2') with (length Ns) by lia.
      etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ].
    + rewrite length_tele_sub, length_app, sb_qn_plus; cbn [sb_of_list].
      apply sb_qn_compose_ext.
      replace (length T2') with (length Ns) by lia.
      etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ].
Qed.

(** The arguments under the identity. *)
Lemma map_exp_sub_id : forall Ns, List.map (fun M => M[Id]) Ns = Ns.
Proof. induction Ns as [| N Ns IH]; cbn; [ reflexivity | rewrite exp_sub_id, IH; reflexivity ]. Qed.

(** The entry [y] of a closed module, read, then given the next
    parameter, has the module part of the entry read in the module given
    it: the outermost outside parameter is substituted, the entry being
    closed; with no outside parameter the argument is recorded, and the
    entry read at it, a definition with a module part's or a type
    former's term part taking it, being a [Π] over the stored telescope
    ([gm_coherent]). *)
Lemma sel_at_closed : forall Θc Ξc, gctx_closed Θc Ξc ->
    forall Γ Θ p T Φ Ns N y E rd R Rs Rs' Rsm,
    gm_coherent T Φ -> all_assumptions T -> unit_closed T Φ -> all_assumptions Θ ->
    (Θ = nil -> List.length Ns < List.length T) ->
    mdesc_entry (mdesc_closed Θ p T Φ Ns) y = Some (nil, E, rd) ->
    edenote Θc Ξc (nil ++ Γ) (Some (qname_in p y)) E R -> mdesc_read rd R = Some Rs ->
    mdesc_mod Rs = Some Rsm -> mdesc_at Rs N = Some Rs' ->
    exists R0m' rd', mdesc_at (mdesc_closed Θ p T Φ Ns) N = Some R0m' /\
      mdesc_entry R0m' y = Some (nil, E, rd') /\ exists Rs'', mdesc_read rd' R = Some Rs'' /\ mdesc_mod Rs'' = mdesc_mod Rs'.
Proof.
  intros Θc Ξc Hc * Hco HTa HU HΘa Hlt He Hed Hrd HRs Hat.
  pose proof (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU He) as (_ & HsE & ->).
  pose proof He as He0; cbn in He0.
  destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
  injection He0 as <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & _); injection Heq as <- -> <-.
  pose proof (gm_coherent_prefix _ _ _ _ _ Hco Hp) as HcoE.
  (** The entry is closed, and so is what it denotes *)
  assert (HsR : mdesc_scoped 0 R).
  { eapply (proj1 (proj2 (proj2 (mdenote_scoped_all _ _ Hc)))); [ exact Hed | intros x U Hx; lia | exact HsE ]. }
  cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
  injection Hrd as <-.
  rewrite mdesc_mod_up, mdesc_mod_named in HRs.
  destruct (mdesc_mod R1) as [Q |] eqn:HQ; cbn [option_map] in HRs; [ injection HRs as <- | discriminate ].
  destruct Θ as [| e Θr] using rev_ind.
  - (** No outside parameter: the argument is recorded *)
    specialize (Hlt eq_refl).
    cbn [mdesc_at tele_split rev]; rewrite map_exp_sub_id.
    exists (mdesc_closed nil p T Φ (Ns ++ N :: nil)), (reader_closed nil (Ns ++ N :: nil) (apps (a_mem (qname_mod p) y) (Ns ++ N :: nil))).
    split; [ reflexivity | split; [ cbn; rewrite Hp; reflexivity |] ].
    rewrite mdesc_up_nil in Hat.
    destruct R as [r0 A0 om | Δr Φr Φxr | Θr pr Tr Φr' Nsr | [| e0 Θd] A0 M0 Rm].
    + exfalso; destruct (mdesc_ats_term _ _ _ _ _ Hats) as (? & ? & ->); discriminate.
    + (** A module: read at one more argument *)
      cbn [mdesc_read mdesc_ats_read]; rewrite mdesc_ats_snoc; cbn [mdesc_ats_read] in Hats; rewrite Hats.
      assert (Hn : mdesc_named nil Ns (apps (a_mem (qname_mod p) y) Ns) R1 = R1)
        by (apply mdesc_named_fix; destruct R1; cbn in HQ |- *; first [ discriminate | reflexivity ]).
      rewrite Hn in Hat; rewrite Hat; cbn [option_map]; eexists; split; [ reflexivity | rewrite mdesc_up_nil, mdesc_mod_named; reflexivity ].
    + cbn [mdesc_read mdesc_ats_read]; rewrite mdesc_ats_snoc; cbn [mdesc_ats_read] in Hats; rewrite Hats.
      assert (Hn : mdesc_named nil Ns (apps (a_mem (qname_mod p) y) Ns) R1 = R1)
        by (apply mdesc_named_fix; destruct R1; cbn in HQ |- *; first [ discriminate | reflexivity ]).
      rewrite Hn in Hat; rewrite Hat; cbn [option_map]; eexists; split; [ reflexivity | rewrite mdesc_up_nil, mdesc_mod_named; reflexivity ].
    + (** A definition with a module part, or a type former: both parts
          take the argument *)
      cbn [mdesc_ats_read] in Hats.
      destruct (mdesc_term_part_ats (mdesc_term ak_relevant A0 (Some M0)) Ns) as [[r1 B [M' |] | | |] |] eqn:Htp;
        try discriminate.
      destruct (mdesc_ats Rm Ns) as [Rm' |] eqn:HRm; [ injection Hats as <- | discriminate ].
      rewrite mdesc_named_fix in Hat by reflexivity.
      cbn [mdesc_at tele_split rev] in Hat.
      destruct (mdesc_at Rm' N) as [Rm'' |] eqn:HRm''; [ injection Hat as <- | discriminate ].
      (** The term part is a [Π] over the stored telescope *)
      assert (Hmore : exists R'', mdesc_term_part_at (mdesc_term r1 B (Some M')) N = Some R'').
      { cbn [ge_read] in Hed.
        destruct E0 as [b pv κ A M | pv [Δ [sm Φy | Ea]] | pv pq k D Φ' | pv A M U | pv pr Rr Φ'];
          [ exfalso; cbn [ge_read] in Hed; inversion Hed
          | exfalso; destruct sm; cbn [ge_read] in Hed; inversion Hed; subst;
            match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end;
            cbn in Hm; contradiction
          | exfalso; cbn [ge_read] in Hed; inversion Hed; subst;
            match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end;
            cbn in Hm; contradiction
          | cbn [ge_read] in Hed; inversion Hed; subst ..].
        - (** a type former of a group *)
          cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HuD & HΔ0) _].
          unfold im_params in Htp; rewrite HuD, !ctx_pi_app in Htp.
          refine (term_part_ats_more _ T _ _ _ _ _ _ _ HTa Hlt _ Htp); left; reflexivity.
        - (** a definition with a module part *)
          cbn [ge_coherent] in HcoE; destruct HcoE as [(A1 & M1 & -> & ->) _].
          refine (term_part_ats_more _ T _ _ _ _ _ _ _ HTa Hlt _ Htp); right; eexists; reflexivity.
        - (** a record type *)
          cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HpR & HΔ0) _].
          unfold record_former_desc in *; rewrite HpR, ctx_pi_app in Htp.
          refine (term_part_ats_more _ T _ _ _ _ _ _ _ HTa Hlt _ Htp); left; reflexivity. }
      destruct Hmore as (R'' & HR'').
      cbn [mdesc_read mdesc_ats_read]; rewrite mdesc_term_part_ats_snoc, Htp, HR'', mdesc_ats_snoc, HRm, HRm''.
      assert (HR''t : exists r2 C M'', R'' = mdesc_term r2 C (Some M'')).
      { cbn [mdesc_term_part_at] in HR''; destruct (pi_view B) as [[? ?] |]; [| discriminate ].
        destruct (fn_view M') as [M1 |] eqn:Ef; [| destruct (app_const M') eqn:Ea ]; try discriminate;
          injection HR'' as <-; eauto. }
      destruct HR''t as (r2 & C & M'' & ->); cbn [option_map].
      eexists; split; [ reflexivity | rewrite mdesc_up_nil, mdesc_named_fix by reflexivity; cbn [mdesc_mod]; reflexivity ].
    + (** A definition with a module part over outside parameters: read as
          a module part *)
      cbn [mdesc_read mdesc_ats_read]; rewrite mdesc_ats_snoc; cbn [mdesc_ats_read] in Hats; rewrite Hats.
      assert (Hn : mdesc_named nil Ns (apps (a_mem (qname_mod p) y) Ns) R1 = R1)
        by (apply mdesc_named_fix; destruct R1; cbn in HQ |- *; first [ discriminate | reflexivity ]).
      rewrite Hn in Hat; rewrite Hat; cbn [option_map]; eexists; split; [ reflexivity | rewrite mdesc_up_nil, mdesc_mod_named; reflexivity ].
  - (** The outermost outside parameter is substituted *)
    clear IHΘr.
    unfold all_assumptions in HΘa; apply Forall_app in HΘa as [HΘr He1]; apply Forall_cons_iff in He1 as [(κ & B & ->) _].
    cbn [mdesc_at]; rewrite tele_split_last.
    do 2 eexists; split; [ reflexivity | split; [ cbn; rewrite Hp; reflexivity |] ].
    cbn [mdesc_read].
    pose proof (mdesc_ats_read_sub _ _ _ (Id ⨟ sb_qn (List.length Θr) (Id,,N)) Hats) as Hats'.
    rewrite (mdesc_sub_fix R 0) in Hats' by (exact HsR || (intros; lia)).
    rewrite Hats'; cbn [option_map]; eexists; split; [ reflexivity |]; rewrite mdesc_mod_up, mdesc_mod_named.
    rewrite (mdesc_mod_sub _ _ _ HQ); cbn [option_map].
    assert (HRsm : mdesc_mod (mdesc_up (Θr ++ ce_ass κ B :: nil) (mdesc_named (Θr ++ ce_ass κ B :: nil) Ns (apps (a_mem (qname_mod p) y) Ns) R1))
                   = Some (mdesc_up (Θr ++ ce_ass κ B :: nil) Q))
      by (rewrite mdesc_mod_up, mdesc_mod_named, HQ; reflexivity).
    destruct (mdesc_at_mod_part _ _ _ _ Hat HRsm) as (Rm' & HRm' & ->).
    rewrite mdesc_at_up in HRm'; injection HRm' as <-.
    pose proof (mdesc_mod_is_mod _ _ HQ) as HQm.
    rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ (mdesc_is_mod_sub _ _ HQm))).
    do 2 f_equal; apply mdesc_sub_sb_eq; rewrite sb_compose_id_left; reflexivity.
Qed.

(** The entry [y] of an open module, read, then given the next parameter,
    is the entry read in the module given it: the parameter is
    substituted into the body ([mdenote_sub_all]), and the entries before
    the entry filled in alike ([gm_fill_sub]). *)
Lemma sel_at_open : forall Θc Ξc, gctx_closed Θc Ξc ->
    forall Γ Δ Φw Φx N R0m' y Γy E rd R Rs Rs',
    ctx_scoped 0 Γ -> mdesc_scoped (List.length Γ) (mdesc_open Δ Φw Φx) -> all_assumptions Δ ->
    mdesc_at (mdesc_open Δ Φw Φx) N = Some R0m' ->
    mdesc_entry (mdesc_open Δ Φw Φx) y = Some (Γy, E, rd) ->
    edenote Θc Ξc (Γy ++ Γ) None E R -> mdesc_read rd R = Some Rs ->
    mdesc_at Rs N = Some Rs' ->
    exists Γy' E' rd' R', mdesc_entry R0m' y = Some (Γy', E', rd') /\
      edenote Θc Ξc (Γy' ++ Γ) None E' R' /\ mdesc_read rd' R' = Some Rs'.
Proof.
  intros Θc Ξc Hc * HΓ Hs HΔa Hat0 He Hed Hrd Hat.
  pose proof (mdesc_entry_scoped _ _ _ _ _ _ Hs He) as (HsΓy & HsE & _).
  destruct Δ as [| e Δ0 _] using rev_ind; [ cbn in Hat0; discriminate |].
  unfold all_assumptions in HΔa; apply Forall_app in HΔa as [HΔ0 He1]; apply Forall_cons_iff in He1 as [(κ & B & ->) _].
  cbn [mdesc_at] in Hat0; rewrite tele_split_last in Hat0; injection Hat0 as <-.
  set (σ := sb_qn (List.length Δ0) (Id,,N)).
  rewrite (gmod_sub_sb_eq Φw _ σ), (gmod_sub_sb_eq Φx _ σ) by (rewrite sb_compose_id_left; reflexivity).
  pose proof He as He0; cbn in He0.
  destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & _); injection Heq as <- -> <-.
  (** The read fills the entries before it *)
  cbn [mdesc_read] in Hrd.
  assert (HE : exists σf, gm_fill Φ' = Some σf /\ rd = reader_open (Δ0 ++ ce_ass κ B :: nil) Φ' /\
                 Γy = body_ctx Φ' ++ Δ0 ++ ce_ass κ B :: nil /\ E = E0 /\
                 mdesc_entry (mdesc_open (tele_sub Δ0 (Id,,N)) (gmod_sub Φw σ) (gmod_sub Φx σ)) y =
                   Some (body_ctx (gmod_sub Φ' σ) ++ tele_sub Δ0 (Id,,N), gentry_sub E0 (sb_qn (gm_binders Φ') σ),
                         reader_open (tele_sub Δ0 (Id,,N)) (gmod_sub Φ' σ))).
  { cbn [mdesc_entry]; rewrite gm_prefix_upto_sub, Hp; cbn [option_map gmod_sub].
    destruct E0 as [[|] pv r A [M |] | pv U | | pv A M U |]; try discriminate; injection He0 as <- <- <-;
      cbn [mdesc_read] in Hrd; destruct (gm_fill Φ') as [σf |]; cbn [option_map] in Hrd; try discriminate;
      exists σf; repeat split. }
  destruct HE as (σf & Hf & -> & -> & -> & HE').
  cbn [mdesc_read] in Hrd; rewrite Hf in Hrd; cbn [option_map] in Hrd; injection Hrd as <-.
  rewrite mdesc_at_up in Hat; injection Hat as <-.
  pose proof (gm_fill_nopens _ _ Hf) as Hno.
  set (s := sb_qn (gm_binders Φ') σ).
  exists (body_ctx (gmod_sub Φ' σ) ++ tele_sub Δ0 (Id,,N)), (gentry_sub E0 s), (reader_open (tele_sub Δ0 (Id,,N)) (gmod_sub Φ' σ)),
    (mdesc_sub R s).
  split; [ exact HE' | split ].
  - (** The entry denotes, substituted *)
    assert (Hsc : sub_mod_compat s ((body_ctx (gmod_sub Φ' σ) ++ tele_sub Δ0 (Id,,N)) ++ Γ)
                    ((body_ctx Φ' ++ Δ0 ++ ce_ass κ B :: nil) ++ Γ)).
    { pose proof (sub_mod_compat_ext (body_ctx Φ' ++ Δ0) (Id,,N) Γ (ce_ass κ B :: Γ) (sub_mod_compat_single Γ κ B N)) as H.
      rewrite tele_sub_app, length_app, sb_qn_plus in H.
      rewrite body_ctx_sub by exact Hno.
      unfold s, σ; rewrite <- (length_body_ctx _ Hno).
      replace ((body_ctx Φ' ++ Δ0 ++ ce_ass κ B :: nil) ++ Γ) with ((body_ctx Φ' ++ Δ0) ++ ce_ass κ B :: Γ)
        by (rewrite <- !app_assoc; reflexivity).
      exact H. }
    eapply (proj1 (proj2 (proj2 (mdenote_sub_all _ _ Hc)))); [ exact Hed | | rewrite <- length_app in HsE; exact HsE | exact Hsc ].
    apply slots_ok_ctx, ctx_scoped_app_iff; split; [ exact HsΓy | exact HΓ ].
  - (** The entries before it filled in alike *)
    destruct (gm_fill_sub Φ' (List.length Δ0) (Id,,N) σf Hf) as (τ' & Hf' & Hτ).
    cbn [mdesc_read]; fold σ in Hf'; rewrite Hf'; cbn [option_map]; do 2 f_equal.
    fold σ.
    rewrite (mdesc_sub_sub_ext R s τ' (σf ⨟ σ)), (mdesc_sub_sub_ext R σf σ (σf ⨟ σ)); [ reflexivity | reflexivity |].
    unfold s, σ; rewrite <- sb_qn_plus; exact Hτ.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** The members [x] of two typed module expressions with the same module
    part, looked up alike, are equal: through their common δ-reduct, or,
    with none, as the filed member of the bare stored body the module part
    is ([mem_alias_filed]). *)
Lemma wf_exp_eq_mem_same_part : forall Γ H0 H1 x R A R0 R1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H0 ≈ H0 -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H1 ≈ H1 ->
    mdenote gc_deps gc_stack Γ (me_mem H0 x) R -> mdenote gc_deps gc_stack Γ (me_mem H1 x) R ->
    mdesc_type R = Some A ->
    mdenote gc_deps gc_stack Γ H0 R0 -> mdenote gc_deps gc_stack Γ H1 R1 -> mdesc_mod R0 = mdesc_mod R1 ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_mem H0 x ≈ a_mem H1 x : A.
Proof.
  intros * HH0 HH1 Hm0 Hm1 Ht HR0 HR1 Ep.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH0)) as Hg.
  destruct (mdesc_reduct R) as [M |] eqn:Hr.
  - (** Both are the reduct *)
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; eassumption |].
    apply wf_exp_eq_sym; eapply wf_exp_eq_mem_delta; eassumption.
  - (** Both are the filed member of the bare body *)
    destruct (mem_no_red _ _ _ _ _ _ _ Hm0 Ht Hr) as (R0' & p & T & Φ & _ & _ & _ & _ & _ & HR0' & Hmd0 & _).
    destruct (mem_no_red _ _ _ _ _ _ _ Hm1 Ht Hr) as (R1' & p' & T' & Φ' & _ & _ & _ & _ & _ & HR1' & Hmd1 & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0' _ HR0) in Hmd0.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1' _ HR1) in Hmd1.
    assert (HR0m : mdesc_mod R0 = Some (mdesc_closed nil p' T' Φ' nil)) by congruence.
    eapply wf_exp_eq_trans; [ exact (mem_alias_filed _ _ _ _ _ _ _ _ _ _ _ HH0 HR0 HR0m Hm0 Ht) |].
    apply wf_exp_eq_sym; exact (mem_alias_filed _ _ _ _ _ _ _ _ _ _ _ HH1 HR1 Hmd1 Hm1 Ht).
Qed.

(** A term glued as the member of [H1] is glued as the member of a typed
    [H0] with the same module part, looked up alike, at the same type: the
    members are equal ([wf_exp_eq_mem_same_part]), read where the gluing
    is. *)
Lemma glu_elem_at_same_part : forall {Γ1 H0 H1 x R A' Δ σ1 a m R0 R1 Rm} {i : nat} {P El},
    gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ H0 ≈ H0 -> gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ H1 ≈ H1 ->
    mdenote gc_deps gc_stack Γ1 (me_mem H0 x) R ->
    mdenote gc_deps gc_stack Γ1 (me_mem H1 x) R ->
    mdesc_type R = Some A' ->
    mdenote gc_deps gc_stack Γ1 H0 R0 -> mdenote gc_deps gc_stack Γ1 H1 R1 ->
    mdesc_mod R0 = Some Rm -> mdesc_mod R1 = Some Rm ->
    Δ ⊢ˢ σ1 : Γ1 ->
    glu_elem_at Δ A'[σ1] (a_mem H1 x)[σ1] a m i P El ->
    glu_elem_at Δ A'[σ1] (a_mem H0 x)[σ1] a m i P El.
Proof.
  intros * HH0 HH1 Hm0 Hm1 HA HR0 HR1 E0 E1 Hσ [Hu HT HM].
  constructor; [ exact Hu | exact HT |].
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hu | exact HM |].
  apply wf_exp_eq_sym; cbn [exp_sub].
  eapply wf_exp_eq_mem_same_part;
    [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hσ) | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH1 Hσ)
    | eapply wf_sub_mdenote_mem; [ exact HH0 | exact Hm0 | exact Hσ ]
    | eapply wf_sub_mdenote_mem; [ exact HH1 | exact Hm1 | exact Hσ ]
    | eapply mdesc_type_sub; exact HA
    | eapply wf_sub_mdenote; [ exact HH0 | exact HR0 | exact Hσ ]
    | eapply wf_sub_mdenote; [ exact HH1 | exact HR1 | exact Hσ ]
    | rewrite (mdesc_mod_sub _ _ _ E0), (mdesc_mod_sub _ _ _ E1); reflexivity ].
Qed.

(** A typed module expression has a module part, the one of whatever it
    denotes. *)
Lemma modexp_mod_part : forall Γ H R, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R ->
    exists Rm, mdesc_mod R = Some Rm.
Proof.
  intros * HH Hm.
  destruct (me_denotes _ _ _ _ _ HH) as (R0 & Rm & Hm0 & HRm).
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ Hm) in HRm; eauto.
Qed.

(** A module value glued as [H1] is glued as a typed [H0] with the same
    module part both ways at every substitution, neither naming an open
    frame: as [glu_dmod_same_part], with no equation between them; the
    members are equal through the module part ([glu_elem_at_same_part]). *)
Lemma glu_dmod_same_part_typed :
  (forall Δ σ0 Γ0 H1 h, glu_dmod Δ σ0 Γ0 H1 h ->
     forall H0, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H0 -> same_part Γ0 H0 H1 -> same_part Γ0 H1 H0 ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> names_no_frame H0[ζ]ᵐ) ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> names_no_frame H1[ζ]ᵐ) ->
       glu_dmod Δ σ0 Γ0 H0 h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module *)
    intros * Hσ HH1 Hl Hlen Hdesc Hargs _ H0 HH Hs01 Hs10 Hq0 Hq1.
    (** The same module part, read off [H1[ζ]] *)
    assert (Hpart : forall Δ' φ Γ1 ζ σ1 RH, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
               mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH ->
               exists R1, mdenote gc_deps gc_stack Γ1 H1[ζ]ᵐ R1 /\ mdesc_mod R1 = mdesc_mod RH).
    { intros * Hst Hm.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      destruct (modexp_mod_part _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) Hm) as (Rm & HRm).
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (R1 & Hm1 & HR1m).
      exists R1; split; [ exact Hm1 | congruence ]. }
    eapply glu_dmod_global; [ exact Hσ | exact HH | exact Hl | exact Hlen | |].
    + intros * Hst Hm.
      destruct (Hpart _ _ _ _ _ _ Hst Hm) as (R1 & Hm1 & E1).
      rewrite <- E1; exact (Hdesc _ _ _ _ _ _ Hst Hm1).
    + intros * Hst Hm HNs.
      destruct (Hpart _ _ _ _ _ _ Hst Hm) as (R1 & Hm1 & E1).
      rewrite <- E1 in HNs; exact (Hargs _ _ _ _ _ _ _ Hst Hm1 HNs).
  - (** A body *)
    intros * Hσ HH1 Hmem Hsub IHsub H0 HH Hs01 Hs10 Hq0 Hq1.
    apply glu_dmod_body; [ exact Hσ | exact HH | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst Hm HA HS HAt.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      pose proof (same_denote_mem_part x Hs01 Hq0 _ _ _ Hζ Hm) as Hm1.
      destruct (Hg _ _ _ _ _ _ _ _ Hst Hm1 HA HS HAt) as (i & P & El & Hgl).
      exists i, P, El.
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) as HH0ζ.
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH1 Hζ) as HH1ζ.
      destruct (me_denotes _ _ _ _ _ HH0ζ) as (R0 & Rm & HR0 & HRm).
      destruct (Hs01 _ _ _ _ Hζ HR0 HRm) as (R1 & HR1 & HR1m).
      exact (glu_elem_at_same_part HH0ζ HH1ζ Hm Hm1 HA HR0 HR1 HRm HR1m (glu_sub_through_rest _ _ _ _ _ _ _ _ Hst) Hgl).
    + intros * Hp Hu Hb Hc.
      pose proof (Hsub _ _ _ _ _ _ _ Hp Hu Hb Hc) as Hg1.
      pose proof (same_denote_mem_part y Hs01 Hq0) as Hd01.
      pose proof (same_denote_mem_part y Hs10 Hq1) as Hd10.
      (** The selection from [H0] is typed: it denotes what the one from
          [H1] does *)
      assert (HHy : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H0 y).
      { assert (HHy1 : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H1 y ≈ me_mem H1 y) by (destruct Hg1; assumption).
        destruct (me_mod_tele_exists HHy1) as (R & T & HR & HT).
        assert (HR0 : mdenote gc_deps gc_stack Γ0 (me_mem H0 y) R).
        { pose proof (Hd10 _ Id R (wf_sub_id _ _ _ (presup_modexp_eq_ctx HH))) as Hd; rewrite !modexp_sub_id in Hd; exact (Hd HR). }
        eapply wf_me_mem; [ exact HH | exact HR0 | exact HT | exact HR0 | exact HT ]. }
      eapply IHsub; [ exact Hp | exact Hu | exact Hb | exact Hc | exact HHy
                    | exact (same_part_of_denote Hd01) | exact (same_part_of_denote Hd10)
                    | intros Γ2 ζ Hζ; apply names_no_frame_mem; [ exact (ctx_wf_gctx _ _ _ (wf_sub_cod _ _ _ _ _ Hζ)) | exact (Hq0 _ _ Hζ) ]
                    | intros Γ2 ζ Hζ; apply names_no_frame_mem; [ exact (ctx_wf_gctx _ _ _ (wf_sub_cod _ _ _ _ _ Hζ)) | exact (Hq1 _ _ Hζ) ] ].
  - (** A value lacking a parameter *)
    intros * Hσ HH1 Hn Hpar Happ IHapp H0 HH Hs01 Hs10 Hq0 Hq1.
    eapply glu_dmod_fun; [ exact Hσ | exact HH | exact Hn | | ].
    + intros * Hst Hm.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      destruct (modexp_mod_part _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) Hm) as (Rm & HRm).
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (RH1 & Hm1 & HRm1).
      destruct (Hpar _ _ _ _ _ _ Hst Hm1) as (T & B & T1 & [HT Hv Hgl]).
      exists T, B, T1; constructor; [| exact Hv | exact Hgl ].
      exact (mdesc_mod_tele_part _ _ _ HT (ex_intro _ Rm (conj HRm1 HRm))).
    + intros * Hst Hm HT Hv HS HB * Hu HP HN Hhc.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      assert (HRm : exists Rm, mdesc_mod RH = Some Rm)
        by (unfold mdesc_mod_tele in HT; destruct (mdesc_mod RH); [ eexists; reflexivity | discriminate ]).
      destruct HRm as [Rm HRm].
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (RH1 & Hm1 & HRm1).
      pose proof (mdesc_mod_tele_part _ _ _ HT (ex_intro _ Rm (conj HRm HRm1))) as HT1.
      pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hst Hm1 HT1 Hv HS HB _ _ _ _ _ _ Hu HP HN Hhc) as Hg1.
      pose proof (same_part_sub Hζ Hs01) as Hs01'; pose proof (same_part_sub Hζ Hs10) as Hs10'.
      eapply IHapp; [ exact Hst | exact Hm1 | exact HT1 | exact Hv | exact HS | exact HB | exact Hu | exact HP | exact HN
                    | exact Hhc | | exact (same_part_app_var _ _ Hs01') | exact (same_part_app_var _ _ Hs10')
                    | intros; apply names_no_frame_of_none; reflexivity | intros; apply names_no_frame_of_none; reflexivity ].
      (** The application of [H0] is typed: its premises are those of
          [H1]'s application, the module parts being the same *)
      assert (HHg : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_app H1[ζ]ᵐ[Wk]ᵐ #0 ≈ me_app H1[ζ]ᵐ[Wk]ᵐ #0)
        by (destruct Hg1; assumption).
      destruct (proj1 (modexp_gen _ _ _ _ _ HHg)) as [HH1w (R' & T' & B' & T1' & S' & HR' & HT' & Hv' & HB' & HS' & HN')].
      assert (HRm' : exists Rm', mdesc_mod R' = Some Rm')
        by (unfold mdesc_mod_tele in HT'; destruct (mdesc_mod R'); [ eexists; reflexivity | discriminate ]).
      destruct HRm' as [Rm' HRm'].
      destruct (Hs10' (Γ1 ▹{domain_kind a} B) Wk R' Rm' ltac:(eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg)) HR' HRm')
        as (R0 & HR0 & HRm0).
      pose proof (mdesc_mod_tele_part _ _ _ HT' (ex_intro _ Rm' (conj HRm' HRm0))) as HT0.
      assert (HHw : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ H0[ζ]ᵐ[Wk]ᵐ ≈ H0[ζ]ᵐ[Wk]ᵐ).
      { eapply sub_preserves_modexp; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) |].
        eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg). }
      eapply wf_me_app; [ exact HHw | exact HR0 | exact HT0 | exact Hv' | exact HB' | exact HS' | exact HN'
                        | apply wf_exp_eq_refl; exact HN' | exact HR0 | exact HT0 | exact Hv' | exact HB' | exact HS' | exact HN' ].
Qed.

(** A module description whose telescope has an outermost parameter
    takes the next argument. *)
Lemma mdesc_at_of_view : forall Γ R0m N T0 B T1, desc_ok gc_deps gc_stack Γ R0m -> mdesc_is_mod R0m ->
    mdesc_tele R0m = Some T0 -> tele_view T0 = Some (B, T1) ->
    exists R0m', mdesc_at R0m N = Some R0m'.
Proof.
  intros * Hok Hm HT Hv.
  destruct R0m as [| Δ Φw Φx | Θ p T Φ Ns |]; cbn in Hm; try contradiction; cbn [mdesc_at].
  - cbn in HT; injection HT as ->; unfold tele_view in Hv.
    destruct (tele_split (rev T0)) as [[[? ?] ?] | τ] eqn:Hs; [ eexists; reflexivity | exfalso ].
    inversion Hok; subst.
    destruct T0 as [| e T0' _] using rev_ind; [ discriminate |].
    match goal with Ha : all_assumptions (T0' ++ e :: nil) |- _ =>
      unfold all_assumptions in Ha; apply Forall_app in Ha as [_ Ha]; apply Forall_cons_iff in Ha as [(κ & X & ->) _] end.
    rewrite tele_split_last in Hs; discriminate.
  - destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; eexists; reflexivity.
Qed.

(** A selection from [X], then applied to [N], has the module part of
    the selection from [X] applied to [N], when [X], naming no open frame,
    has a next parameter: [X] given [N] takes the entry alike
    ([sel_at_open], [sel_at_closed]). *)
Lemma mdenote_mem_app_of_app_mem : forall Γ X N y R1 Rm1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ X ≈ X -> names_no_frame X ->
    (forall R0 T0, mdenote gc_deps gc_stack Γ X R0 -> mdesc_mod_tele R0 = Some T0 -> exists B T1, tele_view T0 = Some (B, T1)) ->
    mdenote gc_deps gc_stack Γ (me_app (me_mem X y) N) R1 -> mdesc_mod R1 = Some Rm1 ->
    exists R2, mdenote gc_deps gc_stack Γ (me_mem (me_app X N) y) R2 /\ mdesc_mod R2 = Some Rm1.
Proof.
  intros * HH Hq Hv Hm1 HRm1.
  pose proof (presup_modexp_eq_ctx HH) as HwΓ.
  pose proof (ctx_wf_gctx _ _ _ HwΓ) as Hg.
  pose proof (wf_gctx_closed _ _ _ HwΓ) as Hc.
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & _ & _).
  inversion Hm1 as [? ? ? ? ? Hq1 _ | ? ? ? ? ? ? ? ? ? Hq1 _ | | | ? ? ? Rsel ? Hsel Hat | | ? ? ? ? ? ? Hq1 _]; subst;
    try (cbn in Hq1; discriminate).
  (** The selection has a module part, as its application does *)
  assert (HRsel : exists Rsm, mdesc_mod Rsel = Some Rsm).
  { destruct (mdesc_mod Rsel) as [Rsm |] eqn:E; [ eauto |].
    rewrite (mdesc_at_no_mod _ _ _ E Hat) in HRm1; discriminate. }
  destruct HRsel as (Rsm & HRsel).
  apply (mdenote_mem_no_frame _ _ _ _ _ Hg Hq Hsel); intros R0 R0m Γy E rd R Hm0 HR0m He Hed Hrd.
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm0) HR0m) as Hok.
  pose proof (mdesc_mod_scoped _ _ _ (wf_mdenote_scoped _ _ _ _ _ _ HH Hm0) HR0m) as Hs0.
  pose proof (mdesc_mod_is_mod _ _ HR0m) as HisR0m.
  (** The module part of [X] takes [N] *)
  destruct (desc_ok_tele _ _ _ _ Hok HisR0m) as (T0 & HT0).
  destruct (Hv _ T0 Hm0 ltac:(unfold mdesc_mod_tele; rewrite HR0m; exact HT0)) as (B & T1 & HvT).
  destruct (mdesc_at_of_view _ _ N _ _ _ Hok HisR0m HT0 HvT) as (R0m' & HR0m').
  destruct (mdesc_at_of_mod_part _ _ _ _ HR0m HR0m') as (R0' & HR0' & HmR0').
  rewrite (mdesc_is_mod_mod _ (mdesc_at_is_mod _ _ _ HisR0m HR0m')) in HmR0'.
  assert (HmX : mdenote gc_deps gc_stack Γ (me_app X N) R0') by (eapply mdenote_app; eassumption).
  destruct R0m as [| Δ Φw Φx | Θ p T Φ Ns |]; cbn in HisR0m; try contradiction.
  - (** An open module *)
    inversion Hok; subst.
    destruct (sel_at_open _ _ Hc _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ Hs0 ltac:(assumption) HR0m' He Hed Hrd Hat)
      as (Γy' & E' & rd' & R' & He' & Hed' & Hrd').
    exists R1; split; [| exact HRm1 ].
    assert (Hpath : mdesc_entry_path R0m' y = None)
      by (cbn [mdesc_at] in HR0m'; destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?];
          [ injection HR0m' as <-; reflexivity | discriminate ]).
    eapply mdenote_mem; [ exact HmX | exact HmR0' | exact He' | rewrite Hpath; exact Hed' | exact Hrd' ].
  - (** A closed module *)
    inversion Hok; subst.
    match goal with Hg0 : ⊢ᵍ ?Θ0 ⍮ ?Ξ0, Hloc : loc ?Θ0 ?Ξ0 p T Φ |- _ =>
      pose proof (loc_coherent _ _ Hg0 _ _ _ Hloc) as Hco end.
    match goal with H : all_assumptions T |- _ => rename H into HTa end.
    match goal with H : all_assumptions Θ |- _ => rename H into HΘa end.
    destruct Hs0 as (_ & HU & _).
    pose proof (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU He) as (-> & _ & _).
    assert (Hlt : Θ = nil -> List.length Ns < List.length T).
    { intros ->; cbn in HT0; destruct (Nat.leb (List.length Ns) (List.length T)) eqn:Hle; [| discriminate ].
      injection HT0 as <-; apply Nat.leb_le in Hle.
      destruct (Nat.eq_dec (List.length Ns) (List.length T)) as [Heq |]; [| lia ].
      exfalso; rewrite Heq, Nat.sub_diag in HvT; cbn in HvT; discriminate. }
    destruct (sel_at_closed _ _ Hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hco HTa HU HΘa Hlt He Hed Hrd HRsel Hat)
      as (R0m'' & rd' & HR0m'' & He' & Rs'' & Hrd' & HRs'').
    rewrite HR0m' in HR0m''; injection HR0m'' as <-.
    exists Rs''; split; [| rewrite HRs''; exact HRm1 ].
    eapply mdenote_mem; [ exact HmX | exact HmR0' | exact He' | | exact Hrd' ].
    cbn [mdesc_at] in HR0m'; destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; injection HR0m' as <-; exact Hed.
Qed.

(** A closed module at arguments still lacking a parameter: the stored
    telescope split at the arguments, the rest instantiated by them being
    its telescope. *)
Lemma closed_tele_split : forall Θ p T Φ Ns T0 B0 T10,
    mdesc_tele (mdesc_closed Θ p T Φ Ns) = Some T0 -> tele_view T0 = Some (B0, T10) -> Θ = nil ->
    List.length Ns < List.length T /\
    T0 = tele_sub (List.firstn (List.length T - List.length Ns) T) (sb_of_list Id Ns).
Proof.
  intros * HT Hv ->; cbn in HT.
  destruct (Nat.leb (List.length Ns) (List.length T)) eqn:Hle; [| discriminate ].
  injection HT as <-; apply Nat.leb_le in Hle; rewrite app_nil_r in Hv |- *.
  split; [| reflexivity ].
  destruct (Nat.eq_dec (List.length Ns) (List.length T)) as [Heq |]; [| lia ].
  exfalso; rewrite Heq, Nat.sub_diag in Hv; cbn in Hv; discriminate.
Qed.

(** A closed module description over a stored telescope extending [T] by
    [Δ], given the arguments [Ns] for the outermost parameters of [T]: its
    telescope ends in the rest of [T] instantiated by them. *)
Lemma closed_ext_tele : forall pq Δ T Φ Ns k,
    k = List.length T - List.length Ns -> List.length Ns < List.length T ->
    exists Z, mdesc_tele (mdesc_closed nil pq (Δ ++ T) Φ Ns) =
      Some (Z ++ tele_sub (List.firstn k T) (sb_of_list Id Ns)).
Proof.
  intros * -> Hlt; cbn [mdesc_tele].
  rewrite length_app; replace (Nat.leb (List.length Ns) (List.length Δ + List.length T)) with true
    by (symmetry; apply Nat.leb_le; lia).
  replace (List.length Δ + List.length T - List.length Ns) with (List.length Δ + (List.length T - List.length Ns)) by lia.
  rewrite firstn_app_2, tele_sub_app, app_nil_r; eexists; reflexivity.
Qed.

(** The outermost parameter of a selection from a module lacking one is
    the module's: the selection's telescope extends the module's, the
    module's outside parameters, or, at a closed module given arguments,
    the rest of its stored telescope instantiated by them, which every
    stored entry with a module part extends ([gm_coherent]). *)
Lemma sel_view : forall Γ X y R0 R0m T0 B0 T10 Rsel T',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ X ≈ X -> names_no_frame X ->
    mdenote gc_deps gc_stack Γ X R0 -> mdesc_mod R0 = Some R0m -> mdesc_tele R0m = Some T0 ->
    tele_view T0 = Some (B0, T10) ->
    mdenote gc_deps gc_stack Γ (me_mem X y) Rsel -> mdesc_mod_tele Rsel = Some T' ->
    exists T1', tele_view T' = Some (B0, T1').
Proof.
  intros * HH Hq Hm0 HR0m HT0 Hv Hsel HT'.
  pose proof (presup_modexp_eq_ctx HH) as HwΓ.
  pose proof (ctx_wf_gctx _ _ _ HwΓ) as Hg.
  apply (mdenote_mem_no_frame _ _ _ _ _ Hg Hq Hsel); intros R0' R0m' Γy E rd R Hm0' HR0m' He Hed Hrd.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0' _ Hm0), HR0m in HR0m'; injection HR0m' as <-.
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm0) HR0m) as Hok.
  pose proof (mdesc_mod_scoped _ _ _ (wf_mdenote_scoped _ _ _ _ _ _ HH Hm0) HR0m) as Hs0.
  pose proof (mdesc_mod_is_mod _ _ HR0m) as HisR0m.
  destruct R0m as [| Δ Φw Φx | Θ p T Φ Ns |]; cbn in HisR0m; try contradiction.
  - (** An open module: the selection is abstracted over its parameters *)
    cbn in HT0; injection HT0 as <-.
    cbn in He; destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |]; try discriminate.
    destruct E0 as [[|] ? ? ? [] | | | |]; try discriminate; injection He as <- <- <-;
      cbn [mdesc_read] in Hrd; destruct (gm_fill Φ'); cbn [option_map] in Hrd; try discriminate; injection Hrd as <-;
      destruct (mdesc_mod_tele_up_inv _ _ _ HT') as (T0' & ->); exact (tele_view_app_r _ _ _ _ Hv).
  - pose proof (mdesc_entry_closed _ _ _ _ _ _ _ _ _ (proj1 (proj2 Hs0)) He) as (-> & HsE & ->).
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as <-.
    inversion Hok; subst.
    match goal with H : all_assumptions Θ |- _ => rename H into HΘa end.
    match goal with H : all_assumptions T |- _ => rename H into HTa end.
    destruct Θ as [| e Θr _] using rev_ind.
    + (** No outside parameter: the stored entry extends the stored
          telescope *)
      destruct (closed_tele_split _ _ _ _ _ _ _ _ HT0 Hv eq_refl) as (Hlt & ->).
      rewrite mdesc_up_nil in HT'; unfold mdesc_mod_tele in HT'; rewrite mdesc_mod_named in HT'.
      match goal with H : ⊢ᵍ ?Θ0 ⍮ ?Ξ0, Hl : loc ?Θ0 ?Ξ0 p T Φ, Hsub : gc_sub ?Θ0 ?Ξ0 _ _ |- _ =>
        rename H into Hg0; rename Hl into Hloc; rename Hsub into Hgs end.
      pose proof (loc_coherent _ _ Hg0 _ _ _ Hloc) as Hco.
      destruct Hs0 as (_ & [_ HbΦ] & _).
      pose proof He as He0; cbn in He0.
      destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
      injection He0 as <-.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & Hent); injection Heq as <- -> <-.
      pose proof (gm_coherent_prefix _ _ _ _ _ Hco Hp) as HcoE.
      cbn [mdesc_entry_path] in Hed.
      set (k := List.length T - List.length Ns) in *.
      (** The stored telescope split at the arguments *)
      assert (HTs : T = List.firstn k T ++ List.skipn k T) by (symmetry; apply firstn_skipn).
      assert (Hlk : List.length (List.skipn k T) = List.length Ns) by (rewrite length_skipn; unfold k; lia).
      assert (Hak : all_assumptions (List.skipn k T))
        by (pose proof HTa as Ha; rewrite HTs in Ha; unfold all_assumptions in Ha; apply Forall_app in Ha as [_ Ha]; exact Ha).
      (** A module part abstracted over the stored telescope extended,
          given the arguments, ends in the rest instantiated *)
      assert (Hup : forall Δ0 R' Rx, mdesc_is_mod R' -> mdesc_ats (mdesc_up (Δ0 ++ T) R') Ns = Some Rx ->
                 mdesc_tele Rx = Some T' -> exists Z, T' = Z ++ tele_sub (List.firstn k T) (sb_of_list Id Ns)).
      { intros * HR' Hx HTx.
        rewrite HTs, app_assoc, (mdesc_ats_up_prefix _ _ _ _ Hak Hlk) in Hx; injection Hx as <-.
        destruct (mdesc_tele_up_inv _ _ _ (mdesc_is_mod_sub _ _ HR') HTx) as (T0' & ->).
        rewrite tele_sub_app, app_assoc; eexists; reflexivity. }
      (** A closed module over the stored telescope extended, given the
          arguments *)
      assert (Hcl : forall pq Δ Φq, mdesc_tele (mdesc_closed nil pq (Δ ++ T) Φq Ns) = Some T' ->
                 exists Z, T' = Z ++ tele_sub (List.firstn k T) (sb_of_list Id Ns)).
      { intros * HTx; destruct (closed_ext_tele pq Δ T Φq Ns k eq_refl Hlt) as (Z & HZ).
        rewrite HZ in HTx; injection HTx as <-; eauto. }
      assert (Hext : exists Z, T' = Z ++ tele_sub (List.firstn k T) (sb_of_list Id Ns)).
      { destruct E0 as [b pv κ A M | pv [Δ [sm Φy | Ea]] | pv pq k' D ΦD | pv A M U | pv pr Rr ΦR];
          cbn [ge_read] in Hed.
        - (** a definition has no module part *)
          inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
          destruct (mdesc_ats_term _ _ _ _ _ Hats) as (? & ? & ->); discriminate.
        - (** a body submodule, stored closed *)
          pose proof (body_closed_entry_mod _ _ _ _ _ _ _ HbΦ Hent) as ->.
          inversion Hed; subst.
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
          match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
          cbn [mdesc_ats_read] in Hats; rewrite mdesc_ats_closed_nil in Hats; injection Hats as <-.
          cbn [mdesc_mod] in HT'; exact (Hcl _ _ _ HT').
        - (** an alias, over the stored telescope extended *)
          cbn [ge_coherent] in HcoE; destruct HcoE as (Δ0 & -> & _).
          inversion Hed; subst.
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
          match goal with Hmd : mdesc_mod ?RE = Some ?R' |- _ => pose proof (mdesc_mod_is_mod _ _ Hmd) as HR' end.
          rewrite (mdesc_ats_read_mod _ _ (mdesc_is_mod_up _ _ HR')) in Hats.
          assert (HR1 : mdesc_is_mod R1) by (eapply mdesc_ats_is_mod; [ apply mdesc_is_mod_up; exact HR' | exact Hats ]).
          rewrite (mdesc_is_mod_mod _ HR1) in HT'.
          exact (Hup _ _ _ HR' Hats HT').
        - (** a type former of a group: its module, filed below *)
          cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HuD & _) _].
          inversion Hed; subst.
          pose proof (gc_entry_selfpath _ _ Hg0 _ _ _ _ _ _ (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent)) as Hsp.
          match goal with Hpm : ind_mpath _ _ = Some ?pm, Hlm : gc_loc _ _ ?pm = Some _ |- _ =>
            rewrite (ind_selfpath_path _ _ _ _ Hsp) in Hpm; injection Hpm as <-;
            pose proof (gc_sub_body_eq _ _ _ _ _ _ _ Hgs (loc_child_ind _ _ Hg0 _ _ _ _ _ _ _ _ _ Hloc Hent)) as Hb';
            unfold gc_loc in Hlm; rewrite (gc_body_not_frame _ _ _ _ Hb'), Hb' in Hlm; injection Hlm as <- <- end.
          unfold ind_former_desc in Hats; cbn [mdesc_ats_read] in Hats.
          destruct (mdesc_term_part_ats _ Ns) as [[? ? [?|] | | |] |]; try discriminate.
          rewrite mdesc_ats_closed_nil in Hats; injection Hats as <-.
          cbn [mdesc_mod] in HT'; rewrite HuD in HT'; exact (Hcl _ _ _ HT').
        - (** a definition with a module part: its module part, an alias *)
          cbn [ge_coherent] in HcoE; destruct HcoE as [_ (Δ0 & Ea & -> & _)].
          inversion Hed; subst.
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
          match goal with Hmd : mdesc_mod ?RE = Some ?R' |- _ => pose proof (mdesc_mod_is_mod _ _ Hmd) as HR' end.
          cbn [mdesc_ats_read] in Hats.
          destruct (mdesc_term_part_ats _ Ns) as [[? ? [?|] | | |] |]; try discriminate.
          destruct (mdesc_ats (mdesc_up (Δ0 ++ T) _) Ns) as [Rx |] eqn:Hx; [ injection Hats as <- | discriminate ].
          cbn [mdesc_mod] in HT'.
          assert (HRx : mdesc_is_mod Rx) by (eapply mdesc_ats_is_mod; [ apply mdesc_is_mod_up; exact HR' | exact Hx ]).
          rewrite (mdesc_is_mod_mod _ HRx) in HT'.
          exact (Hup _ _ _ HR' Hx HT').
        - (** a record type: its module, filed below *)
          cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HpR & HΔ0) _].
          inversion Hed; subst.
          match goal with Hlm : gc_loc _ _ (qname_in p y) = Some _ |- _ =>
            pose proof (gc_sub_body_eq _ _ _ _ _ _ _ Hgs (loc_child_record _ _ Hg0 _ _ _ _ _ _ _ _ Hloc Hent)) as Hb';
            unfold gc_loc in Hlm; rewrite (gc_body_not_frame _ _ _ _ Hb'), Hb' in Hlm; injection Hlm as <- <- end.
          unfold record_former_desc in Hats; cbn [mdesc_ats_read] in Hats.
          destruct (mdesc_term_part_ats _ Ns) as [[? ? [?|] | | |] |]; try discriminate.
          rewrite mdesc_ats_closed_nil in Hats; injection Hats as <-.
          cbn [mdesc_mod] in HT'.
          destruct (record_mod_tele_split pr Rr _ _ HpR HΔ0) as (Hrt & _); rewrite Hrt in HT'.
          exact (Hcl _ _ _ HT'). }
      destruct Hext as (Z & ->).
      exact (tele_view_app_r _ _ _ _ Hv).
    + (** The outermost outside parameter *)
      unfold all_assumptions in HΘa; apply Forall_app in HΘa as [_ He1]; apply Forall_cons_iff in He1 as [(κ & B & ->) _].
      destruct (mdesc_mod_tele_up_inv _ _ _ HT') as (T0' & ->).
      cbn [mdesc_tele] in HT0.
      destruct (Nat.leb (List.length Ns) (List.length T)); [ injection HT0 as <- | discriminate ].
      rewrite app_assoc, tele_view_last in Hv; injection Hv as <- _.
      rewrite app_assoc, tele_view_last; eexists; reflexivity.
Qed.

(** A typed module expression whose telescope has an outermost parameter
    has one at every typed substitution. *)
Lemma tele_view_under_sub : forall Γ X,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ X ≈ X ->
    (forall R0 T0, mdenote gc_deps gc_stack Γ X R0 -> mdesc_mod_tele R0 = Some T0 -> exists B T1, tele_view T0 = Some (B, T1)) ->
    forall Γ' ζ, Γ' ⊢ˢ ζ : Γ ->
    forall R0 T0, mdenote gc_deps gc_stack Γ' X[ζ]ᵐ R0 -> mdesc_mod_tele R0 = Some T0 -> exists B T1, tele_view T0 = Some (B, T1).
Proof.
  intros * HH Hv * Hζ * Hm HT.
  destruct (me_mod_tele_exists HH) as (RX & TX & HmX & HTX).
  destruct (Hv _ _ HmX HTX) as (B & T1 & HvX).
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HH HmX Hζ) as HmXζ.
  pose proof (ctx_wf_gctx _ _ _ (wf_sub_dom _ _ _ _ _ Hζ)) as Hg.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ HmXζ) in HT.
  rewrite (mdesc_mod_tele_sub _ _ ζ _ (wf_mdenote_scoped _ _ _ _ _ _ HH HmX) HTX) in HT; injection HT as <-.
  rewrite tele_view_sub, HvX; cbn; eauto.
Qed.

(** The selection from [X] applied to [N] and the selection from [X]
    given [N] have the same module part both ways, when [X] has a next
    parameter and names no open frame at any substitution, the former
    being typed ([mdenote_mem_app_of_app_mem]). *)
Lemma same_part_app_mem : forall Γ X y N,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ X ≈ X ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app (me_mem X y) N ≈ me_app (me_mem X y) N ->
    (forall Γ' ζ, Γ' ⊢ˢ ζ : Γ -> names_no_frame X[ζ]ᵐ) ->
    (forall R0 T0, mdenote gc_deps gc_stack Γ X R0 -> mdesc_mod_tele R0 = Some T0 -> exists B T1, tele_view T0 = Some (B, T1)) ->
    same_part Γ (me_mem (me_app X N) y) (me_app (me_mem X y) N) /\ same_part Γ (me_app (me_mem X y) N) (me_mem (me_app X N) y).
Proof.
  intros * HX HK Hq Hv; split; intros Γ' ζ R Rm Hζ Hm HRm; cbn [modexp_sub] in Hm |- *.
  - (** The application of the selection denotes, typed; so does the
        selection from the application, alike *)
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HK Hζ) as HKζ; cbn [modexp_sub] in HKζ.
    destruct (me_denotes _ _ _ _ _ HKζ) as (R1 & Rm1 & Hm1 & HRm1).
    destruct (mdenote_mem_app_of_app_mem _ _ _ _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HX Hζ) (Hq _ _ Hζ)
                (tele_view_under_sub _ _ HX Hv _ _ Hζ) Hm1 HRm1) as (R2 & Hm2 & HRm2).
    pose proof (ctx_wf_gctx _ _ _ (wf_sub_dom _ _ _ _ _ Hζ)) as Hg.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm2 _ Hm) in HRm2.
    exists R1; split; [ exact Hm1 | congruence ].
  - exact (mdenote_mem_app_of_app_mem _ _ _ _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HX Hζ) (Hq _ _ Hζ)
             (tele_view_under_sub _ _ HX Hv _ _ Hζ) Hm HRm).
Qed.

(** A value lacking a parameter whose selection is applied is applied
    itself. *)
Lemma appm_of_selm_appm : forall h a, next_param h a -> forall y r c rc,
    h ·ₘ y gc_deps ⍮ gc_stack ↘ r -> $ᵐ| r & c | gc_deps ⍮ gc_stack ↘ rc ->
    exists hc, $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc.
Proof.
  intros * Hn * Hs Hr; inversion Hs; subst.
  - eexists; constructor.
  - eexists; constructor.
  - inversion Hr; subst; eauto.
  - exfalso; eapply next_param_body_nil; exact Hn.
  - inversion Hr; subst.
    match goal with Hc : eval_selmc _ _ _ (_ ++ _) _ |- _ => apply eval_selmc_snoc_inv in Hc as (h1 & Hc0 & _) end.
    eexists; econstructor; eassumption.
Qed.

(** The selections of glued module values are glued, given the case of a
    saturated global module ([glu_dmod_sel_global] supplies it): from a
    body, by its submodule clause; from a value lacking a parameter, by
    recursion through its applications, the selection from the
    application moved to the application of the selection
    ([same_part_app_mem]). *)
Lemma glu_dmod_sel_of_global :
    ⊢ᵍ gc_deps ⍮ gc_stack ->
    (forall Δ σ0 Γ0 H0 p T Φ args y r,
       Δ ⊢ˢ σ0 : Γ0 -> gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H0 ->
       gc_loc gc_deps gc_stack p = Some (T, Φ) -> List.length args = List.length T ->
       (forall Δ' φ Γ1 ζ σ1 RH, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
          mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH -> exists Ns1, mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1)) ->
       (forall Δ' φ Γ1 ζ σ1 RH Ns1, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
          mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
          glu_tele_args Δ' (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args) ->
       dm_global p args ·ₘ y gc_deps ⍮ gc_stack ↘ r ->
       gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H0 y ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> names_no_frame H0[ζ]ᵐ) ->
       glu_dmod Δ σ0 Γ0 (me_mem H0 y) r) ->
    (forall Δ σ0 Γ0 H0 h, glu_dmod Δ σ0 Γ0 H0 h ->
       forall y r, h ·ₘ y gc_deps ⍮ gc_stack ↘ r ->
       gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H0 y ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> names_no_frame H0[ζ]ᵐ) ->
       glu_dmod Δ σ0 Γ0 (me_mem H0 y) r) /\
    (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  intros Hgw Hglob.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A saturated global module *)
    intros * Hσ HH0 Hl Hlen Hd Ha _ y r Hs HHy Hq.
    exact (Hglob _ _ _ _ _ _ _ _ _ _ Hσ HH0 Hl Hlen Hd Ha Hs HHy Hq).
  - (** A body: its submodule clause *)
    intros * Hσ HH0 Hmem Hsub _ y r Hs HHy Hq.
    inversion Hs; subst; [ exfalso; match goal with Hl : 0 < length nil |- _ => cbn in Hl; lia end |].
    eapply Hsub; eassumption.
  - (** A value lacking a parameter *)
    intros * Hσ HH0 Hn Hpar Happ IHapp y r Hs HHy Hq.
    eapply glu_dmod_fun with (a := a); [ exact Hσ | exact HHy | exact (next_param_selm Hgw _ _ Hn _ _ Hs) | | ].
    + (** The selection lacks the module's next parameter *)
      intros * Hst Hm; cbn [modexp_sub] in Hm.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) as HH0ζ.
      destruct (me_denotes _ _ _ _ _ HH0ζ) as (R0 & R0m & Hm0 & HR0m).
      destruct (Hpar _ _ _ _ _ _ Hst Hm0) as (T0 & B0 & T10 & [HT0 Hv0 Hgl0]).
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HHy Hζ) as HHyζ; cbn [modexp_sub] in HHyζ.
      destruct (me_mod_tele_exists HHyζ) as (RS & TS & HmS & HTS).
      pose proof (ctx_wf_gctx _ _ _ (wf_sub_cod _ _ _ _ _ (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst))) as Hg.
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmS _ Hm) in HTS.
      unfold mdesc_mod_tele in HT0; rewrite HR0m in HT0.
      destruct (sel_view _ _ _ _ _ _ _ _ _ _ HH0ζ (Hq _ _ Hζ) Hm0 HR0m HT0 Hv0 Hm HTS) as (T1' & HvS).
      exists TS, B0, T1'; constructor; [ exact HTS | exact HvS | exact Hgl0 ].
    + (** Applied, as the selection from the application *)
      intros * Hst Hm HT Hv HS HB N c rc i P El Hu HP HN Hrc; cbn [modexp_sub] in Hm |- *.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) as HH0ζ.
      destruct (me_denotes _ _ _ _ _ HH0ζ) as (R0 & R0m & Hm0 & HR0m).
      destruct (Hpar _ _ _ _ _ _ Hst Hm0) as (T0 & B0 & T10 & [HT0 Hv0 _]).
      (** The parameter is the module's *)
      assert (HT0' : mdesc_tele R0m = Some T0) by (unfold mdesc_mod_tele in HT0; rewrite HR0m in HT0; exact HT0).
      destruct (sel_view _ _ _ _ _ _ _ _ _ _ HH0ζ (Hq _ _ Hζ) Hm0 HR0m HT0' Hv0 Hm HT) as (T1' & HvS).
      rewrite Hv in HvS; injection HvS as <- _.
      (** The module applied, and its selection *)
      destruct (appm_of_selm_appm _ _ Hn _ _ _ _ Hs Hrc) as (hc & Hhc).
      pose proof (proj1 (selm_appm_comm _ _ Hn _ _ _ _ Hs Hhc rc) Hrc) as Hsc.
      pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hst Hm0 HT0 Hv0 HS HB _ _ _ _ _ _ Hu HP HN Hhc) as Hg1.
      assert (HHg : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_app H0[ζ]ᵐ[Wk]ᵐ #0 ≈ me_app H0[ζ]ᵐ[Wk]ᵐ #0)
        by (destruct Hg1; assumption).
      destruct (proj1 (modexp_gen _ _ _ _ _ HHg)) as [HHw (R' & T' & B' & T1'' & S' & HR' & HT'' & Hv' & HB' & HS' & HN')].
      pose proof (presup_modexp_eq_ctx HHg) as HwΓb.
      assert (HWk : Γ1 ▹{domain_kind a} B ⊢ˢ Wk : Γ1) by (eapply wf_sub_shift; exact HwΓb).
      (** The selection from the module weakened, typed *)
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HHy Hζ) HWk) as HHyX.
      cbn [modexp_sub] in HHyX.
      destruct (me_mod_tele_exists HHyX) as (RS & TS & HmS & HTS).
      assert (HqX : forall Γ' ζ', Γ' ⊢ˢ ζ' : Γ1 ▹{domain_kind a} B -> names_no_frame H0[ζ]ᵐ[Wk]ᵐ[ζ']ᵐ).
      { intros Γ' ζ' Hζ'; rewrite !modexp_sub_sub; eapply Hq.
        repeat first [ eassumption | eapply wf_sub_compose ]. }
      pose proof (HqX _ Id (wf_sub_id _ _ _ HwΓb)) as HqX0; rewrite modexp_sub_id in HqX0.
      destruct (modexp_mod_part _ _ _ HHw HR') as (R'm & HR'm).
      assert (HT'm : mdesc_tele R'm = Some T') by (unfold mdesc_mod_tele in HT''; rewrite HR'm in HT''; exact HT'').
      destruct (sel_view _ _ _ _ _ _ _ _ _ _ HHw HqX0 HR' HR'm HT'm Hv' HmS HTS) as (T1s & HvSX).
      (** The application of the selection, typed *)
      assert (HK : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_app (me_mem H0[ζ]ᵐ[Wk]ᵐ y) #0 ≈ me_app (me_mem H0[ζ]ᵐ[Wk]ᵐ y) #0)
        by (eapply wf_me_app; [ exact HHyX | exact HmS | exact HTS | exact HvSX | exact HB' | exact HS' | exact HN'
                              | apply wf_exp_eq_refl; exact HN' | exact HmS | exact HTS | exact HvSX | exact HB' | exact HS' | exact HN' ]).
      assert (HvX : forall R0 T0, mdenote gc_deps gc_stack (Γ1 ▹{domain_kind a} B) H0[ζ]ᵐ[Wk]ᵐ R0 -> mdesc_mod_tele R0 = Some T0 ->
                 exists B T1, tele_view T0 = Some (B, T1)).
      { intros * Hx Ht.
        rewrite (proj1 (mdenote_functional_all _ _ (ctx_wf_gctx _ _ _ HwΓb)) _ _ _ Hx _ HR'), HT'' in Ht; injection Ht as <-; eauto. }
      destruct (same_part_app_mem _ _ y #0 HHw HK HqX HvX) as [HsAK HsKA].
      (** The selection from the application, typed: it denotes the
          application of the selection's module part *)
      destruct (me_mod_tele_exists HK) as (RK & TK & HmK & HTK).
      destruct (modexp_mod_part _ _ _ HK HmK) as (RKm & HRKm).
      destruct (mdenote_mem_app_of_app_mem _ _ _ _ _ _ HHw HqX0 HvX HmK HRKm) as (RA & HmA & HRAm).
      pose proof (mdesc_mod_tele_part _ _ _ HTK (ex_intro _ RKm (conj HRKm HRAm))) as HTA.
      assert (HA : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_mem (me_app H0[ζ]ᵐ[Wk]ᵐ #0) y ≈ me_mem (me_app H0[ζ]ᵐ[Wk]ᵐ #0) y)
        by (eapply wf_me_mem; [ exact HHg | exact HmA | exact HTA | exact HmA | exact HTA ]).
      (** By recursion, then moved *)
      pose proof (IHapp _ _ _ _ _ _ _ _ _ _ Hst Hm0 HT0 Hv0 HS HB _ _ _ _ _ _ Hu HP HN Hhc y rc Hsc HA) as HgA.
      eapply (proj1 glu_dmod_same_part_typed); [ apply HgA | exact HK | exact HsKA | exact HsAK | | ];
        intros; apply names_no_frame_of_none; reflexivity.
      Unshelve. all: intros; apply names_no_frame_of_none; reflexivity.
Qed.

End Fixed_GCtx.
